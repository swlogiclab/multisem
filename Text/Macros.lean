import Lean
import Lean.Syntax
open Lean Meta Std
syntax (priority := high) "{{" term,+ "}}" : term
macro_rules
  | `({{ $x }}) => `([$x])
  | `({{ $x, $xs:term,* }}) => `([$x] ++ {{$xs,*}})

def chk0 : {{ "hello" }} = ["hello"] := by rfl
def chk1 : {{ "hello","there"}} = ["hello"]++["there"] := by rfl


syntax (priority := high) "&&" ident,+ "&&" : term
macro_rules
  | `(&& $x &&) => `([$x])
  | `(&& $x, $xs:ident,* &&) => `([$x] ++ {{$xs,*}})

-- Works, which is weird since hello is not bound?
def chk2 : && hello && = [hello] := by rfl

#check Lean.Syntax.ident
#print Lean.Syntax
#print Lean.Name
#print Lean.Syntax.CharLit
#print Lean.Syntax.mkStrLit
#print optParam
syntax (name := customParser) "^^" ident,+ "^^" : term
@[macro customParser] def implCustomParser : Lean.Macro :=
  fun stx =>
    let val := stx;
    let arg0 := Lean.Syntax.getArg val 1;
    do
      let info <- Lean.MonadRef.mkInfoFromRefPos;
      match arg0 with
      | Lean.Syntax.ident _ _ (Lean.Name.str _ txt) _ =>
        --pure (Lean.Syntax.ident info (String.toSubstring txt) [])
        pure (Lean.Syntax.mkStrLit txt)
      | _ => pure arg0--throw Lean.Macro.Exception.unsupportedSyntax
-- There's no convenient way to make a string from an ident
-- I could write a function from strings to a Syntax term
-- that explicitly uses String.mk, List.cons, List.nil
-- Not ideal but would get the job done
-- The only problem with this is that I'm not sure it would unify

set_option pp.rawOnError true   
def x : String := ^^ hello ^^

-- Apparently there's also a @[reducible] annotation that
-- marks a function transparent to TC resolution

class Good (s:String) where
  blah : Unit
instance g1 : Good (String.mk ['1']) where 
  blah := ()
def onlyGood (s:String)[Good s] : String := s
-- next line Failed to synthesize instance Good "1"
theorem chk : onlyGood "1" = String.mk ['1'] := by rfl
-- but
theorem but : "1" = String.mk ['1'] := by rfl
-- This is a problem b/c I want to do some manipulation of the inner string / construct human-meaningful strings in macros and have them unify with literals

syntax (name := myExfalsoParser) "myExfalso" : tactic
-- remember that `Macro` is a synonym for `Syntax -> TacticM Unit`
@[macro myExfalsoParser] def implMyExfalso : Lean.Macro :=
fun stx => `(tactic| apply False.elim)
example (p : Prop) (h : p) (f : p -> False) : 3 = 2 := by
  myExfalso
  exact f h

-- Okay, so this works, but moving to ident,+ changes the arg structure and argument 1 doesn't mean the same thing anymore
syntax (name := myStringMakerParser) "myStringMaker" ident : term
@[macro myStringMakerParser] def implMyStringMaker : Lean.Macro :=
  fun stx =>
    let val := stx;
    let arg0 := Lean.Syntax.getArg val 1;
    do
      let info <- Lean.MonadRef.mkInfoFromRefPos;
      match arg0 with
      | Lean.Syntax.ident _ _ (Lean.Name.str _ txt) _ =>
        --pure (Lean.Syntax.ident info (String.toSubstring txt) [])
        pure (Lean.Syntax.mkStrLit txt)
      | _ => pure (arg0) --throw Lean.Macro.Exception.unsupportedSyntax
set_option pp.rawOnError true   
def blah := myStringMaker asdf
theorem chk3 : myStringMaker asdf = "asdf" := by rfl

#print Lean.SyntaxNodeKinds

#print Lean.Macro
#print Lean.Syntax.Term
#print Lean.TSyntax
#print Lean.Term
#print Lean.Expr
#print SyntaxNodeKind
def buildAppend (stx: Lean.Syntax) (l:List Lean.Syntax) : Lean.MacroM (Lean.TSyntax `term) :=
  match l with
  | [] => throw (Lean.Macro.Exception.error stx "Must have at least one word")
  | x::[] => match x with
             | Lean.Syntax.ident _ _ (Lean.Name.str _ txt) _ =>
               pure (Lean.Syntax.mkCApp `List.cons #[Lean.Syntax.mkStrLit txt, Lean.Syntax.mkCApp `List.nil #[]])
               --pure (Lean.Syntax.node Lean.SourceInfo.none `Lean.Parser.)
               --pure (mkApp (mkApp (mkConst `List.cons) (mkStrLit txt)) (mkConst `List.empty))
               --(Lean.Syntax.node Lean.SourceInfo.none 
               --       `List.cons #[(Lean.Syntax.mkStrLit txt) `List.empty])
             | _ => pure (Lean.Syntax.mkStrLit (toString x))
  | x::xs => 
    do
      let rhs <- buildAppend stx xs;
      match x with
      | Lean.Syntax.ident _ _ (Lean.Name.str _ txt) _ =>
        pure (Lean.Syntax.mkCApp `List.cons #[Lean.Syntax.mkStrLit txt, rhs])
      | _ => throw (Lean.Macro.Exception.error stx "Only individual words are valid")

syntax (name := splitParser) "split" ident+ "done": term
@[macro splitParser] def implSplitParser : Lean.Macro :=
  fun stx =>
    let val := stx;
    let argc := Lean.Syntax.getNumArgs stx;
    let text := Lean.Syntax.getArg stx 1;
    let stext := toString text;
    let words := String.splitOn stext " ";
    do
      let info <- Lean.MonadRef.mkInfoFromRefPos;
      match text with
      | Lean.Syntax.node _ _ mid => buildAppend stx mid.data
      | _ => pure (Lean.Syntax.mkNumLit (toString argc))
      --pure (Lean.Syntax.mkStrLit stext)
#print List
def blahh := split asdf asdf2 done
#eval blahh