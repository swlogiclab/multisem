import Lean
import Lean.Syntax
open Lean Meta Std

inductive ContextTree (A:Type) where
  | one : A -> ContextTree A
  | comp : ContextTree A -> ContextTree A -> ContextTree A
instance {A:Type} : Coe A (ContextTree A) where
  coe a := ContextTree.one a
notation:64 x "#" y => ContextTree.comp x y
deriving instance Repr for ContextTree

def buildAppend (stx: Lean.Syntax) (l:List Lean.Syntax) : Lean.MacroM (Lean.TSyntax `term) :=
  match l with
  | [] => throw (Lean.Macro.Exception.error stx "Must have at least one word")
  | x::[] => match x with
             | Lean.Syntax.ident _ _ (Lean.Name.str _ txt) _ =>
               pure (Lean.Syntax.mkCApp `ContextTree.one #[Lean.Syntax.mkStrLit txt])
             | _ => --pure (Lean.Syntax.mkStrLit (toString x))
               throw  (Lean.Macro.Exception.error stx "Only individual words are valid")
  | x::xs => 
    do
      let rhs <- buildAppend stx xs;
      match x with
      | Lean.Syntax.ident _ _ (Lean.Name.str _ txt) _ =>
        pure (Lean.Syntax.mkCApp `ContextTree.comp #[Lean.Syntax.mkStrLit txt, rhs])
      | _ => throw (Lean.Macro.Exception.error stx "Only individual words are valid")

syntax (name := splitParser) "[|" ident+ "|]": term
@[macro splitParser] def implSplitParser : Lean.Macro :=
  fun stx =>
    let val := stx;
    let argc := Lean.Syntax.getNumArgs val;
    let text := Lean.Syntax.getArg val 1;
    --let stext := toString text;
    --let words := String.splitOn stext " ";
    do
      --let info <- Lean.MonadRef.mkInfoFromRefPos;
      match text with
      | Lean.Syntax.node _ _ mid => buildAppend val mid.data
      | _ => pure (Lean.Syntax.mkNumLit (toString argc))
      --pure (Lean.Syntax.mkStrLit stext)
def blahh := [| four equals four |]
#print blahh
--#eval blahh
theorem blahhh : blahh = "four"#("equals"#"four") := by rfl