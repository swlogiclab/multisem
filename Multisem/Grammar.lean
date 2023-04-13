import Multisem.HeytingAlgebras
import Multisem.TemporalLogic
--import Multisem.Text.Macros

-- Need this to do #eval
import Lean

universe u v t

/--
The enumeration of supported prepositional phrase varieties for English
-/
inductive PPType : Type := | IN | INTO | TO | FROM | OF | OFN
deriving instance Repr for PPType
inductive Cat.{q} : Type (q+1)  :=
| S : Cat
| NP : forall {x:Type q}, Cat
| ADJ : forall {x:Type q}, Cat
| CN : forall {x:Type q}, Cat
| PP : forall {x:Type q}, PPType -> Cat
| Ref : Cat -> Cat -> Cat
| rslash : Cat  -> Cat  -> Cat 
| lslash : Cat  -> Cat  -> Cat 
| Var : forall {x:Type q}, String -> Cat
open Cat

-- These are some currently-disabled notations for writing the slashes
-- At the moment we can't get lexicon entries working with a mix of explicit and notation-based categories, which we need for backwards compat right now
-- We can allow writing right slashes by implementing Div for Cat
/- 
  We're dropping the div typeclass instance. Going this route adds noticeable overhead,
  so we've been using the custom `//` notation below, but leaving this instance open
  has caused issues with accidentally using `/` instead of `//` in lexicon entries,
  which then takes forever to track down...
-/
--instance CatDiv.{q} : Div (Cat.{q}) where
--  div := rslash

-- This is probably not best practice, but we really do need typeclass resolution to unfold these right now. Later if we are more uniform in using the notations for lexicon entries, we could probably remove these attribute overrides.
--attribute [simp] HDiv.hDiv
--attribute [simp] Div.div

--theorem _checkCatDiv : (S / (@NP Nat)) = rslash S (@NP Nat) := by simp
-- We also want to write left slashes
class LDiv.{q} (α : Type q) where
  lDiv : α → α → α
attribute [simp] LDiv.lDiv

-- CRITICAL: This is not simply backslash, but \setminus! Lean reserves the backslash character because it's used by all Lean editors for unicode lead character
/-- The idiomatic way to do operator overloading in Lean
    is to define the operator as a typeclass operation.
    When we do this for both left and right slash, it nearly doubles
    parse times. Defining ∖ directly in terms of `lslash` recovers half that slow-down. Can we redefine the / macro to avoid `HDiv`?
-/
infixr:70 " ∖ " => lslash --LDiv.lDiv
infixr:70 " // " => rslash --LDiv.lDiv
--macro_rules |  `($x ∖ $y) => `(binop% lslash $x $y)--`(binop% LDiv.lDiv $x $y)
--macro_rules |  `($x // $y) => `(binop% rslash $x $y)--`(binop% LDiv.lDiv $x $y)

instance CatLDiv.{q} : LDiv (Cat.{q}) where
  lDiv := lslash
theorem _checkCatLDiv : ((@NP Nat) ∖ S) = lslash (@NP Nat) S := by rfl
instance CatMod.{q} : Mod (Cat.{q}) where
  mod := Ref

-- This deriving breaks if any of the category instances are explicit arguments, because in general it cannot print types (or function expressions)
--deriving instance Repr for Cat
def catrepr (c:Cat) : Lean.Format :=
    match c with
    | S => "S" | NP => "NP" | ADJ => "ADJ" | CN => "CN" 
    | PP pp => "PP["++(Repr.reprPrec pp 0)++"]"
    | Ref l r => "("++(catrepr l)++" % "++(catrepr r)++")"
    | rslash l r => "("++(catrepr l)++" / "++(catrepr r)++")"
    | lslash l r => "("++(catrepr l)++" \\ "++(catrepr r)++")"
    | Var v => "$"++v
instance catRepr : Repr Cat where
  reprPrec c _n := catrepr c


#eval reprPrec (rslash (lslash S S) S) 234
#eval (rslash (lslash (@NP Nat) S) (@ADJ Nat))

--axiom polyunit.{α} : Type α
--axiom pu.{α} : polyunit.{α}

-- Would like to use this def, but there's a bug in m4, fixed in nightly: https://github.com/leanprover/lean4/commit/fb45eb49643b2abbc0d057d1fafc5e1eb419fc2a
--inductive polyunit.{α} : Type α where
--| pu : polyunit
def polyunit.{α} : Type α := ULift Unit
def pu.{α} : polyunit.{α} := ULift.up ()

-- We do Lambek-style interpretation of lslash
@[simp]
def interp.{q} (P:Type q) (c:Cat.{q}) : Type q :=
  match c with
  | S => P
  | @NP x => x
  | @Var x _ => x
  | @ADJ x => x -> P
  | rslash a b => interp P b -> interp P a
  | lslash a b => interp P a -> interp P b
  | Ref a b => interp P b -> interp P a
  | @CN x => x -> P
  -- The variety of prepositional phrase has not semantic content, they're basically syntactic tags for disambiguation
  | @PP x PPType.OFN => x -> P -- This is a bit of a hack to make stuff like "of naturals" work, but I haven't found a clear discussion of "of CN" in the literature yet
  | @PP x _ => x

class Coordinator (P:Type u)[HeytingAlgebra P](w:String) where
  denoteCoord : P -> P -> P
attribute [simp] Coordinator.denoteCoord

class SurfaceHeytingAlgebra (P:Type u) (n:Nat) (C:Cat.{u}) where
  combineProps : (P -> P -> P) -> interp P C -> interp P C -> interp P C
attribute [simp] SurfaceHeytingAlgebra.combineProps


-- TODO: Study how to rework combineProps in terms of pointwise lifting
-- These aren't quite homomorphisms. We're not being asked to embed,
-- e.g., a conjunction of Ps into X->P. We're being asked to use
-- the ability to conjoin Ps to conjoin X->Ps.
-- This isn't quite the (pointwise lifting) homomorphism, but instead
-- an embedding of the operation itself rather than the *result* of the operation
-- Are we dealing with a kind of adjunction between P and X->P? Maybe, but
-- while one direction of such an adjunction would certainly be the 
-- pointwise lifting, the other direction seems like it can't be defined 
-- without a spare X lying around, so it's not an adjunction.
-- And the partial adjunction that just maps ```λ_.h``` to h isn't related to this lifting. The solution is constrained by a kind of type-driven translation, but that's not an algebraic characterization of the resulting transformation.

-- But actually, the combineprops of both the ADJ and both slash cases are in fact following the template of the pointwise HA lifting, just with the concrete operation abstracted out!

instance ADJHeytingAlgebra (P:Type u)[HeytingAlgebra P]{T}{n} : SurfaceHeytingAlgebra P n (@ADJ T) where
  combineProps op d1 d2 := fun x => op (d1 x) (d2 x)

instance SHeytingAlgebra (P:Type u)[HeytingAlgebra P]{n} : SurfaceHeytingAlgebra P n S where
  combineProps op d1 d2 := op d1 d2

instance lSlashHeytingAlgebra (P:Type u)[HeytingAlgebra P]{n:Nat}(C C' : Cat)[SurfaceHeytingAlgebra P n C'] : SurfaceHeytingAlgebra P (Nat.succ n) (C ∖ C') where
  combineProps op d1 d2 := fun x => SurfaceHeytingAlgebra.combineProps n op (d1 x) (d2 x)

instance rSlashHeytingAlgebra (P:Type u)[HeytingAlgebra P]{n:Nat}(C C' : Cat)[SurfaceHeytingAlgebra P n C'] : SurfaceHeytingAlgebra P (Nat.succ n) (C' // C) where
  combineProps op d1 d2 := fun x => SurfaceHeytingAlgebra.combineProps n op (d1 x) (d2 x)

instance refHeytingAlgebra (P:Type u)[HeytingAlgebra P]{n:Nat}(C C' : Cat)[SurfaceHeytingAlgebra P n C'] : SurfaceHeytingAlgebra P (Nat.succ n) (C' % C) where
  combineProps op d1 d2 := fun x => SurfaceHeytingAlgebra.combineProps n op (d1 x) (d2 x)

class lexicon.{q} (P : Type q) (w:String) (c:Cat.{q}) where
  denotation : interp P c 
attribute [simp] lexicon.denotation

class NLVar (s:String) where

instance taggedLexVar.{q} {P:Type q} {T : Type q} (w:String) [NLVar w] : lexicon P w ((@NP T) % (@Var T w)) where
  denotation := λ x => x


instance coordLexicon (P:Type)[HeytingAlgebra P](w:String) (C:Cat)[Coordinator P w][SurfaceHeytingAlgebra P (Nat.succ (Nat.succ (Nat.succ Nat.zero))) C] : lexicon P w (C ∖ (C // C)) where
  denotation := fun L R => SurfaceHeytingAlgebra.combineProps 3 (Coordinator.denoteCoord w) L R
-- We don't need the other associativity, as it can be recovered by shifting



-- TODO: Name the lexicon instances introduced with this macro
-- TODO: Allow the macro to enter arbitrary expressions (makes naming harder)
-- TODO: Add support for HA-polymorphic lexicon entries at all levels (currently we only get Type)

-- For now, this will do. It's not ideal because the instance is unnamed, which will make some things harder to debug when stuff goes wrong, but this is a workable solution in the medium-term
macro "lex" n:ident "for" P:term "as" c:term : command => 
  let s := n.getId.toString
  -- This id has type Lean.Ident (no surprise given the construtor), but splicing it in as the instance name with $(id) calls .raw, which requires
  -- an argument of type Lean.TSyntax `Lean.Parser.Command.namedPrio
  -- Need to read more of the metaprogramming book https://github.com/arthurpaulino/lean4-metaprogramming-book to figure this out
  let id := (Lean.mkIdent (s ++ "_lex_"))
`(
  instance : lexicon $(P) $(Lean.quote s) $(c) := { denotation := $(n) }
)
macro "anylex" n:ident "as" c:term : command => 
  let s := n.getId.toString
`(
  instance {T : Type}[HA:HeytingAlgebra T]: lexicon T $(Lean.quote s) $(c) := { denotation := $(n) }
)

namespace LexSyntaxExperiments
  -- One other possible limitation of this macro is that it only enters identifier-bound entities, so you can't directly register 15. But this is nicer that manually specifying 
  def fifteen : Nat := 15
  lex fifteen for Prop as @Cat.NP Nat

  anylex fifteen as @Cat.NP Nat
end LexSyntaxExperiments
