import Multisem.HeytingAlgebras
import Multisem.TemporalLogic
import Multisem.Text.Macros

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
open Cat

-- These are some currently-disabled notations for writing the slashes
-- At the moment we can't get lexicon entries working with a mix of explicit and notation-based categories, which we need for backwards compat right now
-- We can allow writing right slashes by implementing Div for Cat
instance CatDiv.{q} : Div (Cat.{q}) where
  div := rslash

-- This is probably not best practice, but we really do need typeclass resolution to unfold these right now. Later if we are more uniform in using the notations for lexicon entries, we could probably remove these attribute overrides.
attribute [simp] HDiv.hDiv
attribute [simp] Div.div

theorem _checkCatDiv : (S / (@NP Nat)) = rslash S (@NP Nat) := by simp
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
--macro_rules |  `($x ∖ $y) => `(binop% lslash $x $y)--`(binop% LDiv.lDiv $x $y)

instance CatLDiv.{q} : LDiv (Cat.{q}) where
  lDiv := lslash
theorem _checkCatLDiv : ((@NP Nat) ∖ S) = lslash (@NP Nat) S := by rfl
instance CatMod.{q} : Mod (Cat.{q}) where
  mod := Ref

-- This deriving breaks if any of the category instances are explicit arguments, because in general it cannot print types
deriving instance Repr for Cat
#eval reprPrec (rslash (lslash S S) S) 234
#eval (rslash (lslash S S) S)

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

instance rSlashHeytingAlgebra (P:Type u)[HeytingAlgebra P]{n:Nat}(C C' : Cat)[SurfaceHeytingAlgebra P n C'] : SurfaceHeytingAlgebra P (Nat.succ n) (C' / C) where
  combineProps op d1 d2 := fun x => SurfaceHeytingAlgebra.combineProps n op (d1 x) (d2 x)

class lexicon (P : Type u) (w:String) (c:Cat) where
  denotation : interp P c 
attribute [simp] lexicon.denotation


instance coordLexicon (P:Type)[HeytingAlgebra P](w:String) (C:Cat)[Coordinator P w][SurfaceHeytingAlgebra P (Nat.succ (Nat.succ (Nat.succ Nat.zero))) C] : lexicon P w (C ∖ (C / C)) where
  denotation := fun L R => SurfaceHeytingAlgebra.combineProps 3 (Coordinator.denoteCoord w) L R
-- We don't need the other associativity, as it can be recovered by shifting

class Synth (P:Type u)(ws:ContextTree String) (c:Cat) where
  denotation : interp P c
  stringRep : Lean.Format
attribute [simp] Synth.denotation

-- The Repr typeclass is how Lean displays results of #eval commands.
-- Implementing this (and for that matter, requiring Synth.stringRep)
-- lets us print the result of a call to specwitness
instance (P:Type u)(ws:ContextTree String) (c:Cat) : Repr (Synth P ws c) where
  reprPrec inst n := inst.stringRep



instance SynthLex (P:Type u){w:String}{C:Cat}[l:lexicon P w C] : Synth P (ContextTree.one w) C where
  denotation := lexicon.denotation w
  stringRep := "lexicon<"++w++":"++ (reprPrec C 0) ++">"

instance SynthRApp (P:Type u){s1 s2 c1 c2}[L:Synth P s1 (c1 / c2)][R:Synth P s2 c2] : Synth P (s1#s2) c1 where
  denotation := @Synth.denotation P s1 (c1 / c2) L (Synth.denotation s2)
  stringRep := "(SynthRApp "++L.stringRep++" "++R.stringRep++")"
instance SynthLApp (P:Type u){s1 s2 c1 c2}[L:Synth P s1 c1][R:Synth P s2 (c1 ∖ c2)] : Synth P (s1#s2) c2 where
  denotation := R.denotation _ (L.denotation)
  stringRep := "(SynthLApp "++L.stringRep++" "++R.stringRep++")"
--  denotation := @Synth.denotation P _ _ _ R (Synth.denotation s1)

--instance (priority := default-1000) Reassoc (P:Type u){s1 s2 s3 c}[pre:Synth P (s1 ++ (s2 ++ s3)) c] : Synth P ((s1 ++ s2) ++ s3) c where
--  denotation := pre.denotation
instance Reassoc' (P:Type u){s1 s2 s3 c}[pre:Synth P ((s1 # s2) # s3) c] : Synth P (s1 # (s2 # s3)) c where
  denotation := pre.denotation
  stringRep := "(Reassoc' "++pre.stringRep++")"

instance SynthShift (P:Type u){s c l r}[L:Synth P s (l ∖ (c / r))] : Synth P s ((l ∖ c) / r) where
  denotation xr xl := L.denotation s xl xr
  stringRep := "(SynthShift "++L.stringRep++")"

instance RComp (P:Type u){s s' c1 c2 c3}[L:Synth P s (c1 / c2)][R:Synth P s' (c2 / c3)] : Synth P (s # s') (c1 / c3) where
  denotation x := L.denotation _ (R.denotation _ x)
  stringRep := "(RComp "++L.stringRep++" "++R.stringRep++")"
instance LComp (P:Type u){s s' c1 c2 c3}[L:Synth P s (c1 ∖ c2)][R:Synth P s' (c2 ∖ c3)] : Synth P (s # s') (c1 ∖ c3) where
  denotation x := R.denotation _ (L.denotation _ x)
  stringRep := "(LComp "++L.stringRep++" "++R.stringRep++")"

-- Lifting rules for exponents a la Jacobson/Morrill/Carpenter
-- This is used for pronouns and currently for definite articles
-- TODO: lift referents over slash types. Follow Jaeger's exposition.


-- TODO: Need to add type raising!

-- English-specific lifting rules
-- Montague-style lifting for GQs in object position
instance MLift (H:Type u){T U:Type u}{s}[sem:Synth H s (((@NP T) ∖ S) / (@NP U))] :
  Synth H s (((@NP T) ∖ S) / (S / ((@NP U) ∖ S))) where 
  stringRep := "(MLift "++sem.stringRep++")"
  denotation := fun P x => P (fun y => sem.denotation _ y x)

/-
  The rules in here make the search space *much* larger, so they are disabled
  by default.
-/
namespace Anaphora
  -- Slightly simplified (concretized) Jacobson-style extraction (e.g., for anaphora), per Jaeger (p100)
  -- Jacobson restricts the automatic raising to cases where the extraction is a NP, which is all we need now, and also prevents these from completely trashing performance with unconstrained search
  local instance (priority := low) GR {P:Type u}[HeytingAlgebra P]{X A B}{C:Type u}[base:Synth P X (A / B)]
    : Synth P X ((A % (@NP C)) / (B % (@NP C))) where
    denotation := fun x y => base.denotation _ (x y)
    stringRep := "(G> "++base.stringRep++")"
  local instance (priority := low) GL {P:Type u}[HeytingAlgebra P]{X A B}{C:Type u}[base:Synth P X (B ∖ A)]
    : Synth P X ((B % (@NP C)) ∖ (A % (@NP C))) where
    denotation := fun x y => base.denotation _ (x y)
    stringRep := "(G< "++base.stringRep++")"
  
  local instance (priority := low) ZRR {P:Type u}[HeytingAlgebra P]{X A B C}[base:Synth P X ((A / (@NP B)) / C)]
    : Synth P X ((A / (@NP B)) / (C % (@NP B))) where
    denotation := fun x y => base.denotation _ (x y) y
    stringRep := "(Z>> "++base.stringRep++")"
  local instance (priority := low) ZLR {P:Type u}[HeytingAlgebra P]{X A B C}[base:Synth P X (((@NP B) ∖ A) / C)]
    : Synth P X (((@NP B) ∖ A) / (C % (@NP B))) where
    denotation := fun x y => base.denotation _ (x y) y
    stringRep := "(Z<> "++base.stringRep++")"
  local instance (priority := low) ZRL {P:Type u}[HeytingAlgebra P]{X A B C}
    [base:Synth P X (C ∖ (A / (@NP B)))]
    : Synth P X ((C % (@NP B)) ∖ (A / (@NP B))) where
    denotation := fun x y => base.denotation _ (x y) y
    stringRep := "(Z>< "++base.stringRep++")"
  local instance (priority := low) ZLL {P:Type u}[HeytingAlgebra P]{X A B C}
    [base:Synth P X (C ∖ ((@NP B) ∖ A))]
    : Synth P X ((C % (@NP B)) ∖ ((@NP B) ∖ A)) where
    denotation := fun x y => base.denotation _ (x y) y
    stringRep := "(Z<< "++base.stringRep++")"

  /- Even with the NP restrictions, the above still explode performance because
     they essentially result in TC resolution lifting random transitive verbs and such.
     As an alternative, let's consider what the Z rules actually do:
     they lift function types so they can combine with arguments that have extracted referents. But they allow *unnecessary* lifting.
     What if instead we fused them with application, yielding specialized application rules that only apply when it's necessary to combine with an extraction? That should control the slow-down, but would be subtle.

     These rules are much less general than the arbitrary lifting, because they won't automatically play well with other combinators --- we may end up needing quite a few more of these. Each seems to slow down search a little bit, so we will keep these in their own module: these will be scoped instances. We'll keep the original rules around as local instances (which will never be considered in real searches) so we can prove conservativity
  -/
  /-- A condensation of `GR` and `SynthRApp` -/
  scoped instance AppGR {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [f:Synth P X (A / B)][arg:Synth P Y (B % (@NP C))]
    : Synth P (X # Y) (A % (@NP C)) where
    denotation := fun c => f.denotation _ (arg.denotation _ c)
    stringRep := "(AppGR "++f.stringRep++" "++arg.stringRep++")"
  /-- A condensation of `GL` and `SynthLApp` -/
  scoped instance AppGL {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [arg:Synth P X (B % (@NP C))][f:Synth P Y (B ∖ A)]
    : Synth P (X # Y) (A % (@NP C)) where
    denotation := fun c => f.denotation _ (arg.denotation _ c)
    stringRep := "(AppGL "++f.stringRep++" "++arg.stringRep++")"
  scoped instance AppZRR {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [f:Synth P X ((A / (@NP B)) / C)][arg:Synth P Y (C % (@NP B))]
    : Synth P (X # Y) (A / (@NP B)) where
    denotation := fun n => f.denotation _ (arg.denotation _ n) n
    stringRep := "(AppZRR "++f.stringRep++" "++arg.stringRep++")"
  theorem AppZRR_conservative {P X Y A B C}[HeytingAlgebra P]
    (f:Synth P X ((A / (@NP B)) / C))(arg:Synth P Y (C % (@NP B)))
    : (SynthRApp (L := ZRR (base:=f)) (R := arg)).denotation = (AppZRR (f:=f) (arg:=arg)).denotation :=
      by simp
  scoped instance AppZLR {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [f:Synth P X (((@NP B) ∖ A) / C)][arg:Synth P Y (C % (@NP B))]
    : Synth P (X # Y) ((@NP B) ∖ A) where
    denotation := fun n => f.denotation _ (arg.denotation _ n) n
    stringRep := "(AppZLR "++f.stringRep++" "++arg.stringRep++")"
  scoped instance AppZRL {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [arg:Synth P X (C % (@NP B))][f:Synth P Y (C ∖ (A / (@NP B)))]
    : Synth P (X # Y) (A / (@NP B)) where
    denotation := fun n => f.denotation _ (arg.denotation _ n) n
    stringRep := "(AppZRL "++f.stringRep++" "++arg.stringRep++")"
  scoped instance AppZLL {P:Type u}[HeytingAlgebra P]{X Y A B C}
    [arg:Synth P X (C % (@NP B))][f:Synth P Y (C ∖ ((@NP B) ∖ A))]
    : Synth P (X # Y) (A / (@NP B)) where
    denotation := fun n => f.denotation _ (arg.denotation _ n) n
    stringRep := "(AppLRL "++f.stringRep++" "++arg.stringRep++")"

  -- For now we'll keep the word 'the' under wraps as well
  scoped instance (priority := high) the_lex {P}[HeytingAlgebra P]{T}: lexicon P "the" ((@NP T % @NP T) / (@CN T)) where
    denotation := fun _cn x => x
  /- Another difficulty here is that for modified CNs (those that don't just denote true), this definition discards the restriction --- e.g., 'the even number' could resolve to an 'odd number'!

  One option would be to tweak CNs again to have them also reflect their predicate into the typeclass unification problem. But that will lead to problems with TC search failing for equivalent but not definitionally equal predicates (even positive vs positive even).

  Another approach would be to treat 'the' as a GQ that gets its argument externally (so, type is roughtly GQ|NP, so the semantics capture sentence-combining things), then could apply the CN predicate to whatever gets bound as a sanity check.
  -/

end Anaphora




@[simp]
def dbgspec (l:ContextTree String) (C:Cat) [sem:Synth Prop l C] : interp Prop C :=
  sem.denotation
@[simp]
def pspec (l:ContextTree String) [HeytingAlgebra Prop][sem:Synth Prop l S] : Prop :=
  sem.denotation
@[simp]
def specwitness (P:Type u)(l:ContextTree String) [HeytingAlgebra P][sem:Synth P l S] : Synth P l S := sem
@[simp]
def dbgspecwitness (P:Type u)(l:ContextTree String)(C:Cat) [HeytingAlgebra P][sem:Synth P l C] : Synth P l C := sem


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

-- One other possible limitation of this macro is that it only enters identifier-bound entities, so you can't directly register 15. But this is nicer that manually specifying 
def fifteen : Nat := 15
lex fifteen for Prop as @Cat.NP Nat

anylex fifteen as @Cat.NP Nat