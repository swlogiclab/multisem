import Multisem.HeytingAlgebras
import Multisem.TemporalLogic
import Multisem.Text.Macros

universe u v t

-- We're going to go full traditional CCG here
inductive Cat : Type (u+1)  :=
| S : Cat
| NP : forall {x:Type u}, Cat
| ADJ : forall {x:Type u}, Cat
| CN : forall {x:Type u}, Cat
| rslash : Cat  -> Cat  -> Cat 
| lslash : Cat  -> Cat  -> Cat 
open Cat

--axiom polyunit.{α} : Type α
--axiom pu.{α} : polyunit.{α}

-- Would like to use this def, but there's a bug in m4, fixed in nightly: https://github.com/leanprover/lean4/commit/fb45eb49643b2abbc0d057d1fafc5e1eb419fc2a
--inductive polyunit.{α} : Type α where
--| pu : polyunit
def polyunit.{α} : Type α := ULift Unit
def pu.{α} : polyunit.{α} := ULift.up ()

-- We do Lambek-style interpretation of lslash
@[simp]
def interp (P:Type u) (c:Cat) : Type u :=
  match c with
  | S => P
  | @NP x => x
  | @ADJ x => x -> P
  | rslash a b => interp P b -> interp P a
  | lslash a b => interp P a -> interp P b
  | CN => polyunit

class Coordinator (P:Type u)[HeytingAlgebra P](w:String) where
  denoteCoord : P -> P -> P
attribute [simp] Coordinator.denoteCoord

class SurfaceHeytingAlgebra (P:Type u) (n:Nat) (C:Cat) where
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

instance lSlashHeytingAlgebra (P:Type u)[HeytingAlgebra P]{n:Nat}(C C' : Cat)[SurfaceHeytingAlgebra P n C'] : SurfaceHeytingAlgebra P (Nat.succ n) (@lslash C C') where
  combineProps op d1 d2 := fun x => SurfaceHeytingAlgebra.combineProps n op (d1 x) (d2 x)

instance rSlashHeytingAlgebra (P:Type u)[HeytingAlgebra P]{n:Nat}(C C' : Cat)[SurfaceHeytingAlgebra P n C'] : SurfaceHeytingAlgebra P (Nat.succ n) (@rslash C' C) where
  combineProps op d1 d2 := fun x => SurfaceHeytingAlgebra.combineProps n op (d1 x) (d2 x)

class lexicon (P : Type u) (w:String) (c:Cat) :=
  { denotation : interp P c }
attribute [simp] lexicon.denotation


instance coordLexicon (P:Type)[HeytingAlgebra P](w:String) (C:Cat)[Coordinator P w][SurfaceHeytingAlgebra P (Nat.succ (Nat.succ (Nat.succ Nat.zero))) C] : lexicon P w (lslash C (rslash C C)) where
  denotation := fun L R => SurfaceHeytingAlgebra.combineProps 3 (Coordinator.denoteCoord w) L R
-- We don't need the other associativity, as it can be recovered by shifting


class Synth (P:Type u)(ws:tree String) (c:Cat) where
  denotation : interp P c
attribute [simp] Synth.denotation

instance SynthLex (P:Type u){w:String}{C:Cat}[lexicon P w C] : Synth P (tree.one w) C where
  denotation := lexicon.denotation w
instance SynthRApp (P:Type u){s1 s2 c1 c2}[L:Synth P s1 (rslash c1 c2)][Synth P s2 c2] : Synth P (s1#s2) c1 where
  denotation := @Synth.denotation P s1 (rslash c1 c2) L (Synth.denotation s2)
instance SynthLApp (P:Type u){s1 s2 c1 c2}[L:Synth P s1 c1][R:Synth P s2 (lslash c1 c2)] : Synth P (s1#s2) c2 where
  denotation := R.denotation _ (L.denotation)
--  denotation := @Synth.denotation P _ _ _ R (Synth.denotation s1)

--instance (priority := default-1000) Reassoc (P:Type u){s1 s2 s3 c}[pre:Synth P (s1 ++ (s2 ++ s3)) c] : Synth P ((s1 ++ s2) ++ s3) c where
--  denotation := pre.denotation
instance Reassoc' (P:Type u){s1 s2 s3 c}[pre:Synth P ((s1 # s2) # s3) c] : Synth P (s1 # (s2 # s3)) c where
  denotation := pre.denotation

instance SynthShift (P:Type u){s c l r}[L:Synth P s (lslash l (rslash c r))] : Synth P s (rslash (lslash l c) r) where
  denotation xr xl := L.denotation s xl xr

instance RComp (P:Type u){s s' c1 c2 c3}[L:Synth P s (rslash c1 c2)][R:Synth P s' (rslash c2 c3)] : Synth P (s # s') (rslash c1 c3) where
  denotation x := L.denotation _ (R.denotation _ x)
instance LComp (P:Type u){s s' c1 c2 c3}[L:Synth P s (lslash c1 c2)][R:Synth P s' (lslash c2 c3)] : Synth P (s # s') (lslash c1 c3) where
  denotation x := R.denotation _ (L.denotation _ x)

-- TODO: Need to add type raising!


@[simp]
def dbgspec (l:tree String) (C:Cat) [sem:Synth Prop l C] : interp Prop C :=
  sem.denotation
@[simp]
def pspec (l:tree String) [HeytingAlgebra Prop][sem:Synth Prop l S] : Prop :=
  sem.denotation