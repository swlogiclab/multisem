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

#check Unit

--axiom polyunit.{α} : Type α
--axiom pu.{α} : polyunit.{α}

-- Would like to use this def, but there's a bug in m4, fixed in nightly: https://github.com/leanprover/lean4/commit/fb45eb49643b2abbc0d057d1fafc5e1eb419fc2a
--inductive polyunit.{α} : Type α where
--| pu : polyunit
def polyunit.{α} : Type α := ULift Unit
def pu.{α} : polyunit.{α} := ULift.up ()

class HeytingAlgebra (P:Type u) where
  top : P
  bottom : P
  conj : P -> P -> P
  disj : P -> P -> P
  impl : P -> P -> P
class HeytingAlgebraLaws (P : Type u) extends HeytingAlgebra P where
  conj_comm : ∀ x y, conj x y = conj y x
  conj_assoc : ∀ x y z, conj (conj x y) z = conj x (conj y z)
  disj_comm : ∀ x y, disj x y = disj y x
  disj_assoc : ∀ x y z, disj (disj x y) z = disj x (disj y z)
  distrib_left : ∀ x y z, conj x (disj y z) = disj (conj x y) (conj x z)
  distrib_right : ∀ x y z, conj (disj x y) z = disj (conj x z) (conj y z)
  -- TODO: missing impl laws

class HeytingAlgebraMorphism (P : Type u)[HeytingAlgebra P](Q : Type v)[HeytingAlgebra Q] where
  morph : P -> Q
class HeytingAlgebraMorphismLaws (P : Type u)[HeytingAlgebra P](Q : Type v)[HeytingAlgebra Q] extends HeytingAlgebraMorphism P Q where
  preserves_top : morph HeytingAlgebra.top = HeytingAlgebra.top
  preserves_bottom : morph HeytingAlgebra.bottom = HeytingAlgebra.bottom
  preserves_conj : ∀ x y, morph (HeytingAlgebra.conj x y) = HeytingAlgebra.conj (morph x) (morph y)
  preserves_disj : ∀ x y, morph (HeytingAlgebra.disj x y) = HeytingAlgebra.disj (morph x) (morph y)
  preserves_impl : ∀ x y, morph (HeytingAlgebra.impl x y) = HeytingAlgebra.impl (morph x) (morph y)


instance pointwiseHA (X : Type v)(H : Type u)[HeytingAlgebra H] : HeytingAlgebra (X -> H) where
  top := λ_ => HeytingAlgebra.top
  bottom := λ_ => HeytingAlgebra.bottom
  conj x y := λ p => HeytingAlgebra.conj (x p) (y p)
  disj x y := λ p => HeytingAlgebra.disj (x p) (y p)
  impl x y := λ p => HeytingAlgebra.impl (x p) (y p)

instance pointwiseHALaws (X : Type v)(H : Type u)[HeytingAlgebraLaws H] : HeytingAlgebraLaws (X -> H) where
  top := λ_ => HeytingAlgebra.top
  bottom := λ_ => HeytingAlgebra.bottom
  conj x y := λ p => HeytingAlgebra.conj (x p) (y p)
  disj x y := λ p => HeytingAlgebra.disj (x p) (y p)
  impl x y := λ p => HeytingAlgebra.impl (x p) (y p)
  conj_comm x y := by { apply funext; intro p; apply HeytingAlgebraLaws.conj_comm }
  conj_assoc x y z := by { apply funext; intro p; apply HeytingAlgebraLaws.conj_assoc }
  disj_comm x y := by { apply funext; intro p; apply HeytingAlgebraLaws.disj_comm }
  disj_assoc x y z := by { apply funext; intro p; apply HeytingAlgebraLaws.disj_assoc }
  distrib_left x y z := by apply funext; intro p; apply HeytingAlgebraLaws.distrib_left
  distrib_right x y z := by apply funext; intro p; apply HeytingAlgebraLaws.distrib_right


-- We do Lambek-style interpretation of lslash
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

class SurfaceHeytingAlgebra (P:Type u) (n:Nat) (C:Cat) where
  combineProps : (P -> P -> P) -> interp P C -> interp P C -> interp P C

instance ADJHeytingAlgebra (P:Type u)[HeytingAlgebra P]{T}{n} : SurfaceHeytingAlgebra P n (@ADJ T) where
  combineProps op d1 d2 := fun x => op (d1 x) (d2 x)

instance SHeytingAlgebra (P:Type u)[pt:HeytingAlgebra P]{n} : SurfaceHeytingAlgebra P n S where
  combineProps op d1 d2 := op d1 d2

instance lSlashHeytingAlgebra (P:Type u)[pt:HeytingAlgebra P]{n:Nat}(C C' : Cat)[wit:SurfaceHeytingAlgebra P n C'] : SurfaceHeytingAlgebra P (Nat.succ n) (@lslash C C') where
  combineProps op d1 d2 := fun x => SurfaceHeytingAlgebra.combineProps n op (d1 x) (d2 x)

instance rSlashHeytingAlgebra (P:Type u)[pt:HeytingAlgebra P]{n:Nat}(C C' : Cat)[wit:SurfaceHeytingAlgebra P n C'] : SurfaceHeytingAlgebra P (Nat.succ n) (@rslash C' C) where
  combineProps op d1 d2 := fun x => SurfaceHeytingAlgebra.combineProps n op (d1 x) (d2 x)

instance PropHeyting : HeytingAlgebra Prop where
  top := True
  bottom := False
  conj x y := x ∧ y
  disj x y :=  x ∨ y
  impl x y := x -> y

class lexicon (P : Type u) (w:String) (c:Cat) :=
  { denotation : interp P c }


instance coordLexicon (P:Type)[HeytingAlgebra P](w:String) (C:Cat)[Coordinator P w][SurfaceHeytingAlgebra P (Nat.succ (Nat.succ (Nat.succ Nat.zero))) C] : lexicon P w (lslash C (rslash C C)) where
  denotation := fun L R => SurfaceHeytingAlgebra.combineProps 3 (Coordinator.denoteCoord w) L R
-- We don't need the other associativity, as it can be recovered by shifting


class Synth (P:Type u) (ws:List String) (c:Cat) where
  denotation : interp P c
instance SynthLex (P:Type u){w:String}{C:Cat}[lexicon P w C] : Synth P (List.cons w List.nil) C where
  denotation := lexicon.denotation w
instance SynthRApp (P:Type u){s1 s2 c1 c2}[L:Synth P s1 (rslash c1 c2)][R:Synth P s2 c2] : Synth P (s1++s2) c1 where
  denotation := @Synth.denotation P s1 (rslash c1 c2) L (Synth.denotation s2)
instance SynthLApp (P:Type u){s1 s2 c1 c2}[L:Synth P s1 c1][R:Synth P s2 (lslash c1 c2)] : Synth P (s1++s2) c2 where
  denotation := R.denotation _ (L.denotation)
--  denotation := @Synth.denotation P _ _ _ R (Synth.denotation s1)

--instance (priority := default-1000) Reassoc (P:Type u){s1 s2 s3 c}[pre:Synth P (s1 ++ (s2 ++ s3)) c] : Synth P ((s1 ++ s2) ++ s3) c where
--  denotation := pre.denotation
instance Reassoc' (P:Type u){s1 s2 s3 c}[pre:Synth P ((s1 ++ s2) ++ s3) c] : Synth P (s1 ++ (s2 ++ s3)) c where
  denotation := pre.denotation

instance SynthShift (P:Type u){s c l r}[L:Synth P s (lslash l (rslash c r))] : Synth P s (rslash (lslash l c) r) where
  denotation xr xl := L.denotation s xl xr

instance RComp (P:Type u){s s' c1 c2 c3}[L:Synth P s (rslash c1 c2)][R:Synth P s' (rslash c2 c3)] : Synth P (s ++ s') (rslash c1 c3) where
  denotation x := L.denotation _ (R.denotation _ x)
instance LComp (P:Type u){s s' c1 c2 c3}[L:Synth P s (lslash c1 c2)][R:Synth P s' (lslash c2 c3)] : Synth P (s ++ s') (lslash c1 c3) where
  denotation x := R.denotation _ (L.denotation _ x)

-- TODO: Need to add type raising!


def dbgspec (l:List String) (C:Cat) [sem:Synth Prop l C] : interp Prop C :=
  sem.denotation
def pspec (l:List String) [sem:Synth Prop l S] : Prop :=
  sem.denotation

--
--  def oneAsNat : Nat := 1
def asNat (n:Nat) := n
def odd (n:Nat) : Bool :=
  match n with
  | Nat.zero => false
  | Nat.succ Nat.zero => true
  | Nat.succ (Nat.succ x) => odd x
def even (n:Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ Nat.zero => false
  | Nat.succ (Nat.succ x) => even x

--def nameIt {T:Type}(s:String) (x:T) : @lexicon Bs BsBase s (prim (@NP T)) := { denotation := x }



instance onelex   : lexicon Prop "one" (@NP Nat) := { denotation := asNat 1 }
instance twolex   : lexicon Prop "two" (@NP Nat) := { denotation := asNat 2 }
instance threelex : lexicon Prop "three" (@NP Nat) := { denotation := asNat 3 }
instance fourlex  : lexicon Prop "four" (@NP Nat) := { denotation := asNat 4 }
instance fivelex  : lexicon Prop "five" (@NP Nat) := { denotation := asNat 5 }
instance evenlex  : lexicon Prop "even" (@ADJ Nat) := { denotation := fun x => even x = true }
instance oddlex   : lexicon Prop "odd" (@ADJ Nat) := { denotation := fun x => odd x = true }

instance noun_is_adj_lex {T}{P}: lexicon P "is" (rslash (lslash (@NP T) S) (@ADJ T)) where
  denotation := fun a n => a n
instance noun_is_noun_lex {T}: lexicon Prop "is" (rslash (lslash (@NP T) S) (@NP T)) where
  denotation := fun a n => a = n

instance and_coord (P:Type u)[HeytingAlgebra P] : Coordinator P "and" where
  denoteCoord a b := HeytingAlgebra.conj a b
instance or_coord (P:Type u)[HeytingAlgebra P] : Coordinator P "or" where
  denoteCoord a b := HeytingAlgebra.disj a b

#check dbgspec ["one"] (@NP Nat)
#check dbgspec (["is"]++["odd"]) (lslash (@NP Nat) S)


-- These would need a the reverse associativity lemma, which is commented out because:
-- (a) everything comes out associated to the right from the parser (which we haven't yet ported from Coq)
-- (b) leaving it in currently, even with dramatically limited priority, leads typeclass resolution to cycle uselessly flipping the associativity of some sequences back and forth without progress
--#check pspec (["one"]++["is"]++["one"])
--#check pspec (["one"]++["is"]++["odd"])
--#check pspec ((["one"]++["is"])++["odd"])
#check pspec (["one"]++(["is"]++["odd"]))



--  instance and_sent_lex : @lexicon Bs BsBase  "and" (rslash (lslash (prim S) (prim S)) (prim S)) := { denotation := fun a n => a /\ n }
--  instance or_sent_lex : @lexicon Bs BsBase  "or" (rslash (lslash (prim S) (prim S)) (prim S)) := { denotation := fun a n => a \/ n }
--  instance or_adj_lex {T}: @lexicon Bs BsBase  "or" (rslash (lslash (prim (@ADJ T)) (prim (@ADJ T))) (prim (@ADJ T))) := { denotation := fun a n x => a x \/ n x }
--  instance and_adj_lex {T}: @lexicon Bs BsBase  "and" (rslash (lslash (prim (@ADJ T)) (prim (@ADJ T))) (prim (@ADJ T))) := { denotation := fun a n x => a x /\ n x }
--
--
instance equals_eq_lex {T}: lexicon Prop "equals" (rslash (lslash (@NP T) S) (@NP T)) where
  denotation := fun r l => r = l 

#check (pspec (["one"] ++ (["equals"] ++ ["one"])))
#check (pspec (["one"] ++ (["is"] ++ ["odd"])))
#check (pspec (["two"] ++ (["is"] ++ ["even"])))
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
#check (pspec (["one"] ++ (["is"] ++ (["odd"] ++ (["and"] ++ (["two"] ++ (["is"] ++ ["even"])))))))
---- a ha, so the problem is that I'm missing rules to reassociate appropriately...
---- ah, okay, was missing a couple structural rules
---- but so far, while I haven't added universe polymorphism or sorted the primitives by logical type, this seems way snappier than Coq
#check (pspec ((["one"] ++ (["is"] ++ ["odd"])) ++ (["and"] ++ (["two"] ++ (["is"] ++ ["even"])))))
--
--
--
--#check (@synthlex _ _ "one" (prim NP) onelex)
--#check (@synthlex _ _ "equals" _ equals_eq_lex)
--#check @synthlapp Bs _ _ _ _ _ (@synthlex _ _ "one" (prim NP) onelex) (@synthrapp _ _ _ _ _ _ (@synthlex _ _ "equals" _ equals_eq_lex) (@synthlex _ _ "one" (prim NP) onelex))
--
---- More dictionary entries 
--
instance addslex : lexicon Prop "adds" (lslash (@NP (Nat->Nat)) (rslash S (@NP Nat))) where
  denotation (sub:Nat->Nat) (obj:Nat) := forall x, sub x = x + obj
instance monotone : lexicon Prop "monotone" (@ADJ (Nat -> Nat)) where
  denotation f := forall x y, x <= y -> f x <= f y
--instance noun_is_adj_sentence {A:Type} : lexicon "is" (lslash (rslash (prim S) (prim (@ADJ A))) (prim (@NP A))) := { denotation := fun n a => a n }
--instance noun_is_adj_noun {A:Type} : lexicon "is" (lslash (rslash (prim S) (prim (@NP A))) (prim (@NP A))) := { denotation := fun n a => a = n }
--instance equalslex {A:Type} : lexicon "equals" (lslash (rslash (prim S) (prim (@NP A))) (prim (@NP A))) := { denotation := fun (n:A) (a:A) => a = n }
--

--def quant (A:Type) := (rslash (rslash (prim S) (lslash (prim S) (prim (@NP A)))) (prim (@CN A)))

set_option quotPrecheck false

-- This needs to be notation, since typeclass unification doesn't unfold defs
notation:65 "quant" A:65 => (rslash (rslash S (lslash (@NP A) S)) (@CN A))
--
instance exists_lex {A}: lexicon Prop "some" (quant A) where
  denotation := fun _ P => exists x, P x
instance forall_lex {A}: lexicon Prop "every" (quant A) where
  denotation := fun _ P => forall x, P x
--
instance nat_noun : lexicon Prop "natural" (@CN Nat) := { denotation := pu }
--
instance given_lex {A B}: lexicon Prop "given" (lslash (@NP (A -> B)) (rslash (@NP B) (@NP A))) where 
  denotation := fun f arg => f arg 
--
---- These instances are the source of major performance headaches in Coq. Enabling them here leads to timeouts instead
---- of long-running instance search, because the search process generates such huge instances that the typeclasses used
---- to guide unification internally hit their own heartbeat limits (hitting limits for whnf and isDefEq).
---- I've dug up examples of priority-setting for Lean4, but I'm not sure it does anything (not sure if higher or lower
---- numbers are higher or lower priority, but I've tried both). The feature isn't documented yet, so it may not be
---- stable or there may be other subtleties. In either case, I need a new approach to coordination.
---- The current Coq implementation uses Carpenter-style coordination based on con/dis-joining any Prop-targeting
---- category, but this probably has the same issue in general (I think it's more expressive than these rules...). But
---- Since that approach involves an extra typeclass, maybe I could try imposing a depth limit --- e.g., give a fuel
---- parameter to the recursive coordinator class, and in lexicon injection instantiate the fuel parameter to something 
---- modest like 6 or 10, which already seems like deeper category nesting than we'd really need, but would remain configurable
----
----instance (priority := default-20) and_liftL {G G'} [nxt:lexicon "and" (rslash (lslash G G) G)] : @lexicon Bs BsBase "and" (rslash (lslash (lslash G G') (lslash G G')) (lslash G G')):= { denotation := fun R L g' => @lexicon.denotation Bs BsBase "and" _ nxt (R g') (L g')}
----instance (priority := default-20) and_liftR {G G'} [nxt:lexicon "and" (rslash (lslash G G) G)] : @lexicon Bs BsBase "and" (rslash (lslash (rslash G G') (rslash G G')) (rslash G G')):= { denotation := fun R L g' => @lexicon.denotation Bs BsBase "and" _ nxt (R g') (L g')}
----
----instance (priority := default-20) or_liftL {G G'} [nxt:lexicon "or" (rslash (lslash G G) G)] : @lexicon Bs BsBase "or" (rslash (lslash (lslash G G') (lslash G G')) (lslash G G')):= { denotation := fun R L g' => @lexicon.denotation Bs BsBase "or" _ nxt (R g') (L g')}
----instance (priority := default-20) or_liftR {G G'} [nxt:lexicon "or" (rslash (lslash G G) G)] : @lexicon Bs BsBase "or" (rslash (lslash (rslash G G') (rslash G G')) (rslash G G')):= { denotation := fun R L g' => @lexicon.denotation Bs BsBase "or" _ nxt (R g') (L g')}

-- The problematic rules above have been replaced with the depth-bounded coordination

--
---- Specs from original testing file (though in the absence of the and/or lifting rules!!!)
def addone (n:Nat) := n + 1
instance addonelex : lexicon Prop "addone" (@NP (Nat -> Nat)) where 
  denotation := addone 
instance nonneg_lex : lexicon Prop "non-negative" (@ADJ Nat) where
  denotation := fun x => 0 <= x 

#check (pspec (["addone"] ++ (["equals"] ++ ["addone"])))
#check (pspec (["addone"] ++ (["is"] ++ ["monotone"])))
#check (pspec (["addone"] ++ (["given"] ++ (["one"] ++ (["is"] ++ ["two"])))))
#check (pspec (["addone"] ++ (["given"] ++ (["three"] ++ (["is"] ++ ["four"])))))
#check (pspec (["addone"] ++ (["given"] ++ (["three"] ++ (["equals"] ++ ["four"])))))

#check dbgspec (["is"] ++ ["non-negative"]) (lslash (@NP Nat) S)
#check dbgspec ["every"] (quant Nat)
#check dbgspec ["natural"] (@CN Nat)
#check dbgspec (["every"]++["natural"]) (rslash (S) (lslash (@NP Nat) S))

#check (pspec (["every"] ++ (["natural"] ++ (["is"] ++ ["non-negative"]))))
#check (pspec (["some"] ++ (["natural"] ++ (["is"] ++ ["non-negative"]))))
#check (pspec (["some"] ++ (["natural"] ++ (["is"] ++ ["even"]))))

#check (pspec (["four"] ++ (["is"] ++ (["even"] ++ (["and"] ++ ["non-negative"])))))
#check (pspec (["three"] ++ (["is"] ++ (["non-negative"] ++ (["and"] ++ (["four"] ++ (["is"] ++ (["even"]))))))))

theorem exmisc : (pspec (["three"] ++ (["is"] ++ (["non-negative"] ++ (["and"] ++ (["four"] ++ (["is"] ++ (["even"])))))))) :=
  by simp
     apply And.intro
     . simp; sorry
     . simp; rfl

#check (pspec (["every"] ++ (["natural"] ++ (["is"] ++ (["non-negative"] ++ (["and"] ++ (["some"] ++ (["natural"] ++ (["is"] ++ ["even"])))))))))

#check (pspec (["every"] ++ (["natural"] ++ (["is"] ++ (["odd"] ++ (["or"] ++ ["even"]))))))


#print String
#print Char

def StateFormula (T : Type u) := T -> Prop

instance StateFormulatHeyting : HeytingAlgebra (StateFormula T) := pointwiseHA T Prop

namespace ltl
  inductive LTLFormula (T : Type u) where
    | true : LTLFormula T
    | false : LTLFormula T
    | stateProp : StateFormula T -> LTLFormula T
    | not : LTLFormula T -> LTLFormula T
    | next : LTLFormula T -> LTLFormula T
    | or : LTLFormula T -> LTLFormula T -> LTLFormula T
    -- "until" is a reserved keyword in Lean
    | unt : LTLFormula T -> LTLFormula T -> LTLFormula T
  -- Convenient shorthands for outside this namespace
  def true {T : Type u} : LTLFormula T := LTLFormula.true
  def false {T : Type u} : LTLFormula T := LTLFormula.false
  def or {T : Type u} : LTLFormula T -> LTLFormula T -> LTLFormula T:= LTLFormula.or
  def unt {T : Type u} : LTLFormula T -> LTLFormula T -> LTLFormula T:= LTLFormula.unt
  def next {T : Type u} : LTLFormula T -> LTLFormula T:= LTLFormula.next
  def not {T : Type u} : LTLFormula T -> LTLFormula T:= LTLFormula.not
  
  -- LTL is typically classical, so these are derived in the classic way
  def and {T : Type u} (a b : LTLFormula T) : LTLFormula T :=
    LTLFormula.not (LTLFormula.or (LTLFormula.not a) (LTLFormula.not b))
  def impl {T : Type u} (a b : LTLFormula T) : LTLFormula T :=
    LTLFormula.or (LTLFormula.not a) b
  -- other derived forms
  -- "finally" is a reserved keyword
  def final {T : Type u} (a : LTLFormula T) : LTLFormula T :=
    LTLFormula.unt LTLFormula.true a
  -- TODO: G(lobally)
  
end ltl


instance LTLHeyting (T : Type u) : HeytingAlgebra (ltl.LTLFormula T) where
  top := ltl.true
  bottom := ltl.false
  conj := ltl.and
  disj := ltl.or
  impl := ltl.impl

instance ltl_state (T : Type u) : HeytingAlgebraMorphism (StateFormula T) (ltl.LTLFormula T) where
  morph := ltl.LTLFormula.stateProp

namespace ctlstar
  mutual
    inductive CTLStarFormula (T : Type u) where
      | false
      | true
      | stateProp : StateFormula T -> CTLStarFormula T
      | not : CTLStarFormula T -> CTLStarFormula T
      | or : CTLStarFormula T -> CTLStarFormula T -> CTLStarFormula T
      | A : CTLPathFormula T -> CTLStarFormula T
      | E : CTLPathFormula T -> CTLStarFormula T
    inductive CTLPathFormula (T : Type u) where
      | starformula : CTLStarFormula T -> CTLPathFormula T
      | not : CTLPathFormula T -> CTLPathFormula T
      | or : CTLPathFormula T -> CTLPathFormula T -> CTLPathFormula T
      | X : CTLPathFormula T -> CTLPathFormula T
      | F : CTLPathFormula T -> CTLPathFormula T
      | G : CTLPathFormula T -> CTLPathFormula T
      | U : CTLPathFormula T -> CTLPathFormula T -> CTLPathFormula T
    end

  def and {T : Type u} (a b : CTLStarFormula T) : CTLStarFormula T :=
    CTLStarFormula.not (CTLStarFormula.or (CTLStarFormula.not a) (CTLStarFormula.not b))
  def impl {T : Type u} (a b : CTLStarFormula T) : CTLStarFormula T :=
    CTLStarFormula.or (CTLStarFormula.not a) b

end ctlstar

instance CTLStarHeyting (T : Type u) : HeytingAlgebra (ctlstar.CTLStarFormula T) where
  top := ctlstar.CTLStarFormula.true
  bottom := ctlstar.CTLStarFormula.false
  disj := ctlstar.CTLStarFormula.or
  conj := ctlstar.and
  impl := ctlstar.impl

namespace ctl
  inductive CTLFormula (T : Type u) where
    | false
    | true
    | stateProp : StateFormula T -> CTLFormula T
    | not : CTLFormula T -> CTLFormula T
    | or : CTLFormula T -> CTLFormula T -> CTLFormula T
    | EG : CTLFormula T -> CTLFormula T
    | EU : CTLFormula T -> CTLFormula T
    | EX : CTLFormula T -> CTLFormula T
    | AG : CTLFormula T -> CTLFormula T
    | AU : CTLFormula T -> CTLFormula T
    | AX : CTLFormula T -> CTLFormula T
  def and {T : Type u} (a b : CTLFormula T) : CTLFormula T :=
    CTLFormula.not (CTLFormula.or (CTLFormula.not a) (CTLFormula.not b))
  def impl {T : Type u} (a b : CTLFormula T) : CTLFormula T :=
    CTLFormula.or (CTLFormula.not a) b
end ctl

instance CTLHeyting (T : Type u) : HeytingAlgebra (ctl.CTLFormula T) where
  top := ctl.CTLFormula.true
  bottom := ctl.CTLFormula.false
  disj := ctl.CTLFormula.or
  conj := ctl.and
  impl := ctl.impl

def ctl_to_ctlstar {T : Type u} (x : ctl.CTLFormula T) : ctlstar.CTLStarFormula T :=
  match x with
  | ctl.CTLFormula.false => ctlstar.CTLStarFormula.false
  | ctl.CTLFormula.true => ctlstar.CTLStarFormula.true
  | ctl.CTLFormula.or a b => ctlstar.CTLStarFormula.or (ctl_to_ctlstar a) (ctl_to_ctlstar b)
  | ctl.CTLFormula.not a => ctlstar.CTLStarFormula.not (ctl_to_ctlstar a)
  | ctl.CTLFormula.stateProp p => ctlstar.CTLStarFormula.stateProp p
  | ctl.CTLFormula.AX a => ctlstar.CTLStarFormula.A (ctlstar.CTLPathFormula.X (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.AU a => ctlstar.CTLStarFormula.A (ctlstar.CTLPathFormula.U (ctlstar.CTLPathFormula.starformula ctlstar.CTLStarFormula.true) (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.AG a => ctlstar.CTLStarFormula.A (ctlstar.CTLPathFormula.G (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.EX a => ctlstar.CTLStarFormula.E (ctlstar.CTLPathFormula.X (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.EU a => ctlstar.CTLStarFormula.E (ctlstar.CTLPathFormula.U (ctlstar.CTLPathFormula.starformula ctlstar.CTLStarFormula.true) (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))
  | ctl.CTLFormula.EG a => ctlstar.CTLStarFormula.E (ctlstar.CTLPathFormula.G (ctlstar.CTLPathFormula.starformula (ctl_to_ctlstar a)))

instance CTLStarMorphism (T : Type u) : HeytingAlgebraMorphism (ctl.CTLFormula T) (ctlstar.CTLStarFormula T) where
  morph := ctl_to_ctlstar