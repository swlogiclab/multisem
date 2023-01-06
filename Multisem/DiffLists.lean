import Multisem.Grammar
import Multisem.Lexicon
-- Temporary while exploring this as an alternative context structure:
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet
open sort

open Cat

class NonEmptyTail (A B : List String) where
instance NTailRefl {a A} : NonEmptyTail (a::A) A where
instance NTailTail {A B b}[NonEmptyTail A (b::B)] : NonEmptyTail A B where

class StrictSubList (A B : List String) where
instance StrictSubListBase {a}{A} : StrictSubList (a::A) A where
--instance StrictSubListTail {A B}{b} [StrictSubList A (b::B)] : StrictSubList A B where
instance StrictSubtListTail2 {A B}{a} [StrictSubList A B] : StrictSubList (a::A) B where

class DSynth (P:Type u) (Front Back : List String) (C : Cat) where
  dsem : interp P C
attribute [simp] DSynth.dsem

instance DRApp {P}{Front Back1 Back2 : List String} {A B : Cat}
  --[NonEmptyTail Back1 Back2]
  --[NonEmptyTail Front Back1]
  [StrictSubList Front Back1][StrictSubList Back1 Back2]
  [L : DSynth P Front Back1 (B // A)]
  [R : DSynth P Back1 Back2 A]
  : DSynth P Front Back2 B where
  dsem := L.dsem R.dsem
instance DLApp {P}{Front Back1 Back2 : List String} {A B : Cat}
  --[NonEmptyTail Back1 Back2]
  --[NonEmptyTail Front Back1]
  [StrictSubList Front Back1][StrictSubList Back1 Back2]
  [L : DSynth P Front Back1 A]
  [R : DSynth P Back1 Back2 (A ∖ B)]
  : DSynth P Front Back2 B where
  dsem := R.dsem L.dsem

instance DLex {P}{L : List String}{w:String}{C:Cat}
  [l : lexicon P w C]
  : DSynth P (w::L) L C where
  dsem := l.denotation

-- No Reassoc or Reassoc' is necessary!

instance DShift {P}{Front Back : List String}{c l r}[StrictSubList Front Back][L:DSynth P Front Back (l ∖ (c // r))] : DSynth P Front Back ((l ∖ c) // r) where
  dsem xr xl := L.dsem xl xr

instance DRComp (P:Type u){s smid s' c1 c2 c3}[StrictSubList s smid][StrictSubList smid s'][L:DSynth P s smid (c1 // c2)][R:DSynth P smid s' (c2 // c3)] : DSynth P s s' (c1 // c3) where
  dsem x := L.dsem (R.dsem x)
instance DLComp (P:Type u){s smid s' c1 c2 c3}[StrictSubList s smid][StrictSubList smid s'][L:DSynth P s smid (c1 ∖ c2)][R:DSynth P smid s' (c2 ∖ c3)] : DSynth P s s' (c1 ∖ c3) where
  dsem x := R.dsem (L.dsem x)

-- English-specific lifting rules
-- Montague-style lifting for GQs in object position
instance DMLift (H:Type u){T U:Type u}{s s'}[sem:DSynth H s s' (((@NP T) ∖ S) // (@NP U))] :
  DSynth H s s' (((@NP T) ∖ S) // (S // ((@NP U) ∖ S))) where 
  dsem := fun P x => P (fun y => sem.dsem y x)


/-
  The rules in here make the search space *much* larger, so they are disabled
  by default.
-/
namespace DiffJacobson
  -- Slightly simplified (concretized) Jacobson-style extraction (e.g., for anaphora), per Jaeger (p100)
  -- Jacobson restricts the automatic raising to cases where the extraction is a NP, which is all we need now, and also prevents these from completely trashing performance with unconstrained search
  /-
  local instance (priority := low) GR {P:Type u}[HeytingAlgebra P]{X A B}{C:Type u}[base:Synth P X (A // B)]
    : Synth P X ((A % (@NP C)) // (B % (@NP C))) where
    denotation := fun x y => base.denotation (x y)
    stringRep := "(G> "++base.stringRep++")"
  local instance (priority := low) GL {P:Type u}[HeytingAlgebra P]{X A B}{C:Type u}[base:Synth P X (B ∖ A)]
    : Synth P X ((B % (@NP C)) ∖ (A % (@NP C))) where
    denotation := fun x y => base.denotation (x y)
    stringRep := "(G< "++base.stringRep++")"
  
  local instance (priority := low) ZRR {P:Type u}[HeytingAlgebra P]{X A B C}[base:Synth P X ((A // (@NP B)) // C)]
    : Synth P X ((A // (@NP B)) // (C % (@NP B))) where
    denotation := fun x y => base.denotation (x y) y
    stringRep := "(Z>> "++base.stringRep++")"
  local instance (priority := low) ZLR {P:Type u}[HeytingAlgebra P]{X A B C}[base:Synth P X (((@NP B) ∖ A) // C)]
    : Synth P X (((@NP B) ∖ A) // (C % (@NP B))) where
    denotation := fun x y => base.denotation (x y) y
    stringRep := "(Z<> "++base.stringRep++")"
  local instance (priority := low) ZRL {P:Type u}[HeytingAlgebra P]{X A B C}
    [base:Synth P X (C ∖ (A // (@NP B)))]
    : Synth P X ((C % (@NP B)) ∖ (A // (@NP B))) where
    denotation := fun x y => base.denotation (x y) y
    stringRep := "(Z>< "++base.stringRep++")"
  local instance (priority := low) ZLL {P:Type u}[HeytingAlgebra P]{X A B C}
    [base:Synth P X (C ∖ ((@NP B) ∖ A))]
    : Synth P X ((C % (@NP B)) ∖ ((@NP B) ∖ A)) where
    denotation := fun x y => base.denotation (x y) y
    stringRep := "(Z<< "++base.stringRep++")"
      -/

  /- Even with the NP restrictions, the above still explode performance because
     they essentially result in TC resolution lifting random transitive verbs and such.
     As an alternative, let's consider what the Z rules actually do:
     they lift function types so they can combine with arguments that have extracted referents. But they allow *unnecessary* lifting.
     What if instead we fused them with application, yielding specialized application rules that only apply when it's necessary to combine with an extraction? That should control the slow-down, but would be subtle.

     These rules are much less general than the arbitrary lifting, because they won't automatically play well with other combinators --- we may end up needing quite a few more of these. Each seems to slow down search a little bit, so we will keep these in their own module: these will be scoped instances. We'll keep the original rules around as local instances (which will never be considered in real searches) so we can prove conservativity
  -/
  /-- A condensation of `GR` and `SynthRApp` -/
  scoped instance DAppGR {P:Type u}[HeytingAlgebra P]{X mid Y A B C}
    [StrictSubList X mid][StrictSubList mid Y]
    [f:DSynth P X mid (A // B)][arg:DSynth P mid Y (B % (@NP C))]
    : DSynth P X Y (A % (@NP C)) where
    dsem := fun c => f.dsem (arg.dsem c)
  /-- A condensation of `GL` and `SynthLApp` -/
  scoped instance DAppGL {P:Type u}[HeytingAlgebra P]{X mid Y A B C}
    [StrictSubList X mid][StrictSubList mid Y]
    [arg:DSynth P X mid (B % (@NP C))][f:DSynth P mid Y (B ∖ A)]
    : DSynth P X Y (A % (@NP C)) where
    dsem := fun c => f.dsem (arg.dsem c)
  scoped instance DAppZRR {P:Type u}[HeytingAlgebra P]{X mid Y A B C}
    [StrictSubList X mid][StrictSubList mid Y]
    [f:DSynth P X mid ((A // (@NP B)) // C)][arg:DSynth P mid Y (C % (@NP B))]
    : DSynth P X Y (A // (@NP B)) where
    dsem := fun n => f.dsem (arg.dsem n) n
  scoped instance DAppZLR {P:Type u}[HeytingAlgebra P]{X mid Y A B C}
    [StrictSubList X mid][StrictSubList mid Y]
    [f:DSynth P X mid (((@NP B) ∖ A) // C)][arg:DSynth P mid Y (C % (@NP B))]
    : DSynth P X Y ((@NP B) ∖ A) where
    dsem := fun n => f.dsem (arg.dsem n) n
  scoped instance DAppZRL {P:Type u}[HeytingAlgebra P]{X mid Y A B C}
    [StrictSubList X mid][StrictSubList mid Y]
    [arg:DSynth P X mid (C % (@NP B))][f:DSynth P mid Y (C ∖ (A // (@NP B)))]
    : DSynth P X Y (A // (@NP B)) where
    dsem := fun n => f.dsem (arg.dsem n) n
  scoped instance DAppZLL {P:Type u}[HeytingAlgebra P]{X mid Y A B C}
    [StrictSubList X mid][StrictSubList mid Y]
    [arg:DSynth P X mid (C % (@NP B))][f:DSynth P mid Y (C ∖ ((@NP B) ∖ A))]
    : DSynth P X Y (A // (@NP B)) where
    dsem := fun n => f.dsem (arg.dsem n) n

  -- For now we'll keep the word 'the' under wraps as well
  scoped instance (priority := high) the_lex {P}[HeytingAlgebra P]{T}: lexicon P "the" ((@NP T % @NP T) // (@CN T)) where
    denotation := fun _cn x => x
  /- Another difficulty here is that for modified CNs (those that don't just denote true), this definition discards the restriction --- e.g., 'the even number' could resolve to an 'odd number'!

  One option would be to tweak CNs again to have them also reflect their predicate into the typeclass unification problem. But that will lead to problems with TC search failing for equivalent but not definitionally equal predicates (even positive vs positive even).

  Another approach would be to treat 'the' as a GQ that gets its argument externally (so, type is roughtly GQ|NP, so the semantics capture sentence-combining things), then could apply the CN predicate to whatever gets bound as a sanity check.
  -/

end DiffJacobson

@[simp]
def dspec (L : List String) [D: DSynth Prop L [] S] : Prop := D.dsem

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
set_option trace.Meta.synthInstance.instances true
set_option trace.Meta.synthInstance.newAnswer true

-- Let's confirm the proof theory is complete enough to find this
def three_is_even_parse : DSynth Prop ("three"::"is"::"even"::[]) [] S :=
  let three : DSynth Prop ("three"::"is"::"even"::[]) ("is"::"even"::[]) (@NP Nat):= DLex (l:=threelex)
  let is : DSynth Prop ("is"::"even"::[]) ("even"::[]) (((@NP Nat) ∖ S) // (@ADJ Nat)):= DLex (l:=noun_is_adj_lex)
  let even : DSynth Prop ("even"::[]) [] (@ADJ Nat) := DLex (l:=evenlex)
  let is_even : DSynth Prop ("is"::"even"::[]) [] ((@NP Nat) ∖ S) := DRApp (L:=is) (R:=even)
  DLApp (L:=three) (R:=is_even)
#check three_is_even_parse.dsem

@[simp]
def three_is_even_diff := dspec ("three"::"is"::"even"::[])

def three_is_even_pf : three_is_even_diff :=
  by simp
     sorry

-- hack experiment to play with left-side multi-word constituents
instance length_lex : lexicon Prop "length" (@NP (String -> Nat)) where
  denotation := String.length
instance my_lex {A} : lexicon Prop "my" ((@NP A) // (@NP (String -> A))) where
  denotation f := f "my"

def hack_ : dspec ("my"::"length"::"is"::"even"::[]) :=
  by simp

-- VFA Sort examples
def insert_sorted_spec'' : insert_sorted_spec -> dspec ("insertion"::"of"::"any"::"natural"::"maintains"::"sortedness"::[]) :=
  by simp [insert_sorted_spec]
     intro H
     apply H

  def sort_sorted_spec' : sort_sorted_spec -> dspec ("sort"::"sorts"::"any"::"list"::"of"::"naturals"::[]) :=
    by simp [sort_sorted_spec]
       intro H 
       apply H

  def insert_perm_spec' := dspec ("insert"::"is"::"a"::"permutation"::"of"::"cons"::[])

  def sort_perm_spec' : 
    sort_perm_spec -> dspec ("sort"::"is"::"a"::"permutation"::[]) :=
    by simp [sort_perm_spec]
       intro H
       exists sort
  def insertion_sort_correct_spec' : insertion_sort_correct_spec -> dspec ("sort"::"is"::"a"::"sorting"::"permuting"::"algorithm"::[]) :=
    by simp [insertion_sort_correct_spec]
       simp [is_a_sorting_algorithm]
       intro H
       exists sort
       simp
       apply And.intro
       . intro l
         match (H l) with
         | ⟨ _, b ⟩ => exact b
       . intro l
         match (H l) with
         | ⟨ a, _ ⟩ => exact a

-- VFA MultiSet examples
-- TODO: This is only the ones that worked at the time of initial DiffList experiments

@[simp]
def union_assoc_spec_d := dspec ("union"::"is"::"associative"::[])
@[simp]
def insert_contents_spec_d := dspec ("insertion"::"of"::"any"::"value"::"preserves"::"contents"::[])
@[simp]
def sort_contents_spec_d := dspec ("sort"::"preserves"::"contents"::[])

@[simp]
def insertion_sort_correct_spec2_d := dspec ("sort"::"preserves"::"contents"::"and"::"sorts"::[])


open DiffJacobson

instance its_contents_manual_hack : DSynth Prop ("its"::"contents"::"are"::"empty"::[]) ("are"::"empty"::[]) ((@NP multiset) % (@NP (List value))) :=
  DRApp (L:= DLex (l := its_ref)) (R:=DLex (l := contents_lex))

-- TODO: plural values
--def contents_nil_inv_spec_d := dspec ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[])

def dbgdspec (P:Type u) (X Y : List String)[StrictSubList X Y] (C:Cat) [D:DSynth P X Y C] : DSynth P X Y C := D


def contents_nil_inv_spec_d_manual : DSynth Prop ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) [] S :=
  let any_list_of_value := dbgdspec Prop ("any"::"list"::"of"::"value"::"is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) ("is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) (S // ((@NP (List value)) ∖ S)) 
  let is_empty := dbgdspec Prop ("is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) ("when"::"its"::"contents"::"are"::"empty"::[]) ((@NP (List value)) ∖ S)
  -- Yet again, we can't infer semantics for "its contents" even though it's totally trivial. Something about the lexical entries involved are not playing nice with Lean's unification.
  let its_contents := dbgdspec Prop ("its"::"contents"::"are"::"empty"::[]) ("are"::"empty"::[]) ((@NP multiset) % (@NP (List value)))
  --let its_contents_manual : DSynth Prop ("its"::"contents"::"are"::"empty"::[]) ("are"::"empty"::[]) ((@NP multiset) % (@NP (List value))) :=
  --  DRApp (L:= DLex (l := its_ref)) (R:=DLex (l := contents_lex))
  -- Even with the above manual construction lifted as before to a hack instance, this next bit fails to parse, suggesting a bug in the port of the Jacobson specialization... Ah, yes, it helps to actually open the module with the required local instances
  let its_contents_are_empty := dbgdspec Prop ("its"::"contents"::"are"::"empty"::[]) [] (S % (@NP (List value)))
  --let when_its_contents_are_empty := dbgdspec Prop ("when"::"its"::"contents"::"are"::"empty"::[]) [] (((@NP (List value)) ∖ S) ∖ ((@NP (List value)) ∖ S))
  let is_empty_when_its_contents_are_empty := dbgdspec Prop ("is"::"empty"::"when"::"its"::"contents"::"are"::"empty"::[]) [] ((@NP (List value)) ∖ S)
  DRapp (L:=any_list_of_value) (R:=is_empty_when_its_contents_are_empty)


-- Here I have to port the 'experiments' section from Multiset to DSynth (those are the rules for variables) and try "for any list of value al for any list of value bl the contents of al equals the contents of bl when al is a permutation of bl" or similar