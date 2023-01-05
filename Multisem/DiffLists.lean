import Multisem.Grammar
import Multisem.Lexicon
-- Temporary while exploring this as an alternative context structure:
import Multisem.CaseStudies.VFA.Sort
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


-- TODO: Port Jacobson section



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