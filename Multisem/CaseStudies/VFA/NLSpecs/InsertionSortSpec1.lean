import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000


-- Original: Prove that insertion sort's insert function produces the same contents as merely prepending the inserted element to the front of the list
-- Note: This is very verbose, and can be said much more succinctly
-- Proposal: insertion of any value preserves contents
-- Note: value was chosen here rather than natural for unification purposes

/- Candidate replacement: insertion and cons of any value have the same contents
-- insertion/cons : NP (list val -> list val) // PP OFN val
-- and [derivable as] : (NP A // C) \ (NP (A × A) // C) / (NP A // C)
-- ^^ for noun clustering
-- that gets us [insertion and cons of any value] : S // (NP (A×A) \ S)) with existing [any value]
-- contents : NP (list value -> multiset)
-- same ??? // NP (A -> B)
-- have : (NP (A×A) \ S) // ??
-- Replacement candidate 2: insertion and cons of any value have [equal contents]
-- equal : (ADJ (A×A)) // @NP (A -> B)
-- ^^ at least semantically. Could give have a RHS arg of ADJ. Is that grammatically correct? Unclear. Could also make 'equal' a postmodifier of 'have' : NP (A×A) \ S // NP (A -> B), but then unclear what standalone semantics of have would be to permit the modification: can't just be 'exists', which is also trivial since it's taking a function..
-- AH!
-- have : (NP (A×A) \ S) // (NP (A -> B)) // ADJ (B×B)
-- equal : ADJ (A×A)
-/

-- General purpose:
open Cat
instance cons_lex : lexicon Prop "cons" ((@NP (List value -> List value)) // @PP value PPType.OF) where
  denotation pp :=  List.cons pp
instance and_np_cluster_2 {A}{C : Cat}: lexicon Prop "and" (((@NP A // C) ∖ (@NP (A × A) // C)) // (@NP A // C)) where
  denotation r l c := ⟨ l c , r c ⟩
instance have_cluster {A B} : lexicon Prop "_have" (((@NP (A×A) ∖ S) // (@NP (A -> B))) // (@ADJ (B×B))) where
  denotation (adj: B×B -> Prop) (proj:A -> B) (pair:A×A) := adj ⟨ proj pair.1, proj pair.2 ⟩
instance equal_cluster {A} : lexicon Prop "equal" (@ADJ (A×A)) where
  denotation p := p.1 = p.2

-- Apparently [have] is a keyword?
local instance insertionsortspec1 : CurrentString [| insertion and cons of any value yield equal contents |] where

@[simp]
def insert_contents_raw := ∀ x l, contents (sort.insert x l) = contents (x :: l)

-- Testing manual construction
#check @DLex
def insertion_and_cons_of : DSynth Prop 0 4 false true ((@NP ((List value -> List value) × (List value -> List value))) // @NP value) :=
  let ins : DSynth Prop 0 1 false false _ := DLex 0 "insertion" ((@NP (List value -> List value)) // @PP value PPType.OF)
  let A := (List value -> List value)
  let C := @PP value PPType.OF
  let a : DSynth Prop 1 2 false false _ := DLex 1 "and" (((@NP A // C) ∖ (@NP (A × A) // C)) // (@NP A // C))
  let cns : DSynth Prop 2 3 false false _ := DLex 2 "cons" ((@NP (List value -> List value)) // @PP value PPType.OF)
  DRComp (L:=(DLApp (L := ins) (R := DRApp (L:=a) (R:= cns)))) (R:=DLex 3 "of" (@PP value PPType.OF // @NP value))
def any_val {C}: DSynth Prop 4 6 false false ((C // (@NP value)) ∖ (S // (C ∖ S))) :=
  DRApp (L:= DLex 4 "any" (((C // (@NP value)) ∖ (S // (C ∖ S))) // (@CN value)))
        (R:=DLex 5 "value" (@CN value))
def insertion_and_cons_of_any_value : DSynth Prop 0 6 false false (S // ((@NP ((List value -> List value) × (List value -> List value))) ∖ S)) :=
  DLApp (L:=insertion_and_cons_of) (R:=any_val)

instance yield_cluster_lex {I A B:Type}: lexicon Prop "yield" (((@NP ((I->A)×(I->A)) ∖ S) // (@NP (A -> B))) // (@ADJ (B×B))) where
  denotation (adj: B×B -> Prop) (proj:A -> B) (pair:(I->A)×(I->A)) := ∀ (i:I), adj ⟨ proj (pair.1 i), proj (pair.2 i)⟩

def yield_equal_contents : DSynth Prop 6 9 false false ((@NP ((List value -> List value) × (List value -> List value))) ∖ S) :=
  let I := (List value)
  let A := (List value)
  let B := multiset
  let y : DSynth Prop 6 7 false false (((@NP (((List value)->(List value))×((List value)->(List value))) ∖ S) // (@NP ((List value) -> multiset))) // (@ADJ (multiset×multiset))) := DLex 6 "yield" (((@NP ((I->A)×(I->A)) ∖ S) // (@NP (A -> B))) // (@ADJ (B×B)))
  let e := DLex 7 "equal" (@ADJ (B × B))
  let c := DLex 8 "contents" (@NP (List value -> multiset))
  let ye := DRApp (L:=y) (R:=e)
  let yec := DRApp (L:= ye) (R:=c)
  yec
def full : DSynth Prop 0 9 false false S := DRApp (L:= insertion_and_cons_of_any_value) (R:= yield_equal_contents)
theorem manual_correct : insert_contents_raw = full.dsem :=
  by simp [full, insertion_and_cons_of_any_value, insertion_and_cons_of, any_val, yield_equal_contents]


@[simp]
def dbgdspec_range (L : List String) (n n':Nat) [_cur:CurrentString L] {lc rc}(C)[D:DSynth Prop n n' lc rc C] : DSynth Prop n n' lc rc C := D

def insertion_and_cons_of_synth := dbgdspec_range [| insertion and cons of any value yield equal contents |] 0 4 ((@NP ((List value -> List value) × (List value -> List value))) // @NP value)

def insertion_and_cons_of_any_value_synth := dbgdspec_range [| insertion and cons of any value yield equal contents |] 0 6 (S // ((@NP ((List value -> List value) × (List value -> List value))) ∖ S))

def insertion_synth := dbgdspec_range [| insertion and cons of any value yield equal contents |] 0 1 ((@NP (List value -> List value)) // @PP value PPType.OF)

def yield_equal_contents_synth := dbgdspec_range [| insertion and cons of any value yield equal contents |] 6 9 ((@NP ((List value -> List value) × (List value -> List value))) ∖ S)

def value_synth := dbgdspec_range [| insertion and cons of any value yield equal contents |] 5 6 (@CN value)

def yield_synth := dbgdspec_range [| insertion and cons of any value yield equal contents |] 6 7 (((@NP (((List value)->(List value))×((List value)->(List value))) ∖ S) // (@NP ((List value) -> multiset))) // (@ADJ (multiset×multiset)))

def equal_synth  : DSynth Prop 7 8 false false (@ADJ (multiset×multiset)):= 
  dbgdspec_range [| insertion and cons of any value yield equal contents |] 7 8 (@ADJ (multiset × multiset))
  --DLex 7 "equal" _

def contents_synth := dbgdspec_range [| insertion and cons of any value yield equal contents |] 8 9 (@NP (List value -> multiset))

--set_option trace.Meta.synthInstance.instances true
--set_option trace.Meta.synthInstance.newAnswer true
--@[simp]
--def insert_contents_spec := dspec [| insertion and cons of any value yield equal contents |]
--theorem insert_contents_consistent : insert_contents_raw = insert_contents_spec :=
--  by simp