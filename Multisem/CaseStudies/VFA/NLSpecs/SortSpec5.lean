import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
open sort
open sort_specs
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

-- No original English, but can intuit "sort is a sorting algorithm" from the identifier
-- We will split sorting from permuting
local instance sortspec5 : CurrentString ("sort"::"is"::"a"::"sorting"::"permuting"::"algorithm"::[]) where

-- Without outParam on DSynth, this becomes: (∀ (l : List Nat), sorted (sort l)) ∧ ∀ (l : List Nat), Permutation l (sort l)
-- With outParam on DSynth, this becomes: ∃ a, ((∀ (l : List Nat), sorted (a l)) ∧ ∀ (l : List Nat), Permutation l (a l)) ∧ a = sort 
-- So the outParam guides this to using 'a' as an in situ quantifier via `a_directobject`, while without it it ends up using `a_cn_as_adj` (I think, hard to check the exact derivation, should try with the newInstances flag to confirm).
-- Both are equivalent, but this proof of equivalence with the manual spec is sensitive to this change.
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