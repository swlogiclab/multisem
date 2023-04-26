import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

local instance insertionsortspec3 : CurrentString [|sort preserves contents and sorts|] where

-- No original given
-- Note: This pretty much translates the intuition behind `is_a_sorting_algorithm'`
@[simp]
def insertion_sort_correct_raw := is_a_sorting_algorithm' sort.sort
#print is_a_sorting_algorithm'
@[simp]
def insertion_sort_correct_spec2 := dspec [| sort preserves contents and sorts |]
theorem insertion_sort_correct_consistent 
  : insertion_sort_correct_raw -> insertion_sort_correct_spec2 :=
  by simp
     simp [is_a_sorting_algorithm']
     intro H
     apply And.intro
     . intro x
       exact ((H x).1)
     . intro x
       exact ((H x).2)