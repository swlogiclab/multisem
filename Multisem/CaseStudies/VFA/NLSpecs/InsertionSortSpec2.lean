import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

local instance insertionsortspec2 : CurrentString [|sort preserves contents|] where

-- Original: Prove that insertion sort preserves contents
@[simp]
def sort_contents_raw := ∀ l, contents l = contents (sort.sort l)
@[simp]
def sort_contents_spec := dspec [| sort preserves contents |]
theorem sort_contents_consistent : sort_contents_raw = sort_contents_spec :=
  by simp