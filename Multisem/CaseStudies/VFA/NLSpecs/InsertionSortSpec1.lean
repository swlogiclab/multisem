import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

local instance insertionsortspec1 : CurrentString [| insertion of any value preserves contents |] where

-- Original: Prove that insertion sort's insert function produces the same contents as merely prepending the inserted element to the front of the list
-- Note: This is very verbose, and can be said much more succinctly
-- Proposal: insertion of any value preserves contents
-- Note: value was chosen here rather than natural for unification purposes
@[simp]
def insert_contents_raw := ∀ x l, contents (sort.insert x l) = contents (x :: l)

  -- TODO: doesn't deal with cons
  @[simp]
  def insert_contents_spec := dspec [| insertion of any value preserves contents |]
  theorem insert_contents_consistent : insert_contents_raw -> insert_contents_spec :=
    by simp
       intro H a x
       -- Aha! Indeed, this is wrong because there's no cons here
       sorry