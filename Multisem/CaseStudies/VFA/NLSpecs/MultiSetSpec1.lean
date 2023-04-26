import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

-- Original: Prove that multiset union is associative
local instance multisetspec1 : CurrentString [|union is associative|] where

@[simp]
def union_assoc_raw := ∀ (a b c: multiset), union a (union b c) = union (union a b) c
@[simp]
def union_assoc_spec := dspec [| union is associative |]

theorem union_assoc_consistent : union_assoc_raw = union_assoc_spec :=
  by simp