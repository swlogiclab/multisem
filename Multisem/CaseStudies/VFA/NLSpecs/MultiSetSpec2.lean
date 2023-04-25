import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

-- Original: Prove that multiset union is commutative
local instance multisetspec2 : CurrentString [|union is commutative|] where
-- Original: Prove that multiset union is commutative
@[simp]
def union_comm_raw := ∀ (a b: multiset), union a b = union b a
@[simp]
def union_comm_spec := dspec [| union is commutative |]