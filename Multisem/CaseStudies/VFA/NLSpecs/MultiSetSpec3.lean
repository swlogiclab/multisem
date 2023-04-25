import Multisem.Grammar
import Multisem.Lexicon
import Multisem.DiffListEncoding
import Multisem.Text.ListMacros
import Multisem.CaseStudies.VFA.Sort
import Multisem.CaseStudies.VFA.MultiSet
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

  -- Original: Prove that multisets in a nested union can be swapped
  /- Note: This original is actually ambiguous, nothing explicitly 
     suggests that you're swapping in and out of the inner union,
     this text in isolation could mean
     `union a (union b c) = union a (union c b)`
     which is just a consequence of commutativity.
     In fact, the entire property itself follows trivially from commutativity and associativity. The only way this makes sense to describe is as the naive transliteration of the formal spec.

     Codex (davinci-002), prompted with a Coq comment, the core definitions, and a comment with this original description proves something equivalent to what's sought here, but it's worth noting that VFA and countless student solution attempts are in its training set!
  -/
  -- I don't think this makes sense as stated
  @[simp]
  def union_swap_raw := ∀ (a b c : multiset), union a (union b c) = union b (union a c)