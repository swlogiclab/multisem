import Multisem.Text.Macros
import Multisem.Lexicon
import Multisem.CaseStudies.VFA.Sort

section multiset

  /- Note: VFA does a lot of this definition of short-hands for types,
     which interacts poorly with Lean's typeclass inference. Marking
     things `@[simp]` is supposed to make them transparent to typeclass
     inference, but this doesn't always work.
     On one hand this is a pain, on the other hand it's a good indication
     that doing this *outside* the proof assistant could be even worse,
     because in that setting you'd have to duplicate the equivalence checking
     in an external tool
  -/
  @[simp]
  def value := Nat
  attribute [simp] value
  deriving instance BEq for value

  def multiset := value -> Nat

  def empty : multiset := λ _x => 0

  def singleton (v:value) : multiset :=
    λ x => if x == v then 1 else 0

  def union (a b : multiset) : multiset :=
    λ x => a x + b x

  def contents (al : List value) : multiset :=
    match al with
    | [] => empty
    | a :: bl => union (singleton a) (contents bl)

  def is_a_sorting_algorithm' (f : List Nat -> List Nat) :=
    ∀ al, contents al = contents (f al) ∧ sort.sorted (f al)

end multiset

section specs

  open Cat

  section relocate_later
    instance assoc {T:Type}: lexicon Prop "associative" (@ADJ (T -> T -> T)) where
      denotation := λ f => ∀ a b c, f a (f b c) = f (f a b) c
    instance comm {T:Type}: lexicon Prop "commutative" (@ADJ (T -> T -> T)) where
      denotation := λ f => ∀ a b, f a b = f b a
    instance preserves_lex {X Y : Type}: lexicon Prop "preserves" (((@NP (X -> X)) ∖ S) // (@NP (X -> Y))) where
      denotation prop f := ∀ x, prop x = prop (f x)
  end relocate_later

  section locallex
    -- TODO: The lexicon decl needs an extra universe variable, if H is in an arbitrary universe here then it expects the operation type to be in the same universe
    instance union_lex (H:Type) : lexicon H "union" (@NP (multiset -> multiset -> multiset)) where
      denotation := union
    instance contents_lex : lexicon Prop "contents" (@NP (List value -> multiset)) where
      denotation := contents
    instance sort_np : lexicon Prop "sort" (@NP  (List value -> List value)) where
      denotation := sort.sort
    instance sorts_lex2 : lexicon Prop "sorts" ((@NP (List value -> List value)) ∖ S) where
      denotation f := ∀ l, sort.sorted (f l)

  end locallex

  -- General Multiset Specs

  -- Original: Prove that multiset union is associative
  @[simp]
  def union_assoc_raw := ∀ (a b c: multiset), union a (union b c) = union (union a b) c
  @[simp]
  def union_assoc_spec := pspec [| union is associative |]

  theorem union_assoc_consistent : union_assoc_raw -> union_assoc_spec :=
    by simp
       intro H
       apply H

  -- Original: Prove that multiset union is commutative
  @[simp]
  def union_comm_raw := ∀ (a b: multiset), union a b = union b a
  @[simp]
  def union_comm_spec := pspec [| union is commutative |]

  -- Original: Prove that multisets in a nested union can be swapped
  /- Note: This original is actually ambiguous, nothing explicitly 
     suggests that you're swapping in and out of the inner union,
     this text in isolation could mean
     `union a (union b c) = union a (union c b)`
     which is just a consequence of commutativity.
     In fact, the entire property itself follows trivially from commutativity and associativity. The only way this makes sense to describe is as the naive transliteration of the formal spec.

     Codex (davinci-002), prompted with a Coq comment, the core definitions, and a comment with this original description proves something equivalent to what's sought here, but it's worth noting that VFA and countless student solution attempts are in its training set!
  -/
  -- I don't think this makes sense
  @[simp]
  def union_swap_raw := ∀ (a b c : multiset), union a (union b c) = union b (union a c)
  @[simp]
  def union_swap_spec := pspec [|TBD|]
  theorem union_swap_consistent : union_swap_raw -> union_swap_spec :=
    by simp
       intro H
       sorry

  -- Verification of Insertion Sort

  /- TODO: To finish this batch of specs, I really need
     - support for multiple named variables
     - support for 'the' to refer to a referent (named or unnamed) introduced by a quantifier 

     Ideally I could read a solution to the first straight out of Ranta, though I could probably just tweak Jacobson's approach to work with a "named NP" construct used only for the 'hole' with discourse referents, coupled with named-quantifier forms "any list l"). Plus a tag/decl typeclass for marking which identifiers can be converted to variable references (via a lexicon instance). This is basically two minor variations on a single extension, and gets us through this chapter's specs.
  -/

  -- Original: Prove that insertion sort's insert function produces the same contents as merely prepending the inserted element to the front of the list
  -- Note: This is very verbose, and can be said much more succinctly
  -- Proposal: insertion of any value preserves contents
  -- Note: value was chosen here rather than natural for unification purposes
  @[simp]
  def insert_contents_raw := ∀ x l, contents (sort.insert x l) = contents (x :: l)
  instance insertion_func : lexicon Prop "insertion" ((@NP (List value -> List value)) // (@PP value PPType.OF)) := sort.sort_specs.insertion_func
  instance val_noun : lexicon Prop "value" (@CN value) := { denotation := fun _ => True }
  @[simp]
  def insert_contents_spec := pspec [| insertion of any value preserves contents |]
  theorem insert_contents_consistent : insert_contents_raw -> insert_contents_spec :=
    by simp
       intro H a x
       -- Aha! Indeed, this is wrong because there's no cons here

  -- Original: Prove that insertion sort preserves contents
  @[simp]
  def sort_contents_raw := ∀ l, contents l = contents (sort.sort l)
  @[simp]
  def sort_contents_spec := pspec [| sort preserves contents |]
  theorem sort_contents_consistent : sort_contents_raw -> sort_contents_spec :=
    λ x => x

  -- No original given
  -- Note: This pretty much translates the intuition behind `is_a_sorting_algorithm'`
  @[simp]
  def insertion_sort_correct_raw := is_a_sorting_algorithm' sort.sort
  @[simp]
  def insertion_sort_correct_spec2 := pspec [| sort preserves contents and sorts |]
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


  -- Equivalence of Permutation and Multiset Specifications
  -- These require dealing with two lists manipulated in various ways
  -- They also require a range of general list manipulations, which could be generally useful
  -- Arguably some of these are the sorts of "detailed internal specs" that one typically *wouldn't* try to write down explicitly in English

  instance : NLVar "al" where
  instance : NLVar "bl" where
  section experiments
    open Anaphora
    instance permutation_list : lexicon Prop "permutation" ((@CN (List value)) // (@PP (List value) PPType.OF)) where
      denotation := λ a b => sort.Permutation a b 
    instance SynthRAppVar (P:Type u){s1 s2 c1 c2}{v}{T}[L:Synth P s1 (c1 // c2)][R:Synth P s2 (c2 % (@Var T v))] : Synth P (s1#s2) (c1 % (@Var T v)) where
      denotation := λ (t:T) => @Synth.denotation P s1 (c1 // c2) L ((@Synth.denotation _ s2 _ R) t)
      stringRep := "(SynthRAppVar "++L.stringRep++" "++R.stringRep++")"
    def _a := dbgspecwitness Prop [| al is a permutation of bl |] ((S % (@Var ( List value) "bl")) % (@Var (List value) "al"))
    def _b := dbgspecwitness Prop [|permutation of bl|] ((@CN (List value)) % (@Var (List value) "bl"))
    def _bl := dbgspecwitness Prop [|bl|] (@NP (List value) % (@Var (List value) "bl"))
    def _al := dbgspecwitness Prop [|al|] (@NP (List value) % (@Var (List value) "al"))
    def _of_bl := dbgspecwitness Prop [|of bl|] ((@PP (List value) PPType.OF) % (@Var (List value) "bl"))
  end experiments

  -- No explicit English
  -- Candidate: the contents of any list al equal the contents of any list bl if al is a permutation of bl
  def perm_contents_raw := ∀ al bl, sort.Permutation al bl -> contents al = contents bl
  -- No Explicit English
  -- Note: This would be a nice demonstration of grammatical flexibiliy, dealing with nested quantifier scopes
  -- Candidate: if any list has empty contents that list is empty
  -- Candidate: any list is empty if <something about looking up the count of any key in contents>
  def contents_nil_inv_raw := ∀ l, (∀ x, 0 = contents l x) -> l = []

  -- No Explicit English
  def contents_cons_inv_raw := ∀ l x n,
    Nat.succ n = contents l x ->
    (∃ l1 l2,
      l = l1 ++ x :: l2
      ∧ contents (l1 ++ l2) x = n)
  
  -- No Explicit English
  def contents_insert_other_raw := ∀ l1 l2 x y,
    y ≠ x -> contents (l1 ++ x :: l2) y = contents (l1 ++ l2) y

  -- No Explicit English
  -- Proposal, reverse the sentence structure of the perm -> content sentence
  def contents_perm_raw := ∀ al bl, contents al = contents bl -> sort.Permutation al bl

  -- No Explicit English
  def same_contents_iff_perm_raw := ∀ al bl, contents al = contents bl ↔ sort.Permutation al bl
  -- Semi-specified in English, "the two specifications are equivalent"
  -- TODO: How subtle is the grammar for "if and only if"?
  -- TODO: Makes sense to unfold *both* definitions
  #print sort.is_a_sorting_algorithm
  def sort_specifications_equivalent_raw := ∀ f, sort.is_a_sorting_algorithm f ↔ is_a_sorting_algorithm' f





    


end specs