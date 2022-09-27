import Multisem.Text.Macros
import Multisem.Lexicon

universe u v

namespace sort
  open List
  open Option
  def insert (i : Nat) (l : List Nat) :=
    match l with
    | [] => [i]
    | h :: t => if i <= h then i :: h :: t else h :: insert i t
  def sort (l : List Nat) : List Nat :=
    match l with
    | [] => []
    | h :: t => insert h (sort t)

  inductive sorted : List Nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_1 : ∀ x, sorted [x]
  | sorted_cons : ∀ x y l, x ≤ y -> sorted (y :: l) -> sorted (x :: y :: l)

  #check List.get!
  def sorted'' (al : List Nat) := forall i j, i < j -> j < List.length al -> List.get! al i ≤ List.get! al j
  def sorted' (al : List nat) := forall i j iv jv,
    i < j -> List.get? al i = some iv -> List.get? al j = some jv

  axiom Permutation {A : Type u}: List A -> List A -> Prop

  def is_a_sorting_algorithm (f: List Nat -> List Nat) := ∀ al, Permutation al (f al) ∧ sorted (f al)

  -- Prove that insertion maintains sortedness
  def insert_sorted_spec := ∀ a l, sorted l -> sorted (insert a l)
  -- Prove that insertion sort makes a list sorted
  def sort_sorted_spec := ∀ l, sorted (sort l)
  -- No explicit English for this one:
  def insert_perm_spec := ∀ x l, Permutation (x :: l) (insert x l)
  -- Prove that sort is a permutation
  def sort_perm_spec := ∀ l, Permutation l (sort l)
  -- No explicit English
  def insertion_sort_correct_spec := is_a_sorting_algorithm sort

  -- No explicit English
  def sorted_sorted' := ∀ al, sorted al → sorted' al
  def sorted'_sorted := ∀ al, sorted' al → sorted al

  -- Omitting the optional section on Proving Correctness from the Alternative Spec

namespace sort_specs
  open sort
  open Cat

  lex sorted for Prop as (@ADJ (List Nat))
  lex sort for Prop as (@NP (List Nat -> List Nat))
  lex insert for Prop as (@NP (Nat -> List Nat -> List Nat))
  instance cons_lex {T:Type}: lexicon Prop "cons" (@NP (T -> List T -> List T)) where
    denotation := List.cons

  instance permutation_noun {T:Type}: lexicon Prop "permutation" (@CN (List T -> List T)) where
    denotation := fun f => ∀ (l:List T), Permutation l (f l)
  instance permuting_adj {T:Type} : lexicon Prop "permuting" (@ADJ (List T -> List T)) where
    denotation := fun f => ∀ (l:List T), Permutation l (f l)

  instance sorting : lexicon Prop "sorting" (@ADJ  (List Nat -> List Nat)) where
    denotation := fun f => ∀ l, sorted (f l)
  instance sorts_lex : lexicon Prop "sorts" (((@NP (List Nat -> List Nat)) ∖ S) // (@NP (List Nat))) where
    denotation obj subj := sorted (subj obj)

  instance permutation_lifted {A B : Type}: lexicon Prop "permutation" ((@CN (A -> B -> List Nat)) // (@PP (A -> B -> List Nat) PPType.OF)) where
    denotation other f := ∀ a b, Permutation (other a b) (f a b)


  instance insertion_func : lexicon Prop "insertion" ((@NP (List Nat -> List Nat)) // (@PP Nat PPType.OF)) where
    denotation pp := insert pp
  instance maintains_lex : lexicon Prop "maintains" (((@NP (List Nat -> List Nat)) ∖ S) // (@NP (List Nat -> Prop))) where
    denotation prop f := ∀ x, prop x -> prop (f x)

  -- Long long term, we could bake in some morphology that lifts 'sorted' from ADJ to 'sortedness' referring to the underlying predicate
  instance sortedness_lex : lexicon Prop "sortedness" (@NP (List Nat -> Prop)) where
    denotation := sorted
  -- Sanity check: works, just need an updated lexical entry for 'any'
  section DebuggingExample
    def _check := pspec [|insertion of three maintains sortedness|]
    #check (any_ppobject (A:=(List Nat)) (C:=@NP (List Nat -> List Nat)))
    def insertion_of := dbgspecwitness Prop [|insertion of|] ((@NP (List Nat -> List Nat)) // (@NP Nat))
    def any_natural {C:Cat} := dbgspecwitness Prop [|any natural|] ((C // (@NP Nat)) ∖ (S // (C ∖ S)))
    def any_natural_manual {C:Cat} : Synth Prop [|any natural|] ((C // (@NP Nat)) ∖ (S // (C ∖ S))) :=
      SynthRApp (L:=SynthLex (l:= any_ppobject)) (R:=SynthLex (l:= natural_lex))
    def insertion_of_any_natural := dbgspec [|insertion of any natural|] (S // ((@NP (List Nat -> List Nat)) ∖ S))
    def maintains_sortedness := dbgspec [| maintains sortedness |] ((@NP (List Nat -> List Nat)) ∖ S)
  end DebuggingExample

  -- Original was: insertion maintains sortedness
  -- Candidate: insertion of any natural maintains sortedness
  #print insert_sorted_spec
  def insert_sorted_spec' : 
    insert_sorted_spec ->
    pspec [| insertion of any natural maintains sortedness |] :=
  by simp [insert_sorted_spec]
     intro H 
     apply H

  -- Original was: insertion sort makes a list sorted
  -- This use of "a" is universal, rather than existential, let's switch to any
  -- This original is actually ambiguous between the universal and existential reading of "a", so the rewrite improves precision
  -- Proposal is: sort sorts any list
  -- Reasoning: 'makes' here would normally suggest the list is being *mutated*, which of course it is not. Instead, we'd like to be more explicit about it returning a (possibly distinct) sorted list.
  #print sort_sorted_spec
  def sort_sorted_spec' : sort_sorted_spec -> pspec [| sort sorts any list of naturals|] :=
    by simp [sort_sorted_spec]
       intro H 
       apply H

  -- No original English, this is a proposal
  -- We'll take the route of overloading permutation to talk about one function (into `List Nat`, since that's what `Permutation` is defined on) being a permutation of another if the results for any argument set is a permutation.
  -- Technically we could generalize this for any number of arguments, but we'll just hard-code 2 for now.
  -- Proposal: insert is a permutation of cons
  #print insert_perm_spec
  def insert_perm_spec' := pspec [| insert is a permutation of cons |]

  -- Handling the original
  def sort_perm_spec' : 
    sort_perm_spec -> pspec [| sort is a permutation |] :=
    by simp [sort_perm_spec]
       intro H
       exists sort

  -- No original English, but can intuit "sort is a sorting algorithm" from the identifier
  -- We will split sorting from permuting
  #print insertion_sort_correct_spec
  #print is_a_sorting_algorithm
  def insertion_sort_correct_spec' : insertion_sort_correct_spec -> pspec [| sort is a sorting permuting algorithm |] :=
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

  -- This leaves the two lemmas proving equivalence of two sortedness defs
  -- These appear to be below the level of detail we want in English
end sort_specs