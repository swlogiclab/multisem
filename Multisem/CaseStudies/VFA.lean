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
end sort

section searchtree

  @[simp]
  def key := Nat
  deriving instance LT for key --

  -- There's almost certainly a better way to do this, like naming the original instance, but I can't find it in the stdlib
  @[simp] def getDec (x y : Nat)[d:Decidable (x < y)] := d
  instance {x y : key} : Decidable (x < y) :=
    by revert x y
       simp [key]
       intro x y
       apply getDec
  instance {x : Nat} : OfNat key x := OfNat.mk x

       
  inductive tree {V : Type u} : Type u where
  | E
  | T (l: @tree V) (k: key) (v: V) (r: @tree V)
  -- Aiming to preserve the implicit args structure of the original
  open tree

  def empty_tree {V : Type u} : @tree V := E
  def bound {V : Type u} (x : key) (t : @tree V) :=
    match t with
    | E => false
    | T l y v r => if x < y then bound x l
                   else if x > y then bound x r
                   else true
  def lookup {V : Type u} (d : V) (x : key) (t : @tree V) : V :=
    match t with
    | E => d
    | T l y v r => if x < y then lookup d x l
                   else if x > y then lookup d x r
                   else v
  def insert {V : Type u} (x : key) (v : V) (t : @tree V) : @tree V :=
    match t with
    | E => T E x v E
    | T l y v' r => if x < y then T (insert x v l) y v' r
                    else if x > y then T l y v' (insert x v r)
                    else T l x v r

  -- "Unit tests"
  def ex_tree := T (T E 2 "two" E) 4 "four" (T E 5 "five" E)
  def bst_ex1 : insert 5 "five" (insert 2 "two" (insert 4 "four" empty_tree)) = ex_tree := by rfl
  def bst_ex2 : lookup "" 5 ex_tree = "five" := by rfl
  def bst_ex3 : lookup "" 3 ex_tree = "" := by rfl
  def bst_ex4 : bound 3 ex_tree = false := by rfl

  -- BST Invariant section
  def ForallT {V : Type} (P: key → V → Prop) (t: @tree V) : Prop :=
    match t with
    | E => True
    | T l k v r => P k v ∧ ForallT P l ∧ ForallT P r
  inductive BST {V : Type} : @tree V → Prop :=
  | BST_E : BST E
  | BST_T : ∀ l x v r,
      ForallT (fun y _ => y < x) l →
      ForallT (fun y _ => y > x) r →
      BST l →
      BST r →
      BST (T l x v r)

  -- Prove that the empty tree is a BST
  def empty_tree_BST_spec := ∀ (V:Type), BST (@empty_tree V)
  -- insert preserves any node predicate
  def ForallT_insert_spec := ∀ (V : Type) (P : key → V → Prop) (t : @tree V),
    ForallT P t → ∀ (k : key) (v : V),
      P k v → ForallT P (insert k v t)
  -- No explicit English
  def insert_BST_spec := ∀ (V : Type) (k : key) (v : V) (t : @tree V),
    BST t → BST (insert k v t)

  -- Correctness of BST Operations
  -- No explicit English
  def lookup_empty_spec := ∀ (V : Type) (d : V) (k : key), lookup d k empty_tree = d
  -- No explicit English
  def lookup_insert_eq_spec := ∀ (V : Type) (t : @tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v
  -- No explicit English
  def lookup_insert_eq'_spec :=
  ∀ (V : Type) (t : @tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v
  -- No explicit English
  def lookup_insert_neq_spec :=
  ∀ (V : Type) (t : @tree V) (d : V) (k k' : key) (v : V),
   k ≠ k' → lookup d k' (insert k v t) = lookup d k' t

  -- Omitting Exercise 3 (bound_correct) because it's basically a homework assignment, and this file will become public

  -- if bound returns false, then lookup returns the default value
  def bound_default_spec :=
  ∀ (V : Type) (k : key) (d : V) (t : @tree V),
    bound k t = false →
    lookup d k t = d

  -- Omitting: BSTs vs. Higher-order Functions (Optional)
  -- Because we have not transfered the maps module this section relies on

  -- This is a good module to work with, since it explores a bunch of specification styles
  -- TODO: Converting a BST to a List
  def elements {V : Type} (t : @tree V) : List (key × V) :=
  match t with
  | E => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  def elements_ex :
    elements ex_tree = [(2, "two"), (4, "four"), (5, "five")] :=
    by rfl

  -- ATTENTION: This is the broken spec
  def elements_complete_broken_spec :=
  ∀ (V : Type) (k : key) (v d : V) (t : @tree V),
    BST t →
    lookup d k t = v →
    List.Mem (k, v) (elements t)

  -- elements is complete: if a binding is in t then it's in elements t
  def elements_complete_spec :=
  ∀ (V : Type) (k : key) (v d : V) (t : @tree V),
    bound k t = true →
    lookup d k t = v →
    List.Mem (k, v) (elements t)

  --  elements is correct: if a binding is in elements t then it's in t. 
  def elements_correct_spec :=
  ∀ (V : Type) (k : key) (v d : V) (t : @tree V),
    BST t →
    List.Mem (k, v) (elements t) →
    bound k t = true ∧ lookup d k t = v

  def uncurry {X Y Z : Type u} (f : X → Y → Z) (ab: X × Y) :=
  f (ab.fst) (ab.snd)

  -- Implement Coq's List.Forall for this? Need something like List.all but for Prop, all is for Bool
  def Forall {T : Type u} (P : T -> Prop) (l : List T) : Prop :=
    ∀ t, List.Mem t l -> P t

  -- Prove that if a property P holds of every node in a tree t, then that property holds of every pair in elements t. 
  def elements_preserves_forall_spec := ∀ (V : Type) (P : key → V → Prop) (t : @tree V),
    ForallT P t →
    Forall  (uncurry P)  (elements t)

  -- Prove that if all the keys in t are in a relation R with a distinguished key k', then any key k in elements t is also related by R to k'
  def elements_preserves_relation_spec :=
  ∀ (V : Type) (k k' : key) (v : V) (t : @tree V) (R : key → key → Prop),
    ForallT (fun y _ => R y k') t
    → List.Mem (k, v) (elements t)
    → R k k'

  -- No explicit English
  def elements_complete_inverse_spec :=
  ∀ (V : Type) (k : key) (v : V) (t : @tree V),
    BST t →
    bound k t = false →
    ¬ List.Mem (k, v) (elements t)

  -- "Prove the inverse"
  def bound_value_spec := ∀ (V : Type) (k : key) (t : @tree V),
    bound k t = true → ∃ v, ∀ d, lookup d k t = v

  -- "Prove the main result"
  def elements_correct_inverse_spec :=
  ∀ (V : Type) (k : key) (t : @tree V),
    (∀ v, ¬ List.Mem (k, v) (elements t)) →
    bound k t = false

  -- Prove that inserting an intermediate value between two lists maintains sortedness
  def sorted_app_spec := ∀ l1 l2 x,
  sort.sorted l1 → sort.sorted l2 →
  Forall (fun n => n < x) l1 → Forall (fun n => n > x) l2 →
  sort.sorted (l1 ++ x :: l2)

  def list_keys {V : Type} (lst : List (key × V)) :=
  List.map (fun x => x.fst) lst

  --  Prove that elements t is sorted by keys. Proceed by induction on the evidence that t is a BST. 
  def sorted_elements_spec := ∀ (V : Type) (t : @tree V),
    BST t → sort.sorted (list_keys (elements t))

  def disjoint {X:Type u} (l1 l2: List X) := ∀ (x : X),
    List.Mem x l1 → ¬ List.Mem x l2

  -- Coq's List.NoDup
  axiom NoDup {T:Type u} (l:List T) : Prop
  -- Prove that if two lists are disjoint, appending them preserves NoDup.
  def NoDup_append_spec := ∀ (X:Type) (l1 l2: List X),
  NoDup l1 → NoDup l2 → disjoint l1 l2 →
  NoDup (l1 ++ l2)

  -- Prove that there are no duplicate keys in the list returned by elements
  def elements_nodup_keys_spec := ∀ (V : Type) (t : @tree V),
    BST t →
    NoDup (list_keys (elements t))

  -- A Faster elements Implementation
  def fast_elements_tr {V : Type} (t : @tree V)
         (acc : List (key × V)) : List (key × V) :=
  match t with
  | E => acc
  | T l k v r => fast_elements_tr l ((k, v) :: fast_elements_tr r acc)

  def fast_elements {V : Type} (t : @tree V) : List (key × V) :=
  fast_elements_tr t []

  -- No explicit English; this is a helper lemma for the next spec
  def fast_elements_tr_helper_spec :=
  ∀ (V : Type) (t : @tree V) (lst : List (key × V)),
    fast_elements_tr t lst = elements t ++ lst

  -- Prove that fast_elements and elements compute the same function. 
  def fast_elements_eq_elements_spec := ∀ (V : Type) (t : @tree V),
    fast_elements t = elements t

  --  Since the two implementations compute the same function, all the results we proved about the correctness of elements also hold for fast_elements. For example: 
  def fast_elements_correct_spec :=
  ∀ (V : Type) (k : key) (v d : V) (t : @tree V),
    BST t →
    List.Mem (k, v) (fast_elements t) →
    bound k t = true ∧ lookup d k t = v

  -- An Algebraic Specification of elements

  -- No explicit English
  def elements_empty_spec := ∀ (V : Type),
    @elements V empty_tree = []

  def kvs_insert {V : Type} (k : key) (v : V) (kvs : List (key × V)) :=
    match kvs with
    | [] => [(k, v)]
    | (k', v') :: kvs' =>
      if k < k' then (k, v) :: kvs
      else if k > k' then (k', v') :: kvs_insert k v kvs'
           else (k, v) :: kvs'

  -- No explicit English
  -- Part of the point of this section of the chapter is to basically say this kind of spec is hideous and should be avoided
  def kvs_insert_split_spec :=
  ∀ (V : Type) (v v0 : V) (e1 e2 : List (key × V)) (k k0 : key),
    Forall (fun (k',_) => k' < k0) e1 →
    Forall (fun (k',_) => k' > k0) e2 →
    kvs_insert k v (e1 ++ (k0,v0):: e2) =
    if k < k0 then
      (kvs_insert k v e1) ++ (k0,v0)::e2
    else if k > k0 then
           e1 ++ (k0,v0)::(kvs_insert k v e2)
         else
           e1 ++ (k,v)::e2

  -- No explicit English
  def kvs_insert_elements_spec := ∀ (V : Type) (t : @tree V),
    BST t →
    ∀ (k : key) (v : V),
      elements (insert k v t) = kvs_insert k v (elements t)

  -- Omitting: Model-based Specifications
  -- For now: there are no English specs
  -- Omitting: An Alternative Abstraction Relation (Optional, Advanced)

end searchtree

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
  instance sorts_lex : lexicon Prop "sorts" (rslash (lslash (@NP (List Nat -> List Nat)) S) (@NP (List Nat))) where
    denotation obj subj := sorted (subj obj)

  instance permutation_lifted {A B : Type}: lexicon Prop "permutation" (rslash (@CN (A -> B -> List Nat)) (@PP (A -> B -> List Nat) PPType.OF)) where
    denotation other f := ∀ a b, Permutation (other a b) (f a b)


  instance insertion_func : lexicon Prop "insertion" (rslash (@NP (List Nat -> List Nat)) (@PP Nat PPType.OF)) where
    denotation pp := insert pp
  instance maintains_lex : lexicon Prop "maintains" (rslash (lslash (@NP (List Nat -> List Nat)) S) (@NP (List Nat -> Prop))) where
    denotation prop f := ∀ x, prop x -> prop (f x)

  -- Long long term, we could bake in some morphology that lifts 'sorted' from ADJ to 'sortedness' referring to the underlying predicate
  instance sortedness_lex : lexicon Prop "sortedness" (@NP (List Nat -> Prop)) where
    denotation := sorted
  -- Sanity check: works, just need an updated lexical entry for 'any'
  section DebuggingExample
    def _check := pspec [|insertion of three maintains sortedness|]
    #check (any_ppobject (A:=(List Nat)) (C:=@NP (List Nat -> List Nat)))
    def insertion_of := dbgspecwitness Prop [|insertion of|] (rslash (@NP (List Nat -> List Nat)) (@NP Nat))
    def any_natural {C:Cat} := dbgspecwitness Prop [|any natural|] (lslash (rslash C (@NP Nat)) (rslash S (lslash C S)))
    def any_natural_manual {C:Cat} : Synth Prop [|any natural|] (lslash (rslash C (@NP Nat)) (rslash S (lslash C S))) :=
      SynthRApp (L:=SynthLex (l:= any_ppobject)) (R:=SynthLex (l:= natural_lex))
    def insertion_of_any_natural := dbgspec [|insertion of any natural|] (rslash S (lslash (@NP (List Nat -> List Nat)) S))
    def maintains_sortedness := dbgspec [| maintains sortedness |] (lslash (@NP (List Nat -> List Nat)) S)
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