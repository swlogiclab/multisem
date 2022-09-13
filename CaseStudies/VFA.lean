
import Multisem.Text.Macros
import Multisem.Lexicon

universe u

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

       
  -- tree is the name of the structure used for parsing, which should probably be renamed
  inductive vfatree {V : Type u} : Type u where
  | E
  | T (l: @vfatree V) (k: key) (v: V) (r: @vfatree V)
  -- Aiming to preserve the implicit args structure of the original
  open vfatree

  def empty_tree {V : Type u} : @vfatree V := E
  def bound {V : Type u} (x : key) (t : @vfatree V) :=
    match t with
    | E => false
    | T l y v r => if x < y then bound x l
                   else if x > y then bound x r
                   else true
  def lookup {V : Type u} (d : V) (x : key) (t : @vfatree V) : V :=
    match t with
    | E => d
    | T l y v r => if x < y then lookup d x l
                   else if x > y then lookup d x r
                   else v
  def insert {V : Type u} (x : key) (v : V) (t : @vfatree V) : @vfatree V :=
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
  def ForallT {V : Type} (P: key → V → Prop) (t: @vfatree V) : Prop :=
    match t with
    | E => True
    | T l k v r => P k v ∧ ForallT P l ∧ ForallT P r
  inductive BST {V : Type} : @vfatree V → Prop :=
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
  def ForallT_insert_spec := ∀ (V : Type) (P : key → V → Prop) (t : @vfatree V),
    ForallT P t → ∀ (k : key) (v : V),
      P k v → ForallT P (insert k v t)
  -- No explicit English
  def insert_BST_spec := ∀ (V : Type) (k : key) (v : V) (t : @vfatree V),
    BST t → BST (insert k v t)

  -- Correctness of BST Operations
  -- No explicit English
  def lookup_empty_spec := ∀ (V : Type) (d : V) (k : key), lookup d k empty_tree = d
  -- No explicit English
  def lookup_insert_eq_spec := ∀ (V : Type) (t : @vfatree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v
  -- No explicit English
  def lookup_insert_eq'_spec :=
  ∀ (V : Type) (t : @vfatree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v
  -- No explicit English
  def lookup_insert_neq_spec :=
  ∀ (V : Type) (t : @vfatree V) (d : V) (k k' : key) (v : V),
   k ≠ k' → lookup d k' (insert k v t) = lookup d k' t

  -- Omitting Exercise 3 (bound_correct) because it's basically a homework assignment, and this file will become public

  -- if bound returns false, then lookup returns the default value
  def bound_default_spec :=
  ∀ (V : Type) (k : key) (d : V) (t : @vfatree V),
    bound k t = false →
    lookup d k t = d

  -- Omitting: BSTs vs. Higher-order Functions (Optional)
  -- Because we have not transfered the maps module this section relies on

  -- This is a good module to work with, since it explores a bunch of specification styles
  -- TODO: Converting a BST to a List
  def elements {V : Type} (t : @vfatree V) : List (key × V) :=
  match t with
  | E => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  def elements_ex :
    elements ex_tree = [(2, "two"), (4, "four"), (5, "five")] :=
    by rfl

  -- ATTENTION: This is the broken spec
  def elements_complete_broken_spec :=
  ∀ (V : Type) (k : key) (v d : V) (t : @vfatree V),
    BST t →
    lookup d k t = v →
    List.Mem (k, v) (elements t)

  -- elements is complete: if a binding is in t then it's in elements t
  def elements_complete_spec :=
  ∀ (V : Type) (k : key) (v d : V) (t : @vfatree V),
    bound k t = true →
    lookup d k t = v →
    List.Mem (k, v) (elements t)

  --  elements is correct: if a binding is in elements t then it's in t. 
  def elements_correct_spec :=
  ∀ (V : Type) (k : key) (v d : V) (t : @vfatree V),
    BST t →
    List.Mem (k, v) (elements t) →
    bound k t = true ∧ lookup d k t = v

  def uncurry {X Y Z : Type u} (f : X → Y → Z) (ab: X × Y) :=
  f (ab.fst) (ab.snd)
  -- Prove that if a property P holds of every node in a tree t, then that property holds of every pair in elements t. 
  def elements_preserves_forall_spec := ∀ (V : Type) (P : key → V → Prop) (t : @vfatree V),
    ForallT P t →
    -- TODO: implement Coq's List.Forall for this? Need something like List.all but for Prop, all is for Bool
    List.all (elements t)  (uncurry P)

  -- TODO: A Faster elements Implementation
  -- TODO: An Algebraic Specification of elements
  -- TODO: Model-based Specifications
  -- Omitting: An Alternative Abstraction Relation (Optional, Advanced)

end searchtree