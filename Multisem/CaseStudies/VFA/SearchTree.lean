import Multisem.Text.Macros
import Multisem.Lexicon
import Multisem.CaseStudies.VFA.Sort

universe u v

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
    | T l y _v r => if x < y then bound x l
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

section searchtree_specs
  open Cat
  /-- A temp hack to sketch specs without asking Lean to synthesize them -/
  axiom untranslated : ∀ (P:Type u) (t:ContextTree String), Synth P t S

  -- We'll handle polymorphism by using section variables for now
  --variable (V : Type)
  -- Okay, nevermind, that leads to tricky unification problems


  instance BST_CN {V:Type} : lexicon Prop "BST" (@CN (@tree V)) where
    denotation := BST
  -- This notion of binding is contxt/program-specific
  instance binding_CN {V:Type} : lexicon Prop "binding" (@CN (key × V)) where
    denotation := λ _ => True
  instance elements_of_NP {V:Type} : lexicon Prop "elements" ((@NP (List (key \times V))) // (@PP (@tree V) PPType.OF))
  -- TODO{V:Type} : unclear if I need this, but useful for debugging
  instance empty_tree_np {V:Type} : lexicon Prop "empty_tree" (@NP (@tree V)) where
    denotation := empty_tree

  instance tree_cn {V:Type} : lexicon Prop "tree" (@CN (@tree V)) where 
    denotation := λ _ => True
  -- TODO{V:Type} : still need to consider the ADJ --> CN/CN lift
  instance empty_cn_mod {V:Type} : lexicon Prop "empty_tree" ((@CN (@tree V)) // (@CN (@tree V))) where
    denotation := λ p x => p x ∧ x = empty_tree
  
  section general_instances_to_move
    -- TODO: Here are some general-purpose lexicon entries to move
    instance the_def_single_subj {T:Type} : lexicon Prop "the" ((S // ((@NP T) ∖ S)) // (@CN T)) where
      denotation := λ p rest => ∃ (t:T), p t ∧ (∀ t', p t' -> t' = t) ∧ rest t
    -- TODO: not really sure about how classic syntacticians would feel about this, which abuses the fact that adjectives and CNs have the same semantics
    instance a_cn_as_adj {C:Cat}{H}[HeytingAlgebra H]{T:Type} 
      : lexicon H "a" (((C // (@ADJ T)) ∖ C) // (@CN T)) where
      denotation := λ cn other => other cn
  end general_instances_to_move

  -- This is an interesting experiment with an approach to lifting polymorphism out of subterms, but I really need to try writing out and using some of the lifted application rules to make sure I don't hit problems with some cats being under a function binder.... even if it works with explicit application it might work poorly with unification
  axiom polycat.{w} : (Type w -> Cat) -> Cat
  macro_rules |  `($x ↑ $y) => `(polycat (fun $y => $x))--`(binop% LDiv.lDiv $x $y)
  #check (S ↑ x)
  axiom polycat_hack.{w} : ∀ (f:Type w -> Cat), (∀ (T:Type w), interp Prop (f t)) -> interp Prop (polycat f)
  instance empty_tree_poly : lexicon Prop "tree" ((@NP (@tree V)) ↑ V) where
    denotation := polycat_hack (fun V => ((@NP (@tree V)) ↑ V)) (fun T => @empty_tree T)

  /- The following is an interesting approach, but doesn't work because Lean doesn't actually infer universals the way the syntax suggests-/
  #check Synth.denotation
  instance polysyn : [∀ T, Synth Prop ws ((@NP (@tree T)) ∖ S)] -> Synth Prop ws S where
    denotation := (∀ (T:Type), (Synth.denotation ws (c:= ((@NP (@tree T)) ∖ S))) (@empty_tree T))
    stringRep := "(polysyn "++(Synth.stringRep Prop ws (c:=((@NP (@tree Nat)) ∖ S)))++")"
    --∀ T, Synth.denotation ws T
  
  section selfcontained
  def fakeEven (i:Nat) : Prop := True
  def fakeOdd (i:Nat) : Prop := False
  class isNum (i:Nat) where
    p : fakeEven i ∨ fakeOdd i
  class hasP (P:Nat -> Prop) where
    p : ∀ i, P i
  instance hasNum : [∀ i, isNum i] -> hasP (fun x => fakeEven x ∨ fakeOdd x) where
    p := by intro i
            apply isNum.p
  instance hasNum2 [sem:∀ i, isNum i] : hasP (fun x => fakeEven x ∨ fakeOdd x) where
    p := by intro i
            apply isNum.p
  class proveUniv (P:Nat -> Prop) where
    p := Prop
  instance hasUniv' [sem:∀ i, isNum i] : proveUniv (fun x => fakeEven x ∨ fakeOdd x) where
    p := (∀ (y:Nat), sem.p y)
  instance hasUniv : [∀ i, isNum i] -> proveUniv (fun x => fakeEven x ∨ fakeOdd x) where
    p := (∀ (y:Nat), isNum.p (i:=y))
  end selfcontained

  section selfcontained2
  class isNum2 (i:Nat) where
    p : Nat -> Prop
  class proveUniv2 where
    p := Prop
  #check isNum2.p
  instance hasUniv2' [sem:∀ i, isNum2 i] : proveUniv2  where
    p := (∀ (y:Nat), isNum2.p y y)
  end selfcontained2
  
  -- Total hack to see if this polymorphism approach has legs
  -- Yes! This works! Now the question is how to generalize this appropriately
  -- Perhaps via a Polylex class that indexes a word by a Type->Cat, plus left and right app rules like this? as in PolyLex w f and [∀ T, Synth Prop ws (f T ∖ S)] or similar?
  instance polyhack : [∀ T, Synth Prop ws ((@NP (@tree T)) ∖ S)] -> Synth Prop ("empty_tree"#ws) S where
    denotation := (∀ (T:Type), (Synth.denotation ws (c:= ((@NP (@tree T)) ∖ S))) (@empty_tree T))
    stringRep := "(polysyn "++(Synth.stringRep Prop ws (c:=((@NP (@tree Nat)) ∖ S)))++")"


  -- Original: The empty tree is a BST
  -- This actually hits *another* use for 'a' beyond universal and existential quantification. This one seems to have a unique grammatical type, so there's no need to change it to avoid ambiguity.
  -- This spec nearly works, except for choosing a V. Section variables don't help because it tries to instantiate the section variable. Manually specifying the type (e.g., Nat) lets the debug spec work, but we need this to work from text
  -- maybe we could have some of these act like generalize quantifiers to introduce quantification? But then that needs to show up in the categories of the rest of the sentence
  def debugging_empty_tree_BST_spec' := pspec [|empty_tree is a BST|]
  #print BST_CN
  #print empty_tree_np
  def debugging_empty_tree_BST_spec'' : Synth Prop [|empty_tree is a BST|] S :=
    let et_lex := SynthLex (l:=empty_tree_np)
    let bst_lex := SynthLex (l:=BST_CN)
    let a_lex := SynthLex (l:=a_cn_as_adj) -- (C:=((@NP (@tree V)) ∖ S)))
    let is_lex := SynthLex (l:=noun_is_adj_lex)
    let is_a_bst := SynthLApp (L:= is_lex) (R:=(SynthRApp (L := a_lex) (R := bst_lex)))
    SynthLApp (L:=et_lex) (R:=is_a_bst)

  noncomputable def empty_tree_BST_spec' := pspec [|the empty tree is a BST|]

  -- Original: insert preserves any node predicate
  noncomputable def ForallT_insert_spec' := untranslated Prop [|insert preserves any node predicate|]

  -- No explicit English
  -- Candidate: inserting any key and any value into any BST yields a BST
  noncomputable def insert_BST_spec' := untranslated Prop [|inserting any key and any value into any BST yields a BST|]

  -- No explicit English
  -- Note: candidate will need to talk about the default. Should we define language for 'default' in this specific context?
  noncomputable def lookup_empty_spec' := untranslated Prop [|looking up any key with any default in the empty tree yields the default|]

  -- No explicit English
  -- Note: checks that looking up a key just inserted finds the inserted value
  -- Note: Still avoiding past tense
  noncomputable def lookup_insert_eq_spec' := untranslated Prop [|TBD|]

  -- No explicit English
  -- Note: exact same spec as previous: TODO check I didn't translate it incorrectly from Coq, which I must have, otherwise why have the second def?
  -- Note: if it is slightly different, will make a good pairwise example
  noncomputable def lookup_insert_eq'_spec' := untranslated Prop [|TBD|]

  -- No explicit English
  -- Note: requires expressing inequality; natural phrasing would say 'not equal'
  noncomputable def lookup_insert_neq_spec' := untranslated Prop [|TBD|]

  -- Omitting Exercise 3 (bound_correct) b/c it's a homework assignment, and we don't want it to become public.
  -- BUT: Should translate it

  -- Ah: apparently can't use 'if' since it's a keyword, not an ident
  noncomputable def bound_default_spec' := untranslated Prop [|if bound returns false then lookup returns the default value|]

  -- Omitting: BSTs vs. Higher-order Functions (Optional)
  -- Because we have not transfered the maps module this section relies on

  -- Note: Broken (as a pedagogical example)
  -- Original: if a binding is in t then it's in elements t
  noncomputable def elements_complete_broken_spec' := untranslated Prop [|TBD|]

  -- Note: Same original spec as for the intentionally broken example above, so makes for a good contrast
  -- Original: if a binding is in t then it's in elements t
  noncomputable def elements_complete_spec' := untranslated Prop [|TBD|]

  -- Original: if a binding is in elements t then it's in t
  noncomputable def elements_correct_spec' := untranslated Prop [|TBD|]

  -- Original: if a property P holds of every node in a tree t, then that property holds of every pair in elements t. 
  noncomputable def elements_preserves_forall_spec' := untranslated Prop [|TBD|]

  -- Original: if all the keys in t are in a relation R with a distinguished key k', then any key k in elements t is also related by R to k'
  noncomputable def elements_preserves_relation_spec' := untranslated Prop [|TBD|]

  -- No explicit English
  noncomputable def elements_complete_inverse_spec' := untranslated Prop [|TBD|]

  -- Original: "prove the inverse" must be explicitly expanded
  noncomputable def bound_value_spec' := untranslated Prop [|TBD|]

  -- Original: "prove the main result" (TODO: there must be an explicit statement elsewhere for this)
  noncomputable def elements_correct_inverse_spec' := untranslated Prop [|TBD|]

  -- Original: inserting an intermediate value between two lists maintains sortedness
  noncomputable def sorted_app_spec' := untranslated Prop [|TBD|]

  -- Original: elements t is sorted by keys. Proceed by induction on the evidence that t is a BST. 
  noncomputable def sorted_elements_spec' := untranslated Prop [|TBD|]

  -- Original: if two lists are disjoint, appending them preserves NoDup
  noncomputable def NoDup_append_spec := untranslated Prop [|if two lists are disjoint then appending them preserves NoDup|]

  -- Original: there are no duplicate keys in the list returned by elements
  noncomputable def elements_nodup_keys_spec' := untranslated Prop [|TBD|]

  -- No explicit English, helper for next
  noncomputable def fast_elements_tr_helper_spec' := untranslated Prop [|TBD|]

  -- Original: fast_elements and elements compute the same function
  -- Rather than just going for equality via function extensionality, let's go direct
  noncomputable def fast_elements_eq_elements_spec' := untranslated Prop [|fast_elements and elements compute the same result for any tree |]

  -- No explicit English, but alludes to `elements_correct_spec`
  noncomputable def fast_elements_correct_spec' : Prop := sorry

  -- An Algebraic Specification of Elements

  -- No explicit English
  -- This should work, modulo polymorphism over the value type, and reconsidering if we want to deal with plurals
  noncomputable def elements_empty_spec' := untranslated Prop [|the elements of the empty tree are the empty list|]


  -- No explicit English
  -- Part of the point of this section of the chapter is to basically say this kind of spec is hideous and should be avoided
  noncomputable def kvs_insert_split_spec' : Prop := sorry

  -- No explicit English
  noncomputable def kvs_insert_elements_spec' := untranslated Prop [|on every BST every key and every value the elements of inserting the key and value into the BST are the same as kvs_inserting into the elements of the BST|]

  


end searchtree_specs