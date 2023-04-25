import Multisem.Lexicon
import Multisem.CaseStudies.VFA.Sort

-- Most of this file works fine with 200K for each, but the longer ones fail with 400K
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

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
    instance the_X_of_Y {X Y : Type}: lexicon Prop "the" (((@NP Y) // (@PP X PPType.OF)) // (@NP (X -> Y))) where
      denotation := fun f x => f x
    instance empty_list {T:Type}: lexicon Prop "empty" (@ADJ (List T)) where
      denotation := λ l => l = []
    /--
      This instance feels slightly over-specialized, like it should be derivable from a more general property.
      It seems to be in the same spirit as e.g. `Multisem.Grammar.Jacobson.ZRR`, but the version of Jacobson's
      work I took that from (Gerhard 2005) didn't address anaphora across coordinators.
    -/
    instance if_lift_ref {A:Type}: lexicon Prop "if" ((((@NP A) ∖ S) ∖ ((@NP A) ∖ S)) // (S % (@NP A))) where
      denotation := λ r l x => r x -> l x
    instance when_lwhent_ref {A:Type}: lexicon Prop "when" ((((@NP A) ∖ S) ∖ ((@NP A) ∖ S)) // (S % (@NP A))) where
      denotation := λ r l x => r x -> l x
    instance its_ref {A B:Type}: lexicon Prop "its" (((@NP B) % (@NP A)) // (@NP (A -> B))) where
      denotation := λ p a => p a
    instance any_head {A:Type}: lexicon Prop "any" ((S // ((@NP A) ∖ S)) // (@CN A)) where
      denotation := λ p rest => ∀ (x:A), p x -> rest x
    instance are_adj_lex {A:Type}: lexicon Prop "are" (((@NP A) ∖ S) // (@ADJ A)) where
      denotation := λ p x => p x

    instance iff_prop : lexicon Prop "iff" ((S ∖ S) // S) where
      denotation x y := x <-> y

    -- These should be obtained by lifting other entries, but for now we'll define them manually
    -- This is slightly odd because it's conceivable the 'v' portion might be more than a variable
    instance every_named {A}{w}: lexicon Prop "every" (((S // (S % (@Var A w))) // ((@NP A) % (@Var A w))) // (@CN A)) where
      denotation cn _v rest := ∀ (a:A), cn a -> rest a
    --instance and_named_coord {A B}{w v} : lexicon Prop "and" ((S // (S % (@Var A w))) ∖ S) // (S // (S % (@Var B v))) where
    --  denotation rhs lhs := 
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
    instance empty_multiset : lexicon Prop "empty" (@ADJ multiset) where
      denotation := λ ms => ∀ x, 0 = ms x
    instance permutation_list : lexicon Prop "permutation" ((@CN (List value)) // (@PP (List value) PPType.OF)) where
      denotation := λ a b => sort.Permutation a b 
  end locallex

  /- TODO: To finish this batch of specs, I really need
     - support for multiple named variables
     - support for 'the' to refer to a referent (named or unnamed) introduced by a quantifier 

     Ideally I could read a solution to the first straight out of Ranta, though I could probably just tweak Jacobson's approach to work with a "named NP" construct used only for the 'hole' with discourse referents, coupled with named-quantifier forms "any list l"). Plus a tag/decl typeclass for marking which identifiers can be converted to variable references (via a lexicon instance). This is basically two minor variations on a single extension, and gets us through this chapter's specs.
  -/

  instance insertion_func : lexicon Prop "insertion" ((@NP (List value -> List value)) // (@PP value PPType.OF)) := sort.sort_specs.insertion_func
  instance val_noun : lexicon Prop "value" (@CN value) := { denotation := fun _ => True }
