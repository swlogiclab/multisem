import Multisem.Grammar
open Cat

def asNat (n:Nat) := n
def odd (n:Nat) : Bool :=
  match n with
  | Nat.zero => false
  | Nat.succ Nat.zero => true
  | Nat.succ (Nat.succ x) => odd x
def even (n:Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ Nat.zero => false
  | Nat.succ (Nat.succ x) => even x

--def nameIt {T:Type}(s:String) (x:T) : @lexicon Bs BsBase s (prim (@NP T)) := { denotation := x }



instance zerolex  : lexicon Prop "zero"   (@NP Nat) := { denotation := asNat 0 }
instance onelex   : lexicon Prop "one"    (@NP Nat) := { denotation := asNat 1 }
instance twolex   : lexicon Prop "two"    (@NP Nat) := { denotation := asNat 2 }
instance threelex : lexicon Prop "three"  (@NP Nat) := { denotation := asNat 3 }
instance fourlex  : lexicon Prop "four"   (@NP Nat) := { denotation := asNat 4 }
instance fivelex  : lexicon Prop "five"   (@NP Nat) := { denotation := asNat 5 }

instance evenlex  : lexicon Prop "even" (@ADJ Nat) := { denotation := fun x => even x = true }
instance oddlex   : lexicon Prop "odd" (@ADJ Nat) := { denotation := fun x => odd x = true }

instance noun_is_adj_lex {T}{P}: lexicon P "is" (((@NP T) ∖ S) // (@ADJ T)) where
  denotation := fun a n => a n
instance noun_is_noun_lex {T}: lexicon Prop "is" (((@NP T) ∖ S) // (@NP T)) where
  denotation := fun a n => a = n
-- TODO: not really sure about how classic syntacticians would feel about this, which abuses the fact that adjectives and CNs have the same semantics
instance a_cn_as_adj {C:Cat}{H}[HeytingAlgebra H]{T:Type} 
  : lexicon H "a" (((C // (@ADJ T)) ∖ C) // (@CN T)) where
  denotation := λ cn other => other cn

instance and_coord (P:Type u)[HeytingAlgebra P] : Coordinator P "and" where
  denoteCoord a b := HeytingAlgebra.conj a b
instance or_coord (P:Type u)[HeytingAlgebra P] : Coordinator P "or" where
  denoteCoord a b := HeytingAlgebra.disj a b

--#check (@synthlex _ _ "one" (prim NP) onelex)
--#check (@synthlex _ _ "equals" _ equals_eq_lex)
--#check @synthlapp Bs _ _ _ _ _ (@synthlex _ _ "one" (prim NP) onelex) (@synthrapp _ _ _ _ _ _ (@synthlex _ _ "equals" _ equals_eq_lex) (@synthlex _ _ "one" (prim NP) onelex))
--
---- More dictionary entries 
--
instance addslex : lexicon Prop "adds" ((@NP (Nat->Nat)) ∖ (S // (@NP Nat))) where
  denotation (subj:Nat->Nat) (obj:Nat) := forall x, subj x = x + obj

instance monotone : lexicon Prop "monotone" (@ADJ (Nat -> Nat)) where
  denotation f := forall x y, x <= y -> f x <= f y
--instance noun_is_adj_sentence {A:Type} : lexicon "is" (lslash (rslash (prim S) (prim (@ADJ A))) (prim (@NP A))) := { denotation := fun n a => a n }
--instance noun_is_adj_noun {A:Type} : lexicon "is" (lslash (rslash (prim S) (prim (@NP A))) (prim (@NP A))) := { denotation := fun n a => a = n }
--instance equalslex {A:Type} : lexicon "equals" (lslash (rslash (prim S) (prim (@NP A))) (prim (@NP A))) := { denotation := fun (n:A) (a:A) => a = n }
--

--def quant (A:Type) := (rslash (rslash (prim S) (lslash (prim S) (prim (@NP A)))) (prim (@CN A)))

set_option quotPrecheck false

-- This needs to be notation, since typeclass unification doesn't unfold defs
notation:65 "quant" A:65 => ((S // ((@NP A) ∖ S)) // (@CN A))
--
instance exists_lex {A}: lexicon Prop "some" (quant A) where
  denotation := fun _ P => exists x, P x
instance forall_lex {A}: lexicon Prop "every" (quant A) where
  denotation := fun _ P => forall x, P x
--
instance nat_noun : lexicon Prop "natural" (@CN Nat) := { denotation := fun _ => True }
--
instance given_lex {A B}: lexicon Prop "given" ((@NP (A -> B)) ∖ ((@NP B) // (@NP A))) where 
  denotation := fun f arg => f arg 

-- One down-side to the current macro system is that we can't have hyphens
instance nonneg_lex : lexicon Prop "non-negative" (@ADJ Nat) where
  denotation := fun x => 0 <= x 
instance nonneg_lex' : lexicon Prop "nonnegative" (@ADJ Nat) where
  denotation := fun x => 0 <= x 


-- Prepositional phrases
instance of_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "of" ((@PP T PPType.OF) // (@NP T)) where
  denotation := fun x => x
instance of_cn_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "of" ((@PP T PPType.OFN) // (@CN T)) where
  denotation := fun x => x
instance to_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "to" ((@PP T PPType.TO) // (@NP T)) where
  denotation := fun x => x
instance from_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "from" ((@PP T PPType.FROM) // (@NP T)) where
  denotation := fun x => x
instance in_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "in" ((@PP T PPType.IN) // (@NP T)) where
  denotation := fun x => x
instance into_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "into" ((@PP T PPType.INTO) // (@NP T)) where
  denotation := fun x => x

-- So the tricky brain switch that needs to happen with compositional semantics
-- is that "phrase types" with the "same distribution" don't have the
-- same grammatical type. This is most apparent with determiners:
-- "Classically" [a noun] is a noun phrase. But [a] has existential flavor,
-- while other noun phrases are simply individuals. So the trick is that
-- determiners in English compose on the right with some noun, but
-- the result is not a noun phrase: it's something that can be used in 
-- all the same places as a noun phrase, but actually has a separate 
-- grammatical type so it can have different semantics.
-- Thus, the word 'a' has a type that combines with a noun on the right,
-- and then "something" on the left that's looking for a noun phrase to
-- *its* right.
-- The entry below is not as general as possible, but works for using
-- the indefinite article in a direct object position. It will require
-- further generalization in the future.
-- This has args in Type rather than Type u b/c it's a Prop entry
-- We could generalize that bit directly to any cylindrical algebra
instance a_directobject {A:Type}{B:Type} : lexicon Prop "a" 
  (((((@NP B) ∖ S) // (@NP A)) ∖ ((@NP B) ∖ S)) // (@CN A)) where
  denotation (cn:interp Prop (@CN A)) frag := fun subj => ∃ (a:A), cn a /\ frag a subj
instance any_directobject {A:Type}{B:Type} : lexicon Prop "any" 
  (((((@NP B) ∖ S) // (@NP A)) ∖ ((@NP B) ∖ S)) // (@CN A)) where
  denotation (cn:interp Prop (@CN A)) frag := fun subj => ∀ (a:A), cn a -> frag a subj
-- We can lift any adjective to a modifier of common nouns
instance AdjModifier {H:Type u}{A : Type u}[ha:HeytingAlgebra H](s:String)[l:lexicon H s (@ADJ A)] : lexicon H s ((@CN A) // (@CN A)) where
  denotation cn := fun x => ha.conj (l.denotation s x) (cn x)

-- For now we're ignoring pluralization
instance naturals_lex : lexicon Prop "naturals" (@CN Nat) where
  denotation _ := True
instance natural_lex : lexicon Prop "natural" (@CN Nat) where
  denotation _ := True

-- This is of course highly overspecialized, but the right general-purpose definition of 'algorithm' in a dependent type theory is itself a reasonably deep philosophical question
instance algorithm_basic {T:Type}: lexicon Prop "algorithm" (@CN (List T -> List T)) where
  denotation := fun _ => True

instance list_lex {P:Type u}[HeytingAlgebra P]{T:Type u}: lexicon P "list" ((@CN (List T)) // (@PP T PPType.OFN)) where
  denotation _ := fun _ => HeytingAlgebra.top

instance any_ppobject {A:Type}{C:Cat} : lexicon Prop "any" 
  (((C // (@NP A)) ∖ (S // (C ∖ S))) // (@CN A)) where
  denotation (cn:interp Prop (@CN A)) frag tail := ∀ (a:A), cn a -> tail (frag a)

namespace NamedAnaphora
end NamedAnaphora