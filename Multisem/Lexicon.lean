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

instance noun_is_adj_lex {T}{P}: lexicon P "is" (rslash (lslash (@NP T) S) (@ADJ T)) where
  denotation := fun a n => a n
instance noun_is_noun_lex {T}: lexicon Prop "is" (rslash (lslash (@NP T) S) (@NP T)) where
  denotation := fun a n => a = n

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
instance addslex : lexicon Prop "adds" (lslash (@NP (Nat->Nat)) (rslash S (@NP Nat))) where
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
notation:65 "quant" A:65 => (rslash (rslash S (lslash (@NP A) S)) (@CN A))
--
instance exists_lex {A}: lexicon Prop "some" (quant A) where
  denotation := fun _ P => exists x, P x
instance forall_lex {A}: lexicon Prop "every" (quant A) where
  denotation := fun _ P => forall x, P x
--
instance nat_noun : lexicon Prop "natural" (@CN Nat) := { denotation := fun _ => True }
--
instance given_lex {A B}: lexicon Prop "given" (lslash (@NP (A -> B)) (rslash (@NP B) (@NP A))) where 
  denotation := fun f arg => f arg 

-- One down-side to the current macro system is that we can't have hyphens
instance nonneg_lex : lexicon Prop "non-negative" (@ADJ Nat) where
  denotation := fun x => 0 <= x 
instance nonneg_lex' : lexicon Prop "nonnegative" (@ADJ Nat) where
  denotation := fun x => 0 <= x 


-- Prepositional phrases
instance of_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "of" (rslash (@PP T PPType.OF) (@NP T)) where
  denotation := fun x => x
instance of_cn_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "of" (rslash (@PP T PPType.OFN) (@CN T)) where
  denotation := fun x => x
instance to_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "to" (rslash (@PP T PPType.TO) (@NP T)) where
  denotation := fun x => x
instance from_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "from" (rslash (@PP T PPType.FROM) (@NP T)) where
  denotation := fun x => x
instance in_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "in" (rslash (@PP T PPType.IN) (@NP T)) where
  denotation := fun x => x
instance into_lex (P:Type u)[HeytingAlgebra P](T:Type u) : lexicon P "into" (rslash (@PP T PPType.INTO) (@NP T)) where
  denotation := fun x => x