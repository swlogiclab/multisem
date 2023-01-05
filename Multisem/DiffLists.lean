import Multisem.Grammar
import Multisem.Lexicon
open Cat

class NonEmptyTail (A B : List String) where
instance NTailRefl {a A} : NonEmptyTail (a::A) A where
instance NTailTail {A B b}[NonEmptyTail A (b::B)] : NonEmptyTail A B where

class StrictSubList (A B : List String) where
instance StrictSubListBase {a}{A} : StrictSubList (a::A) A where
--instance StrictSubListTail {A B}{b} [StrictSubList A (b::B)] : StrictSubList A B where
instance StrictSubtListTail2 {A B}{a} [StrictSubList A B] : StrictSubList (a::A) B where

class DSynth (Front Back : List String) (C : Cat) where
  dsem : interp Prop C
attribute [simp] DSynth.dsem

instance DRApp {Front Back1 Back2 : List String} {A B : Cat}
  --[NonEmptyTail Back1 Back2]
  --[NonEmptyTail Front Back1]
  [StrictSubList Front Back1][StrictSubList Back1 Back2]
  [L : DSynth Front Back1 (B // A)]
  [R : DSynth Back1 Back2 A]
  : DSynth Front Back2 B where
  dsem := L.dsem R.dsem
instance DLApp {Front Back1 Back2 : List String} {A B : Cat}
  --[NonEmptyTail Back1 Back2]
  --[NonEmptyTail Front Back1]
  [StrictSubList Front Back1][StrictSubList Back1 Back2]
  [L : DSynth Front Back1 A]
  [R : DSynth Back1 Back2 (A ∖ B)]
  : DSynth Front Back2 B where
  dsem := R.dsem L.dsem
--instance DRApp1 {x}{Front Back1 Back2 : List String} {A B : Cat}
--  --[NonEmptyTail Back1 Back2]
--  --[NonEmptyTail Front Back1]
--  [L : DSynth (x::Front) Back1 (B // A)]
--  [R : DSynth Back1 Back2 A]
--  : DSynth (x::Front) Back2 B where
--  dsem := L.dsem R.dsem
--instance DLApp2 {x}{Front Back1 Back2 : List String} {A B : Cat}
--  --[NonEmptyTail Back1 Back2]
--  --[NonEmptyTail Front Back1]
--  [L : DSynth (x::Front) Back1 A]
--  [R : DSynth Back1 Back2 (A ∖ B)]
--  : DSynth (x::Front) Back2 B where
--  dsem := R.dsem L.dsem

instance DLex {L : List String}{w:String}{C:Cat}
  [l : lexicon Prop w C]
  : DSynth (w::L) L C where
  dsem := l.denotation

@[simp]
def dspec (L : List String) [D: DSynth L [] S] : Prop := D.dsem

set_option synthInstance.maxHeartbeats 40000
set_option maxHeartbeats 40000
set_option trace.Meta.synthInstance.instances true
set_option trace.Meta.synthInstance.newAnswer true

-- Let's confirm the proof theory is complete enough to find this
def three_is_even_parse : DSynth ("three"::"is"::"even"::[]) [] S :=
  let three : DSynth ("three"::"is"::"even"::[]) ("is"::"even"::[]) (@NP Nat):= DLex (l:=threelex)
  let is : DSynth ("is"::"even"::[]) ("even"::[]) (((@NP Nat) ∖ S) // (@ADJ Nat)):= DLex (l:=noun_is_adj_lex)
  let even : DSynth ("even"::[]) [] (@ADJ Nat) := DLex (l:=evenlex)
  let is_even : DSynth ("is"::"even"::[]) [] ((@NP Nat) ∖ S) := DRApp (L:=is) (R:=even)
  DLApp (L:=three) (R:=is_even)
#check three_is_even_parse.dsem

@[simp]
def three_is_even_diff := dspec ("three"::"is"::"even"::[])

def three_is_even_pf : three_is_even_diff :=
  by simp
     sorry

-- hack experiment to play with left-side multi-word constituents
instance length_lex : lexicon Prop "length" (@NP (String -> Nat)) where
  denotation := String.length
instance my_lex {A} : lexicon Prop "my" ((@NP A) // (@NP (String -> A))) where
  denotation f := f "my"

def hack_ : dspec ("my"::"length"::"is"::"even"::[]) :=
  by simp