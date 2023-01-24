class Exemplar (T : Type) where
  f : T

instance pair_ex (T U : Type) [t:Exemplar T][u:Exemplar U] : Exemplar (T × U) where
  f := ⟨t.f, u.f⟩

def exhibit (T:Type) [e:Exemplar T] : T := e.f

/-
  This example shows that Lean searches left-to-right (first-to-last) for argument typeclass instances. If the N instance is given first, that's the exemplar that yields an error. If the U instance is listed first, that's the exemplar that yields an error.
-/
def exhibit_pair (U N : Type) 
  [n:Exemplar N]
  [u:Exemplar U] 
  : U × N :=
  ⟨u.f, n.f⟩

def which_failure := exhibit_pair Unit Nat
