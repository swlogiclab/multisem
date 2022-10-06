/-- The classic Heyting Algebra -/
class HeytingAlgebra.{u} (P:Type u) where
  top : P
  bottom : P
  conj : P -> P -> P
  disj : P -> P -> P
  impl : P -> P -> P
attribute [simp] HeytingAlgebra.top
attribute [simp] HeytingAlgebra.bottom
attribute [simp] HeytingAlgebra.conj
attribute [simp] HeytingAlgebra.disj
attribute [simp] HeytingAlgebra.impl

/-- A child class which imposes the actual laws.
  We omit the laws from `HeytingAlgebra` because we're mostly interested in the interface to the logic, not necessarily its properties. It is convenient to be able to define just the basic HA structure without proving all the laws, when we're just axiomatizing existing well-known logics.
-/
class HeytingAlgebraLaws (P : Type u) extends HeytingAlgebra P where
  conj_comm : ∀ x y, conj x y = conj y x
  conj_assoc : ∀ x y z, conj (conj x y) z = conj x (conj y z)
  disj_comm : ∀ x y, disj x y = disj y x
  disj_assoc : ∀ x y z, disj (disj x y) z = disj x (disj y z)
  distrib_left : ∀ x y z, conj x (disj y z) = disj (conj x y) (conj x z)
  distrib_right : ∀ x y z, conj (disj x y) z = disj (conj x z) (conj y z)
  -- TODO: missing impl laws

class HeytingAlgebraMorphism (P : Type u)[HeytingAlgebra P](Q : Type v)[HeytingAlgebra Q] where
  morph : P -> Q
class HeytingAlgebraMorphismLaws (P : Type u)[HeytingAlgebra P](Q : Type v)[HeytingAlgebra Q] extends HeytingAlgebraMorphism P Q where
  preserves_top : morph HeytingAlgebra.top = HeytingAlgebra.top
  preserves_bottom : morph HeytingAlgebra.bottom = HeytingAlgebra.bottom
  preserves_conj : ∀ x y, morph (HeytingAlgebra.conj x y) = HeytingAlgebra.conj (morph x) (morph y)
  preserves_disj : ∀ x y, morph (HeytingAlgebra.disj x y) = HeytingAlgebra.disj (morph x) (morph y)
  preserves_impl : ∀ x y, morph (HeytingAlgebra.impl x y) = HeytingAlgebra.impl (morph x) (morph y)

/--
  An intuitionistic version of a Polyadic Algebra.

  This is one algebraic extension of Heyting Algebras to quantifiers.
  We've gone intuitionistic by not assuming existentials and universals
  are related by negation; the classic version due to Halmos is classical.

  This is also a close cousin of the Cylindric Algebra, which is *approximately*
  a Polyadic Algebra with an equality predicate. For the full details, see
  - Galler, Bernard A. Cylindric and Polyadic Algebras.  Proceedings of the American Mathematical Society. Vol. 8, No. 1 (Feb., 1957), pp. 176-183.
  - Halmos, Paul R. Transactions of the American Mathematical Society. Vol. 86, No. 1 (Sep., 1957), pp. 1-27.
-/
class PolyadicAlgebra.{u} (P : Type u) [HeytingAlgebra P] where
  all : forall {T:Type u}, (T -> P) -> P
  ex : forall {T:Type u}, (T -> P) -> P


instance pointwiseHA (X : Type v)(H : Type u)[HeytingAlgebra H] : HeytingAlgebra (X -> H) where
  top := λ_ => HeytingAlgebra.top
  bottom := λ_ => HeytingAlgebra.bottom
  conj x y := λ p => HeytingAlgebra.conj (x p) (y p)
  disj x y := λ p => HeytingAlgebra.disj (x p) (y p)
  impl x y := λ p => HeytingAlgebra.impl (x p) (y p)

instance pointwise_lift (X : Type v)(H : Type u)[HeytingAlgebra H] : HeytingAlgebraMorphism H (X -> H) where
  morph := λ h _ => h 

instance pointwiseHALaws (X : Type v)(H : Type u)[HeytingAlgebraLaws H] : HeytingAlgebraLaws (X -> H) where
  top := λ_ => HeytingAlgebra.top
  bottom := λ_ => HeytingAlgebra.bottom
  conj x y := λ p => HeytingAlgebra.conj (x p) (y p)
  disj x y := λ p => HeytingAlgebra.disj (x p) (y p)
  impl x y := λ p => HeytingAlgebra.impl (x p) (y p)
  conj_comm x y := by { apply funext; intro p; apply HeytingAlgebraLaws.conj_comm }
  conj_assoc x y z := by { apply funext; intro p; apply HeytingAlgebraLaws.conj_assoc }
  disj_comm x y := by { apply funext; intro p; apply HeytingAlgebraLaws.disj_comm }
  disj_assoc x y z := by { apply funext; intro p; apply HeytingAlgebraLaws.disj_assoc }
  distrib_left x y z := by apply funext; intro p; apply HeytingAlgebraLaws.distrib_left
  distrib_right x y z := by apply funext; intro p; apply HeytingAlgebraLaws.distrib_right

instance PropHeyting : HeytingAlgebra Prop where
  top := True
  bottom := False
  conj x y := x ∧ y
  disj x y :=  x ∨ y
  impl x y := x -> y

instance PropPolyadic : PolyadicAlgebra Prop where
  all {T} f := ∀ (t:T), f t
  ex {T} f := ∃ (t:T), f t