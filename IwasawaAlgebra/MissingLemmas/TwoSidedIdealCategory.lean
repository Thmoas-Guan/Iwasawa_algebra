import Mathlib
import IwasawaAlgebra.MissingLemmas.Twosidedideal

variable {R : Type*} [Ring R] (I J K : TwoSidedIdeal R)

open TwoSidedIdealextra TwoSidedIdeal CategoryTheory

theorem factorEqid :
    RingCat.ofHom (Quotient.factor I I (le_refl I)) = 𝟙 (RingCat.of (I.ringCon).Quotient) := by
  show Quotient.factor I I (le_refl I) = RingHom.id ((I.ringCon).Quotient)
  ext t
  unfold Quotient.factor
  simp
  sorry
  sorry


theorem factorcomp (h₁ : I ≤ J) (h₂ : J ≤ K) :
    RingCat.ofHom (Quotient.factor I K (h₁.trans h₂)) =
    RingCat.ofHom (Quotient.factor I J h₁) ≫ RingCat.ofHom (Quotient.factor J K h₂) := sorry
