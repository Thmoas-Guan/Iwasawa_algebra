import Mathlib
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.Ideal.Pointwise

variable {M R : Type*}

open TwoSidedIdeal

variable [Monoid M] [Ring R] [MulAction M R] {I : TwoSidedIdeal R}

/- protected def pointwiseMulSemiringAction'  {I : TwoSidedIdeal R} : MulSemiringAction M (asIdeal I) where
  smul a := Ideal.map (MulSemiringAction.toRingHom _ _ a)
  one_smul I :=
    congr_arg (I.map ·) (RingHom.ext <| one_smul M) |>.trans I.map_id
  mul_smul a₁ a₂ I :=
    congr_arg (I.map ·) (RingHom.ext <| mul_smul _ _) |>.trans (I.map_map _ _).symm
  smul_one a := by simp only [Ideal.one_eq_top]; exact Ideal.map_top _
  smul_mul a I J := Ideal.map_mul (MulSemiringAction.toRingHom _ _ a) I J
  smul_add a I J := Ideal.map_sup _ I J
  smul_zero a := Ideal.map_bot

 -/
