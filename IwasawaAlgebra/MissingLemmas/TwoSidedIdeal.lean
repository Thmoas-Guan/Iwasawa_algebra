import Mathlib
import Mathlib.RingTheory.TwoSidedIdeal.Basic


variable {M R : Type*}

namespace test

open TwoSidedIdeal

variable [Ring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] {I  J : TwoSidedIdeal R}

#check asIdeal (I : TwoSidedIdeal R)
--Here we view TwoSidedIdeal R as a left ideal R

/- def lsmul : R →ₗ[R] M →ₗ[R] M :=
  mk₂ R (· • ·) add_smul (fun _ _ _ => mul_smul _ _ _) smul_add fun r s m => by
    simp only [smul_smul, smul_eq_mul, mul_comm]

instance hasSMul' : SMul (Ideal R) (Submodule R M) :=
  ⟨Submodule.map₂ (LinearMap.lsmul R M)⟩

instance : Mul (Ideal R) :=
  ⟨(· • ·)⟩
 -/
-- Remark : The above is mulaction about ideal of commRing!!!! So all the definition need to rewrite.


def product (I J : TwoSidedIdeal R) : TwoSidedIdeal R := sorry


instance : Mul (TwoSidedIdeal R) :=
  ⟨ product ⟩
