import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib
variable {R : Type*} [Ring R]

namespace TwoSidedIdealextra

open TwoSidedIdeal

section Definitions

/--Define two two-sided ideals product `I * J`
as the smallest two-sided ideal containing
all elements of the form `a * b ` for some `a ∈ I, b ∈ J`. -/
def product (I J : TwoSidedIdeal R) : TwoSidedIdeal R :=
  span {x : R | ∃ a ∈ I, ∃ b ∈ J, a * b = x}


instance : Mul (TwoSidedIdeal R) :=
  ⟨product⟩


def pow (I: TwoSidedIdeal R) : Nat → TwoSidedIdeal R
  | 0 => ⊤
  | 1 => I
  | n + 1 => I * (pow I n)

instance : NatPow (TwoSidedIdeal R) :=
  ⟨pow⟩

end Definitions


section Product

variable {I : TwoSidedIdeal R} {J : TwoSidedIdeal R}

theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J := by
  apply RingConGen.Rel.of
  simp only [sub_zero, Set.mem_setOf_eq]
  exact ⟨r, hr, s, hs, rfl⟩


theorem pow_mem_pow {x : R} (hx : x ∈ I) (n : ℕ) : x ^ n ∈ I ^ n := by sorry

end Product




variable (I J : TwoSidedIdeal R)


theorem subsingleton_iff : Subsingleton (I.ringCon).Quotient ↔ I = ⊤ := by sorry


namespace Quotient


/-- The ring homomorphism from the quotient by a smaller ideal to the quotient by a larger ideal.

This is the `TwoSidedIdeal.Quotient` version of `Quot.Factor` -/
def factor (H : I ≤ J) : (I.ringCon).Quotient →+* (J.ringCon).Quotient where
  toFun := Quot.factor I.ringCon J.ringCon (by simp only [← RingCon.le_def, ringCon_le_iff.1 H])
  map_one' := rfl
  map_mul' := sorry
  map_zero' := rfl
  map_add' := sorry




end Quotient

#check Ideal.Quotient.factor
#check Quot.mk
#check Quot.factor


end TwoSidedIdealextra
