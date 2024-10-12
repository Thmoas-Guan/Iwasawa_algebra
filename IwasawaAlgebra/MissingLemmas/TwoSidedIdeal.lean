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

namespace Quotient

open Quotient


theorem subsingleton_iff : Subsingleton (I.ringCon).Quotient ↔ I = ⊤ := by
  rw [← one_mem_iff, ← subsingleton_iff_zero_eq_one]
  sorry


variable [Semiring S]  (J : TwoSidedIdeal R) (I : TwoSidedIdeal R)

/--Reinterpret a submodule as an additive subgroup.-/
def toAddSubgroup : AddSubgroup R := sorry

/-- Given a ring homomorphism `f : R →+* S` sending all elements of an two-sided ideal to zero,
lift it to the quotient by this ideal. -/
def lift  (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) : (I.ringCon).Quotient →+* S := sorry

/-- The ring homomorphism from the quotient by a smaller ideal to the quotient by a larger ideal.
This is the `TwoSidedIdeal.Quotient` version of `Quot.Factor` -/
def factor (H : I ≤ J) :
    (I.ringCon).Quotient →+* (J.ringCon).Quotient := sorry



end Quotient

#check Ideal.Quotient.lift



end TwoSidedIdealextra
