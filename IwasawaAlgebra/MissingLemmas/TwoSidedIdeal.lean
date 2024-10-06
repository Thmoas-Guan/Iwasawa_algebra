import Mathlib.RingTheory.TwoSidedIdeal.Operations

variable {R : Type*} [Ring R]

namespace TwoSidedIdealextra

open TwoSidedIdeal

section Definitions
/--Define two two-sided ideals product `I * J`
as the smallest two-sided ideal containing
all elements of the form `a * b ` for some `a ∈ I, b ∈ J`.-/

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


variable {I J : TwoSidedIdeal R}


theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J := by
  rw [mem_iff]
  apply RingConGen.Rel.of
  simp only [sub_zero, Set.mem_setOf_eq]
  exact ⟨r, hr, s, hs, rfl⟩


theorem pow_mem_pow {x : R} (hx : x ∈ I) (n : ℕ) : x ^ n ∈ I ^ n := sorry




end TwoSidedIdealextra
