import Mathlib.RingTheory.TwoSidedIdeal.Operations

variable {R : Type*} [Ring R]

namespace TwoSidedIdealextra

open TwoSidedIdeal

/--Define two two-sided ideals product `I * J`
as the smallest two-sided ideal containing
all elements of the form `a * b ` for some `a ∈ I, b ∈ J`.-/
def product (I J : TwoSidedIdeal R) : TwoSidedIdeal R :=
  span {x : R | ∃ a ∈ I, ∃ b ∈ J, a * b = x}


instance : Mul (TwoSidedIdeal R) :=
  ⟨product⟩

end TwoSidedIdealextra
