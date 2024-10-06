import Mathlib.RingTheory.TwoSidedIdeal.Operations

variable {R : Type*} [Ring R]

namespace TwoSidedIdealextra

open TwoSidedIdeal

/--Define two two-sided ideals product `I * J`
as the smallest two-sided ideal containing
all elements of the form `a * b ` for some `a ∈ I, b ∈ J`.-/
def product (I J : TwoSidedIdeal R) : TwoSidedIdeal R :=
  TwoSidedIdeal.mk'
  (carrier := span {x : R | ∃ a ∈ I, ∃ b ∈ J, a * b = x})
  (ZeroMemClass.zero_mem _)
  (fun {_ _} h₁ h₂ ↦ AddMemClass.add_mem h₁ h₂)
  (fun {_} h ↦ NegMemClass.neg_mem h)
  (fun {x y} h ↦ mul_mem_left _ x y h)
  (fun {x y} h ↦ mul_mem_right _ x y h)


instance : Mul (TwoSidedIdeal R) :=
  ⟨product⟩

end TwoSidedIdealextra
