import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompletePartialOrder
import IwasawaAlgebra.MissingLemmas.TwoSidedIdeal
import Mathlib.Algebra.Category.Ring.Limits

variable {α : Type v} [CanonicallyOrderedAddCommMonoid α]

section definition

variable (R : Type u) [Ring R]

structure RingFiltration  where
  Fil : α → TwoSidedIdeal R
  bot : Fil (0 : α) = ⊤
  intersection_eq  : ∀ i : α, Fil i = ⨅ j < i, Fil j
  inclusion_le : ∀ i j : α,  ((Fil i) * (Fil j)) ≤ Fil (i + j)

end definition

section RingFiltration

variable (R : Type u) [Ring R] (P : RingFiltration R (α := α)) {x : α}

open CategoryTheory

def Intermap (P : RingFiltration R (α := α)) :=
  fun (i : α) ↦ (⨅ μ > i, P.Fil μ)

variable {J : Type v} [Category.{w} J] (F : J ⥤ RingCat.{u})

/-- Auxiliary construction to obtain the group structure on the limit of rings. -/
def limitConePtAux : Subring (Π j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp_all only [Set.mem_setOf_eq, Pi.mul_apply, map_mul]
  one_mem' := by simp_all only [Set.mem_setOf_eq, Pi.one_apply, map_one, implies_true]
  add_mem' := by simp_all only [Set.mem_setOf_eq, Pi.add_apply, map_add, implies_true]
  zero_mem' := by simp_all only [Set.mem_setOf_eq, Pi.zero_apply, map_zero, implies_true]
  neg_mem' := by simp_all only [Set.mem_setOf_eq, Pi.neg_apply, map_neg, implies_true]
