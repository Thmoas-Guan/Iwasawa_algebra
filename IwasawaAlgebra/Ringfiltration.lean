import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompletePartialOrder
import IwasawaAlgebra.MissingLemmas.TwoSidedIdeal

variable {α : Type v} [CanonicallyOrderedAddCommMonoid α]
section definition

structure RingFiltration (R : Type u) [Ring R] where
  Fil : α → TwoSidedIdeal R
  bot : Fil (0 : α) = ⊤
  intersection_eq  : ∀ i : α, Fil i = ⨅ j < i, Fil j
  inclusion_le : ∀ i j : α,  ((Fil i) * (Fil j)) ≤ Fil (i + j)

end definition

section RingFiltration

variable (R : Type u) [Ring R] (P : RingFiltration R (α := α)) {x : α}

open CategoryTheory Topology


variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{max v u})


def limitConePtAux : Ring (Π j : J, F.obj j) := sorry
