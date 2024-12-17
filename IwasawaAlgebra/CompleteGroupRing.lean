import Mathlib
import IwasawaAlgebra.MissingLemmas.ContinuousMulEquiv
import IwasawaAlgebra.MissingLemmas.Subgroup
import IwasawaAlgebra.MissingLemmas.Limits


universe u v

open CategoryTheory Topology
section lemmas

open Subgroup MonoidAlgebra
#check Profinite


variable {G : Type*} {R : Type*} [Group G] [CommRing R]

def canonical_map {N₁ N₂ : Subgroup G} [N₁.Normal] [N₂.Normal] (h : N₁ ≤ N₂) : G ⧸ N₁ →* G ⧸ N₂ :=
  QuotientGroup.map (f := MonoidHom.id G) N₁ N₂ h

noncomputable instance test (N : Subgroup G) [N.Normal] : Algebra R (MonoidAlgebra R (G ⧸ N)) := by
  exact algebra

/-- The transition map R[G/N₁] → R[G/N₂] for N₁ ≤ N₂. -/
noncomputable def transition_map {N₁ N₂ : Subgroup G} [N₁.Normal] [N₂.Normal] (h : N₁ ≤ N₂) :
  letI := test (R := R) N₂
  MonoidAlgebra R (G ⧸ N₁) →ₐ[R] MonoidAlgebra R (G ⧸ N₂) := by
  exact mapDomainAlgHom R R (canonical_map h)

end lemmas






section limits

variable {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})


variable {G : Type*} {R : Type*} (G : ProfiniteGrp) [CommRing R]
