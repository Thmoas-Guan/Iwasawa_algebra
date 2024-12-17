import Mathlib
import IwasawaAlgebra.MissingLemmas.ContinuousMulEquiv
import IwasawaAlgebra.MissingLemmas.Subgroup
import IwasawaAlgebra.MissingLemmas.Limits


universe u v

open CategoryTheory Topology
section lemmas

open Subgroup MonoidAlgebra


variable {G : Type*} {R : Type*} [Group G] [CommRing R]


/-- The transition map R[G/N₁] → R[G/N₂] for N₁ ≤ N₂. -/
noncomputable def transition_map {N₁ N₂ : Subgroup G} [N₁.Normal] [N₂.Normal] (h : N₁ ≤ N₂) :
    MonoidAlgebra R (G ⧸ N₁) →ₐ[R] MonoidAlgebra R (G ⧸ N₂) :=
    let f := QuotientGroup.map (f := MonoidHom.id G) N₁ N₂ h
    mapDomainAlgHom R R f


end lemmas







section limits

variable {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})


variable {G : Type*} {R : Type*} (G : ProfiniteGrp) [CommRing R]
