import Mathlib
import IwasawaAlgebra.MissingLemmas.ContinuousMulEquiv
import IwasawaAlgebra.MissingLemmas.Subgroup
import IwasawaAlgebra.MissingLemmas.Limits


universe u v

open CategoryTheory Topology


section lemmas

open MonoidAlgebra

variable {G : Type u} {R : Type v} [Group G] [CommRing R]

/-- The transition Alghom `MonoidAlgebra R (G ⧸ N₁)` → `MonoidAlgebra R (G ⧸ N₂)` for N₁ ≤ N₂. -/
noncomputable def transition_map {N₁ N₂ : Subgroup G} [N₁.Normal] [N₂.Normal] (h : N₁ ≤ N₂) :
    MonoidAlgebra R (G ⧸ N₁) →ₐ[R] MonoidAlgebra R (G ⧸ N₂) :=
  let f := QuotientGroup.map (f := MonoidHom.id G) N₁ N₂ h
  mapDomainAlgHom R R f

/-- Define the functor from OpenNormalSubgroup of a profinite group to the group ring of its
quotient group -/
def QuotientOpenNormalSubgroup (G : ProfiniteGrp) :
    OpenNormalSubgroup G ⥤ (AlgebraCat R) := {
    obj := fun H => sorry --MonoidAlgebra R (G ⧸ H.toSubgroup) "have universe problem"
    map := fun {H K} fHK => sorry
    map_id := fun H => sorry
    map_comp := fun {X Y Z} f g => sorry}

end lemmas







section limits

variable {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})


variable {G : Type u} {R : Type v} (G : ProfiniteGrp) [CommRing R]
