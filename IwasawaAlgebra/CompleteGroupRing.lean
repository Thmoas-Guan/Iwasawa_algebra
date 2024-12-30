import Mathlib
import IwasawaAlgebra.MissingLemmas.ContinuousMulEquiv
import IwasawaAlgebra.MissingLemmas.Subgroup
import IwasawaAlgebra.MissingLemmas.Limits


universe u v

namespace CompleteGroupRing

noncomputable section lemmas

open MonoidAlgebra

variable {R : Type u} {G : Type v} [CommRing R] [Group G]

/-- The transition Alghom `MonoidAlgebra R (G ⧸ N₁) →ₐ[R] MonoidAlgebra R (G ⧸ N₂)` for N₁ ≤ N₂. -/
def transition_map (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal] (h : N₁ ≤ N₂) :
    MonoidAlgebra R (G ⧸ N₁) →ₐ[R] MonoidAlgebra R (G ⧸ N₂) :=
  let f := QuotientGroup.map (f := MonoidHom.id G) N₁ N₂ h
  mapDomainAlgHom R R f

lemma transition_map_id (N : Subgroup G) [N.Normal] : transition_map N N (le_refl N) = AlgHom.id R _ := by
  simp only [transition_map, QuotientGroup.map_id, mapDomainAlgHom_id]

lemma transition_map_comp {N₁ N₂ N₃ : Subgroup G} [N₁.Normal] [N₂.Normal] [N₃.Normal] (h₁ : N₁ ≤ N₂) (h₂ : N₂ ≤ N₃) :
    transition_map N₁ N₃ (h₁.trans h₂) =
    AlgHom.comp (R := R) (transition_map N₂ N₃ h₂) (transition_map N₁ N₂ h₁) := by
  ext x y
  simp only [transition_map, MonoidHom.coe_comp, MonoidHom.coe_coe, QuotientGroup.coe_mk', Function.comp_apply,
    of_apply, mapDomainAlgHom_apply, Finsupp.mapDomain_single, QuotientGroup.map_mk,
    MonoidHom.id_apply, AlgHom.coe_comp]


variable (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal]


end lemmas


noncomputable section limits

open AlgebraCat CategoryTheory

variable (R : Type u) {G : Type v} [CommRing R] (G : ProfiniteGrp)


/-- Define the functor from OpenNormalSubgroup of a profinite group to the group ring of its
quotient group -/
def QuotientOpenNormalSubgroup :
    OpenNormalSubgroup G ⥤ AlgebraCat R where
    obj := fun H => of R <| MonoidAlgebra R (G ⧸ H.toSubgroup)
    map := fun {H K} fHK =>
      let f := transition_map (R := R) H.toSubgroup K.toSubgroup (leOfHom fHK)
      ofHom f
    map_id := fun H => by simp only [transition_map_id, ofHom_id]
    map_comp := fun {X Y Z} f g => by simp only [transition_map_comp (leOfHom f) (leOfHom g),
      ofHom_comp]

/-- The explicit limit cone in `AlgebraCat R`. -/
abbrev limitCone := HasLimits.limitCone (QuotientOpenNormalSubgroup R G)

/-- The abbreviation for the limit of `AlgebraCat R`. -/
abbrev limit : AlgebraCat R := (limitCone R G).pt



end limits
