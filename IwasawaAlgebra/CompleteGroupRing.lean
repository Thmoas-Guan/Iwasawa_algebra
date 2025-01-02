import Mathlib
import IwasawaAlgebra.MissingLemmas.ContinuousMulEquiv
import IwasawaAlgebra.MissingLemmas.Subgroup
import IwasawaAlgebra.MissingLemmas.Limits


universe u v


noncomputable section lemmas

open MonoidAlgebra

variable {G : Type u} {R : Type v} [Group G] [CommRing R]

/-- The transition Alghom `MonoidAlgebra R (G ⧸ N₁) →ₐ[R] MonoidAlgebra R (G ⧸ N₂)` for N₁ ≤ N₂. -/
def transition_map (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal] (h : N₁ ≤ N₂) :
    MonoidAlgebra R (G ⧸ N₁) →ₐ[R] MonoidAlgebra R (G ⧸ N₂) :=
  mapDomainAlgHom R R (QuotientGroup.map N₁ N₂ (MonoidHom.id G) h)

@[simp]
lemma transition_map_id (N : Subgroup G) [N.Normal] : transition_map N N (le_refl N) = AlgHom.id R _ := by
  simp_rw [transition_map, QuotientGroup.map_id, mapDomainAlgHom_id]

@[simp]
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

variable (R : Type v) [CommRing R] (G : ProfiniteGrp.{u})

/-- Define the functor from OpenNormalSubgroup of a profinite group to the group ring of its
quotient group -/
def QuotientOpenNormalSubgroup :
    OpenNormalSubgroup G ⥤ AlgebraCat R where
    obj := fun N => of R <| MonoidAlgebra R (G ⧸ N.toSubgroup)
    map := fun {H K} fHK =>
      ofHom (transition_map H.toSubgroup K.toSubgroup (leOfHom fHK))
    map_id := fun H => by simp only [transition_map_id, ofHom_id]
    map_comp := fun {N₁ N₂ N₃} f g => by simp only [transition_map_comp (leOfHom f) (leOfHom g),
      ofHom_comp]

/-- The explicit limit cone in `AlgebraCat R`. -/
abbrev limitCone := HasLimits.limitCone (QuotientOpenNormalSubgroup R G)

/-- The abbreviation for the limit of `AlgebraCat R`. -/
abbrev limit_ONS : AlgebraCat R := (limitCone R G).pt

/- The completed group algebra `R[[G]]` is defined as the inverse limit of `R[Gᵢ]`
where `N` ranges over the open normal subgroups of `G`. -/

-- PreorderGroup
structure PreGroup (Λ : Type w) [CanonicallyLinearOrderedAddCommMonoid Λ] where
  toONS : Λ → OpenNormalSubgroup G
  le : ∀ {i j}, i ≤ j → toONS i ≤ toONS j
  eq_bot : (toONS 0).toSubgroup = ⊥

/-- The functor from index to the group ring of its group -/
def QuotientIndex {Λ : Type w} [CanonicallyLinearOrderedAddCommMonoid Λ]
  (POG : PreGroup G Λ) : Λ ⥤ AlgebraCat R where
  obj i := of R <| MonoidAlgebra R <| G ⧸ (POG.toONS i).toSubgroup
  map {i j} f := ofHom <| MonoidAlgebra.mapDomainAlgHom R R <|
    QuotientGroup.map (POG.toONS i).toSubgroup (POG.toONS j).toSubgroup (MonoidHom.id G) <| POG.le (leOfHom f)

-- Don't know how to prove this
variable {Λ : Type w} [CanonicallyLinearOrderedAddCommMonoid Λ] in
instance (POG : PreGroup G Λ) : Small ((QuotientIndex R G POG) ⋙ forget (AlgebraCat R)).sections := by
  constructor

  sorry

/- The index limit cone in `AlgebraCat R`. -/
variable {Λ : Type w} [CanonicallyLinearOrderedAddCommMonoid Λ] (POG : PreGroup G Λ) in
abbrev limitConeIndex := AlgebraCat.HasLimits.limitCone (QuotientIndex R G POG)

variable {Λ : Type w} [CanonicallyLinearOrderedAddCommMonoid Λ] (POG : PreGroup G Λ) in
abbrev limit_index : AlgebraCat R := (limitConeIndex R G POG).pt

/-- The isomorphism between the completed group algebra of a profinite group and the inverse
limit of the group algebras of its finite quotients. -/
def completedGroupAlgebraIso {Λ : Type w} [CanonicallyLinearOrderedAddCommMonoid Λ] (POG : PreGroup G Λ):
  limit_ONS R G ≅ limit_index R G POG := by
  simp_rw [limit_ONS, limit_index, limitCone, limitConeIndex]

  sorry



end limits
