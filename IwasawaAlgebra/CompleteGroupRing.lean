import Mathlib
import IwasawaAlgebra.MissingLemmas.ContinuousMulEquiv
import IwasawaAlgebra.MissingLemmas.Subgroup
import IwasawaAlgebra.MissingLemmas.Limits


universe u v

open CategoryTheory Topology


section lemmas

open Subgroup

#check MonoidAlgebra

variable {G : Type*} {R : Type*} [Group G] [CommRing R]


def caninocal_map {N₁ N₂ : Subgroup G} [N₁.Normal] [N₂.Normal] (h : N₁ ≤ N₂) : G ⧸ N₁ →* G ⧸ N₂ := by
  refine QuotientGroup.map (f := MonoidHom.id G) N₁ N₂ h

def canonical_map_GroupRing {N₁ N₂ : Subgroup G} [N₁.Normal] [N₂.Normal] (h : N₁ ≤ N₂) :
    MonoidAlgebra R (G ⧸ N₁)  →+* MonoidAlgebra R (G ⧸ N₂) := by
  sorry

  sorry









end lemmas






section limits

variable {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})


variable {G : Type*} {R : Type*} (G : ProfiniteGrp) [CommRing R]
