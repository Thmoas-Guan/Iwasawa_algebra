/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib
set_option maxHeartbeats 0
noncomputable section

open BigOperators DirectSum ENNReal Subgroup

universe u

variable (G : Type u) [Group G]
variable (Λ : Type*) [CanonicallyOrderedAddCommMonoid Λ]

class GroupFiltration where
  orderMap : Λ → Subgroup G
  union_eq_top : (⨆ i > (0 : Λ), orderMap i) = ⊤
  commutator_mem : ∀ (i j : Λ), i > 0 → j > 0 → ∀ x ∈ orderMap i, ∀ y ∈ orderMap j, (x⁻¹ * y⁻¹ * x * y) ∈ orderMap (i + j)
  inter_eq : ∀ (i : Λ), i > 0 → orderMap i = (⨅ j < i, orderMap j)

variable (filtration : GroupFiltration G Λ) {G} {Λ}

namespace GroupFiltration

def pos_orderMap := fun (i : Λ) => (⨆ μ > i, filtration.orderMap μ)

end GroupFiltration

lemma filtration_normal [Nonempty { i : Λ // i > 0 }] (hd : Directed (ι := { i : Λ // i > 0 }) (· ≤ ·) fun i ↦ GroupFiltration.orderMap (G := G) i.val) :
    ∀ (i : Λ), i > 0 → Subgroup.Normal (filtration.orderMap i) := by
  intro i hi
  refine {conj_mem := ?_}
  intro x hx g
  have h_union : ∃ δ : Λ, δ > 0 ∧ g⁻¹ ∈ filtration.orderMap δ := by
    have hg_top : g⁻¹ ∈ (⨆ i > (0 : Λ), filtration.orderMap i) := by
      rw [filtration.union_eq_top]
      exact mem_top g⁻¹
    rw [iSup_subtype'] at hg_top
    rw [Subgroup.mem_iSup_of_directed hd, Subtype.exists] at hg_top
    simp only [exists_prop] at hg_top
    exact hg_top
  obtain ⟨delta, hδ_pos, hgδ⟩ := h_union
  have h_comm : x⁻¹ * g * x * g⁻¹ ∈ filtration.orderMap (i + delta) := by
    let z := filtration.commutator_mem i delta hi hδ_pos x hx g⁻¹ hgδ
    simp only [inv_inv] at z
    exact z
  have : i + delta > 0 := by
    rw [@gt_iff_lt]
    rw [@gt_iff_lt] at hi hδ_pos
    exact Right.add_pos' hi hδ_pos
  have h_subset : filtration.orderMap (i + delta) ≤ filtration.orderMap i := by
    rw [filtration.inter_eq i hi, filtration.inter_eq (i + delta) this]
    simp only [le_iInf_iff]
    intro k hk
    apply iInf_le_of_le k
    rw [@iInf_le_iff]
    intro b hb1 hb2 hb3
    have : k < i + delta := by
      exact lt_add_of_lt_of_pos' hk hδ_pos
    exact hb1 this hb3
  have h_comm_i : x⁻¹ * g * x * g⁻¹ ∈ filtration.orderMap i := h_subset h_comm
  have h_gxg_inv : g * x * g⁻¹ = (x * (x⁻¹ * g * x * g⁻¹)) := by
    calc
    _ = 1 * (g * x * g⁻¹) := by
      rw [@self_eq_mul_left]
    _ = (x * x⁻¹) * (g * x * g⁻¹) := by
      rw [@mul_inv_cancel]
    _ = x * (x⁻¹ * g * x * g⁻¹) := by
      noncomm_ring
  have : g * x * g⁻¹ ∈ filtration.orderMap i := by
        rw [h_gxg_inv]
        exact Subgroup.mul_mem (filtration.orderMap i) hx h_comm_i
  exact this

lemma filtration_pos_sub (i : Λ) : (filtration.pos_orderMap i) ≤ filtration.orderMap i := by
  unfold GroupFiltration.pos_orderMap
  show ⨆ μ, ⨆ (_ : μ > i), GroupFiltration.orderMap μ ≤ GroupFiltration.orderMap i
  rw [@iSup₂_le_iff]
  intro j hj
  have hj₀ : j > 0 := pos_of_gt hj
  rw [filtration.inter_eq j hj₀]
  rw [@iInf_le_iff]
  intro b hb
  specialize hb i
  simp only [le_iInf_iff] at hb
  apply hb
  exact hj

variable [Nonempty { i : Λ // i > 0 }]
instance fil_inf_nonempty_1 (i : Λ) (hi : 0 < i) : Nonempty { μ : Λ // 0 < i } := by
  simp only [nonempty_subtype, exists_const, hi]

instance fil_inf_nonempty_2 (i : Λ) (hi : 0 < i) : Nonempty { μ : Λ // μ < i } := by
  simp only [nonempty_subtype]
  exact Exists.intro 0 hi

instance fil_inf_nonempty_3 (i : Λ) (hi : 0 < i) : Nonempty { μ : Λ // 0 < μ ∧ μ < i } := by
  simp only [nonempty_subtype]
  haveI : DenselyOrdered Λ := sorry
  refine exists_between hi

lemma filtration_pos_normal (hd : Directed (ι := { i : Λ // i > 0 }) (· ≤ ·) fun i ↦ GroupFiltration.orderMap (G := G) i.val) {i : Λ} (hi : i > 0) : Subgroup.Normal (filtration.pos_orderMap i) := by
  refine { conj_mem := ?conj_mem }
  intro x hx g
  have h_union : ∃ δ : Λ, δ > 0 ∧ g⁻¹ ∈ filtration.pos_orderMap δ := by
    have hg_top : g⁻¹ ∈ (⨆ i > (0 : Λ), filtration.orderMap i) := by
      rw [filtration.union_eq_top]
      exact mem_top g⁻¹
    rw [iSup_subtype'] at hg_top
    rw [Subgroup.mem_iSup_of_directed, Subtype.exists] at hg_top
    simp only [exists_prop] at hg_top
    have hg_top_pos : g⁻¹ ∈ (⨆ i > (0 : Λ), filtration.pos_orderMap i) := by
      unfold GroupFiltration.pos_orderMap
      simp only [gt_iff_lt, inv_mem_iff]
      have : ⨆ (i : Λ), ⨆ (_ : 0 < i), ⨆ μ, ⨆ (_ : i < μ), GroupFiltration.orderMap (G := G) μ = ⨆ (μ : Λ), ⨆ (_ : 0 < μ), ⨆ (i : Λ), ⨆ (_ : 0 < i ∧ i < μ), GroupFiltration.orderMap (G := G) μ := by
        apply le_antisymm
        · simp only [iSup_le_iff]
          intro j hj k hk
          have : GroupFiltration.orderMap k ≤ ⨆ (i : Λ) (_ : j < i), GroupFiltration.orderMap (G := G) i := le_biSup GroupFiltration.orderMap hk
          apply LE.le.trans this
          simp only [iSup_le_iff]
          intro b hb
          rw [@le_iSup_iff]
          intro c hc
          specialize hc b
          have : 0 < b := by
            exact pos_of_gt hb
          simp only [iSup_le_iff, this, true_implies] at hc
          specialize hc j ⟨hj, hb⟩
          exact hc
        · simp only [iSup_le_iff]
          intro j hj k hk
          rw [@le_iSup_iff]
          intro b hb
          specialize hb k
          simp only [iSup_le_iff, hk.1, true_implies] at hb
          specialize hb j hk.2
          exact hb
      rw [this]
      have : ⨆ (μ : Λ), ⨆ (_ : 0 < μ), ⨆ (i : Λ), ⨆ (_ : 0 < i ∧ i < μ), GroupFiltration.orderMap (G := G) μ = ⊤ := by
        have : ∀(μ : Λ), ⨆ (i : Λ), ⨆ (_ : 0 < i ∧ i < μ), GroupFiltration.orderMap μ = GroupFiltration.orderMap (G := G) μ := by
          intro μ
          rw [@iSup_subtype', @iSup_eq_closure]
          have : @Set.iUnion G { i // 0 < i ∧ i < μ } (fun i => ↑(GroupFiltration.orderMap (G := G) μ)) = (@SetLike.coe (Subgroup G) G instSetLike (GroupFiltration.orderMap μ)) := by
            rw [@Set.Subset.antisymm_iff]
            constructor
            . sorry
            . refine Set.subset_iUnion_of_subset ?right.i fun ⦃a⦄ a => a
              refine Classical.indefiniteDescription (fun x => 0 < x ∧ x < μ) ?_
              dsimp only

              sorry
            sorry
          sorry
        sorry
      rw [this]
      exact trivial
    rw [iSup_subtype', Subgroup.mem_iSup_of_directed, Subtype.exists] at hg_top_pos
    simp only [exists_prop] at hg_top_pos
    exact hg_top_pos
    . sorry
    . sorry
  obtain ⟨delta, hδ_pos, hgδ⟩ := h_union
  have h_comm : x⁻¹ * g * x * g⁻¹ ∈ filtration.pos_orderMap (i + delta) := by

    sorry
  have : i + delta > 0 := by sorry
  have h_subset : filtration.pos_orderMap (i + delta) ≤ filtration.pos_orderMap i := by
    rw [@SetLike.le_def]
    intro y hy
    have : y ∈ (⨅ μ > i, filtration.orderMap μ) := sorry
    show y ∈ filtration.pos_orderMap i
--simp only [GroupFiltration.pos_orderMap]

      --unfold GroupFiltration.pos_orderMap
    sorry
  have h_comm_i : x⁻¹ * g * x * g⁻¹ ∈ filtration.pos_orderMap i := h_subset h_comm
  have h_gxg_inv : g * x * g⁻¹ = (x * (x⁻¹ * g * x * g⁻¹)) := by
    calc
    _ = 1 * (g * x * g⁻¹) := by
      rw [@self_eq_mul_left]
    _ = (x * x⁻¹) * (g * x * g⁻¹) := by
      rw [@mul_inv_cancel]
    _ = x * (x⁻¹ * g * x * g⁻¹) := by
      noncomm_ring
  have : g * x * g⁻¹ ∈ filtration.pos_orderMap i := by
    rw [h_gxg_inv]
    exact Subgroup.mul_mem (filtration.pos_orderMap i) hx h_comm_i
  exact this

#check subgroupOf
-- (filtration.pos_orderMap i)是filtration.orderMap i的正规子群
def filtrationQuotient [Nonempty { i : Λ // i > 0 }] (i : Λ) (hi : i > 0): ((filtration.pos_orderMap i).subgroupOf (filtration.orderMap i)).Normal :=
  letI : (filtration.pos_orderMap i).Normal := filtration_pos_normal _ hi
  Subgroup.normal_subgroupOf

  /-refine { conj_mem := ?_ }
  intro x hx g
  refine mem_subgroupOf.mpr ?_
  rw [@mem_subgroupOf] at hx
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  sorry-/
#check Subgroup.prod
variable (H₁ H₂ : Subgroup G)
#check Π (i : Λ), (filtration.orderMap i)
def gr_fil := Π (i : Λ) (hi : i > (0 : Λ)), (filtration.orderMap i) ⧸ (filtration.pos_orderMap i).subgroupOf (filtration.orderMap i)
