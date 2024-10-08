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

/- variable [CanonicallyOrderedAddCommMonoid Λ] (fil : GroupFiltration G ℝ≥0∞) (test : GroupFiltration G (WithTop Λ))

def valuation : G → ℝ≥0∞ := by
    intro x
    let y := {i : ℝ≥0∞ | x ∈ fil.orderMap i}
    let z := sSup y
    use z

instance : SupSet (WithTop Λ) := by
  by_cases h : ∀ b < (⊤ : (WithTop Λ)), ∃ a : (WithTop Λ), b < a
  . refine { sSup := ?_ }
    exact fun _ => (⊤ : (WithTop Λ))
  . simp only [not_forall, Classical.not_imp, not_exists, not_lt] at h
    -- replace h : ∃ x, ∃ (_ : x < ⊤), ∀ (x_1 : WithTop Λ), x_1 ≤ x
    refine { sSup := ?_ }
    exact fun _ => Classical.choose h

def valuation_test : G → WithTop Λ := by
    intro x
    let y := {i : WithTop Λ | x ∈ test.orderMap i}
    let z := sSup y
    use z -/

--#check filtration.pos_orderMap

#check Subgroup.iSup_induction'
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

-- def AssociatedGradedGroup : Type* := Π (i : Λ), (filtration.orderMap i)

-- (filtration_pos i).subgroupOf (filtration.orderMap i)

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

instance fil_inf_nonempty_2 (i : Λ) (hi : 0 < i) : Nonempty { μ : Λ // μ < i } := by sorry

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

      have : ⨆ (i : Λ), ⨆ (_ : 0 < i), ⨆ μ, ⨆ (_ : i < μ), GroupFiltration.orderMap μ = ⨆ (μ : Λ), ⨆ (_ : 0 < μ), ⨆ i, ⨆ (_ : i < μ), GroupFiltration.orderMap (G := G) μ := by
        -- rw [@Subgroup.ext_iff]
        apply le_antisymm
        · simp only [iSup_le_iff]
          intro j hj k hk
          have : GroupFiltration.orderMap k ≤ ⨆ (i : Λ) (_ : j < i), GroupFiltration.orderMap (G := G) i := le_biSup GroupFiltration.orderMap hk
          have this_1 : ⨆ (i : Λ) (_ : i > j), GroupFiltration.orderMap (G := G) i = ⨆ (i : Λ) (_ : j < i), GroupFiltration.orderMap (G := G) i := by
            simp only [gt_iff_lt]
          rw [@le_iSup_iff]
          intro b hb
          simp only [iSup_le_iff] at hb
          sorry
        · sorry
        /-ext x
        constructor
        . intro hy
          have temp1 : ∃ (i : Λ), 0 < i ∧ x ∈ ⨆ μ, ⨆ (_ : i < μ), GroupFiltration.orderMap μ := by

            sorry
          have temp2 : ∃ (i μ : Λ), 0 < i ∧ i < μ ∧ x ∈ GroupFiltration.orderMap μ := by

            sorry
          -- have : Nonempty {(μ : Λ) // (0 : Λ) < (i : Λ)} := sorry
          --letI : Nonempty { μ // 0 < i } := sorry
          rw [iSup_subtype']
          --Subgroup.mem_iSup_of_directed
          simp only [Subtype.exists, exists_const, hi]
          . have : ∀ (a : Λ), ⨆ (j : Λ), ⨆ (_ : j < a), GroupFiltration.orderMap a = GroupFiltration.orderMap (G := G) a := by
              intro a
              rw [@iSup_subtype']
              rw [@iSup_eq_closure]
              have : ⋃ (i : { j : Λ // j < a }), (@SetLike.coe (Subgroup G) G instSetLike (GroupFiltration.orderMap a) ) = (@SetLike.coe (Subgroup G) G instSetLike (GroupFiltration.orderMap a)) := by
                -- haveI :
                rw [@Set.iUnion_const]
              nth_rw 2 [← closure_eq (K := GroupFiltration.orderMap a)]

              nth_rw 2 [← this]

              -- rw [@Subgroup.closure_iUnion]
              -- simp only [closure_eq]

              sorry
            obtain ⟨i₀, μ₀, hi₀μ₀⟩ := temp2
            use μ₀
            rw [this μ₀]
            exact hi₀μ₀.2.2
          .
            sorry
          sorry
        . intro hy

          sorry
        sorry-/

      have : ⨆ (i : Λ), ⨆ (_ : 0 < i), ⨆ μ, ⨆ (_ : i < μ), GroupFiltration.orderMap μ = ⨆ (μ : Λ), ⨆ (_ : 0 < μ), GroupFiltration.orderMap (G := G) μ := by
        -- rw [@iSup_subtype', iSup_subtype']
        -- rw [@iSup_prod']
        rw [@Subgroup.ext_iff]
        intro y
        constructor
        . intro hy
          rw [@iSup_subtype'] at hy

          sorry
        . sorry
        sorry
      sorry
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
