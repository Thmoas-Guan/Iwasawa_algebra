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
variable (Λ : Type*) [CanonicallyLinearOrderedAddCommMonoid Λ]

/-- The fil -/
class GroupFiltration where
  orderMap : Λ → Subgroup G
  index_bot_eq_top : orderMap 0 = ⊤
  union_eq_top : (⨆ i > (0 : Λ), orderMap i) = ⊤
  commutator_mem : ∀ (i j : Λ), i > 0 → j > 0 → ∀ x ∈ orderMap i, ∀ y ∈ orderMap j, (x⁻¹ * y⁻¹ * x * y) ∈ orderMap (i + j)
  inter_eq : ∀ (i : Λ), i > 0 → orderMap i = (⨅ j < i, orderMap j)

variable (filtration : GroupFiltration G Λ) {G} {Λ}
variable (i : Λ) (hi : i > 0)

#check filtration
#check GroupFiltration.union_eq_top


lemma filtration_index_trivial (h : ¬ Nonempty { i : Λ // i > 0 }) (filtration : GroupFiltration G Λ) : (⊥ : Subgroup G) = ⊤ := by
  simp only [gt_iff_lt, nonempty_subtype, not_exists, not_lt, nonpos_iff_eq_zero] at h
  ext x
  constructor
  . intro _
    trivial
  . intro hx
    rw [← filtration.union_eq_top] at hx
    simp only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, iSup_neg, iSup_bot, mem_bot, h] at hx
    trivial

lemma filtration_anti : Antitone (fun (i : Λ) => filtration.orderMap i) := by
  intro i j h
  dsimp
  by_cases h₀ : i = 0
  . rw [h₀, filtration.index_bot_eq_top]
    exact le_top
  . replace h₀ : i > 0 := pos_iff_ne_zero.mpr h₀
    have : j > 0 := gt_of_ge_of_gt h h₀
    rw [filtration.inter_eq i h₀, filtration.inter_eq j this]
    simp only [le_iInf_iff]
    intro b hb
    rw [@iInf_le_iff]
    intro c hc
    simp only [le_iInf_iff] at hc
    exact hc b (gt_of_ge_of_gt h hb)

lemma filtration_anti' {j : Λ} : Antitone (fun (b : (@Subtype Λ fun i => i > j)) => filtration.orderMap b.val) := by
  intro x1 x2 h
  dsimp
  rw [← @Subtype.coe_le_coe] at h
  exact filtration_anti filtration h

namespace GroupFiltration

def pos_orderMap := fun (i : Λ) => (⨆ μ > i, filtration.orderMap μ)

def pos_orderMap' : Λ → Subgroup G := by
  intro j
  if h : ∃ (b : Λ), IsMax b then
    if _ : j < Classical.choose h then
      exact (⨆ μ > j, filtration.orderMap μ)
    else
      exact (⊥ : Subgroup G)
  else
    exact (⨆ μ > j, filtration.orderMap μ)

end GroupFiltration

lemma filtration_pos_anti : Antitone (fun (i : Λ) => filtration.pos_orderMap i) := by
  intro i j h
  dsimp
  unfold GroupFiltration.pos_orderMap
  simp only [gt_iff_lt, iSup_le_iff]
  intro b hb
  rw [@le_iSup_iff]
  intro c hc
  specialize hc b
  simp only [iSup_le_iff] at hc
  have : i < b := by
    exact lt_of_le_of_lt h hb
  exact hc this

lemma filtration_pos'_anti : Antitone (fun (i : Λ) => filtration.pos_orderMap' i) := by
  intro x y h
  dsimp
  unfold GroupFiltration.pos_orderMap'
  dsimp
  simp only [gt_iff_lt]
  intro b hb
  by_cases h₀ : ∃ (d : Λ), IsMax d
  . simp_all only [dite_true]
    by_cases h₁ : y < Classical.choose h₀
    . have : x < Classical.choose h₀ := by exact lt_of_le_of_lt h h₁
      simp_all only [ite_true]
      exact filtration_pos_anti filtration h hb
    . simp_all only [ite_false, mem_bot, not_lt]
      exact Subgroup.one_mem _
  . simp only [↓reduceDIte, h₀] at hb ⊢
    exact filtration_pos_anti filtration h hb

lemma filtration_pos_anti' {j : Λ} : Antitone (fun (b : (@Subtype Λ fun i => i > j)) => filtration.pos_orderMap b.val) := by
  intro x1 x2 h
  dsimp
  rw [← @Subtype.coe_le_coe] at h
  exact filtration_pos_anti filtration h

lemma filtration_pos'_anti' {j : Λ} : Antitone (fun (b : (@Subtype Λ fun i => i > j)) => filtration.pos_orderMap' b.val) := by
  intro x1 x2 h
  dsimp
  rw [← @Subtype.coe_le_coe] at h
  exact filtration_pos'_anti filtration h

lemma filtration_union_le : x < b → filtration.orderMap b ≤ ⨆ (μ : Λ) (_ : x < μ), filtration.orderMap μ := by
  intro h
  rw [@le_iSup_iff]
  intro c hc
  specialize hc b
  simp only [iSup_le_iff] at hc
  exact hc h

instance filtration_index_directed {j : Λ} : IsDirected { i : Λ // i > j } fun x1 x2 => x1 ≤ x2 := by
  refine { directed := ?directed }
  intro a b
  simp only [Subtype.exists, gt_iff_lt]
  use (max a.1 b.1)
  have : j < (max a.1 b.1) := lt_max_of_lt_left a.2
  simp only [exists_true_left, this]
  constructor
  . exact Subtype.coe_le_coe.mp (le_max_left ↑a ↑b)
  . exact Subtype.coe_le_coe.mp (le_max_right ↑a ↑b)

instance filtraion_pos_directed : @Directed (Subgroup G) (@Subtype Λ fun i => i > 0) (fun x1 x2 => x1 ≤ x2) fun x => GroupFiltration.pos_orderMap filtration x.val := by
  let f := fun (x : { i // i > 0 }) => GroupFiltration.pos_orderMap filtration x.val
  apply Antitone.directed_le (f := f) ?_
  intro x1 x2 h
  unfold f GroupFiltration.pos_orderMap
  simp only [gt_iff_lt, iSup_le_iff]
  intro b hb
  have : x1 < b := by exact lt_of_le_of_lt h hb
  exact filtration_union_le filtration this

instance filtration_directed : @Directed (Subgroup G) (@Subtype Λ fun i => i > 0) (fun x1 x2 => x1 ≤ x2) fun x => filtration.orderMap (G := G) x.val := by
  refine Antitone.directed_le ?_
  intro x1 x2 h
  dsimp
  rw [← @Subtype.coe_le_coe] at h
  exact filtration_anti filtration h

instance filtration_directed' {j : Λ} : @Directed (Subgroup G) (@Subtype Λ fun i => i > j) (fun x1 x2 => x1 ≤ x2) fun x => filtration.orderMap (G := G) x.val := by
  intro x1 x2
  dsimp
  use min x1 x2
  constructor
  . apply filtration_anti
    simp only [Subtype.coe_le_coe, min_le_iff, le_refl, true_or]
  . apply filtration_anti
    simp only [Subtype.coe_le_coe, min_le_iff, le_refl, or_true]

lemma filtration_union [Nonempty { i : Λ // i > 0 }] (g : G) : ∃ δ : Λ, δ > 0 ∧ g ∈ filtration.orderMap δ := by
  have hg_top : g ∈ (⨆ i > (0 : Λ), filtration.orderMap i) := by
      rw [filtration.union_eq_top]
      exact mem_top g
  rw [iSup_subtype', Subgroup.mem_iSup_of_directed (filtration_directed filtration), Subtype.exists] at hg_top
  simp only [gt_iff_lt, exists_prop] at hg_top
  exact hg_top

lemma filtration_eq_top [DenselyOrdered Λ] : ⨆ (μ : Λ) (_ : 0 < μ), ⨆ (i : Λ) (_ : 0 < i ∧ i < μ), filtration.orderMap (G := G) μ = ⊤ := by
  have : ∀(μ : Λ), 0 < μ → ⨆ (i : Λ) (_ : 0 < i ∧ i < μ), filtration.orderMap μ = filtration.orderMap (G := G) μ := by
    intro μ hμ
    rw [@iSup_subtype', @iSup_eq_closure]
    have : @Set.iUnion G { i // 0 < i ∧ i < μ } (fun _ => ↑(filtration.orderMap (G := G) μ)) = (@SetLike.coe (Subgroup G) G instSetLike (filtration.orderMap μ)) := by
      rw [@Set.Subset.antisymm_iff]
      constructor
      . simp only [Set.iUnion_subset_iff, subset_refl, implies_true]
      . refine Set.subset_iUnion_of_subset ?right.i fun ⦃a⦄ a => a
        exact Classical.indefiniteDescription (fun x => 0 < x ∧ x < μ) (exists_between hμ)
    rw [this]
    simp only [closure_eq]
  rw [@eq_top_iff, @le_iSup_iff, ← filtration.union_eq_top]
  intro b hb
  simp only [gt_iff_lt, iSup_le_iff]
  intro c hc
  specialize hb c
  simp only [iSup_pos, hc, this] at hb
  exact hb

lemma filtration_pos_union [Nonempty { i : Λ // i > 0 }] [DenselyOrdered Λ] (g : G) : ∃ δ : Λ, δ > 0 ∧ g ∈ filtration.pos_orderMap δ := by
  have hg_top : g⁻¹ ∈ (⨆ i > (0 : Λ), filtration.orderMap i) := by
      rw [filtration.union_eq_top]
      exact mem_top g⁻¹
  rw [iSup_subtype', Subgroup.mem_iSup_of_directed, Subtype.exists] at hg_top
  simp only [exists_prop] at hg_top
  have hg_top_pos : g⁻¹ ∈ (⨆ i > (0 : Λ), filtration.pos_orderMap i) := by
    unfold GroupFiltration.pos_orderMap
    simp only [gt_iff_lt, inv_mem_iff]
    have : ⨆ (i : Λ) (_ : 0 < i), ⨆ (μ : Λ) (_ : i < μ), GroupFiltration.orderMap (G := G) μ = ⨆ (μ : Λ) (_ : 0 < μ), ⨆ (i : Λ), ⨆ (_ : 0 < i ∧ i < μ), GroupFiltration.orderMap (G := G) μ := by
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
        intro j _ k hk
        rw [@le_iSup_iff]
        intro b hb
        specialize hb k
        simp only [iSup_le_iff, hk.1, true_implies] at hb
        specialize hb j hk.2
        exact hb
    rw [this, filtration_eq_top]
    trivial
  . rw [iSup_subtype', Subgroup.mem_iSup_of_directed, Subtype.exists] at hg_top_pos
    simp only [inv_mem_iff, gt_iff_lt, exists_prop] at hg_top_pos
    . exact hg_top_pos
    . exact filtraion_pos_directed filtration
  . exact filtration_directed filtration

lemma filtration_normal :
    ∀ (i : Λ), i > 0 → Subgroup.Normal (filtration.orderMap i) := by
  by_cases h : ¬ Nonempty { i : Λ // i > 0 }
  . intro i hi
    simp only [nonempty_subtype, not_exists, not_lt, nonpos_iff_eq_zero] at h
    specialize h i
    simp_all only [lt_self_iff_false]
  haveI : Nonempty { i : Λ // i > 0 } := by
    rw [Mathlib.Tactic.PushNeg.not_not_eq] at h
    exact h
  intro i hi
  refine {conj_mem := ?_}
  intro x hx g
  obtain ⟨delta, hδ_pos, hgδ⟩ := filtration_union filtration g⁻¹
  have h_comm : x⁻¹ * g * x * g⁻¹ ∈ filtration.orderMap (i + delta) := by
    simp only [(inv_inv g) ▸ (filtration.commutator_mem i delta hi hδ_pos x hx g⁻¹ hgδ)]
  have : i + delta > 0 := by
    rw [@gt_iff_lt] at hi hδ_pos ⊢
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

lemma filtration_pos_sub : (filtration.pos_orderMap i) ≤ filtration.orderMap i := by
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

instance filtration_index_nomax [NoMaxOrder Λ] : Nonempty { μ : Λ // μ > i } := by
  simp only [nonempty_subtype]
  exact exists_gt i

lemma filtration_pos_normal [DenselyOrdered Λ] [NoMaxOrder Λ] :
  ∀ (i : Λ), i > 0 → Subgroup.Normal (filtration.pos_orderMap i) := by
  intro i _
  refine { conj_mem := ?conj_mem }
  intro x hx g
  have h_gxg_inv : g * x * g⁻¹ = (x * (x⁻¹ * g * x * g⁻¹)) := by
    rw [← one_mul (a := g * x * g⁻¹), ← mul_inv_cancel (a := x)]
    noncomm_ring
  rw [h_gxg_inv]
  apply Subgroup.mul_mem (filtration.pos_orderMap i) hx
  unfold GroupFiltration.pos_orderMap at hx ⊢
  rw [iSup_subtype', Subgroup.mem_iSup_of_directed (filtration_directed' filtration), Subtype.exists] at hx ⊢
  obtain ⟨delta, hδ_pos, hgδ⟩ := filtration_union filtration g⁻¹
  obtain ⟨j, hj_pos, hj⟩ := hx
  use j + delta, (lt_add_of_lt_of_pos' hj_pos hδ_pos)
  replace hj_pos : j > 0 := pos_of_gt hj_pos
  simp only [(inv_inv g) ▸ filtration.commutator_mem j delta hj_pos hδ_pos x hj g⁻¹ hgδ]

def filtrationQuotient [DenselyOrdered Λ] [NoMaxOrder Λ] (i : Λ) (hi : i > 0) :
  ((filtration.pos_orderMap i).subgroupOf (filtration.orderMap i)).Normal :=
  letI : (filtration.pos_orderMap i).Normal := filtration_pos_normal filtration i hi
  Subgroup.normal_subgroupOf

def gr_fil := Π (i : Λ) (_ : i > (0 : Λ)), (filtration.orderMap i) ⧸ (filtration.pos_orderMap i).subgroupOf (filtration.orderMap i)
