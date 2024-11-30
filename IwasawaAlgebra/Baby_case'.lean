import Mathlib

set_option maxHeartbeats 500000
set_option linter.unusedTactic false

open Polynomial PowerSeries

theorem PowerSeries.map_surjective {R : Type u} {S : Type v} [Semiring R] [Semiring S] (f : R →+* S) (hf : Function.Surjective ⇑f) :
    Function.Surjective (PowerSeries.map f) := by
  intro g
  use PowerSeries.mk fun k ↦ Function.surjInv hf (PowerSeries.coeff _ k g)
  ext k
  simp only [Function.surjInv, coeff_map, coeff_mk]
  exact Classical.choose_spec (hf ((coeff S k) g))

lemma Polynomial.map_coe {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] {φ : R →+* S} {f : R[X]} : Polynomial.map φ f = PowerSeries.map φ f := by
  ext
  simp

noncomputable def PowerSeries.lowerpart {R : Type u} [Semiring R] (f : R⟦X⟧) (n : ℕ) : R[X] where
  toFinsupp := {
    support :=
      have : Fintype {i | i < n ∧ PowerSeries.coeff R i f ≠ 0} :=
        Fintype.ofInjective (fun i ↦ (⟨i.1, i.2.1⟩ : Fin n)) (fun i j  hij ↦ Subtype.val_inj.mp <| Fin.mk.inj_iff.mp hij)
      Set.toFinset {i | i < n ∧ PowerSeries.coeff R i f ≠ 0}
    toFun := fun i ↦ if i < n then PowerSeries.coeff R i f else 0
    mem_support_toFun := by simp }

lemma lowerpart_deg_lt {R : Type u} [Semiring R] (f : R⟦X⟧) (n : ℕ) : (PowerSeries.lowerpart f n).degree < n := by
  apply (degree_lt_iff_coeff_zero (f.lowerpart n) n).mpr
  intro m hm
  simp only [lowerpart, ne_eq, Set.coe_setOf, Set.mem_setOf_eq, coeff_ofFinsupp, Finsupp.coe_mk]
  exact if_neg (Nat.not_lt.mpr hm)

lemma exist_special_lift {R : Type u} {S : Type v} [Ring R] [Ring S] [Nontrivial R] [Nontrivial S] (hom : R →+* S) (surj : Function.Surjective ⇑hom) {f : S[X]} (mon : Monic f) : ∃ g : R[X], g.map hom = f ∧ Monic g ∧ g.degree = f.degree := by
  have fne0 : f ≠ 0 := Monic.ne_zero_of_ne (zero_ne_one' S) mon
  let tofun : ℕ → R := fun i ↦ if i = f.natDegree then 1 else if i > f.natDegree then 0 else Classical.choose (surj (f.coeff i))
  have lt {i : ℕ} : tofun i ≠ 0 → i < f.natDegree + 1 := fun hi ↦ by
    by_contra gt
    have gt : f.natDegree < i := Nat.lt_of_succ_le (Nat.le_of_not_lt gt)
    simp only [Nat.ne_of_lt' gt, ↓reduceIte, gt, ne_eq, not_true_eq_false, tofun] at hi
  let g : R[X] := {
    toFinsupp := {
      support :=
        have : Fintype {i | tofun i ≠ 0} :=
          Fintype.ofInjective (fun i ↦ (⟨i.1, lt i.2⟩ : Fin (f.natDegree + 1))) (fun i j  hij ↦ Subtype.val_inj.mp <| Fin.mk.inj_iff.mp hij)
        Set.toFinset {i | tofun i ≠ 0}
      toFun := tofun
      mem_support_toFun := by simp
    }}
  use g
  constructor
  · apply Polynomial.ext
    intro i
    simp only [gt_iff_lt, ne_eq, Set.coe_setOf, Set.mem_setOf_eq, Polynomial.coeff_map,
      coeff_ofFinsupp, Finsupp.coe_mk, g, tofun]
    by_cases ne : i = f.natDegree
    · simp only [ne, ↓reduceIte, map_one, coeff_natDegree, ← Monic.leadingCoeff mon]
    · rcases lt_or_gt_of_ne ne with lt|gt
      · simp [ne, Nat.not_lt_of_gt lt, Classical.choose_spec (surj (f.coeff i))]
      · simp [ne, gt, ← (coeff_eq_zero_of_natDegree_lt gt)]
  · have gne0 : g ≠ 0 := by
      have : g.coeff f.natDegree ≠ 0 := by simp [g, tofun]
      by_contra h
      simp [h] at this
    have degeq : g.natDegree = f.natDegree := by
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · apply natDegree_le_iff_degree_le.mpr
        apply (Polynomial.degree_le_iff_coeff_zero g f.natDegree).mpr
        intro m hm
        have lt : f.natDegree < m := WithBot.coe_lt_coe.mp hm
        simp [g, tofun, (Nat.ne_of_lt (lt)).symm, lt]
      · simp [g, tofun]
    constructor
    · show g.coeff g.natDegree = 1
      simp [degeq, g, tofun]
    · rw [degree_eq_natDegree fne0, degree_eq_natDegree gne0, degeq]

variable {R : Type*} [CommRing R] {m : Ideal R} (hmax : m.IsMaximal)

section

variable (m)

open Set

lemma map_eq_range (n : ℕ) : m.map (Ideal.Quotient.mk (m ^ n)) = (Ideal.Quotient.mk (m ^ n))'' m := by
  ext x
  exact ⟨fun h ↦ Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ n)) Ideal.Quotient.mk_surjective h,
    fun ⟨r, hr, eq⟩ ↦ eq ▸ (Ideal.mem_map_of_mem _ hr)⟩

def hom (n : ℕ) : (R ⧸ m ^ (n + 1)) →+* (R ⧸ m ^ n) :=
  Ideal.Quotient.lift (m ^ (n + 1)) (Ideal.Quotient.mk (m ^ n))
  (fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.pow_le_pow_right (Nat.le_add_right n 1)) ha))

lemma hom_commute (n : ℕ) : ((hom m n).comp (Ideal.Quotient.mk (m ^ (n + 1)))) = (Ideal.Quotient.mk (m ^ n)) := rfl

lemma hom_surjective (n : ℕ) : Function.Surjective (hom m n) := by
  apply Ideal.Quotient.lift_surjective_of_surjective
  exact Ideal.Quotient.mk_surjective

lemma hom_ker (n : ℕ) : RingHom.ker (hom m n) = (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [hom, RingHom.mem_ker, Ideal.Quotient.lift_mk, Ideal.Quotient.eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa only [hom, ← eq, RingHom.mem_ker, Ideal.Quotient.lift_mk, Ideal.Quotient.eq_zero_iff_mem] using hr

lemma hom_preimage {n : ℕ} (npos : n > 0) : m.map (Ideal.Quotient.mk (m ^ (n + 1))) = (hom m n)⁻¹' (m.map (Ideal.Quotient.mk (m ^ n))) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simp [hom, ← eq, Submodule.mem_sup_left hr]
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ n)) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    rw [← hom_commute] at eq
    have : x - ((Ideal.Quotient.mk (m ^ (n + 1))) r) ∈ (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by simp [← hom_ker, ← eq]
    rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective this with ⟨s, hs, eq'⟩
    rw [← add_sub_cancel ((Ideal.Quotient.mk (m ^ (n + 1))) r) x, ← eq', ← map_add]
    apply Ideal.mem_map_of_mem
    apply Submodule.add_mem _ hr
    rw [← Nat.sub_add_cancel npos, pow_add, pow_one] at hs
    exact Ideal.mul_le_left (I := m ^ (n - 1)) hs

variable {m} in
lemma IsUnit_of_IsUnit_image {n : ℕ} (npos : n > 0) {a : R ⧸ m ^ (n + 1)} (h : IsUnit ((hom m n) a)) : IsUnit a := by
  rcases isUnit_iff_exists.mp h with ⟨b, hb, _⟩
  rcases hom_surjective m n b with ⟨b', hb'⟩
  rw [← hb', ← map_one (hom m n), ← map_mul] at hb
  apply (RingHom.sub_mem_ker_iff (hom m n)).mpr at hb
  rw [hom_ker m n] at hb
  rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective hb with ⟨c, hc, eq⟩
  have : a * (b' * (1 - ((Ideal.Quotient.mk (m ^ (n + 1))) c))) = 1 := by
    calc
      _ = (a * b' - 1) * (1 - ((Ideal.Quotient.mk (m ^ (n + 1))) c)) + (1 - ((Ideal.Quotient.mk (m ^ (n + 1))) c)) := by ring
      _ = 1 := by
        rw [← eq, mul_sub, mul_one, sub_add_sub_cancel', sub_eq_self, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_add]
        apply Ideal.mul_mem_mul hc (Ideal.mul_le_left (I := m ^ (n - 1)) _)
        simpa only [← pow_add, Nat.sub_add_cancel npos] using hc
  exact isUnit_of_mul_eq_one _ _ this

end

lemma ne0 {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) : f ≠ 0 := by
  rcases ntriv with ⟨k, hk⟩
  have : (PowerSeries.coeff _ k) f ≠ 0 := by
    by_contra h
    exact (h ▸ hk) (Submodule.zero_mem (Ideal.map (Ideal.Quotient.mk (m ^ n)) m))
  exact (ne_of_apply_ne ⇑(PowerSeries.coeff _ k) fun a => this a.symm).symm

open Classical

/-
If don't want to open Classical then try def and lemma below.

noncomputable def ntriv_deg {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) : ℕ :=
  sInf {k | (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))}

lemma ntriv_deg_spec {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) :
    (PowerSeries.coeff _ (ntriv_deg ntriv)) f ∉ m.map (Ideal.Quotient.mk (m ^ n)) ∧ ∀ i < (ntriv_deg ntriv), (PowerSeries.coeff _ i) f ∈ m.map (Ideal.Quotient.mk (m ^ n)) :=
  sorry
-/

lemma map_ntriv {n : ℕ} (npos : n > 0) {f : PowerSeries (R ⧸ m ^ (n + 1))} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ (n + 1)))) :
    ∃ k, (PowerSeries.coeff (R ⧸ m ^ n) k) (PowerSeries.map (hom m n) f) ∉ Ideal.map (Ideal.Quotient.mk (m ^ n)) m := by
  rcases ntriv with ⟨k, hk⟩
  use k
  by_contra h
  absurd hk
  show _ ∈ (_ : Set _)
  rw [hom_preimage m npos]
  exact h

lemma map_ntriv_findeq {n : ℕ} (npos : n > 0) {f : PowerSeries (R ⧸ m ^ (n + 1))} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ (n + 1)))) :
    Nat.find (map_ntriv npos ntriv) = Nat.find ntriv := by
  apply (Nat.find_eq_iff _).mpr
  simp only [PowerSeries.coeff_map]
  constructor
  · show ((PowerSeries.coeff (R ⧸ m ^ (n + 1)) (Nat.find ntriv)) f) ∉ (hom m n)⁻¹' (m.map (Ideal.Quotient.mk (m ^ n)))
    rw [← hom_preimage m npos]
    exact Nat.find_spec ntriv
  · intro k hk
    show ¬ ((PowerSeries.coeff (R ⧸ m ^ (n + 1)) k) f) ∉ (hom m n)⁻¹' (m.map (Ideal.Quotient.mk (m ^ n)))
    rw [← hom_preimage m npos]
    exact Nat.find_min ntriv hk

lemma preparation_lift_triv {n : ℕ} (neq0 : n = 0) [hmax : m.IsMaximal] (f : PowerSeries (R ⧸ m ^ (n + 1)))
    (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ (n + 1)))) :
    ∃! (h : (R ⧸ m ^ (n + 1))⟦X⟧ˣ), ∃ (g : Polynomial (R ⧸ m ^ (n + 1))), Monic g ∧ g.degree = Nat.find ntriv ∧
    (∀ i : ℕ, i < degree g → coeff g i ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1)))) ∧ f = g * h := by
  have {x : (R ⧸ m ^ (n + 1))} (hx : x ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1)))): x = 0 := by
    rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective hx with ⟨r, hr, eq⟩
    rw [← eq, Ideal.Quotient.eq_zero_iff_mem, neq0, zero_add, pow_one]
    exact hr
  have eqfind : f.order.get (order_finite_iff_ne_zero.mpr (ne0 ntriv)) = Nat.find ntriv := by
    apply PartENat.get_eq_iff_eq_coe.mpr (order_eq_nat.mpr _)
    constructor
    · by_contra h
      absurd Nat.find_spec ntriv
      simp only [h, Submodule.zero_mem]
    · exact fun i hi ↦ this <| Decidable.not_not.mp (Nat.find_min ntriv hi)
  let max' : (m ^ (n + 1)).IsMaximal := by simpa only [neq0, zero_add, pow_one] using hmax
  let hField : Field (R ⧸ m ^ (n + 1)) := Ideal.Quotient.field (m ^ (n + 1))
  have muleq : f = ((Polynomial.X (R := (R ⧸ m ^ (n + 1))) ^ (Nat.find ntriv)) : (R ⧸ m ^ (n + 1))[X]) * ↑f.Unit_of_divided_by_X_pow_order := by
    rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero (ne0 ntriv)]
    convert (PowerSeries.self_eq_X_pow_order_mul_divided_by_X_pow_order (ne0 ntriv)).symm
    simp only [Polynomial.coe_pow, Polynomial.coe_X, eqfind]
  use PowerSeries.Unit_of_divided_by_X_pow_order f
  constructor
  · use Polynomial.X ^ Nat.find ntriv
    constructor
    · apply monic_X_pow
    · simp only [degree_pow, degree_X, nsmul_eq_mul, mul_one, Nat.cast_lt,
      Polynomial.coeff_X_pow, Nat.cast_inj, eqfind, true_and]
      constructor
      · intro a ha
        convert (Submodule.zero_mem (Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m))
        simp [Nat.ne_of_lt ha]
      · exact muleq
  · rintro h' ⟨g', mon, deg, hg', eq⟩
    have : g' = Polynomial.X ^ Nat.find ntriv := by
      apply Polynomial.ext
      intro i
      simp only [Polynomial.coeff_X_pow]
      by_cases H' : i = Nat.find ntriv
      · rw [if_pos H', H', ← (natDegree_eq_of_degree_eq_some deg), Polynomial.Monic.coeff_natDegree mon]
      · rcases Nat.lt_or_gt_of_ne H' with gt|lt
        · rw [if_neg (Nat.ne_of_lt gt)]
          exact this ((hg' i) (deg ▸ Nat.cast_lt.mpr gt))
        · rw [if_neg (Nat.ne_of_gt lt)]
          apply Polynomial.coeff_eq_zero_of_degree_lt
          exact deg ▸ (Nat.cast_lt.mpr lt)
    rw [muleq, this] at eq
    apply Units.eq_iff.mp ((mul_right_inj' _).mp eq.symm)
    simp

lemma preparation_lift {n : ℕ} (npos : n > 0) [hmax : m.IsMaximal] (f : PowerSeries (R ⧸ m ^ n))
    (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) :
    ∃! (h : (R ⧸ m ^ n)⟦X⟧ˣ), ∃ (g : Polynomial (R ⧸ m ^ n)), Monic g ∧ g.degree = Nat.find ntriv ∧
    (∀ i : ℕ, i < degree g → coeff g i ∈ m.map (Ideal.Quotient.mk (m ^ n))) ∧ f = g * h := by
    let nontriv_all {k : ℕ} (pos : k > 0): Nontrivial (R ⧸ m ^ k) := Submodule.Quotient.nontrivial_of_lt_top (m ^ k) (lt_of_le_of_lt (Ideal.pow_le_self (Nat.not_eq_zero_of_lt pos)) (Ne.lt_top (Ideal.IsMaximal.ne_top hmax)))
    induction' n with n ih
    · absurd npos
      exact Nat.not_lt_zero 0
    · by_cases neq0 : n = 0
      · exact preparation_lift_triv neq0 f ntriv
      · rcases ih (Nat.zero_lt_of_ne_zero neq0) (PowerSeries.map (hom m n) f) (map_ntriv (Nat.zero_lt_of_ne_zero neq0) ntriv) with ⟨h, ⟨g, mon, deg, hg, eq⟩, uniq⟩
        have findeq := map_ntriv_findeq (Nat.zero_lt_of_ne_zero neq0) ntriv
        rw [findeq] at deg
        rcases PowerSeries.map_surjective (hom m n) (hom_surjective m n) h.val with ⟨h'', hh''⟩
        have : IsUnit h'' := by
          apply PowerSeries.isUnit_iff_constantCoeff.mpr
          have := PowerSeries.isUnit_iff_constantCoeff.mp (Units.isUnit h)
          rw [← hh'', ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
          simp only [PowerSeries.coeff_map, coeff_zero_eq_constantCoeff] at this
          exact IsUnit_of_IsUnit_image (Nat.zero_lt_of_ne_zero neq0) this
        let h' : (R ⧸ m ^ (n + 1))⟦X⟧ˣ := IsUnit.unit this
        have val : h'.1 = h'' := rfl
        let nontriv : Nontrivial (R ⧸ m ^ n) := nontriv_all (Nat.zero_lt_of_ne_zero neq0)
        let nontriv' : Nontrivial (R ⧸ m ^ (n + 1)) := nontriv_all npos
        rcases exist_special_lift (hom m n) (hom_surjective m n) mon with ⟨g', hg', mon', deg'⟩
        rw [deg] at deg'
        have : (PowerSeries.map (hom m n)) (f - g' * h') = 0 := by
          rw [map_sub, map_mul, ← Polynomial.map_coe, hg', val, hh'', eq, sub_eq_zero_of_eq rfl]
        set c : (R ⧸ m ^ (n + 1))⟦X⟧ := h'.inv * (f - g' * h')
        have map0 : (PowerSeries.map (hom m n)) c = 0 := by rw [map_mul, this, mul_zero]
        let α := PowerSeries.lowerpart c (Nat.find ntriv)
        let γ := (PowerSeries.mk fun i ↦ PowerSeries.coeff (R ⧸ m ^ (n + 1)) (i + (Nat.find ntriv)) c)
        have hu1 : IsUnit (1 + γ) := by
          apply PowerSeries.isUnit_iff_constantCoeff.mpr
          apply IsUnit_of_IsUnit_image (Nat.zero_lt_of_ne_zero neq0)
          convert isUnit_one
          simp [γ, ← PowerSeries.coeff_map, map0]
        have hu2 : IsUnit (h'.1 * (1 + γ)) := IsUnit.mul (Units.isUnit h') hu1
        have heq : (α : (R ⧸ m ^ (n + 1))⟦X⟧) + ((PowerSeries.X) ^ (Nat.find ntriv)) * γ = c := by
          ext k
          simp only [lowerpart, ne_eq, Set.coe_setOf, Set.mem_setOf_eq, map_add, Polynomial.coeff_coe, coeff_ofFinsupp, Finsupp.coe_mk, α, PowerSeries.coeff_X_pow_mul', coeff_mk, γ]
          by_cases lt : k < Nat.find ntriv
          · rw [if_pos lt, if_neg (Nat.not_le_of_lt lt), add_zero]
          · rw [if_neg lt, if_pos (Nat.le_of_not_lt lt), zero_add, Nat.sub_add_cancel (Nat.le_of_not_lt lt)]
        have deg'' : (g' + α).degree = Nat.find ntriv :=
          deg' ▸ Polynomial.degree_add_eq_left_of_degree_lt (deg' ▸ lowerpart_deg_lt c (Nat.find ntriv))
        have mon'' : Monic (g' + α) :=
          Polynomial.Monic.add_of_left mon' (deg' ▸ lowerpart_deg_lt c (Nat.find ntriv))
        have αcoeff (l : ℕ) : (hom m n) (α.coeff l) = 0 := by
            simp only [lowerpart, Set.coe_setOf, Set.mem_setOf_eq, coeff_ofFinsupp, Finsupp.coe_mk, α]
            by_cases lt : l < Nat.find ntriv
            · rw [if_pos lt, ← PowerSeries.coeff_map, map0]
              rfl
            · rw [if_neg lt, map_zero]
        have hgα : ∀ i : ℕ, i < (g' + α).degree → (g' + α).coeff i ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
          intro i hi
          show _ ∈ (_ : Set _)
          simp only [hom_preimage m (Nat.zero_lt_of_ne_zero neq0), coeff_add, Set.mem_preimage,
            map_add, αcoeff, add_zero, SetLike.mem_coe]
          rw [← (Polynomial.coeff_map (hom m n) i), hg']
          apply hg
          rw [deg, ← deg'']
          exact hi
        have hgcoeff (l : ℕ): (g.coeff l - if l = Nat.find ntriv then 1 else 0) ∈ Ideal.map (Ideal.Quotient.mk (m ^ n)) m := by
          by_cases leq : l = Nat.find ntriv
          · simp [leq, ← natDegree_eq_of_degree_eq_some deg, Polynomial.Monic.def.mp mon]
          · simp only [leq, ↓reduceIte, sub_zero]
            rcases lt_or_gt_of_ne leq with lt|gt
            · apply hg
              rw [deg]
              exact Nat.cast_lt.mpr lt
            · convert Submodule.zero_mem (Ideal.map (Ideal.Quotient.mk (m ^ n)) m)
              apply Polynomial.coeff_eq_zero_of_degree_lt
              rw [deg]
              exact Nat.cast_lt.mpr gt
        have hcoeff (l : ℕ): (PowerSeries.coeff (R ⧸ m ^ (n + 1)) l) (((g' + α)  : (R ⧸ m ^ (n + 1))⟦X⟧) - PowerSeries.X ^ Nat.find ntriv) ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
          simp only [map_sub, map_add, Polynomial.coeff_coe]
          show _ ∈ (_ : Set _)
          simp only [hom_preimage m (Nat.zero_lt_of_ne_zero neq0), PowerSeries.coeff_X_pow,
            Set.mem_preimage, map_sub, map_add, αcoeff, add_zero, RingHom.map_ite_one_zero,
            SetLike.mem_coe, ← (Polynomial.coeff_map (hom m n) l), hg']
          exact hgcoeff l
        have mul0 : (((g' + α)  : (R ⧸ m ^ (n + 1))⟦X⟧) - ((PowerSeries.X) ^ (Nat.find ntriv))) * γ = 0 := by
          ext
          simp only [PowerSeries.coeff_mul, map_zero]
          apply Finset.sum_eq_zero fun x _ => ?_
          rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective (hcoeff x.1) with ⟨r, hr, eqr⟩
          have : (PowerSeries.coeff (R ⧸ m ^ (n + 1)) x.2) γ ∈ (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
            simp [← hom_ker, RingHom.mem_ker, γ, ← PowerSeries.coeff_map, map0]
          rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective this with ⟨s, hs, eqs⟩
          rw [← eqr, ← eqs, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, add_comm, pow_add, pow_one]
          exact Submodule.mul_mem_mul hr hs
        have muleq : (g' + α) * (h'.1 * (1 + γ)) = f := by
          calc
          _ = (g' : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 + h'.1 * ((α : (R ⧸ m ^ (n + 1))⟦X⟧) + ((PowerSeries.X) ^ (Nat.find ntriv)) * γ) + (((g' + α)  : (R ⧸ m ^ (n + 1))⟦X⟧) - ((PowerSeries.X) ^ (Nat.find ntriv))) * γ * h'.1 := by ring
          _ = f := by simp [mul0, heq, c]
        use hu2.unit
        constructor
        · use (g' + α)
          exact ⟨mon'', deg'', hgα, by simp [muleq]⟩
        · rintro H ⟨G, monG, degG, hG, muleq'⟩
          have mapHu: IsUnit (PowerSeries.map (hom m n) H) := by
            apply RingHom.isUnit_map
            exact Units.isUnit H
          have mapeq : mapHu.unit = h := by
            apply uniq
            use Polynomial.map (hom m n) G
            constructor
            · apply Polynomial.Monic.map _ monG
            · have : (Polynomial.map (hom m n) G).degree = Nat.find ntriv := by
                rw [← degG]
                apply Polynomial.degree_map_eq_iff.mpr
                simp [monG]
              constructor
              · rw [this, findeq]
              · constructor
                · intro i hi
                  simp only [Polynomial.coeff_map]
                  show G.coeff i ∈ (hom m n)⁻¹' (m.map (Ideal.Quotient.mk (m ^ n)))
                  rw [← hom_preimage m (Nat.zero_lt_of_ne_zero neq0)]
                  apply hG
                  rw [degG, ← this]
                  exact hi
                · simp [muleq', Polynomial.map_coe]
          have mapeq' : (Polynomial.map (hom m n) G) = g := by
            apply coe_inj.mp
            calc
            _= (Polynomial.map (hom m n) G) * mapHu.unit.1 * mapHu.unit.inv := by rw [mul_assoc, mapHu.unit.val_inv, mul_one]
            _= (PowerSeries.map (hom m n) f) * mapHu.unit.inv := by simp [muleq', Polynomial.map_coe]
            _= _ := by rw [congrArg Units.inv mapeq, eq, mul_assoc, h.val_inv, mul_one]
          have : (PowerSeries.map (hom m n)) H.1 = h.1 := by simp [← mapeq]
          have map0' : (PowerSeries.map (hom m n)) (H.1 - h'.1) = 0 := by
            rw [map_sub, val, this, hh'', sub_eq_zero_of_eq rfl]
          have hcoeff' (l : ℕ): (PowerSeries.coeff (R ⧸ m ^ (n + 1)) l) ((G  : (R ⧸ m ^ (n + 1))⟦X⟧) - PowerSeries.X ^ Nat.find ntriv) ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
            simp only [map_sub, Polynomial.coeff_coe]
            show _ ∈ (_ : Set _)
            simp only [hom_preimage m (Nat.zero_lt_of_ne_zero neq0), Set.mem_preimage, map_sub,
              SetLike.mem_coe]
            rw [← (Polynomial.coeff_map (hom m n) l), mapeq']
            simp only [PowerSeries.coeff_X_pow, RingHom.map_ite_one_zero]
            exact hgcoeff l
          have mul0' : ((G  : (R ⧸ m ^ (n + 1))⟦X⟧) - ((PowerSeries.X) ^ (Nat.find ntriv))) * (H.1 - h'.1) = 0 := by
            ext
            simp only [PowerSeries.coeff_mul, map_zero]
            apply Finset.sum_eq_zero fun x _ => ?_
            rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective (hcoeff' x.1) with ⟨r, hr, eqr⟩
            have : (PowerSeries.coeff (R ⧸ m ^ (n + 1)) x.2) (H.1 - h'.1) ∈ (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
              simp only [← hom_ker, RingHom.mem_ker, ← PowerSeries.coeff_map, map0', map_zero]
            rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective this with ⟨s, hs, eqs⟩
            rw [← eqr, ← eqs, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, add_comm, pow_add, pow_one]
            exact Submodule.mul_mem_mul hr hs
          have eq' : f = (g'  : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 + ((PowerSeries.X) ^ (Nat.find ntriv)) * (H.1 - h'.1) + ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 := by
            calc
            _= G * H.1 := by rw [muleq']
            _= (g'  : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 + ((G  : (R ⧸ m ^ (n + 1))⟦X⟧) - ((PowerSeries.X) ^ (Nat.find ntriv))) * (H.1 - h'.1) + ((PowerSeries.X) ^ (Nat.find ntriv)) * (H.1 - h'.1) + ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 := by ring
            _= _ := by simp [mul0']
          have c_decomp : c = PowerSeries.X ^ Nat.find ntriv * ((H.1 - h'.1) * h'.inv) + ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) := by
            calc
            _= h'.inv * (f - ↑g' * h'.1) := rfl
            _= h'.inv * ((g'  : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 + ((PowerSeries.X) ^ (Nat.find ntriv)) * (H.1 - h'.1) + ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 - ↑g' * h'.1) := by
              simp only [Units.inv_eq_val_inv, Units.mul_right_inj, sub_left_inj]
              exact eq'
            _= PowerSeries.X ^ Nat.find ntriv * ((H.1 - h'.1) * h'.inv) + ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 * h'.inv := by ring
            _= _ := by rw [mul_assoc, h'.val_inv, mul_one]
          have coeff_ge {l : ℕ} (lge : l ≥ (Nat.find ntriv)): G.coeff l - g'.coeff l = 0 := by
            have h1 : G.natDegree = Nat.find ntriv := natDegree_eq_of_degree_eq_some degG
            have h2 : g'.natDegree = Nat.find ntriv := natDegree_eq_of_degree_eq_some deg'
            by_cases leq : l = (Nat.find ntriv)
            · simp only [leq]
              nth_rw 1 [← h1, ← h2]
              simp [monG, mon']
            · have lgt : l > (Nat.find ntriv) := Nat.lt_of_le_of_ne lge fun a => leq a.symm
              have : G.natDegree < l := lt_of_eq_of_lt h1 lgt
              simp [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_eq_of_lt h1 lgt),Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_eq_of_lt h2 lgt)]
          have eqγ : ((H.1 - h'.1) * h'.inv) = γ := by
            apply PowerSeries.ext
            intro k
            rw [coeff_mk, c_decomp, map_add, PowerSeries.coeff_X_pow_mul]
            simp [coeff_ge (Nat.le_add_left (Nat.find ntriv) k)]
          apply Units.eq_iff.mp
          simp only [IsUnit.unit_spec, mul_add, mul_one]
          rw [← eqγ, mul_comm (H.1 - h'.1) _, ← mul_assoc, h'.val_inv, one_mul, add_sub_cancel h'.1 H.1]

section

section

variable (m)

open Set

def BIGHOM {a b : ℕ} (le : a ≤ b) : R⧸m ^ b →+* R⧸m ^ a :=
  Ideal.Quotient.lift (m ^ b) (Ideal.Quotient.mk (m ^ a))
  (fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.pow_le_pow_right le) ha))

lemma BIGHOM_comm {a b : ℕ} (le : a ≤ b) (r : R) : (Ideal.Quotient.mk (m ^ a)) r = (BIGHOM m le) ((Ideal.Quotient.mk (m ^ b)) r) := rfl

lemma BIGHOM_surjective {a b : ℕ} (le : a ≤ b) : Function.Surjective (BIGHOM m le) := by
  apply Ideal.Quotient.lift_surjective_of_surjective
  exact Ideal.Quotient.mk_surjective

lemma BIGHOM_ker {a b : ℕ} (le : a ≤ b) : RingHom.ker (BIGHOM m le) = (m ^ a).map (Ideal.Quotient.mk (m ^ b)) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [BIGHOM, RingHom.mem_ker, Ideal.Quotient.lift_mk, Ideal.Quotient.eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ b)) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa only [BIGHOM, ← eq, RingHom.mem_ker, Ideal.Quotient.lift_mk, Ideal.Quotient.eq_zero_iff_mem] using hr

lemma BIGHOM_preimage {a b : ℕ} (apos : a > 0) (le : a ≤ b) : m.map (Ideal.Quotient.mk (m ^ b)) = (BIGHOM m le)⁻¹' (m.map (Ideal.Quotient.mk (m ^ a))) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ b)) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simp [BIGHOM, ← eq, Submodule.mem_sup_left hr]
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ a)) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    rw [BIGHOM_comm m le _] at eq
    have : x - ((Ideal.Quotient.mk (m ^ b)) r) ∈ (m ^ a).map (Ideal.Quotient.mk (m ^ b)) := by simp [← BIGHOM_ker m le, ← eq]
    rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ b)) Ideal.Quotient.mk_surjective this with ⟨s, hs, eq'⟩
    rw [← add_sub_cancel ((Ideal.Quotient.mk (m ^ b)) r) x, ← eq', ← map_add]
    apply Ideal.mem_map_of_mem
    apply Submodule.add_mem _ hr
    exact Ideal.pow_le_self (Nat.not_eq_zero_of_lt apos) hs

end

variable (m) in
lemma isUnit_iff_nmem [hmax : m.IsMaximal] [comp : IsAdicComplete m R] (r : R) : IsUnit r ↔ r ∉ m := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra mem
    rcases IsUnit.exists_left_inv h with ⟨s, hs⟩
    absurd (Ideal.ne_top_iff_one m).mp (Ideal.IsMaximal.ne_top hmax)
    simp [← hs, Ideal.mul_mem_left m s mem]
  · have mapu {n : ℕ} (npos : n > 0) : IsUnit (Ideal.Quotient.mk (m ^ n) r) := by
      induction' n with n ih
      · absurd npos
        exact Nat.not_lt_zero 0
      · by_cases neq0 : n = 0
        · let max' : (m ^ (n + 1)).IsMaximal := by simpa only [neq0, zero_add, pow_one] using hmax
          let hField : Field (R ⧸ m ^ (n + 1)) := Ideal.Quotient.field (m ^ (n + 1))
          simpa [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem.not, neq0] using h
        · apply IsUnit_of_IsUnit_image (Nat.zero_lt_of_ne_zero neq0)
          simpa [hom] using (ih (Nat.zero_lt_of_ne_zero neq0))
    choose inv_series' inv_series_spec' using fun (n : {n : ℕ // n > 0}) ↦ (IsUnit.exists_left_inv (mapu n.2))
    let inv_series : ℕ → R := fun n ↦ if h : n = 0 then 0 else Classical.choose <| (Ideal.Quotient.mk_surjective (I := m ^ n)) <| inv_series' ⟨n, (Nat.zero_lt_of_ne_zero h)⟩
    have inv_series_spec {n : ℕ} (npos : n > 0): (Ideal.Quotient.mk (m ^ n)) (inv_series n) = inv_series' ⟨n, npos⟩ := by
      simp only [Nat.not_eq_zero_of_lt npos, ↓reduceDIte, inv_series]
      exact Classical.choose_spec <| (Ideal.Quotient.mk_surjective (I := m ^ n)) <| inv_series' ⟨n, npos⟩
    have mod : ∀ {a b : ℕ}, a ≤ b → inv_series a ≡ inv_series b [SMOD m ^ a • (⊤ : Submodule R R)] := by
      intro a b le
      by_cases apos : a > 0
      · have bpos : b > 0 := Nat.lt_of_lt_of_le apos le
        simp only [smul_eq_mul, Ideal.mul_top]
        apply SModEq.sub_mem.mpr
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub]
        apply (IsUnit.mul_right_inj (mapu apos)).mp
        simp only [mul_zero, mul_sub]
        nth_rw 3 [BIGHOM_comm m le _, BIGHOM_comm m le _]
        simp only [inv_series_spec apos, inv_series_spec bpos, ← map_mul]
        rw [mul_comm, inv_series_spec', mul_comm, inv_series_spec']
        simp only [map_one, sub_self]
      · simp [Nat.eq_zero_of_not_pos apos]
    rcases IsPrecomplete.prec IsAdicComplete.toIsPrecomplete mod with ⟨inv, hinv⟩
    have eq (n : ℕ): inv * r - 1 ≡ 0 [SMOD m ^ n • (⊤ : Submodule R R)] := by
      by_cases npos : n > 0
      · apply SModEq.sub_mem.mpr
        simp only [smul_eq_mul, Ideal.mul_top, sub_zero]
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, map_one, map_mul, ← sub_add_cancel inv (inv_series n), map_add]
        have := SModEq.sub_mem.mp (hinv n).symm
        simp only [smul_eq_mul, Ideal.mul_top] at this
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr this, inv_series_spec npos, zero_add, inv_series_spec', sub_self]
      · simp [Nat.eq_zero_of_not_pos npos]
    apply isUnit_iff_exists_inv'.mpr
    use inv
    exact sub_eq_zero.mp <| IsHausdorff.haus IsAdicComplete.toIsHausdorff (inv * r - 1) eq

lemma map_ntriv' {n : ℕ} (npos : n > 0) {f : PowerSeries R} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff R k) f ∉ m) : ∃ (k : ℕ), (PowerSeries.coeff (R ⧸ m ^ n) k) (PowerSeries.map (Ideal.Quotient.mk (m ^ n)) f) ∉ m.map (Ideal.Quotient.mk (m ^ n)) := by
  rcases ntriv with ⟨k, hk⟩
  use k
  simp [Ideal.pow_le_self (Nat.not_eq_zero_of_lt npos), hk]

lemma map_ntriv_findeq' {n : ℕ} (npos : n > 0) {f : PowerSeries R} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff R k) f ∉ m) : Nat.find (map_ntriv' npos ntriv) = Nat.find ntriv := by
  apply (Nat.find_eq_iff _).mpr
  simp only [PowerSeries.coeff_map]
  constructor
  · by_contra h
    absurd Nat.find_spec ntriv
    simp only [Ideal.mem_quotient_iff_mem_sup, Ideal.pow_le_self (Nat.not_eq_zero_of_lt npos),
      sup_of_le_left] at h
    exact h
  · intro k hk
    exact Decidable.not_not.mpr <| Ideal.mem_map_of_mem (Ideal.Quotient.mk (m ^ n)) (Decidable.not_not.mp (Nat.find_min ntriv hk))

theorem Weierstrass_preparation [hmax : m.IsMaximal] [comp : IsAdicComplete m R] (f : PowerSeries R)
    (ntriv : ∃ (k : ℕ), (PowerSeries.coeff R k) f ∉ m) : ∃! (h : R⟦X⟧ˣ), ∃ (g : R[X]), Monic g ∧ g.degree = Nat.find ntriv ∧
    (∀ i : ℕ, i < degree g → coeff g i ∈ m) ∧ f = g * h := by
  let R_ntriv : Nontrivial R := nontrivial_of_ne 0 1 (ne_of_mem_of_not_mem (Submodule.zero_mem m) ((Ideal.ne_top_iff_one m).mp (Ideal.IsMaximal.ne_top hmax)))
  let R_ntriv' {k : ℕ} (kpos : k > 0): Nontrivial (R ⧸ m ^ k) := Submodule.Quotient.nontrivial_of_lt_top (m ^ k) <| lt_of_le_of_lt (Ideal.pow_le_self (Nat.not_eq_zero_of_lt kpos)) (Ne.lt_top (Ideal.IsMaximal.ne_top hmax))
  have findeq {n : ℕ} (npos : n > 0) : Nat.find (map_ntriv' npos ntriv) = Nat.find ntriv := map_ntriv_findeq' npos ntriv
  choose h_series' hh series_uniq using fun (n : {n : ℕ // n > 0}) ↦ preparation_lift n.2 (PowerSeries.map (Ideal.Quotient.mk (m ^ n.1)) f) (map_ntriv' n.2 ntriv)
  dsimp at hh series_uniq
  conv at hh =>
    ext n
    simp only [findeq n.2]
    skip
  conv at series_uniq =>
    ext n
    simp only [findeq n.2]
    skip
  choose g_series' series_mon series_deg series_coeff series_eq using hh
  --induced by uniqueness
  have BIGHOM_h_IsUnit {a b : ℕ} (bpos : b > 0) (le : a ≤ b): IsUnit ((PowerSeries.map (BIGHOM m le)) (h_series' ⟨b, bpos⟩)) := by
    apply RingHom.isUnit_map
    exact Units.isUnit (h_series' ⟨b, bpos⟩)
  have h_series_BIGHOMeq' {a b : ℕ} (apos : a > 0) (bpos : b > 0) (le : a ≤ b): (BIGHOM_h_IsUnit bpos le).unit = (h_series' ⟨a, apos⟩) := by
    apply series_uniq ⟨a, apos⟩ (BIGHOM_h_IsUnit bpos le).unit
    simp only [IsUnit.unit_spec]
    use (Polynomial.map (BIGHOM m le)) (g_series' ⟨b, bpos⟩)
    have degeq : (Polynomial.map (BIGHOM m le) (g_series' ⟨b, bpos⟩)).degree = (Nat.find ntriv) := by
      rw [← series_deg ⟨b, bpos⟩]
      letI : Nontrivial (R ⧸ m ^ a) := R_ntriv' apos
      exact Monic.degree_map (series_mon ⟨b, bpos⟩) (BIGHOM m le)
    constructor
    · exact Monic.map (BIGHOM m le) (series_mon ⟨b, bpos⟩)
    · constructor
      · exact degeq
      · constructor
        · simp only [degeq]
          intro i hi
          rw [← series_deg ⟨b, bpos⟩] at hi
          simp only [Polynomial.coeff_map]
          show (g_series' ⟨b, bpos⟩).coeff i ∈ (BIGHOM m le)⁻¹' (m.map (Ideal.Quotient.mk (m ^ a)))
          rw [← BIGHOM_preimage m apos le]
          exact series_coeff ⟨b, bpos⟩ i hi
        · rw [Polynomial.map_coe, ← map_mul,← series_eq ⟨b, bpos⟩]
          ext
          simp [BIGHOM]
  have h_series_BIGHOMeq {a b : ℕ} (apos : a > 0) (bpos : b > 0) (le : a ≤ b): (PowerSeries.map (BIGHOM m le)) (h_series' ⟨b, bpos⟩) = (h_series' ⟨a, apos⟩):= by
    show (BIGHOM_h_IsUnit bpos le).unit.1 = (h_series' ⟨a, apos⟩).1
    rw [h_series_BIGHOMeq' apos bpos le]
  have g_series_BIGHOMeq {a b : ℕ} (apos : a > 0) (bpos : b > 0) (le : a ≤ b): (g_series' ⟨a, apos⟩) = (Polynomial.map (BIGHOM m le)) (g_series' ⟨b, bpos⟩) := by
    apply coe_inj.mp
    calc
      _= (PowerSeries.map (Ideal.Quotient.mk (m ^ a))) f * (h_series' ⟨a, apos⟩).inv := by
        simp only [series_eq ⟨a, apos⟩, Units.inv_eq_val_inv, Units.mul_inv_cancel_right]
      _= (PowerSeries.map (Ideal.Quotient.mk (m ^ a))) f * (BIGHOM_h_IsUnit bpos le).unit.inv := by
        rw [h_series_BIGHOMeq' apos bpos le]
      _= ((Polynomial.map (BIGHOM m le)) (g_series' ⟨b, bpos⟩)) * (BIGHOM_h_IsUnit bpos le).unit * (BIGHOM_h_IsUnit bpos le).unit.inv := by
        simp only [IsUnit.unit_spec, Units.inv_eq_val_inv, Units.mul_left_inj]
        rw [Polynomial.map_coe, ← map_mul, ← series_eq ⟨b, bpos⟩]
        ext
        simp [BIGHOM]
      _= _ := by simp only [Units.inv_eq_val_inv, Units.mul_inv_cancel_right]
  let h_series : ℕ → R⟦X⟧ := fun k ↦ if h : k = 0 then 1 else
    Classical.choose <| PowerSeries.map_surjective (Ideal.Quotient.mk (m ^ k)) Ideal.Quotient.mk_surjective (h_series' ⟨k, Nat.zero_lt_of_ne_zero h⟩)
  have h_series_spec {k : ℕ} (kpos : k > 0) : PowerSeries.map (Ideal.Quotient.mk (m ^ k)) (h_series k) = (h_series' ⟨k, kpos⟩) := by
    simp only [Nat.not_eq_zero_of_lt kpos, ↓reduceDIte, h_series]
    exact Classical.choose_spec <| PowerSeries.map_surjective (Ideal.Quotient.mk (m ^ k)) Ideal.Quotient.mk_surjective (h_series' ⟨k, kpos⟩)
  let g_series : ℕ → R[X] := fun k ↦ if h : k = 0 then 0 else
    let _ := R_ntriv' (Nat.zero_lt_of_ne_zero h)
    Classical.choose <| exist_special_lift (Ideal.Quotient.mk (m ^ k)) Ideal.Quotient.mk_surjective (series_mon ⟨k, Nat.zero_lt_of_ne_zero h⟩)
  have g_series_spec {k : ℕ} (kpos : k > 0) : Polynomial.map (Ideal.Quotient.mk (m ^ k)) (g_series k) = (g_series' ⟨k, kpos⟩) ∧
      Monic (g_series k) ∧ (g_series k).degree = (g_series' ⟨k, kpos⟩).degree := by
    simp only [Nat.not_eq_zero_of_lt kpos, ↓reduceDIte, g_series]
    let _ := R_ntriv' kpos
    refine Classical.choose_spec <| exist_special_lift (Ideal.Quotient.mk (m ^ k)) Ideal.Quotient.mk_surjective ?_
    exact series_mon _
  have h_series_mod {a b : ℕ} (apos : a > 0) (le : a ≤ b) : PowerSeries.map (Ideal.Quotient.mk (m ^ a)) (h_series a) = PowerSeries.map (Ideal.Quotient.mk (m ^ a)) (h_series b) := by
    have bpos : b > 0 := Nat.lt_of_lt_of_le apos le
    ext t
    simp only [PowerSeries.coeff_map]
    nth_rw 2 [BIGHOM_comm m le _]
    simp only [← PowerSeries.coeff_map]
    congr 1
    rw [h_series_spec apos, h_series_spec bpos, h_series_BIGHOMeq apos bpos le]
  have g_series_mod {a b : ℕ} (apos : a > 0) (le : a ≤ b) : Polynomial.map (Ideal.Quotient.mk (m ^ a)) (g_series a) = Polynomial.map (Ideal.Quotient.mk (m ^ a)) (g_series b) := by
    have bpos : b > 0 := Nat.lt_of_lt_of_le apos le
    ext t
    simp only [Polynomial.coeff_map]
    nth_rw 2 [BIGHOM_comm m le _]
    simp only [← Polynomial.coeff_map]
    congr 1
    rw [(g_series_spec apos).1, (g_series_spec bpos).1, g_series_BIGHOMeq apos bpos le]
  have h_coeff_series_mod (i : ℕ): ∀ {a b : ℕ}, a ≤ b → PowerSeries.coeff R i (h_series a) ≡ PowerSeries.coeff R i (h_series b) [SMOD m ^ a • (⊤ : Submodule R R)] := by
    intro a b le
    by_cases apos : a > 0
    · simp only [smul_eq_mul, Ideal.mul_top]
      apply SModEq.sub_mem.mpr
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp [map_sub, ← PowerSeries.coeff_map, h_series_mod apos le]
    · simp [Nat.eq_zero_of_not_pos apos]
  let h : R⟦X⟧ := PowerSeries.mk fun i ↦ Classical.choose (IsPrecomplete.prec IsAdicComplete.toIsPrecomplete (h_coeff_series_mod i))
  have h_spec (i : ℕ) : ∀ n : ℕ, (PowerSeries.coeff R i) (h_series n) ≡ (PowerSeries.coeff R i) h [SMOD m ^ n • (⊤ : Submodule R R)]:= by
    simp only [coeff_mk, h]
    exact Classical.choose_spec (IsPrecomplete.prec IsAdicComplete.toIsPrecomplete (h_coeff_series_mod i))
  have h_spec' {n : ℕ} (npos : n > 0) : PowerSeries.map (Ideal.Quotient.mk (m ^ n)) h = h_series' ⟨n, npos⟩ := by
    rw [← h_series_spec npos]
    ext i
    simp only [PowerSeries.coeff_map]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    convert SModEq.sub_mem.mp (h_spec i n).symm
    simp only [smul_eq_mul, Ideal.mul_top]
  have hu : IsUnit h := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply (isUnit_iff_nmem m _).mpr
    by_contra mem
    rw [← pow_one m] at mem
    have := Ideal.Quotient.eq_zero_iff_mem.mpr mem
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_map, h_spec' Nat.one_pos, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    absurd PowerSeries.isUnit_iff_constantCoeff.mp (h_series' ⟨1, Nat.one_pos⟩).isUnit
    dsimp at this
    simp only [PNat.mk_ofNat, Positive.val_one, this, isUnit_zero_iff]
    let _ : Nontrivial (R ⧸ m ^ 1) := R_ntriv' Nat.one_pos
    exact zero_ne_one' (R ⧸ m ^ 1)
  have g_coeff_series_mod (i : ℕ) : ∀ {a b : ℕ}, a ≤ b → Polynomial.coeff (g_series a) i ≡ Polynomial.coeff (g_series b) i [SMOD m ^ a • (⊤ : Submodule R R)] := by
    intro a b le
    by_cases apos : a > 0
    · simp only [smul_eq_mul, Ideal.mul_top]
      apply SModEq.sub_mem.mpr
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp [map_sub, ← Polynomial.coeff_map, g_series_mod apos le]
    · simp [Nat.eq_zero_of_not_pos apos]
  let g_coeff : ℕ → R := fun i ↦ if i = (Nat.find ntriv) then 1 else if i > (Nat.find ntriv) then 0 else
    Classical.choose (IsPrecomplete.prec IsAdicComplete.toIsPrecomplete (g_coeff_series_mod i))
  have lt {i : ℕ}: g_coeff i ≠ 0 → i < (Nat.find ntriv) + 1 := by
    intro ne0
    by_contra gt
    have gt := Nat.lt_of_succ_le (Nat.le_of_not_lt gt)
    simp only [Nat.ne_of_lt' gt, ↓reduceIte, gt, ne_eq, not_true_eq_false, g_coeff] at ne0
  let g : R[X] := {
    toFinsupp := {
      support :=
        have : Fintype {i | g_coeff i ≠ 0} :=
          Fintype.ofInjective (fun i ↦ (⟨i.1, lt i.2⟩ : Fin ((Nat.find ntriv) + 1))) (fun i j  hij ↦ Subtype.val_inj.mp <| Fin.mk.inj_iff.mp hij)
        Set.toFinset {i | g_coeff i ≠ 0}
      toFun := g_coeff
      mem_support_toFun := by simp
    }}
  have g_spec {i : ℕ} (hi : i < Nat.find ntriv) : ∀ n : ℕ, (g_series n).coeff i ≡ g_coeff i [SMOD m ^ n • (⊤ : Submodule R R)] := by
    simp only [gt_iff_lt, Nat.ne_of_lt hi, ↓reduceIte, g_coeff, Nat.not_lt_of_gt hi]
    exact Classical.choose_spec (IsPrecomplete.prec IsAdicComplete.toIsPrecomplete (g_coeff_series_mod i))
  have g_spec' {n : ℕ} (npos : n > 0) : Polynomial.map (Ideal.Quotient.mk (m ^ n)) g = g_series' ⟨n, npos⟩ := by
    rw [← (g_series_spec npos).1]
    have deg : (g_series n).degree = Nat.find ntriv := by rw [(g_series_spec npos).2.2, series_deg]
    have ndeg : (g_series n).natDegree = Nat.find ntriv := natDegree_eq_of_degree_eq_some deg
    ext i
    simp only [Polynomial.coeff_map]
    by_cases ne : i = Nat.find ntriv
    · simp [ne, g, g_coeff, ← ndeg, (g_series_spec npos).2.1]
    · rcases lt_or_gt_of_ne ne with lt|gt
      · apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
        convert SModEq.sub_mem.mp (g_spec lt n).symm
        simp only [smul_eq_mul, Ideal.mul_top]
      · simp only [gt_iff_lt.mp gt, smul_eq_mul, Ideal.mul_top, ne_eq, Set.coe_setOf,
        Set.mem_setOf_eq, coeff_ofFinsupp, Finsupp.coe_mk, ne, ↓reduceIte, g, g_coeff, map_zero]
        have : ((g_series n).coeff i) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          exact ndeg ▸ gt
        simp only [this, map_zero]
  use hu.unit
  constructor
  · use g
    have degeq : g.natDegree = Nat.find ntriv := by
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · apply natDegree_le_iff_degree_le.mpr
        apply (Polynomial.degree_le_iff_coeff_zero g (Nat.find ntriv)).mpr
        intro k hk
        have lt : Nat.find ntriv < k := WithBot.coe_lt_coe.mp hk
        simp only [gt_iff_lt, ne_eq, Set.coe_setOf, coeff_ofFinsupp, Finsupp.coe_mk,
          (Nat.ne_of_lt (lt)).symm, ↓reduceIte, g, g_coeff, lt]
      · simp [g, g_coeff]
    have gne0 : g ≠ 0 := by
      have : g.coeff (Nat.find ntriv) ≠ 0 := by simp [g, g_coeff]
      by_contra h
      simp [h] at this
    constructor
    · show g.coeff g.natDegree = 1
      simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, degeq, coeff_ofFinsupp, Finsupp.coe_mk, g, ↓reduceIte, g_coeff]
    · constructor
      · rw [← degeq, degree_eq_natDegree gne0]
      · constructor
        · simp only [degree_eq_natDegree gne0, Nat.cast_lt, degeq]
          intro i hi
          rw [← pow_one m]
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          rw [← Polynomial.coeff_map, g_spec' Nat.one_pos]
          have := series_coeff ⟨1, Nat.one_pos⟩
          have map_bot: Ideal.map (Ideal.Quotient.mk (m ^ 1)) m = ⊥ := by
            apply (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk (m ^ 1))).mpr
            simp only [Ideal.mk_ker, pow_one, le_refl]
          simp only [series_deg ⟨1, Nat.one_pos⟩, Nat.cast_lt, map_bot, Ideal.mem_bot] at this
          exact this i hi
        · simp only [IsUnit.unit_spec]
          have {n : ℕ} (npos : n > 0): PowerSeries.map (Ideal.Quotient.mk (m ^ n)) f = PowerSeries.map (Ideal.Quotient.mk (m ^ n)) (g * h) := by
            simp only [map_mul,← Polynomial.map_coe, h_spec' npos, g_spec' npos, ← series_eq]
          ext i
          have modeq (n : ℕ) : (PowerSeries.coeff R i) f - (PowerSeries.coeff R i) (g * h) ≡ 0 [SMOD m ^ n • (⊤ : Submodule R R)] := by
            by_cases npos : n > 0
            · apply SModEq.zero.mpr
              simp only [smul_eq_mul, Ideal.mul_top]
              apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
              simp only [← PowerSeries.coeff_map]
              rw [this npos]
            · simp [Nat.eq_zero_of_not_pos npos]
          exact sub_eq_zero.mp <|  IsHausdorff.haus IsAdicComplete.toIsHausdorff ((PowerSeries.coeff R i) f - (PowerSeries.coeff R i) (g * h)) modeq
  · rintro H ⟨G, monG, degG, hG, muleq⟩
    have Hu (n : ℕ): IsUnit ((PowerSeries.map (Ideal.Quotient.mk (m ^ n))) H) := by
      apply RingHom.isUnit_map
      exact Units.isUnit H
    have modeq' {n : ℕ} (npos : n > 0) : (Hu n).unit = (h_series' ⟨n, npos⟩) := by
      apply series_uniq ⟨n, npos⟩
      use Polynomial.map (Ideal.Quotient.mk (m ^ n)) G
      constructor
      · exact Monic.map (Ideal.Quotient.mk (m ^ n)) monG
      · have degmapeq : (Polynomial.map (Ideal.Quotient.mk (m ^ n)) G).degree = (Nat.find ntriv) := by
          rw [← degG]
          letI : Nontrivial (R ⧸ m ^ n) := R_ntriv' npos
          exact Monic.degree_map monG (Ideal.Quotient.mk (m ^ n))
        constructor
        · exact degmapeq
        · constructor
          · intro i hi
            rw [degmapeq, ← degG] at hi
            simp [Submodule.mem_sup_left (hG i hi)]
          · simp [Polynomial.map_coe, ← map_mul, muleq]
    have modeq {n : ℕ} (npos : n > 0) : PowerSeries.map (Ideal.Quotient.mk (m ^ n)) H = (PowerSeries.map (Ideal.Quotient.mk (m ^ n))) (h_series n) := by
      rw [h_series_spec npos, ← modeq' npos]
      rfl
    apply Units.eq_iff.mp
    ext i
    simp only [IsUnit.unit_spec]
    have coeff_modeq' (n : ℕ): (PowerSeries.coeff R i) ↑H ≡ (PowerSeries.coeff R i) h [SMOD m ^ n • (⊤ : Submodule R R)] := by
      by_cases npos : n > 0
      · apply SModEq.trans (SModEq.sub_mem.mpr _) (h_spec i n)
        simp only [smul_eq_mul, Ideal.mul_top]
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, ← PowerSeries.coeff_map, ← PowerSeries.coeff_map, modeq npos, sub_self]
      · simp [Nat.eq_zero_of_not_pos npos]
    have coeff_modeq (n : ℕ): (PowerSeries.coeff R i) H - (PowerSeries.coeff R i) h ≡ 0 [SMOD m ^ n • (⊤ : Submodule R R)] :=
      SModEq.zero.mpr (SModEq.sub_mem.mp (coeff_modeq' n))
    exact sub_eq_zero.mp <|  IsHausdorff.haus IsAdicComplete.toIsHausdorff ((PowerSeries.coeff R i) H - (PowerSeries.coeff R i) h) coeff_modeq

end

section

variable (F : Type*) [Field F] (ι : outParam Type*) [LinearOrderedCommGroupWithZero ι] [vR : Valued F ι]
open Valued

theorem Weierstrass_preparation' (f : PowerSeries 𝒪[F]) (ne : f ≠ 0)
    (π : 𝒪[F] ) (hyp : Ideal.span {π} = 𝓂[F] ) : ∃ (m : ℕ),
    ∃! (g : Polynomial 𝒪[F] ), ∃ (h : (PowerSeries 𝒪[F])ˣ),
    Monic g ∧ (∀ i : ℕ, i < degree g → (coeff g i) ∈ 𝓂[F]) ∧
    f = (π ^ m) • g • h := sorry

end
