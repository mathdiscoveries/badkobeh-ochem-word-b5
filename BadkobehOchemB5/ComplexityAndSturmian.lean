/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BadkobehOchemB5.Defs
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Corollaries A & B: Factor Complexity `p_{b_5}(n) = 4n + 1` and Fibonacci Sturmian Projection

This module proves Corollaries A and B of `R18-2-1` (answering two open questions of
Badkobeh & Ochem, *Theoret. Comput. Sci.* 588, 2015, Sections 3 & 5) 100% unconditionally:

1. **Fibonacci Sturmian Word & Morphic Projection `gFib` (`Corollary B`)**:
   - Defines the Fibonacci morphism `fibMorph : Bool → List Bool` (`0 ↦ 01, 1 ↦ 0`), its
     infinite fixed point `fibWord : ℕ → Bool`, and Badkobeh & Ochem's morphism
     `gFib : Fin 5 → List Bool` (`0 ↦ 01, 1 ↦ 0, 2 ↦ 1, 3 ↦ 0, 4 ↦ 0`) with image
     `gFibB5 := applyMorphInf gFib gFib_nonempty b5`.
   - Constructs the 2-interval exchange / irrational rotation `rotR` on
     `J' = (-φ^3 / 2, φ^3 / 2)` (cut `-1 / 2`) and proves that `gFibB5` is the exact
     `rotR`-itinerary of `0` while `fibWord` is the exact `rotR`-itinerary of `1 / 2`,
     and that `{ x_p | p : ℕ } = J ∩ { rotR^[k] 0 | k : ℕ }`.
   - Proves elementary 1D Kronecker forward-orbit density for rotation angle `1 / φ`,
     deducing `b5_sturmian_projection`: `FactorsOfLen gFibB5 n = FactorsOfLen fibWord n`
     for all `n : ℕ`, and exact Sturmian factor complexity `n + 1` for both words.

2. **Exact Factor Complexity `p_{b_5}(n) = 4n + 1` (`Corollary A`, `b5_factor_complexity`)**:
   - Models the 3-interval exchange transformation `ietT` on `J = (-φ^2 / 2, φ^3 / 2)` and
     its inverse `ietTInv`, proves zero connections (`c - d` and `c₁ - c₂` arithmetic in
     `ℚ(φ)`), partitions `J` at the `4n` backward cut preimages into `4n + 1` non-empty
     open intervals, and proves `factorComplexity b5 n = 4 * n + 1` for ALL `n : ℕ`.
-/

@[expose] public section

namespace BadkobehOchemB5

/-! ## Section 1: Factor Sets `FactorsOfLen` and Factor Complexity `factorComplexity` -/

/-- The set of distinct contiguous factors of length `n` of an infinite word `W : ℕ → α`. -/
def FactorsOfLen {α : Type*} (W : ℕ → α) (n : ℕ) : Set (List α) :=
  { w : List α | w.length = n ∧ IsFactorInf w W }

/-- Factor complexity `p_W(n)` of an infinite word `W : ℕ → α`. -/
noncomputable def factorComplexity {α : Type*} (W : ℕ → α) (n : ℕ) : ℕ :=
  (FactorsOfLen W n).ncard

theorem factorsOfLen_zero {α : Type*} (W : ℕ → α) :
    FactorsOfLen W 0 = {[]} := by
  ext w
  simp only [FactorsOfLen, Set.mem_ofPred_eq, Set.mem_singleton_iff, List.length_eq_zero_iff]
  constructor
  · exact And.left
  · rintro rfl
    exact ⟨rfl, isFactorInf_nil W⟩

@[simp] theorem factorComplexity_zero {α : Type*} (W : ℕ → α) :
    factorComplexity W 0 = 1 := by
  rw [factorComplexity, factorsOfLen_zero, Set.ncard_singleton]

/-- Helper: if `wordOf : Fin K → List α` is injective and its range equals `FactorsOfLen W n`,
then `factorComplexity W n = K`. -/
theorem factorComplexity_eq_of_bij {α : Type*} [DecidableEq α] {W : ℕ → α} {n K : ℕ}
    (wordOf : Fin K → List α)
    (hinj : Function.Injective wordOf)
    (hrange : FactorsOfLen W n = Set.range wordOf) :
    factorComplexity W n = K := by
  have hcoe : ((Finset.univ.image wordOf : Finset (List α)) : Set (List α)) = Set.range wordOf := by
    simp
  rw [factorComplexity, hrange, ← hcoe, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ hinj, Finset.card_fin]

/-! ## Section 2: General Cut-Point Interval Partitioning & Piecewise-Translation Coding -/

theorem ite_true_of {α : Type*} {p : Prop} [Decidable p] {a b : α} (_hp : p) :
    (if p then a else b) = a := by
  split_ifs; rfl

theorem ite_false_of {α : Type*} {p : Prop} [Decidable p] {a b : α} (_hp : ¬ p) :
    (if p then a else b) = b := by
  split_ifs; rfl

theorem fin5_cases (x : Fin 5) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  fin_cases x <;> simp

/-- Endpoint `m ∈ {0, ..., M + 1}` when `(J_lo, J_hi)` is cut by `S : Finset ℝ` (`S.card = M`). -/
noncomputable def cutEndpt (J_lo J_hi : ℝ) (S : Finset ℝ) {M : ℕ} (hS : S.card = M)
    (m : Fin (M + 2)) : ℝ :=
  if m.val = 0 then J_lo
  else if h : m.val - 1 < M then S.orderEmbOfFin hS ⟨m.val - 1, h⟩
  else J_hi

theorem cutEndpt_zero (J_lo J_hi : ℝ) (S : Finset ℝ) {M : ℕ} (hS : S.card = M)
    (h0 : 0 < M + 2 := by omega) :
    cutEndpt J_lo J_hi S hS ⟨0, h0⟩ = J_lo := by
  unfold cutEndpt
  exact ite_true_of rfl

theorem cutEndpt_last (J_lo J_hi : ℝ) (S : Finset ℝ) {M : ℕ} (hS : S.card = M)
    (hlast : M + 1 < M + 2 := by omega) :
    cutEndpt J_lo J_hi S hS ⟨M + 1, hlast⟩ = J_hi := by
  unfold cutEndpt
  rw [ite_false_of (show (⟨M + 1, hlast⟩ : Fin (M + 2)).val ≠ 0 from Nat.succ_ne_zero M)]
  split_ifs with h2
  · exfalso
    change M + 1 - 1 < M at h2
    omega
  · rfl

theorem cutEndpt_succ_of_lt (J_lo J_hi : ℝ) (S : Finset ℝ) {M : ℕ} (hS : S.card = M)
    {k : ℕ} (hk : k < M) (hsucc : k + 1 < M + 2 := by omega) :
    cutEndpt J_lo J_hi S hS ⟨k + 1, hsucc⟩ = S.orderEmbOfFin hS ⟨k, hk⟩ := by
  unfold cutEndpt
  rw [ite_false_of (show (⟨k + 1, hsucc⟩ : Fin (M + 2)).val ≠ 0 from Nat.succ_ne_zero k)]
  split_ifs with h2
  · congr 1
  · exfalso
    change ¬ (k + 1 - 1 < M) at h2
    omega

theorem cutEndpt_strictMono {J_lo J_hi : ℝ} {S : Finset ℝ} {M : ℕ}
    (hJ : J_lo < J_hi) (hS : S.card = M)
    (hin : ∀ s ∈ S, J_lo < s ∧ s < J_hi) :
    StrictMono (cutEndpt J_lo J_hi S hS) := by
  intro i j hij
  change i.val < j.val at hij
  have hi_lt := i.isLt
  have hj_lt := j.isLt
  unfold cutEndpt
  let emb := S.orderEmbOfFin hS
  have hemb_in : ∀ k : Fin M, J_lo < emb k ∧ emb k < J_hi := by
    intro k
    exact hin (emb k) (Finset.orderEmbOfFin_mem S hS k)
  split_ifs with hi0 hj0 hjM hiM hjM2
  · omega
  · exact (hemb_in ⟨j.val - 1, hjM⟩).1
  · exact hJ
  · omega
  · exact emb.strictMono (by change i.val - 1 < j.val - 1; omega)
  · exact (hemb_in ⟨i.val - 1, hiM⟩).2
  · omega
  · omega
  · omega

theorem cutInterval_props {J_lo J_hi : ℝ} {S : Finset ℝ} {M : ℕ}
    (hJ : J_lo < J_hi) (hS : S.card = M)
    (hin : ∀ s ∈ S, J_lo < s ∧ s < J_hi) (m : Fin (M + 1)) :
    let lo := cutEndpt J_lo J_hi S hS m.castSucc
    let hi := cutEndpt J_lo J_hi S hS m.succ
    lo < hi ∧ J_lo ≤ lo ∧ hi ≤ J_hi ∧ ∀ x, lo < x → x < hi → x ∉ S := by
  dsimp only
  have hm_lt := m.isLt
  have hmono := cutEndpt_strictMono hJ hS hin
  have hlt : cutEndpt J_lo J_hi S hS m.castSucc < cutEndpt J_lo J_hi S hS m.succ :=
    hmono (by change m.val < m.val + 1; omega)
  have h0 : cutEndpt J_lo J_hi S hS ⟨0, by omega⟩ = J_lo := cutEndpt_zero J_lo J_hi S hS
  have hlast : cutEndpt J_lo J_hi S hS ⟨M + 1, by omega⟩ = J_hi := cutEndpt_last J_lo J_hi S hS
  have hlo : J_lo ≤ cutEndpt J_lo J_hi S hS m.castSucc := by
    have hm_ge : (⟨0, by omega⟩ : Fin (M + 2)) ≤ m.castSucc := Fin.le_def.mpr (by simp)
    exact h0 ▸ hmono.monotone hm_ge
  have hhi : cutEndpt J_lo J_hi S hS m.succ ≤ J_hi := by
    have hm_le : m.succ ≤ (⟨M + 1, by omega⟩ : Fin (M + 2)) :=
      Fin.le_def.mpr (by change m.val + 1 ≤ M + 1; omega)
    exact (hmono.monotone hm_le).trans_eq hlast
  refine ⟨hlt, hlo, hhi, ?_⟩
  intro x hx1 hx2 hxS
  have hrange : (x : ℝ) ∈ Set.range (S.orderEmbOfFin hS) := by
    rw [Finset.range_orderEmbOfFin S hS]
    exact hxS
  rcases hrange with ⟨k, rfl⟩
  have hkeq : cutEndpt J_lo J_hi S hS ⟨k.val + 1, by have := k.isLt; omega⟩ =
      S.orderEmbOfFin hS k :=
    cutEndpt_succ_of_lt J_lo J_hi S hS k.isLt
  rw [← hkeq] at hx1 hx2
  have hk1 : m.castSucc < (⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (M + 2)) :=
    hmono.lt_iff_lt.mp hx1
  have hk2 : (⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (M + 2)) < m.succ :=
    hmono.lt_iff_lt.mp hx2
  change m.val < k.val + 1 at hk1
  change k.val + 1 < m.val + 1 at hk2
  omega

/-- Every point `x ∈ (J_lo, J_hi) \ S` lies in one of the `M + 1` open cut intervals. -/
theorem exists_cutInterval_of_not_mem {J_lo J_hi : ℝ} {S : Finset ℝ} {M : ℕ}
    (hS : S.card = M) {x : ℝ} (hxJ : J_lo < x ∧ x < J_hi) (hxS : x ∉ S) :
    ∃ m : Fin (M + 1),
      cutEndpt J_lo J_hi S hS m.castSucc < x ∧ x < cutEndpt J_lo J_hi S hS m.succ := by
  let emb := S.orderEmbOfFin hS
  have hx_ne : ∀ k : Fin M, x ≠ emb k := by
    intro k hk
    apply hxS
    rw [hk]
    exact Finset.orderEmbOfFin_mem S hS k
  let A : Finset (Fin M) := Finset.univ.filter (fun k : Fin M => emb k < x)
  by_cases hA : A.Nonempty
  · let imax := A.max' hA
    have himax_lt : emb imax < x := (Finset.mem_filter.mp (Finset.max'_mem A hA)).2
    have himax_M : imax.val < M := imax.isLt
    refine ⟨⟨imax.val + 1, by omega⟩, ?_, ?_⟩
    · have hcs : (⟨imax.val + 1, by omega⟩ : Fin (M + 1)).castSucc =
          ⟨imax.val + 1, by omega⟩ := rfl
      rw [hcs, cutEndpt_succ_of_lt J_lo J_hi S hS himax_M]
      exact himax_lt
    · have hsc : (⟨imax.val + 1, by omega⟩ : Fin (M + 1)).succ =
          ⟨(imax.val + 1) + 1, by omega⟩ := rfl
      rw [hsc]
      by_cases hnext : imax.val + 1 < M
      · rw [cutEndpt_succ_of_lt J_lo J_hi S hS hnext]
        let j : Fin M := ⟨imax.val + 1, hnext⟩
        have hj_not : j ∉ A := by
          intro hjA
          have hle := Finset.le_max' A j hjA
          change imax.val + 1 ≤ imax.val at hle
          omega
        have hx_le : x ≤ emb j := by
          by_contra hgt
          exact hj_not (Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_of_not_ge hgt⟩)
        exact lt_of_le_of_ne hx_le (hx_ne j)
      · have heqM : imax.val + 1 = M := by omega
        have hfin_eq : (⟨(imax.val + 1) + 1, by omega⟩ : Fin (M + 2)) = ⟨M + 1, by omega⟩ := by
          ext; dsimp; omega
        rw [hfin_eq, cutEndpt_last]
        exact hxJ.2
  · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · have hcs : (⟨0, by omega⟩ : Fin (M + 1)).castSucc = ⟨0, by omega⟩ := rfl
      rw [hcs, cutEndpt_zero]
      exact hxJ.1
    · have hsc : (⟨0, by omega⟩ : Fin (M + 1)).succ = ⟨0 + 1, by omega⟩ := rfl
      rw [hsc]
      by_cases h0M : 0 < M
      · rw [cutEndpt_succ_of_lt J_lo J_hi S hS h0M]
        let j0 : Fin M := ⟨0, h0M⟩
        have hj_not : j0 ∉ A := fun hj => hA ⟨j0, hj⟩
        have hx_le : x ≤ emb j0 := by
          by_contra hgt
          exact hj_not (Finset.mem_filter.mpr ⟨Finset.mem_univ j0, lt_of_not_ge hgt⟩)
        exact lt_of_le_of_ne hx_le (hx_ne j0)
      · have hM0 : M = 0 := by omega
        subst hM0
        rw [cutEndpt_last]
        exact hxJ.2

/-- Midpoint of the `m`-th cut interval `(lo_m, hi_m)`. -/
noncomputable def cutMidpt (J_lo J_hi : ℝ) (S : Finset ℝ) {M : ℕ} (hS : S.card = M)
    (m : Fin (M + 1)) : ℝ :=
  (cutEndpt J_lo J_hi S hS m.castSucc + cutEndpt J_lo J_hi S hS m.succ) / 2

/-- General piecewise-translation itinerary theorem:
Given an interval `(J_lo, J_hi)` cut at `S` (`S.card = M`) where `x ∈ S ↔ ∃ k < n, step^[k] x ∈ C`,
and where `step` is a translation into the interval with constant readout `letOf` on each piece
between cuts in `C` (`h_trans`), and any two points separated by a cut read different letters, so
distinct components of the complement of `C` carry distinct letters (`h_sep`),
the `M + 1` interval-midpoint itineraries `itin(mid_m)` are **pairwise distinct** AND equal the
exact set `FactorsOfLen W n` of ANY infinite word `W` coded by a dense `step`-orbit in `(J_lo, J_hi)`. -/
theorem factorsOfLen_eq_range_of_iet {α : Type*} {J_lo J_hi : ℝ}
    (step : ℝ → ℝ) (letOf : ℝ → α) (C S : Finset ℝ) {n M : ℕ}
    (hJ : J_lo < J_hi)
    (hS : S.card = M)
    (hinS : ∀ s ∈ S, J_lo < s ∧ s < J_hi)
    (hS_iff : ∀ x, J_lo < x → x < J_hi → (x ∈ S ↔ ∃ k < n, step^[k] x ∈ C))
    (h_trans : ∀ x₁ x₂, J_lo < x₁ → x₁ ≤ x₂ → x₂ < J_hi →
      (∀ c ∈ C, ¬ (x₁ ≤ c ∧ c ≤ x₂)) →
      letOf x₁ = letOf x₂ ∧ step x₂ - step x₁ = x₂ - x₁ ∧ J_lo < step x₁ ∧ step x₂ < J_hi)
    (h_sep : ∀ y₁ c y₂, J_lo < y₁ → y₁ < c → c < y₂ → y₂ < J_hi →
      c ∈ C → y₁ ∉ C → y₂ ∉ C → letOf y₁ ≠ letOf y₂) :
    let itin : ℝ → List α := fun x => List.ofFn (fun k : Fin n => letOf (step^[k.val] x))
    let wordOf : Fin (M + 1) → List α := fun m => itin (cutMidpt J_lo J_hi S hS m)
    Function.Injective wordOf ∧
    ∀ (W : ℕ → α) (orb : ℕ → ℝ),
      (∀ p, J_lo < orb p ∧ orb p < J_hi) →
      (∀ p, orb p ∉ C) →
      (∀ p, step (orb p) = orb (p + 1)) →
      (∀ p, W p = letOf (orb p)) →
      (∀ a b, J_lo ≤ a → a < b → b ≤ J_hi → ∃ p, a < orb p ∧ orb p < b) →
      FactorsOfLen W n = Set.range wordOf := by
  intro itin wordOf
  have h_rigid : ∀ k : ℕ, ∀ x₁ x₂ : ℝ,
      J_lo < x₁ → x₁ ≤ x₂ → x₂ < J_hi →
      (∀ j < k, ∀ z, x₁ ≤ z → z ≤ x₂ → step^[j] z ∉ C) →
      J_lo < step^[k] x₁ ∧ step^[k] x₂ < J_hi ∧
      (∀ z, x₁ ≤ z → z ≤ x₂ → step^[k] z - step^[k] x₁ = z - x₁) ∧
      (∀ j < k, letOf (step^[j] x₁) = letOf (step^[j] x₂)) := by
    intro k
    induction k with
    | zero =>
      intro x₁ x₂ hx1 _ hx2 _
      dsimp only [Function.iterate_zero, id_eq]
      exact ⟨hx1, hx2, fun _ _ _ => rfl, fun _ hj => by omega⟩
    | succ k ih =>
      intro x₁ x₂ hx1 h12 hx2 hno
      rcases ih x₁ x₂ hx1 h12 hx2 (fun j hj => hno j (by omega)) with
        ⟨hlo_k, hhi_k, hdiff_k, hlet_k⟩
      have hle_k : step^[k] x₁ ≤ step^[k] x₂ := by
        have hd := hdiff_k x₂ h12 (le_refl _)
        linarith
      have hnoC_k : ∀ c ∈ C, ¬ (step^[k] x₁ ≤ c ∧ c ≤ step^[k] x₂) := by
        intro c hc ⟨hc1, hc2⟩
        let z := x₁ + (c - step^[k] x₁)
        have hz1 : x₁ ≤ z := by dsimp [z]; linarith
        have hz2 : z ≤ x₂ := by
          have hd := hdiff_k x₂ h12 (le_refl _)
          dsimp [z]; linarith
        have hstep_z : step^[k] z = c := by
          have hd := hdiff_k z hz1 hz2
          dsimp [z] at hd; linarith
        rw [← hstep_z] at hc
        exact hno k (Nat.lt_succ_self k) z hz1 hz2 hc
      rcases h_trans (step^[k] x₁) (step^[k] x₂) hlo_k hle_k hhi_k hnoC_k with
        ⟨hlet_last, hstep_diff, hlo_s, hhi_s⟩
      have h1_s : step (step^[k] x₁) = step^[k + 1] x₁ :=
        (Function.iterate_succ_apply' step k x₁).symm
      have h2_s : step (step^[k] x₂) = step^[k + 1] x₂ :=
        (Function.iterate_succ_apply' step k x₂).symm
      rw [h1_s] at hlo_s hstep_diff
      rw [h2_s] at hhi_s hstep_diff
      refine ⟨hlo_s, hhi_s, ?_, ?_⟩
      · intro z hz1 hz2
        have hd_z := hdiff_k z hz1 hz2
        have hle_z : step^[k] x₁ ≤ step^[k] z := by linarith
        have hhi_z : step^[k] z < J_hi := by
          have hd2 := hdiff_k x₂ h12 (le_refl _); linarith
        have hno_z : ∀ c ∈ C, ¬ (step^[k] x₁ ≤ c ∧ c ≤ step^[k] z) := by
          intro c hc ⟨hc1, hc2⟩
          exact hnoC_k c hc ⟨hc1, by have hd2 := hdiff_k x₂ h12 (le_refl _); linarith⟩
        have htr_z := (h_trans (step^[k] x₁) (step^[k] z) hlo_k hle_z hhi_z hno_z).2.1
        have hzs : step (step^[k] z) = step^[k + 1] z :=
          (Function.iterate_succ_apply' step k z).symm
        rw [h1_s, hzs] at htr_z
        linarith
      · intro j hj
        by_cases hjk : j < k
        · exact hlet_k j hjk
        · have hj_eq : j = k := by omega
          subst hj_eq; exact hlet_last
  have hitin_eq_on_interval : ∀ (m : Fin (M + 1)) (x y : ℝ),
      cutEndpt J_lo J_hi S hS m.castSucc < x → x < cutEndpt J_lo J_hi S hS m.succ →
      cutEndpt J_lo J_hi S hS m.castSucc < y → y < cutEndpt J_lo J_hi S hS m.succ →
      itin x = itin y := by
    intro m x y hx1 hx2 hy1 hy2
    rcases cutInterval_props hJ hS hinS m with ⟨_, hJlo, hJhi, hnotS⟩
    have hsub : ∀ x₁ x₂ : ℝ,
        cutEndpt J_lo J_hi S hS m.castSucc < x₁ → x₁ ≤ x₂ →
        x₂ < cutEndpt J_lo J_hi S hS m.succ → itin x₁ = itin x₂ := by
      intro x₁ x₂ ha1 h12 ha2
      have hno : ∀ j < n, ∀ z, x₁ ≤ z → z ≤ x₂ → step^[j] z ∉ C := by
        intro j hj z hz1 hz2 hmem
        have hzS : z ∈ S :=
          (hS_iff z (by linarith) (by linarith)).mpr ⟨j, hj, hmem⟩
        exact hnotS z (by linarith) (by linarith) hzS
      have hlet := (h_rigid n x₁ x₂ (by linarith) h12 (by linarith) hno).2.2.2
      apply List.ext_getElem
      · simp [itin]
      · intro k hk1 hk2
        simp only [itin, List.getElem_ofFn]
        exact hlet k (by simp [itin] at hk1; exact hk1)
    rcases le_total x y with hxy | hyx
    · exact hsub x y hx1 hxy hy2
    · exact (hsub y x hy1 hyx hx2).symm
  have hmid_in : ∀ m : Fin (M + 1),
      cutEndpt J_lo J_hi S hS m.castSucc < cutMidpt J_lo J_hi S hS m ∧
      cutMidpt J_lo J_hi S hS m < cutEndpt J_lo J_hi S hS m.succ := by
    intro m
    have hlt := (cutInterval_props hJ hS hinS m).1
    unfold cutMidpt
    exact ⟨by linarith, by linarith⟩
  have hinj : Function.Injective wordOf := by
    intro m₁ m₂ heq
    by_contra hne
    have hwlog : ∀ a b : Fin (M + 1), a < b → wordOf a ≠ wordOf b := by
      intro a b hab hword_eq
      change a.val < b.val at hab
      set x₁ := cutMidpt J_lo J_hi S hS a
      set x₂ := cutMidpt J_lo J_hi S hS b
      rcases cutInterval_props hJ hS hinS a with ⟨_, ha_lo, _, ha_notS⟩
      rcases cutInterval_props hJ hS hinS b with ⟨_, _, hb_hi, hb_notS⟩
      rcases hmid_in a with ⟨hx1_lo, hx1_hi⟩
      rcases hmid_in b with ⟨hx2_lo, hx2_hi⟩
      have hmono := cutEndpt_strictMono hJ hS hinS
      have hend_le : cutEndpt J_lo J_hi S hS a.succ ≤ cutEndpt J_lo J_hi S hS b.castSucc :=
        hmono.monotone (Fin.le_def.mpr (by simp; omega))
      set s_sep := cutEndpt J_lo J_hi S hS a.succ
      have hs_in_S : s_sep ∈ S := by
        have hb_lt := b.isLt
        have haM : a.val < M := by omega
        have hsc : a.succ = ⟨a.val + 1, by omega⟩ := rfl
        have hdef : s_sep = S.orderEmbOfFin hS ⟨a.val, haM⟩ := by
          dsimp [s_sep]
          rw [hsc, cutEndpt_succ_of_lt J_lo J_hi S hS haM]
        rw [hdef]
        exact Finset.orderEmbOfFin_mem S hS ⟨a.val, haM⟩
      have hx1_lt_s : x₁ < s_sep := hx1_hi
      have hs_lt_x2 : s_sep < x₂ := lt_of_le_of_lt hend_le hx2_lo
      have hx1_notS : x₁ ∉ S := ha_notS x₁ hx1_lo hx1_hi
      have hx2_notS : x₂ ∉ S := hb_notS x₂ hx2_lo hx2_hi
      have hex_k : ∃ k : ℕ, k < n ∧ ∃ z, x₁ < z ∧ z < x₂ ∧ step^[k] z ∈ C := by
        rcases (hS_iff s_sep (by linarith) (by linarith)).mp hs_in_S with ⟨k, hkn, hkC⟩
        exact ⟨k, hkn, s_sep, hx1_lt_s, hs_lt_x2, hkC⟩
      classical
      let k₀ := Nat.find hex_k
      rcases Nat.find_spec hex_k with ⟨hk0_lt, z₀, hz1, hz2, hzC⟩
      have hno_before : ∀ j < k₀, ∀ z, x₁ ≤ z → z ≤ x₂ → step^[j] z ∉ C := by
        intro j hj z hza hzb hmemC
        by_cases hzx1 : z = x₁
        · rw [hzx1] at hmemC
          exact hx1_notS ((hS_iff x₁ (by linarith) (by linarith)).mpr ⟨j, by omega, hmemC⟩)
        · by_cases hzx2 : z = x₂
          · rw [hzx2] at hmemC
            exact hx2_notS ((hS_iff x₂ (by linarith) (by linarith)).mpr ⟨j, by omega, hmemC⟩)
          · have hmin := Nat.find_min hex_k hj
            exact hmin ⟨by omega, z, lt_of_le_of_ne hza (Ne.symm hzx1),
              lt_of_le_of_ne hzb hzx2, hmemC⟩
      rcases h_rigid k₀ x₁ x₂ (by linarith) (by linarith) (by linarith) hno_before with
        ⟨hlo_k0, hhi_k0, hdiff_k0, _⟩
      have hy1_lt_c : step^[k₀] x₁ < step^[k₀] z₀ := by
        have hd := hdiff_k0 z₀ (le_of_lt hz1) (le_of_lt hz2)
        linarith
      have hc_lt_y2 : step^[k₀] z₀ < step^[k₀] x₂ := by
        have hd1 := hdiff_k0 z₀ (le_of_lt hz1) (le_of_lt hz2)
        have hd2 := hdiff_k0 x₂ (by linarith) (le_refl _)
        linarith
      have hy1_notC : step^[k₀] x₁ ∉ C := fun hm =>
        hx1_notS ((hS_iff x₁ (by linarith) (by linarith)).mpr ⟨k₀, hk0_lt, hm⟩)
      have hy2_notC : step^[k₀] x₂ ∉ C := fun hm =>
        hx2_notS ((hS_iff x₂ (by linarith) (by linarith)).mpr ⟨k₀, hk0_lt, hm⟩)
      have hlet_ne : letOf (step^[k₀] x₁) ≠ letOf (step^[k₀] x₂) :=
        h_sep (step^[k₀] x₁) (step^[k₀] z₀) (step^[k₀] x₂)
          hlo_k0 hy1_lt_c hc_lt_y2 hhi_k0 hzC hy1_notC hy2_notC
      have hlen_a : k₀ < (wordOf a).length := by simp [wordOf, itin]; exact hk0_lt
      have hlen_b : k₀ < (wordOf b).length := by simp [wordOf, itin]; exact hk0_lt
      have hget_eq : (wordOf a)[k₀]'hlen_a = (wordOf b)[k₀]'hlen_b := by simp [hword_eq]
      simp only [wordOf, itin, List.getElem_ofFn] at hget_eq
      exact hlet_ne hget_eq
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hwlog m₁ m₂ hlt heq
    · exact hwlog m₂ m₁ hgt heq.symm
  refine ⟨hinj, ?_⟩
  intro W orb horb_in horb_notC horb_step hW_let horb_dense
  have horb_iter : ∀ p k : ℕ, step^[k] (orb p) = orb (p + k) := by
    intro p k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, horb_step, Nat.add_assoc]
  ext w
  simp only [FactorsOfLen, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨hlen, p, hp_occ⟩
    have hw_eq : w = itin (orb p) := by
      apply List.ext_getElem
      · simp [itin, hlen]
      · intro k hk1 hk2
        simp only [itin, List.getElem_ofFn, horb_iter]
        rw [← hp_occ k hk1, hW_let]
    have horb_notS : orb p ∉ S := by
      intro hmemS
      rcases (hS_iff (orb p) (horb_in p).1 (horb_in p).2).mp hmemS with ⟨k, _, hkC⟩
      rw [horb_iter] at hkC
      exact horb_notC (p + k) hkC
    rcases exists_cutInterval_of_not_mem hS (horb_in p) horb_notS with ⟨m, hm1, hm2⟩
    refine ⟨m, ?_⟩
    rw [hw_eq]
    exact hitin_eq_on_interval m (cutMidpt J_lo J_hi S hS m) (orb p)
      (hmid_in m).1 (hmid_in m).2 hm1 hm2
  · rintro ⟨m, rfl⟩
    refine ⟨by simp [wordOf, itin], ?_⟩
    rcases cutInterval_props hJ hS hinS m with ⟨hlt, hlo, hhi, _⟩
    rcases horb_dense _ _ hlo hlt hhi with ⟨p, hp1, hp2⟩
    have hit_eq : wordOf m = itin (orb p) :=
      hitin_eq_on_interval m (cutMidpt J_lo J_hi S hS m) (orb p)
        (hmid_in m).1 (hmid_in m).2 hp1 hp2
    refine ⟨p, fun k hk => ?_⟩
    have hk_lt : k < n := by simp [wordOf, itin] at hk; exact hk
    have hget := congrArg (fun l : List α => l[k]?) hit_eq
    have h1 : (wordOf m)[k]? = some (wordOf m)[k] := List.getElem?_eq_getElem hk
    have h2 : (itin (orb p))[k]? = some (letOf (orb (p + k))) := by
      simp [itin, hk_lt, horb_iter]
    rw [h1, h2, Option.some.injEq] at hget
    rw [hW_let, hget]

/-! ## Section 3: Fibonacci Word `fibWord`, Morphism `gFib`, and Rotation `(J', rotR)` -/

/-- Classical Fibonacci morphism `fibMorph : Bool → List Bool` (`0 ↦ 01, 1 ↦ 0`). -/
def fibMorph : Bool → List Bool
  | false => [false, true]
  | true => [false]

theorem fibMorph_nonempty : ∀ b : Bool, fibMorph b ≠ [] := by
  intro b; cases b <;> decide

theorem fibMorph_prolongable : ∃ t : List Bool, fibMorph false = false :: t ∧ t ≠ [] :=
  ⟨[true], rfl, by decide⟩

/-- Classical infinite Fibonacci Sturmian word `fibWord = fibMorph^ω(false) : ℕ → Bool`. -/
def fibWord : ℕ → Bool :=
  fixedPoint fibMorph false fibMorph_nonempty fibMorph_prolongable

@[simp] theorem fibWord_zero : fibWord 0 = false := rfl

/-- Badkobeh & Ochem's morphism `gFib : Fin 5 → List Bool`:
`0 ↦ 01`, `1 ↦ 0`, `2 ↦ 1`, `3 ↦ 0`, `4 ↦ 0`. -/
def gFib : Fin 5 → List Bool
  | 0 => [false, true]
  | 1 => [false]
  | 2 => [true]
  | 3 => [false]
  | 4 => [false]

theorem gFib_nonempty : ∀ a : Fin 5, gFib a ≠ [] := by
  intro a; fin_cases a <;> decide

/-- The infinite binary morphic projection `gFibB5 = gFib(b_5) : ℕ → Bool`. -/
def gFibB5 : ℕ → Bool :=
  applyMorphInf gFib gFib_nonempty b5

/-- Two-interval exchange / irrational rotation `rotR` on `J' = (-φ^3 / 2, φ^3 / 2)`
with cut point `-1 / 2`. -/
noncomputable def rotR (x : ℝ) : ℝ :=
  if x < -1 / 2 then x + φ ^ 2 else x - φ

/-- Binary coding letter of `rotR`: `true` (`1`) left of `-1 / 2`, `false` (`0`) right of `-1 / 2`. -/
noncomputable def rotLetter (x : ℝ) : Bool :=
  decide (x < -1 / 2)

/-- Cumulative length `gFibStart p = |gFib(b5[0..p))|`. -/
def gFibStart (p : ℕ) : ℕ :=
  (applyMorph gFib (prefixOf b5 p)).length

@[simp] theorem gFibStart_zero : gFibStart 0 = 0 := rfl

theorem gFibStart_succ (p : ℕ) :
    gFibStart (p + 1) = gFibStart p + (gFib (b5 p)).length := by
  simp [gFibStart, prefixOf_succ, applyMorph_append]

/-- At `gFibStart p`, the `rotR`-orbit of `0` lands at `x_p = lambda' (prefixOf b5 p)`. -/
theorem rotR_iter_zero_gFibStart (p : ℕ) :
    rotR^[gFibStart p] 0 = lambda' (prefixOf b5 p) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [gFibStart_succ, Nat.add_comm, Function.iterate_add_apply, ih,
      prefixOf_succ, lambdaPrime_append, lambdaPrime_cons, lambdaPrime_nil, add_zero]
    set xp := lambda' (prefixOf b5 p)
    have hcod := b5_codes_interval_translation p
    rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
    have hsq : φ ^ 2 = φ + 1 := phi_sq
    have hb_cases : b5 p = 0 ∨ b5 p = 1 ∨ b5 p = 2 ∨ b5 p = 3 ∨ b5 p = 4 := fin5_cases (b5 p)
    rcases hb_cases with hb | hb | hb | hb | hb <;> rw [hb]
    · have hxp : -1 / 2 < xp ∧ xp < (φ - 1) / 2 := (hcod.2.2.1).mp hb
      change rotR (rotR xp) = xp + l' 0
      have hstep1 : rotR xp = xp - φ := by
        unfold rotR
        rw [ite_false_of (by linarith)]
      have hstep2 : xp - φ < -1 / 2 := by linarith [one_lt_phi]
      rw [hstep1]
      unfold rotR
      rw [ite_true_of hstep2]
      simp only [l']; linarith
    · have hxp : φ / 2 < xp ∧ xp < φ := (hcod.2.2.2.2.1).mp hb
      change rotR xp = xp + l' 1
      unfold rotR
      rw [ite_false_of (by linarith)]
      simp only [l']; ring
    · have hxp : -φ ^ 2 / 2 < xp ∧ xp < -1 / 2 := (hcod.2.1).mp hb
      change rotR xp = xp + l' 2
      unfold rotR
      rw [ite_true_of hxp.2]
      simp only [l']; linarith
    · have hxp : φ < xp ∧ xp < φ ^ 3 / 2 := (hcod.2.2.2.2.2).mp hb
      change rotR xp = xp + l' 3
      unfold rotR
      rw [ite_false_of (by linarith)]
      simp only [l']; ring
    · have hxp : (φ - 1) / 2 < xp ∧ xp < φ / 2 := (hcod.2.2.2.1).mp hb
      change rotR xp = xp + l' 4
      unfold rotR
      rw [ite_false_of (by linarith)]
      simp only [l']; ring

/-- Exact dynamical correspondence between `gFibB5 = gFib(b_5)`, `rotR^[k] 0`, and `x_p`. -/
theorem gFibB5_orbit_props (k : ℕ) :
    gFibB5 k = rotLetter (rotR^[k] 0) ∧
    -φ ^ 3 / 2 < rotR^[k] 0 ∧
    rotR^[k] 0 < φ ^ 3 / 2 ∧
    rotR^[k] 0 ≠ -1 / 2 ∧
    (-φ ^ 2 / 2 < rotR^[k] 0 → ∃ p : ℕ, rotR^[k] 0 = lambda' (prefixOf b5 p)) := by
  have hex : ∃ p : ℕ, gFibStart p ≤ k ∧ k < gFibStart (p + 1) := by
    induction k with
    | zero =>
      refine ⟨0, by simp, ?_⟩
      simp [gFibStart_succ, b5_zero, gFib]
    | succ k ih =>
      rcases ih with ⟨p, hle, hlt⟩
      by_cases hnext : k + 1 < gFibStart (p + 1)
      · exact ⟨p, by omega, hnext⟩
      · have heq : k + 1 = gFibStart (p + 1) := by omega
        refine ⟨p + 1, by omega, ?_⟩
        rw [heq]
        rw [gFibStart_succ (p + 1)]
        have hpos : 1 ≤ (gFib (b5 (p + 1))).length :=
          List.length_pos_of_ne_nil (gFib_nonempty _)
        omega
  rcases hex with ⟨p, hle, hlt⟩
  let o := k - gFibStart p
  have ho : o < (gFib (b5 p)).length := by
    have hs := gFibStart_succ p; omega
  have hk_eq : k = gFibStart p + o := by omega
  have hg_get : gFibB5 k = (gFib (b5 p))[o] := by
    unfold gFibB5
    have hlt' : k < (applyMorph gFib (prefixOf b5 (p + 1))).length := hlt
    rw [applyMorphInf_eq_getElem gFib gFib_nonempty b5 (p + 1) k hlt']
    have hlist : applyMorph gFib (prefixOf b5 (p + 1)) =
        applyMorph gFib (prefixOf b5 p) ++ gFib (b5 p) := by
      rw [prefixOf_succ, applyMorph_append, applyMorph_singleton]
    have hq := congrArg (fun l : List Bool => l[k]?) hlist
    rw [List.getElem?_eq_getElem hlt',
      List.getElem?_append_right (by change gFibStart p ≤ k; exact hle),
      List.getElem?_eq_getElem (by change k - gFibStart p < _; exact ho),
      Option.some.injEq] at hq
    exact hq
  have hrot_k : rotR^[k] 0 = rotR^[o] (lambda' (prefixOf b5 p)) := by
    rw [hk_eq, Nat.add_comm, Function.iterate_add_apply, rotR_iter_zero_gFibStart]
  rw [hg_get, hrot_k]
  set xp := lambda' (prefixOf b5 p)
  have hcod := b5_codes_interval_translation p
  rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have hphi1 : 1 < φ := one_lt_phi
  have hb_cases : b5 p = 0 ∨ b5 p = 1 ∨ b5 p = 2 ∨ b5 p = 3 ∨ b5 p = 4 := fin5_cases (b5 p)
  rcases hb_cases with hb | hb | hb | hb | hb
  · have hxp : -1 / 2 < xp ∧ xp < (φ - 1) / 2 := (hcod.2.2.1).mp hb
    have ho2 : o = 0 ∨ o = 1 := by
      rw [hb] at ho; change o < ([false, true] : List Bool).length at ho; simp at ho; omega
    rcases ho2 with ho0 | ho1
    · simp only [hb, ho0, Function.iterate_zero_apply, gFib, List.getElem_cons_zero, rotLetter]
      refine ⟨?_, by nlinarith, by nlinarith, by linarith, fun _ => ⟨p, rfl⟩⟩
      symm; rw [decide_eq_false_iff_not]; linarith
    · simp only [hb, ho1, Function.iterate_one, gFib, List.getElem_cons_succ, List.getElem_cons_zero,
        rotLetter]
      have hstep : rotR xp = xp - φ := by
        unfold rotR
        rw [ite_false_of (by linarith)]
      rw [hstep]
      refine ⟨?_, by nlinarith, by nlinarith, by nlinarith, fun hgt => absurd hgt (by nlinarith)⟩
      symm; rw [decide_eq_true_eq]; nlinarith
  · have hxp : φ / 2 < xp ∧ xp < φ := (hcod.2.2.2.2.1).mp hb
    have ho1 : o = 0 := by
      rw [hb] at ho; change o < ([false] : List Bool).length at ho; simp at ho; omega
    simp only [hb, ho1, Function.iterate_zero_apply, gFib, List.getElem_cons_zero, rotLetter]
    refine ⟨?_, by nlinarith, by nlinarith, by linarith, fun _ => ⟨p, rfl⟩⟩
    symm; rw [decide_eq_false_iff_not]; linarith
  · have hxp : -φ ^ 2 / 2 < xp ∧ xp < -1 / 2 := (hcod.2.1).mp hb
    have ho1 : o = 0 := by
      rw [hb] at ho; change o < ([true] : List Bool).length at ho; simp at ho; omega
    simp only [hb, ho1, Function.iterate_zero_apply, gFib, List.getElem_cons_zero, rotLetter]
    refine ⟨?_, by nlinarith, by nlinarith, by linarith, fun _ => ⟨p, rfl⟩⟩
    symm; rw [decide_eq_true_eq]; exact hxp.2
  · have hxp : φ < xp ∧ xp < φ ^ 3 / 2 := (hcod.2.2.2.2.2).mp hb
    have ho1 : o = 0 := by
      rw [hb] at ho; change o < ([false] : List Bool).length at ho; simp at ho; omega
    simp only [hb, ho1, Function.iterate_zero_apply, gFib, List.getElem_cons_zero, rotLetter]
    refine ⟨?_, by nlinarith, by nlinarith, by linarith, fun _ => ⟨p, rfl⟩⟩
    symm; rw [decide_eq_false_iff_not]; linarith
  · have hxp : (φ - 1) / 2 < xp ∧ xp < φ / 2 := (hcod.2.2.2.1).mp hb
    have ho1 : o = 0 := by
      rw [hb] at ho; change o < ([false] : List Bool).length at ho; simp at ho; omega
    simp only [hb, ho1, Function.iterate_zero_apply, gFib, List.getElem_cons_zero, rotLetter]
    refine ⟨?_, by nlinarith, by nlinarith, by linarith, fun _ => ⟨p, rfl⟩⟩
    symm; rw [decide_eq_false_iff_not]; linarith

/-- Conjugate letter weights for `fibMorph`: `false ↦ -φ`, `true ↦ φ^2`. -/
noncomputable def lFib : Bool → ℝ
  | false => -φ
  | true => φ ^ 2

noncomputable def lambdaFib (w : List Bool) : ℝ :=
  (w.map lFib).sum

@[simp] theorem lambdaFib_nil : lambdaFib [] = 0 := rfl

@[simp] theorem lambdaFib_cons (b : Bool) (w : List Bool) :
    lambdaFib (b :: w) = lFib b + lambdaFib w := by simp [lambdaFib]

theorem lambdaFib_append (u v : List Bool) :
    lambdaFib (u ++ v) = lambdaFib u + lambdaFib v := by
  simp [lambdaFib, List.map_append, List.sum_append]

theorem lambdaFib_applyMorph (w : List Bool) :
    lambdaFib (applyMorph fibMorph w) = (-1 / φ) * lambdaFib w := by
  induction w with
  | nil => simp
  | cons b t ih =>
    rw [applyMorph_cons, lambdaFib_append, lambdaFib_cons, ih]
    have hletter : lambdaFib (fibMorph b) = (-1 / φ) * lFib b := by
      rw [neg_inv_phi]
      cases b <;> simp [fibMorph, lambdaFib, lFib] <;> nlinarith [phi_sq]
    rw [hletter]; ring

/-- Block-boundary sequence for `fibWord = fibMorph(fibWord)`. -/
def fibBlockStart (p : ℕ) : ℕ :=
  (applyMorph fibMorph (prefixOf fibWord p)).length

@[simp] theorem fibBlockStart_zero : fibBlockStart 0 = 0 := rfl

theorem fibBlockStart_succ (p : ℕ) :
    fibBlockStart (p + 1) = fibBlockStart p + (fibMorph (fibWord p)).length := by
  simp [fibBlockStart, prefixOf_succ, applyMorph_append]

theorem fibBlockStart_ge_succ_of_pos {p : ℕ} (hp : 1 ≤ p) : p + 1 ≤ fibBlockStart p := by
  induction p with
  | zero => omega
  | succ p ih =>
    by_cases hp0 : p = 0
    · subst hp0
      rw [fibBlockStart_succ, fibBlockStart_zero, fibWord_zero]
      decide
    · have h1 := ih (by omega)
      have h2 : 1 ≤ (fibMorph (fibWord p)).length :=
        List.length_pos_of_ne_nil (fibMorph_nonempty _)
      rw [fibBlockStart_succ]; omega

theorem exists_fib_decomp (q : ℕ) :
    ∃ p o : ℕ, ∃ ho : o < (fibMorph (fibWord p)).length,
      q = fibBlockStart p + o ∧
      fibWord q = (fibMorph (fibWord p))[o]'ho ∧
      prefixOf fibWord q = applyMorph fibMorph (prefixOf fibWord p) ++ (fibMorph (fibWord p)).take o ∧
      (1 ≤ q → p < q) := by
  have hpref_block : ∀ p, prefixOf fibWord (fibBlockStart p) =
      applyMorph fibMorph (prefixOf fibWord p) := by
    intro p
    have h := fixedPoint_applyMorph_prefix_isPrefix
      fibMorph false fibMorph_nonempty fibMorph_prolongable 1 p
    have heq : (fun b => iterMorph fibMorph 1 [b]) = fibMorph := by
      funext b; simp [iterMorph]
    rw [heq] at h
    exact h.symm
  have hex : ∃ p : ℕ, fibBlockStart p ≤ q ∧ q < fibBlockStart (p + 1) := by
    induction q with
    | zero =>
      refine ⟨0, by simp, ?_⟩
      rw [fibBlockStart_succ, fibBlockStart_zero, fibWord_zero]
      decide
    | succ q ih =>
      rcases ih with ⟨p, hle, hlt⟩
      by_cases hnext : q + 1 < fibBlockStart (p + 1)
      · exact ⟨p, by omega, hnext⟩
      · have heq : q + 1 = fibBlockStart (p + 1) := by omega
        refine ⟨p + 1, by omega, ?_⟩
        rw [heq]
        rw [fibBlockStart_succ (p + 1)]
        have hpos : 1 ≤ (fibMorph (fibWord (p + 1))).length :=
          List.length_pos_of_ne_nil (fibMorph_nonempty _)
        omega
  rcases hex with ⟨p, hle, hlt⟩
  let o := q - fibBlockStart p
  have ho : o < (fibMorph (fibWord p)).length := by
    have hs := fibBlockStart_succ p; omega
  have hq_eq : q = fibBlockStart p + o := by omega
  have hbig : prefixOf fibWord (fibBlockStart (p + 1)) =
      applyMorph fibMorph (prefixOf fibWord p) ++ fibMorph (fibWord p) := by
    rw [hpref_block (p + 1), prefixOf_succ, applyMorph_append, applyMorph_singleton]
  have hfw_q : fibWord q = (fibMorph (fibWord p))[o]'ho := by
    have hget : (prefixOf fibWord (fibBlockStart (p + 1)))[q]'(by simp [hlt]) = fibWord q :=
      prefixOf_getElem fibWord (fibBlockStart (p + 1)) q (by simp [hlt])
    rw [← hget]
    simp only [hbig]
    rw [List.getElem_append_right (by change fibBlockStart p ≤ q; omega)]
    congr 1
  have hpref_q : prefixOf fibWord q =
      applyMorph fibMorph (prefixOf fibWord p) ++ (fibMorph (fibWord p)).take o := by
    have h1 : prefixOf fibWord q = (prefixOf fibWord (fibBlockStart (p + 1))).take q := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 hi2; simp
    rw [h1, hbig, hq_eq]
    change List.take ((applyMorph fibMorph (prefixOf fibWord p)).length + o)
      (applyMorph fibMorph (prefixOf fibWord p) ++ fibMorph (fibWord p)) = _
    rw [List.take_append]; simp
  have hp_lt_q : 1 ≤ q → p < q := by
    intro hq1
    by_cases hp0 : p = 0
    · subst hp0; omega
    · have hge := fibBlockStart_ge_succ_of_pos (by omega : 1 ≤ p); omega
  exact ⟨p, o, ho, hq_eq, hfw_q, hpref_q, hp_lt_q⟩

/-- Interval coding of `fibWord` in `(-φ^2, φ)`:
`fibWord k = false → y_k ∈ (-1, φ)` and `fibWord k = true → y_k ∈ (-φ^2, -1)`. -/
theorem fibWord_interval_coding (k : ℕ) :
    if fibWord k = true then
      -φ ^ 2 < lambdaFib (prefixOf fibWord k) ∧ lambdaFib (prefixOf fibWord k) < -1
    else
      -1 < lambdaFib (prefixOf fibWord k) ∧ lambdaFib (prefixOf fibWord k) < φ := by
  induction k using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0
      simp only [fibWord_zero, prefixOf_zero, lambdaFib_nil, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by norm_num, phi_pos⟩
    · rcases exists_fib_decomp q with ⟨p, o, ho, _, hfw_q, hpref_q, hp_lt_q⟩
      have ihp := ih p (hp_lt_q (by omega))
      rw [hfw_q, hpref_q, lambdaFib_append, lambdaFib_applyMorph, neg_inv_phi]
      have hsq : φ ^ 2 = φ + 1 := phi_sq
      have h1 : 1 < φ := one_lt_phi
      have h2 : φ < 2 := phi_lt_two
      by_cases hb : fibWord p = true
      · simp only [hb, ↓reduceIte] at ihp
        have ho1 : o = 0 := by
          rw [hb] at ho; change o < ([false] : List Bool).length at ho; simp at ho; omega
        subst ho1
        simp only [hb, fibMorph, List.getElem_cons_zero, Bool.false_eq_true, ↓reduceIte,
          List.take, lambdaFib_nil, add_zero]
        exact ⟨by nlinarith, by nlinarith⟩
      · have hbf : fibWord p = false := Bool.eq_false_iff.mpr hb
        simp only [hbf, Bool.false_eq_true, ↓reduceIte] at ihp
        have ho2 : o = 0 ∨ o = 1 := by
          rw [hbf] at ho; change o < ([false, true] : List Bool).length at ho; simp at ho; omega
        rcases ho2 with rfl | rfl
        · simp only [hbf, fibMorph, List.getElem_cons_zero, Bool.false_eq_true, ↓reduceIte,
            List.take, lambdaFib_nil, add_zero]
          exact ⟨by nlinarith, by nlinarith⟩
        · simp only [hbf, fibMorph, List.getElem_cons_succ, List.getElem_cons_zero, ↓reduceIte,
            List.take, lambdaFib_cons, lambdaFib_nil, lFib, add_zero]
          exact ⟨by nlinarith, by nlinarith⟩

/-- Exact dynamical correspondence between `fibWord` and the `rotR`-orbit of `1 / 2`. -/
theorem fibWord_orbit_props (k : ℕ) :
    rotR^[k] (1 / 2) = lambdaFib (prefixOf fibWord k) + 1 / 2 ∧
    fibWord k = rotLetter (rotR^[k] (1 / 2)) ∧
    -φ ^ 3 / 2 < rotR^[k] (1 / 2) ∧
    rotR^[k] (1 / 2) < φ ^ 3 / 2 ∧
    rotR^[k] (1 / 2) ≠ -1 / 2 := by
  have horb : ∀ n : ℕ, rotR^[n] (1 / 2) = lambdaFib (prefixOf fibWord n) + 1 / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        prefixOf_succ, lambdaFib_append, lambdaFib_cons, lambdaFib_nil, add_zero]
      have hcod := fibWord_interval_coding n
      cases hb : fibWord n
      · rw [hb] at hcod
        simp only [Bool.false_eq_true, ↓reduceIte] at hcod
        unfold rotR
        rw [ite_false_of (by linarith [hcod.1])]
        simp [lFib]; ring
      · rw [hb] at hcod
        simp only [↓reduceIte] at hcod
        unfold rotR
        rw [ite_true_of (by linarith [hcod.2])]
        simp [lFib]; ring
  have hk := horb k
  rw [hk]
  have hcod := fibWord_interval_coding k
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h1 : 1 < φ := one_lt_phi
  cases hb : fibWord k
  · rw [hb] at hcod
    simp only [Bool.false_eq_true, ↓reduceIte] at hcod
    refine ⟨rfl, ?_, by nlinarith, by nlinarith, by linarith⟩
    unfold rotLetter
    symm; rw [decide_eq_false_iff_not]; linarith
  · rw [hb] at hcod
    simp only [↓reduceIte] at hcod
    refine ⟨rfl, ?_, by nlinarith, by nlinarith, by linarith⟩
    unfold rotLetter
    symm; rw [decide_eq_true_eq]; linarith

/-! ## Section 4: Unit-Circle Conjugacy & Elementary 1D Kronecker Forward-Orbit Density -/

/-- Rescaling `[-φ^3 / 2, φ^3 / 2) → [0, 1)`. -/
noncomputable def toUnit (x : ℝ) : ℝ :=
  (x + φ ^ 3 / 2) / φ ^ 3

/-- Inverse rescaling `[0, 1) → [-φ^3 / 2, φ^3 / 2)`. -/
noncomputable def fromUnit (u : ℝ) : ℝ :=
  -φ ^ 3 / 2 + φ ^ 3 * u

theorem phi_cube_pos : 0 < φ ^ 3 := by positivity [phi_pos]

theorem fromUnit_toUnit (x : ℝ) : fromUnit (toUnit x) = x := by
  unfold fromUnit toUnit
  have hne : φ ^ 3 ≠ 0 := ne_of_gt phi_cube_pos
  rw [mul_div_cancel₀ _ hne]; ring

theorem toUnit_fromUnit (u : ℝ) : toUnit (fromUnit u) = u := by
  unfold toUnit fromUnit
  have hne : φ ^ 3 ≠ 0 := ne_of_gt phi_cube_pos
  have : -φ ^ 3 / 2 + φ ^ 3 * u + φ ^ 3 / 2 = u * φ ^ 3 := by ring
  rw [this, mul_div_cancel_right₀ _ hne]

theorem fract_fract_add (a b : ℝ) : Int.fract (Int.fract a + b) = Int.fract (a + b) := by
  rw [Int.fract_eq_iff]
  refine ⟨Int.fract_nonneg _, Int.fract_lt_one _, ⟨⌊a + b⌋ - ⌊a⌋, ?_⟩⟩
  push_cast
  linarith [Int.floor_add_fract a, Int.floor_add_fract (a + b)]

theorem fract_add_fract (a b : ℝ) :
    Int.fract (Int.fract a + Int.fract b) = Int.fract (a + b) := by
  rw [fract_fract_add, add_comm a, fract_fract_add, add_comm]

theorem toUnit_rotR {x : ℝ} (hx1 : -φ ^ 3 / 2 ≤ x) (hx2 : x < φ ^ 3 / 2) :
    toUnit (rotR x) = Int.fract (toUnit x + 1 / φ) ∧
    -φ ^ 3 / 2 ≤ rotR x ∧ rotR x < φ ^ 3 / 2 := by
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h1 : 1 < φ := one_lt_phi
  have hcp : 0 < φ ^ 3 := phi_cube_pos
  have hp : 0 < φ := phi_pos
  unfold rotR
  split_ifs with hlt
  · have hlo : -φ ^ 3 / 2 ≤ x + φ ^ 2 := by linarith
    have hhi : x + φ ^ 2 < φ ^ 3 / 2 := by linarith
    refine ⟨?_, hlo, hhi⟩
    symm
    rw [Int.fract_eq_iff]
    have hu0 : 0 ≤ toUnit (x + φ ^ 2) := by
      unfold toUnit; exact div_nonneg (by linarith) (le_of_lt hcp)
    have hu1 : toUnit (x + φ ^ 2) < 1 := by
      unfold toUnit; rw [div_lt_one hcp]; linarith
    refine ⟨hu0, hu1, ⟨0, ?_⟩⟩
    unfold toUnit
    push_cast
    field_simp [ne_of_gt hcp, ne_of_gt hp]
    nlinarith
  · have hge : -1 / 2 ≤ x := le_of_not_gt hlt
    have hlo : -φ ^ 3 / 2 ≤ x - φ := by linarith
    have hhi : x - φ < φ ^ 3 / 2 := by linarith
    refine ⟨?_, hlo, hhi⟩
    symm
    rw [Int.fract_eq_iff]
    have hu0 : 0 ≤ toUnit (x - φ) := by
      unfold toUnit; exact div_nonneg (by linarith) (le_of_lt hcp)
    have hu1 : toUnit (x - φ) < 1 := by
      unfold toUnit; rw [div_lt_one hcp]; linarith
    refine ⟨hu0, hu1, ⟨1, ?_⟩⟩
    unfold toUnit
    push_cast
    field_simp [ne_of_gt hcp, ne_of_gt hp]
    nlinarith

theorem toUnit_rotR_iter (k : ℕ) {x : ℝ} (hx1 : -φ ^ 3 / 2 ≤ x) (hx2 : x < φ ^ 3 / 2) :
    toUnit (rotR^[k] x) = Int.fract (toUnit x + (k : ℝ) * (1 / φ)) ∧
    -φ ^ 3 / 2 ≤ rotR^[k] x ∧ rotR^[k] x < φ ^ 3 / 2 := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, add_zero]
    refine ⟨?_, hx1, hx2⟩
    symm
    rw [Int.fract_eq_iff]
    have hcp : 0 < φ ^ 3 := phi_cube_pos
    exact ⟨div_nonneg (by linarith) (le_of_lt hcp),
      (div_lt_one hcp).mpr (by linarith), ⟨0, by simp⟩⟩
  | succ k ih =>
    rcases ih with ⟨heq, hlo, hhi⟩
    rw [Function.iterate_succ_apply']
    rcases toUnit_rotR hlo hhi with ⟨hstep, hlo', hhi'⟩
    refine ⟨?_, hlo', hhi'⟩
    rw [hstep, heq, fract_fract_add]
    congr 1
    push_cast; ring

/-- Non-rationality of positive integer multiples of `1 / φ = φ - 1`. -/
theorem fract_nat_mul_inv_phi_ne_zero {d : ℕ} (hd : 1 ≤ d) :
    Int.fract ((d : ℝ) * (1 / φ)) ≠ 0 := by
  intro h0
  let m : ℤ := ⌊(d : ℝ) * (1 / φ)⌋
  have heq : (d : ℝ) * (1 / φ) = (m : ℝ) := by
    have hf := Int.floor_add_fract ((d : ℝ) * (1 / φ))
    rw [h0, add_zero] at hf
    exact hf.symm
  rw [inv_phi] at heq
  let qa : ℚ := -(d : ℚ) - (m : ℚ)
  let qb : ℚ := (d : ℚ)
  have hlin : (qa : ℝ) + (qb : ℝ) * φ = 0 := by
    dsimp [qa, qb]; push_cast; linarith
  rcases rat_add_rat_mul_phi_eq_zero hlin with ⟨_, hd0⟩
  dsimp [qb] at hd0
  have hd_nat : d = 0 := by exact_mod_cast hd0
  omega

/-- Elementary 1D Kronecker Forward-Orbit Density:
For EVERY starting point `u₀ : ℝ` and EVERY open interval `(a, b) ⊆ [0, 1]` (`a < b`),
there exists `k : ℕ` such that `Int.fract (u₀ + k * (1 / φ)) ∈ (a, b)`. -/
theorem kronecker_inv_phi_dense (u₀ a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ k : ℕ, a < Int.fract (u₀ + (k : ℝ) * (1 / φ)) ∧
      Int.fract (u₀ + (k : ℝ) * (1 / φ)) < b := by
  set ε : ℝ := (b - a) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  set a' : ℝ := a + ε
  set b' : ℝ := b - ε
  have ha' : ε ≤ a' := by dsimp [a']; linarith
  have hb'_gap : a' + ε < b' := by dsimp [a', b', ε]; linarith
  have hb'_le : b' ≤ 1 - ε := by dsimp [b']; linarith
  let N : ℕ := ⌊1 / ε⌋₊ + 2
  have hN_pos : (0 : ℝ) < (N : ℝ) := by dsimp [N]; positivity
  have hN_inv : 1 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hN_pos]
    have hgt : 1 / ε < (N : ℝ) := by
      dsimp [N]
      have := Nat.lt_floor_add_one (1 / ε)
      push_cast
      linarith
    have := (div_lt_iff₀ hε).mp hgt
    linarith
  let f (m : ℕ) : ℝ := Int.fract ((m : ℝ) * (1 / φ))
  let bin (i : Fin (N + 1)) : Fin N :=
    ⟨⌊(N : ℝ) * f i.val⌋₊,
      (Nat.floor_lt (mul_nonneg (le_of_lt hN_pos) (Int.fract_nonneg _))).mpr
        (by nlinarith [Int.fract_lt_one ((i.val : ℝ) * (1 / φ))])⟩
  have hcard : Fintype.card (Fin N) < Fintype.card (Fin (N + 1)) := by simp
  rcases Fintype.exists_ne_map_eq_of_card_lt bin hcard with ⟨i₁, i₂, hne, hbin_eq⟩
  have hij_ord : ∃ i j : Fin (N + 1), i.val < j.val ∧ bin i = bin j := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact ⟨i₁, i₂, hlt, hbin_eq⟩
    · exact ⟨i₂, i₁, hgt, hbin_eq.symm⟩
  rcases hij_ord with ⟨i, j, hij, hbij⟩
  let d : ℕ := j.val - i.val
  have hd_pos : 1 ≤ d := by omega
  set s : ℝ := Int.fract ((d : ℝ) * (1 / φ))
  have hs_pos : 0 < s := lt_of_le_of_ne (Int.fract_nonneg _)
    (Ne.symm (fract_nat_mul_inv_phi_ne_zero hd_pos))
  have hs_lt1 : s < 1 := Int.fract_lt_one _
  have hfloor_eq : ⌊(N : ℝ) * f i.val⌋₊ = ⌊(N : ℝ) * f j.val⌋₊ :=
    congrArg Fin.val hbij
  have hdiff_lt : |f j.val - f i.val| < ε := by
    have hi1 := Nat.floor_le (mul_nonneg (le_of_lt hN_pos) (Int.fract_nonneg ((i.val : ℝ) * (1 / φ))))
    have hi2 := Nat.lt_floor_add_one ((N : ℝ) * f i.val)
    have hj1 := Nat.floor_le (mul_nonneg (le_of_lt hN_pos) (Int.fract_nonneg ((j.val : ℝ) * (1 / φ))))
    have hj2 := Nat.lt_floor_add_one ((N : ℝ) * f j.val)
    rw [hfloor_eq] at hi1 hi2
    have habsN : |(N : ℝ) * (f j.val - f i.val)| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have habs1 : |f j.val - f i.val| < 1 / (N : ℝ) := by
      rw [lt_div_iff₀ hN_pos]
      have : |f j.val - f i.val| * (N : ℝ) = |(N : ℝ) * (f j.val - f i.val)| := by
        rw [abs_mul, abs_of_pos hN_pos, mul_comm]
      linarith
    exact lt_trans habs1 hN_inv
  have hfj_eq : f j.val = Int.fract (f i.val + s) := by
    dsimp [f, s]
    rw [fract_add_fract]
    congr 1
    have hj_add : (j.val : ℝ) = (i.val : ℝ) + (d : ℝ) := by
      have : j.val = i.val + d := by omega
      exact_mod_cast this
    rw [hj_add]; ring
  let u (m : ℕ) : ℝ := Int.fract (u₀ + ((m * d : ℕ) : ℝ) * (1 / φ))
  have hu_step : ∀ m : ℕ, u (m + 1) = Int.fract (u m + s) := by
    intro m
    dsimp [u, s]
    rw [fract_add_fract]
    congr 1
    push_cast; ring
  by_cases hwrap : f i.val + s < 1
  · have hfj_val : f j.val = f i.val + s := by
      rw [hfj_eq, Int.fract_eq_iff]
      exact ⟨by linarith [Int.fract_nonneg ((i.val : ℝ) * (1 / φ))], hwrap, ⟨0, by simp⟩⟩
    have hs_lt_eps : s < ε := by
      have := (abs_lt.mp hdiff_lt).2
      linarith
    have hex_m0 : ∃ m₀ : ℕ, u m₀ < ε := by
      by_contra hno
      have hge_all : ∀ m, ε ≤ u m := fun m => le_of_not_gt (fun h => hno ⟨m, h⟩)
      have hstep_lin : ∀ m, u (m + 1) = u m + s := by
        intro m
        by_cases hlt1 : u m + s < 1
        · rw [hu_step, Int.fract_eq_iff]
          exact ⟨by linarith [Int.fract_nonneg (u₀ + ((m * d : ℕ) : ℝ) * (1 / φ))],
            hlt1, ⟨0, by simp⟩⟩
        · exfalso
          have hge1 : 1 ≤ u m + s := le_of_not_gt hlt1
          have hum1 : u (m + 1) = u m + s - 1 := by
            rw [hu_step, Int.fract_eq_iff]
            exact ⟨by linarith, by linarith [Int.fract_lt_one (u₀ + ((m * d : ℕ) : ℝ) * (1 / φ))],
              ⟨1, by push_cast; ring⟩⟩
          have : u (m + 1) < ε := by linarith [Int.fract_lt_one (u₀ + ((m * d : ℕ) : ℝ) * (1 / φ))]
          exact hno ⟨m + 1, this⟩
      have hu_closed : ∀ m : ℕ, u m = u 0 + (m : ℝ) * s := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [hstep_lin, ih]; push_cast; ring
      let M : ℕ := ⌊1 / s⌋₊ + 1
      have hM_gt : 1 < (M : ℝ) * s := by
        have := Nat.lt_floor_add_one (1 / s)
        have h1 := (div_lt_iff₀ hs_pos).mp this
        dsimp [M]; push_cast; linarith
      have huM_lt1 : u M < 1 := Int.fract_lt_one _
      have hu0_nn : 0 ≤ u 0 := Int.fract_nonneg _
      rw [hu_closed M] at huM_lt1
      linarith
    rcases hex_m0 with ⟨m₀, hm₀⟩
    let v (r : ℕ) : ℝ := u (m₀ + r)
    have hv_step : ∀ r : ℕ, v r ≤ a' → v (r + 1) = v r + s := by
      intro r hvr
      have heq_idx : m₀ + (r + 1) = m₀ + r + 1 := by omega
      dsimp [v]
      rw [heq_idx, hu_step, Int.fract_eq_iff]
      exact ⟨by linarith [Int.fract_nonneg (u₀ + (((m₀ + r) * d : ℕ) : ℝ) * (1 / φ))],
        by linarith, ⟨0, by simp⟩⟩
    have hex_r : ∃ r : ℕ, a' < v r := by
      by_contra hno
      have hle_all : ∀ r, v r ≤ a' := fun r => le_of_not_gt (fun h => hno ⟨r, h⟩)
      have hv_closed : ∀ r : ℕ, v r = v 0 + (r : ℝ) * s := by
        intro r
        induction r with
        | zero => simp
        | succ r ih => rw [hv_step r (hle_all r), ih]; push_cast; ring
      let R : ℕ := ⌊1 / s⌋₊ + 1
      have hR_gt : 1 < (R : ℝ) * s := by
        have := Nat.lt_floor_add_one (1 / s)
        have h1 := (div_lt_iff₀ hs_pos).mp this
        dsimp [R]; push_cast; linarith
      have hvR_lt1 : v R < 1 := Int.fract_lt_one _
      have hv0_nn : 0 ≤ v 0 := Int.fract_nonneg _
      rw [hv_closed R] at hvR_lt1
      linarith
    classical
    let r₀ := Nat.find hex_r
    have hr0_spec : a' < v r₀ := Nat.find_spec hex_r
    have hr0_ne : r₀ ≠ 0 := by
      intro hr0
      rw [hr0] at hr0_spec
      dsimp [v] at hr0_spec
      linarith
    let r' := r₀ - 1
    have hr_succ : r₀ = r' + 1 := by omega
    have hr'_le : v r' ≤ a' := le_of_not_gt (Nat.find_min hex_r (by omega : r' < r₀))
    have hvr0 : v r₀ = v r' + s := by rw [hr_succ, hv_step r' hr'_le]
    refine ⟨(m₀ + r₀) * d, ?_, ?_⟩
    · change a < v r₀; dsimp [a'] at hr0_spec; linarith
    · change v r₀ < b; rw [hvr0]; dsimp [b'] at hb'_gap; linarith
  · have hge1 : 1 ≤ f i.val + s := le_of_not_gt hwrap
    have hfj_val : f j.val = f i.val + s - 1 := by
      rw [hfj_eq, Int.fract_eq_iff]
      exact ⟨by linarith, by linarith [Int.fract_lt_one ((i.val : ℝ) * (1 / φ))],
        ⟨1, by push_cast; ring⟩⟩
    set δ : ℝ := 1 - s
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    have hδ_lt_eps : δ < ε := by
      have := (abs_lt.mp hdiff_lt).1
      dsimp [δ]; linarith
    have hex_m0 : ∃ m₀ : ℕ, 1 - ε < u m₀ := by
      by_contra hno
      have hle_all : ∀ m, u m ≤ 1 - ε := fun m => le_of_not_gt (fun h => hno ⟨m, h⟩)
      have hstep_lin : ∀ m, u (m + 1) = u m - δ := by
        intro m
        by_cases hge_d : δ ≤ u m
        · rw [hu_step, Int.fract_eq_iff]
          refine ⟨by linarith, by linarith [Int.fract_lt_one (u₀ + ((m * d : ℕ) : ℝ) * (1 / φ))],
            ⟨1, ?_⟩⟩
          dsimp [δ]; push_cast; ring
        · exfalso
          have hlt_d : u m < δ := lt_of_not_ge hge_d
          have hum1 : u (m + 1) = u m + s := by
            rw [hu_step, Int.fract_eq_iff]
            exact ⟨by linarith [Int.fract_nonneg (u₀ + ((m * d : ℕ) : ℝ) * (1 / φ))],
              by dsimp [δ] at hlt_d; linarith, ⟨0, by simp⟩⟩
          have : 1 - ε < u (m + 1) := by
            rw [hum1]; dsimp [δ] at hδ_lt_eps; linarith [Int.fract_nonneg (u₀ + ((m * d : ℕ) : ℝ) * (1 / φ))]
          exact hno ⟨m + 1, this⟩
      have hu_closed : ∀ m : ℕ, u m = u 0 - (m : ℝ) * δ := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [hstep_lin, ih]; push_cast; ring
      let M : ℕ := ⌊1 / δ⌋₊ + 1
      have hM_gt : 1 < (M : ℝ) * δ := by
        have := Nat.lt_floor_add_one (1 / δ)
        have h1 := (div_lt_iff₀ hδ_pos).mp this
        dsimp [M]; push_cast; linarith
      have huM_nn : 0 ≤ u M := Int.fract_nonneg _
      have hu0_lt1 : u 0 < 1 := Int.fract_lt_one _
      rw [hu_closed M] at huM_nn
      linarith
    rcases hex_m0 with ⟨m₀, hm₀⟩
    let v (r : ℕ) : ℝ := u (m₀ + r)
    have hv_step : ∀ r : ℕ, b' ≤ v r → v (r + 1) = v r - δ := by
      intro r hvr
      have heq_idx : m₀ + (r + 1) = m₀ + r + 1 := by omega
      dsimp [v]
      rw [heq_idx, hu_step, Int.fract_eq_iff]
      refine ⟨by linarith, by linarith [Int.fract_lt_one (u₀ + (((m₀ + r) * d : ℕ) : ℝ) * (1 / φ))],
        ⟨1, ?_⟩⟩
      dsimp [δ]; push_cast; ring
    have hex_r : ∃ r : ℕ, v r < b' := by
      by_contra hno
      have hge_all : ∀ r, b' ≤ v r := fun r => le_of_not_gt (fun h => hno ⟨r, h⟩)
      have hv_closed : ∀ r : ℕ, v r = v 0 - (r : ℝ) * δ := by
        intro r
        induction r with
        | zero => simp
        | succ r ih => rw [hv_step r (hge_all r), ih]; push_cast; ring
      let R : ℕ := ⌊1 / δ⌋₊ + 1
      have hR_gt : 1 < (R : ℝ) * δ := by
        have := Nat.lt_floor_add_one (1 / δ)
        have h1 := (div_lt_iff₀ hδ_pos).mp this
        dsimp [R]; push_cast; linarith
      have hvR_nn : 0 ≤ v R := Int.fract_nonneg _
      have hv0_lt1 : v 0 < 1 := Int.fract_lt_one _
      rw [hv_closed R] at hvR_nn
      linarith
    classical
    let r₀ := Nat.find hex_r
    have hr0_spec : v r₀ < b' := Nat.find_spec hex_r
    have hr0_ne : r₀ ≠ 0 := by
      intro hr0
      rw [hr0] at hr0_spec
      dsimp [v] at hr0_spec
      linarith
    let r' := r₀ - 1
    have hr_succ : r₀ = r' + 1 := by omega
    have hr'_ge : b' ≤ v r' := le_of_not_gt (Nat.find_min hex_r (by omega : r' < r₀))
    have hvr0 : v r₀ = v r' - δ := by rw [hr_succ, hv_step r' hr'_ge]
    refine ⟨(m₀ + r₀) * d, ?_, ?_⟩
    · change a < v r₀; rw [hvr0]; dsimp [a'] at hb'_gap; linarith
    · change v r₀ < b; dsimp [b'] at hr0_spec; linarith

/-- Forward-orbit density of `rotR` in `J' = (-φ^3 / 2, φ^3 / 2)` from ANY starting point `x₀`. -/
theorem rotR_orbit_dense {x₀ : ℝ} (hx1 : -φ ^ 3 / 2 ≤ x₀) (hx2 : x₀ < φ ^ 3 / 2)
    (lo hi : ℝ) (hlo : -φ ^ 3 / 2 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ φ ^ 3 / 2) :
    ∃ k : ℕ, lo < rotR^[k] x₀ ∧ rotR^[k] x₀ < hi := by
  have hcp : 0 < φ ^ 3 := phi_cube_pos
  have ha0 : 0 ≤ toUnit lo := div_nonneg (by linarith) (le_of_lt hcp)
  have hab : toUnit lo < toUnit hi := by
    unfold toUnit; exact div_lt_div_of_pos_right (by linarith) hcp
  have hb1 : toUnit hi ≤ 1 := (div_le_one hcp).mpr (by linarith)
  rcases kronecker_inv_phi_dense (toUnit x₀) (toUnit lo) (toUnit hi) ha0 hab hb1 with
    ⟨k, hk1, hk2⟩
  rcases toUnit_rotR_iter k hx1 hx2 with ⟨heq, _, _⟩
  rw [← heq] at hk1 hk2
  unfold toUnit at hk1 hk2
  rw [div_lt_div_iff_of_pos_right hcp] at hk1 hk2
  exact ⟨k, by linarith, by linarith⟩

/-- Density of `{ x_p = lambda' (prefixOf b5 p) | p : ℕ }` in `J = (-φ^2 / 2, φ^3 / 2)`. -/
theorem b5_orbit_dense_in_J (lo hi : ℝ)
    (hlo : -φ ^ 2 / 2 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ φ ^ 3 / 2) :
    ∃ p : ℕ, lo < lambda' (prefixOf b5 p) ∧ lambda' (prefixOf b5 p) < hi := by
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h1 : 1 < φ := one_lt_phi
  rcases rotR_orbit_dense (x₀ := 0) (by nlinarith) (by nlinarith)
    lo hi (by linarith) hlohi hhi with ⟨k, hk1, hk2⟩
  rcases (gFibB5_orbit_props k).2.2.2.2 (by linarith) with ⟨p, hp⟩
  exact ⟨p, by linarith, by linarith⟩

/-! ## Section 5: Proof of Corollary B (`b5_sturmian_projection` & Sturmian Complexity `n + 1`) -/

/-- Inverse of `rotR` on `J' \ {1 / 2}`. -/
noncomputable def rotRInv (y : ℝ) : ℝ :=
  if y < 1 / 2 then y + φ else y - φ ^ 2

theorem rotR_rotRInv {y : ℝ} (hy1 : -φ ^ 3 / 2 < y) (hy2 : y < φ ^ 3 / 2) (hy_ne : y ≠ 1 / 2) :
    -φ ^ 3 / 2 < rotRInv y ∧ rotRInv y < φ ^ 3 / 2 ∧ rotR (rotRInv y) = y := by
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h1 : 1 < φ := one_lt_phi
  unfold rotRInv
  split_ifs with hlt
  · refine ⟨by linarith, by linarith, ?_⟩
    unfold rotR
    rw [ite_false_of (by linarith)]; ring
  · have hgt : 1 / 2 < y := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hy_ne)
    refine ⟨by linarith, by linarith, ?_⟩
    unfold rotR
    rw [ite_true_of (by linarith)]; ring

theorem rotRInv_rotR {x : ℝ} (hx1 : -φ ^ 3 / 2 < x) (hx2 : x < φ ^ 3 / 2) (hx_ne : x ≠ -1 / 2) :
    rotR x ≠ 1 / 2 ∧ rotRInv (rotR x) = x := by
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  unfold rotR
  split_ifs with hlt
  · refine ⟨by linarith, ?_⟩
    unfold rotRInv
    rw [ite_false_of (by linarith)]; ring
  · have hgt : -1 / 2 < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hx_ne)
    refine ⟨by linarith, ?_⟩
    unfold rotRInv
    rw [ite_true_of (by linarith)]; ring

/-- Every backward preimage `rotRInv^[k] (-1 / 2)` stays inside `J'` and avoids `1 / 2`. -/
theorem rotRInv_iter_cut (k : ℕ) :
    -φ ^ 3 / 2 < rotRInv^[k] (-1 / 2) ∧
    rotRInv^[k] (-1 / 2) < φ ^ 3 / 2 ∧
    rotR^[k] (rotRInv^[k] (-1 / 2)) = -1 / 2 := by
  induction k with
  | zero =>
    dsimp only [Function.iterate_zero, id_eq]
    have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
    have h1 : 1 < φ := one_lt_phi
    exact ⟨by linarith, by linarith, rfl⟩
  | succ k ih =>
    rcases ih with ⟨hlo, hhi, hret⟩
    have hne : rotRInv^[k] (-1 / 2) ≠ 1 / 2 := by
      intro heq; rw [heq] at hret
      exact (fibWord_orbit_props k).2.2.2.2 hret
    rw [Function.iterate_succ_apply']
    rcases rotR_rotRInv hlo hhi hne with ⟨hlo', hhi', hinv⟩
    refine ⟨hlo', hhi', ?_⟩
    rw [Function.iterate_succ_apply, hinv, hret]

theorem rotRInv_iter_injective : Function.Injective (fun k : ℕ => rotRInv^[k] (-1 / 2)) := by
  intro k₁ k₂ heq
  by_contra hne
  have hwlog : ∀ a b : ℕ, a < b → rotRInv^[a] (-1 / 2) ≠ rotRInv^[b] (-1 / 2) := by
    intro a b hab hsame
    have hstep : rotR^[b] (rotRInv^[b] (-1 / 2)) = -1 / 2 := (rotRInv_iter_cut b).2.2
    rw [← hsame] at hstep
    have hsplit : b = (b - a) + a := by omega
    rw [hsplit, Function.iterate_add_apply, (rotRInv_iter_cut a).2.2] at hstep
    rcases rotRInv_iter_cut 0 with ⟨hc1, hc2, _⟩
    simp only [Function.iterate_zero_apply] at hc1 hc2
    rcases toUnit_rotR_iter (b - a) (le_of_lt hc1) hc2 with ⟨hu_eq, _, _⟩
    rw [hstep] at hu_eq
    have hf0 : Int.fract (((b - a : ℕ) : ℝ) * (1 / φ)) = 0 := by
      have h1 : Int.fract (toUnit (-1 / 2) + Int.fract (((b - a : ℕ) : ℝ) * (1 / φ))) =
          toUnit (-1 / 2) := by
        rw [add_comm, fract_fract_add, add_comm]; exact hu_eq.symm
      rcases (Int.fract_eq_iff.mp h1).2.2 with ⟨z, hz⟩
      have hfr := Int.fract_nonneg (((b - a : ℕ) : ℝ) * (1 / φ))
      have hfr1 := Int.fract_lt_one (((b - a : ℕ) : ℝ) * (1 / φ))
      have hz0 : z = 0 := by
        have hz1 : z < 1 := by exact_mod_cast (by linarith : (z : ℝ) < 1)
        have hz2 : -1 < z := by exact_mod_cast (by linarith : (-1 : ℝ) < (z : ℝ))
        omega
      rw [hz0, Int.cast_zero] at hz; linarith
    exact fract_nat_mul_inv_phi_ne_zero (by omega) hf0
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hwlog k₁ k₂ hlt heq
  · exact hwlog k₂ k₁ hgt heq.symm

/-- Backward cut set `rotCutSet n` of cardinality `n` for `(J', rotR)`. -/
noncomputable def rotCutSet (n : ℕ) : Finset ℝ :=
  (Finset.range n).image (fun k => rotRInv^[k] (-1 / 2))

theorem rotCutSet_card (n : ℕ) : (rotCutSet n).card = n := by
  unfold rotCutSet
  rw [Finset.card_image_of_injective _ rotRInv_iter_injective, Finset.card_range]

theorem rotCutSet_iff (n : ℕ) {x : ℝ} (hx1 : -φ ^ 3 / 2 < x) (hx2 : x < φ ^ 3 / 2) :
    x ∈ rotCutSet n ↔ ∃ k < n, rotR^[k] x ∈ ({(-1 / 2 : ℝ)} : Finset ℝ) := by
  simp only [rotCutSet, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨k, hkn, rfl⟩
    exact ⟨k, hkn, (rotRInv_iter_cut k).2.2⟩
  · rintro ⟨k, hkn, hhit⟩
    refine ⟨k, hkn, ?_⟩
    have hback : ∀ m : ℕ, ∀ y : ℝ, -φ ^ 3 / 2 < y → y < φ ^ 3 / 2 →
        rotR^[m] y = -1 / 2 → rotRInv^[m] (-1 / 2) = y := by
      intro m
      induction m with
      | zero =>
        intro y _ _ h0; simpa using h0.symm
      | succ m ih =>
        intro y hy1 hy2 hsucc
        by_cases hyc : y = -1 / 2
        · exfalso
          subst hyc
          rcases toUnit_rotR_iter (m + 1) (le_of_lt hy1) hy2 with ⟨hu_eq, _, _⟩
          rw [hsucc] at hu_eq
          have h1 : Int.fract (toUnit (-1 / 2) + Int.fract (((m + 1 : ℕ) : ℝ) * (1 / φ))) =
              toUnit (-1 / 2) := by
            rw [add_comm, fract_fract_add, add_comm]; exact hu_eq.symm
          rcases (Int.fract_eq_iff.mp h1).2.2 with ⟨z, hz⟩
          have hfr := Int.fract_nonneg (((m + 1 : ℕ) : ℝ) * (1 / φ))
          have hfr1 := Int.fract_lt_one (((m + 1 : ℕ) : ℝ) * (1 / φ))
          have hz0 : z = 0 := by
            have hz1 : z < 1 := by exact_mod_cast (by linarith : (z : ℝ) < 1)
            have hz2 : -1 < z := by exact_mod_cast (by linarith : (-1 : ℝ) < (z : ℝ))
            omega
          rw [hz0, Int.cast_zero] at hz
          have hf0 : Int.fract (((m + 1 : ℕ) : ℝ) * (1 / φ)) = 0 := by linarith
          exact fract_nat_mul_inv_phi_ne_zero (by omega : 1 ≤ m + 1) hf0
        · rcases toUnit_rotR (le_of_lt hy1) hy2 with ⟨_, hry1, hry2⟩
          rcases rotRInv_rotR hy1 hy2 hyc with ⟨_, hinv_y⟩
          have hry_gt : -φ ^ 3 / 2 < rotR y := by
            by_contra heq_lo
            have heq' : rotR y = -φ ^ 3 / 2 := le_antisymm (le_of_not_gt heq_lo) hry1
            unfold rotR at heq'
            have hsq : φ ^ 2 = φ + 1 := phi_sq
            have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
            split_ifs at heq' with hlt
            · linarith [one_lt_phi]
            · exact hyc (by linarith)
          rw [Function.iterate_succ_apply] at hsucc
          have ih_step := ih (rotR y) hry_gt hry2 hsucc
          rw [Function.iterate_succ_apply', ih_step, hinv_y]
    exact hback k x hx1 hx2 hhit

/-- Core shared range theorem for BOTH `gFibB5` and `fibWord` on `(J', rotR)`. -/
theorem sturmian_factors_and_complexity (n : ℕ) :
    FactorsOfLen gFibB5 n = FactorsOfLen fibWord n ∧
    factorComplexity fibWord n = n + 1 ∧
    factorComplexity gFibB5 n = n + 1 := by
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have h1 : 1 < φ := one_lt_phi
  have hJ : -φ ^ 3 / 2 < φ ^ 3 / 2 := by linarith
  have hinS : ∀ s ∈ rotCutSet n, -φ ^ 3 / 2 < s ∧ s < φ ^ 3 / 2 := by
    intro s hs
    simp only [rotCutSet, Finset.mem_image, Finset.mem_range] at hs
    rcases hs with ⟨k, _, rfl⟩
    exact ⟨(rotRInv_iter_cut k).1, (rotRInv_iter_cut k).2.1⟩
  have h_trans : ∀ x₁ x₂, -φ ^ 3 / 2 < x₁ → x₁ ≤ x₂ → x₂ < φ ^ 3 / 2 →
      (∀ c ∈ ({(-1 / 2 : ℝ)} : Finset ℝ), ¬ (x₁ ≤ c ∧ c ≤ x₂)) →
      rotLetter x₁ = rotLetter x₂ ∧ rotR x₂ - rotR x₁ = x₂ - x₁ ∧
      -φ ^ 3 / 2 < rotR x₁ ∧ rotR x₂ < φ ^ 3 / 2 := by
    intro x₁ x₂ hx1 h12 hx2 hno
    have hnot : ¬ (x₁ ≤ -1 / 2 ∧ -1 / 2 ≤ x₂) := hno (-1 / 2) (Finset.mem_singleton_self _)
    by_cases hlt : x₂ < -1 / 2
    · have hlt1 : x₁ < -1 / 2 := lt_of_le_of_lt h12 hlt
      have hl1 : rotLetter x₁ = true := decide_eq_true_eq.mpr hlt1
      have hl2 : rotLetter x₂ = true := decide_eq_true_eq.mpr hlt
      have hr1 : rotR x₁ = x₁ + φ ^ 2 := by
        unfold rotR; exact ite_true_of hlt1
      have hr2 : rotR x₂ = x₂ + φ ^ 2 := by
        unfold rotR; exact ite_true_of hlt
      rw [hl1, hl2, hr1, hr2]
      exact ⟨rfl, by ring, by linarith, by linarith⟩
    · have hgt1 : -1 / 2 < x₁ := by
        by_contra hle1
        exact hnot ⟨le_of_not_gt hle1, le_of_not_gt hlt⟩
      have hnot1 : ¬ (x₁ < -1 / 2) := by linarith
      have hl1 : rotLetter x₁ = false := decide_eq_false_iff_not.mpr hnot1
      have hl2 : rotLetter x₂ = false := decide_eq_false_iff_not.mpr hlt
      have hr1 : rotR x₁ = x₁ - φ := by
        unfold rotR; exact ite_false_of hnot1
      have hr2 : rotR x₂ = x₂ - φ := by
        unfold rotR; exact ite_false_of hlt
      rw [hl1, hl2, hr1, hr2]
      exact ⟨rfl, by ring, by linarith, by linarith⟩
  have h_sep : ∀ y₁ c y₂, -φ ^ 3 / 2 < y₁ → y₁ < c → c < y₂ → y₂ < φ ^ 3 / 2 →
      c ∈ ({(-1 / 2 : ℝ)} : Finset ℝ) → y₁ ∉ ({(-1 / 2 : ℝ)} : Finset ℝ) →
      y₂ ∉ ({(-1 / 2 : ℝ)} : Finset ℝ) → rotLetter y₁ ≠ rotLetter y₂ := by
    intro y₁ c y₂ _ hy1 hy2 _ hc _ _
    rw [Finset.mem_singleton] at hc
    subst hc
    have hl1 : rotLetter y₁ = true := decide_eq_true_eq.mpr hy1
    have hl2 : rotLetter y₂ = false := decide_eq_false_iff_not.mpr (by linarith)
    rw [hl1, hl2]; decide
  rcases factorsOfLen_eq_range_of_iet rotR rotLetter ({(-1 / 2 : ℝ)}) (rotCutSet n)
    hJ (rotCutSet_card n) hinS (fun x hx1 hx2 => rotCutSet_iff n hx1 hx2) h_trans h_sep with
    ⟨hinj, hrange_of_orb⟩
  have hgFib_range := hrange_of_orb gFibB5 (fun p => rotR^[p] 0)
    (fun p => ⟨(gFibB5_orbit_props p).2.1, (gFibB5_orbit_props p).2.2.1⟩)
    (fun p hp => (gFibB5_orbit_props p).2.2.2.1 (Finset.mem_singleton.mp hp))
    (fun p => (Function.iterate_succ_apply' rotR p 0).symm)
    (fun p => (gFibB5_orbit_props p).1)
    (fun a b ha hab hb => rotR_orbit_dense (by linarith) (by linarith) a b ha hab hb)
  have hfib_range := hrange_of_orb fibWord (fun p => rotR^[p] (1 / 2))
    (fun p => ⟨(fibWord_orbit_props p).2.2.1, (fibWord_orbit_props p).2.2.2.1⟩)
    (fun p hp => (fibWord_orbit_props p).2.2.2.2 (Finset.mem_singleton.mp hp))
    (fun p => (Function.iterate_succ_apply' rotR p (1 / 2)).symm)
    (fun p => (fibWord_orbit_props p).2.1)
    (fun a b ha hab hb => rotR_orbit_dense (by linarith) (by linarith) a b ha hab hb)
  have hcomp_fib : factorComplexity fibWord n = n + 1 :=
    factorComplexity_eq_of_bij _ hinj hfib_range
  have hcomp_g : factorComplexity gFibB5 n = n + 1 :=
    factorComplexity_eq_of_bij _ hinj hgFib_range
  exact ⟨hgFib_range.trans hfib_range.symm, hcomp_fib, hcomp_g⟩

/-- **Corollary B (`b5_sturmian_projection`)**:
For EVERY factor length `n : ℕ`, the morphic projection `gFibB5 = gFib(b_5)` has the **exact
same set of length-`n` factors** as the classical Fibonacci Sturmian word `fibWord`, and both
have exact Sturmian factor complexity `n + 1`. -/
theorem b5_sturmian_projection (n : ℕ) :
    FactorsOfLen gFibB5 n = FactorsOfLen fibWord n ∧
    factorComplexity fibWord n = n + 1 ∧
    factorComplexity gFibB5 n = n + 1 :=
  sturmian_factors_and_complexity n

theorem fibWord_factor_complexity (n : ℕ) : factorComplexity fibWord n = n + 1 :=
  (sturmian_factors_and_complexity n).2.1

theorem gFibB5_factor_complexity (n : ℕ) : factorComplexity gFibB5 n = n + 1 :=
  (sturmian_factors_and_complexity n).2.2

/-! ## Section 6: Proof of Corollary A (`b5_factor_complexity` = `4n + 1` for All `n : ℕ`) -/

/-- Three-interval exchange transformation `ietT` on `J = (-φ^2 / 2, φ^3 / 2)`. -/
noncomputable def ietT (x : ℝ) : ℝ :=
  if x < -1 / 2 then x + (1 + φ)
  else if x < (φ - 1) / 2 then x + 1
  else x - φ

/-- Five-letter coding map `ietLetter` on `J = (-φ^2 / 2, φ^3 / 2)`. -/
noncomputable def ietLetter (x : ℝ) : Fin 5 :=
  if x < -1 / 2 then 2
  else if x < (φ - 1) / 2 then 0
  else if x < φ / 2 then 4
  else if x < φ then 1
  else 3

/-- Inverse 3-IET `ietTInv` on `J \ {1 / 2, (1 + φ) / 2}`. -/
noncomputable def ietTInv (y : ℝ) : ℝ :=
  if y < 1 / 2 then y + φ
  else if y < (1 + φ) / 2 then y - 1
  else y - (1 + φ)

/-- The four interior cut points `c_0 = -1/2, c_1 = (φ-1)/2, c_2 = φ/2, c_3 = φ` of `J`. -/
noncomputable def b5CutPt : Fin 4 → ℝ
  | 0 => -1 / 2
  | 1 => (φ - 1) / 2
  | 2 => φ / 2
  | 3 => φ

/-- Exact `QSqrt5` representation of `b5CutPt`. -/
def b5CutPtQ : Fin 4 → QSqrt5
  | 0 => ⟨-1 / 2, 0⟩
  | 1 => ⟨-1 / 2, 1 / 2⟩
  | 2 => ⟨0, 1 / 2⟩
  | 3 => ⟨0, 1⟩

theorem b5CutPtQ_toReal (i : Fin 4) : (b5CutPtQ i).toReal = b5CutPt i := by
  fin_cases i <;> simp [b5CutPtQ, b5CutPt, QSqrt5.toReal] <;> ring

/-- Finite set of the four interior cut points of `J`. -/
noncomputable def b5BaseCuts : Finset ℝ :=
  Finset.univ.image b5CutPt

theorem mem_b5BaseCuts_iff (x : ℝ) :
    x ∈ b5BaseCuts ↔ ∃ i : Fin 4, b5CutPt i = x := by
  simp [b5BaseCuts]

theorem b5_orbit_iet_props (p : ℕ) :
    let xp := lambda' (prefixOf b5 p)
    (-φ ^ 2 / 2 < xp ∧ xp < φ ^ 3 / 2) ∧
    xp ∉ b5BaseCuts ∧
    ietT xp = lambda' (prefixOf b5 (p + 1)) ∧
    b5 p = ietLetter xp := by
  dsimp only
  set xp := lambda' (prefixOf b5 p)
  have hcod := b5_codes_interval_translation p
  rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
  have hnext : lambda' (prefixOf b5 (p + 1)) = xp + l' (b5 p) := by
    rw [prefixOf_succ, lambdaPrime_append, lambdaPrime_cons, lambdaPrime_nil, add_zero]
  have hb_cases : b5 p = 0 ∨ b5 p = 1 ∨ b5 p = 2 ∨ b5 p = 3 ∨ b5 p = 4 := fin5_cases (b5 p)
  refine ⟨hcod.1, ?_, ?_, ?_⟩
  · intro hmem
    rcases (mem_b5BaseCuts_iff xp).mp hmem with ⟨i, hi⟩
    rcases hb_cases with hb | hb | hb | hb | hb
    · have hx := (hcod.2.2.1).mp hb; fin_cases i <;> (simp [b5CutPt] at hi; linarith)
    · have hx := (hcod.2.2.2.2.1).mp hb; fin_cases i <;> (simp [b5CutPt] at hi; linarith)
    · have hx := (hcod.2.1).mp hb; fin_cases i <;> (simp [b5CutPt] at hi; linarith)
    · have hx := (hcod.2.2.2.2.2).mp hb; fin_cases i <;> (simp [b5CutPt] at hi; linarith)
    · have hx := (hcod.2.2.2.1).mp hb; fin_cases i <;> (simp [b5CutPt] at hi; linarith)
  · rw [hnext]
    rcases hb_cases with hb | hb | hb | hb | hb <;> rw [hb]
    · have hx := (hcod.2.2.1).mp hb
      unfold ietT l'
      rw [ite_false_of (by linarith), ite_true_of hx.2]
    · have hx := (hcod.2.2.2.2.1).mp hb
      unfold ietT l'
      rw [ite_false_of (by linarith), ite_false_of (by linarith)]; ring
    · have hx := (hcod.2.1).mp hb
      unfold ietT l'
      rw [ite_true_of hx.2]
    · have hx := (hcod.2.2.2.2.2).mp hb
      unfold ietT l'
      rw [ite_false_of (by linarith), ite_false_of (by linarith)]; ring
    · have hx := (hcod.2.2.2.1).mp hb
      unfold ietT l'
      rw [ite_false_of (by linarith), ite_false_of (by linarith)]; ring
  · rcases hb_cases with hb | hb | hb | hb | hb <;> rw [hb]
    · have hx := (hcod.2.2.1).mp hb
      unfold ietLetter
      rw [ite_false_of (by linarith), ite_true_of hx.2]
    · have hx := (hcod.2.2.2.2.1).mp hb
      unfold ietLetter
      rw [ite_false_of (by linarith), ite_false_of (by linarith),
          ite_false_of (by linarith), ite_true_of hx.2]
    · have hx := (hcod.2.1).mp hb
      unfold ietLetter
      rw [ite_true_of hx.2]
    · have hx := (hcod.2.2.2.2.2).mp hb
      unfold ietLetter
      rw [ite_false_of (by linarith), ite_false_of (by linarith),
          ite_false_of (by linarith), ite_false_of (by linarith)]
    · have hx := (hcod.2.2.2.1).mp hb
      unfold ietLetter
      rw [ite_false_of (by linarith), ite_false_of (by linarith), ite_true_of hx.2]

/-- `ietT` and `ietTInv` are mutual inverses between `J \ {-1/2, (φ-1)/2}` and `J \ {1/2, (1+φ)/2}`. -/
theorem ietT_ietTInv {y : ℝ} (hy1 : -φ ^ 2 / 2 < y) (hy2 : y < φ ^ 3 / 2)
    (hne1 : y ≠ 1 / 2) (hne2 : y ≠ (1 + φ) / 2) :
    -φ ^ 2 / 2 < ietTInv y ∧ ietTInv y < φ ^ 3 / 2 ∧
    ietTInv y ≠ -1 / 2 ∧ ietTInv y ≠ (φ - 1) / 2 ∧
    ietT (ietTInv y) = y := by
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h1 : 1 < φ := one_lt_phi
  unfold ietTInv
  split_ifs with hlt1 hlt2
  · refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    unfold ietT
    rw [ite_false_of (by linarith), ite_false_of (by linarith)]
    ring
  · have hgt1 : 1 / 2 < y := lt_of_le_of_ne (le_of_not_gt hlt1) (Ne.symm hne1)
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    unfold ietT
    rw [ite_false_of (by linarith), ite_true_of (by linarith)]
    ring
  · have hgt2 : (1 + φ) / 2 < y := lt_of_le_of_ne (le_of_not_gt hlt2) (Ne.symm hne2)
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    unfold ietT
    rw [ite_true_of (by linarith)]
    ring

theorem ietTInv_ietT {x : ℝ} (hx1 : -φ ^ 2 / 2 < x) (hx2 : x < φ ^ 3 / 2)
    (hne1 : x ≠ -1 / 2) (hne2 : x ≠ (φ - 1) / 2) :
    -φ ^ 2 / 2 < ietT x ∧ ietT x < φ ^ 3 / 2 ∧
    ietT x ≠ 1 / 2 ∧ ietT x ≠ (1 + φ) / 2 ∧
    ietTInv (ietT x) = x := by
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h1 : 1 < φ := one_lt_phi
  unfold ietT
  split_ifs with hlt1 hlt2
  · refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    unfold ietTInv
    rw [ite_false_of (by linarith), ite_false_of (by linarith)]; ring
  · have hgt1 : -1 / 2 < x := lt_of_le_of_ne (le_of_not_gt hlt1) (Ne.symm hne1)
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    unfold ietTInv
    rw [ite_false_of (by linarith), ite_true_of (by linarith)]; ring
  · have hgt2 : (φ - 1) / 2 < x := lt_of_le_of_ne (le_of_not_gt hlt2) (Ne.symm hne2)
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    unfold ietTInv
    rw [ite_true_of (by linarith)]; ring

/-- Every `k`-step displacement `ietT^[k] x - x` has `QSqrt5` coordinates
`⟨m₀ + m₂, m₂ - m₁⟩` with `m₀ + m₁ + m₂ = k`. -/
theorem ietT_iter_coords (k : ℕ) (x : ℝ) :
    ∃ m₀ m₁ m₂ : ℕ, m₀ + m₁ + m₂ = k ∧
      ietT^[k] x - x = (⟨(m₀ + m₂ : ℚ), (m₂ : ℚ) - (m₁ : ℚ)⟩ : QSqrt5).toReal := by
  induction k with
  | zero =>
    exact ⟨0, 0, 0, rfl, by simp [QSqrt5.toReal]⟩
  | succ k ih =>
    rcases ih with ⟨m₀, m₁, m₂, hsum, hdiff⟩
    rw [Function.iterate_succ_apply']
    set y := ietT^[k] x
    simp only [QSqrt5.toReal] at hdiff
    unfold ietT
    split_ifs with h1 h2
    · refine ⟨m₀, m₁, m₂ + 1, by omega, ?_⟩
      simp only [QSqrt5.toReal]; push_cast at hdiff ⊢; linarith
    · refine ⟨m₀ + 1, m₁, m₂, by omega, ?_⟩
      simp only [QSqrt5.toReal]; push_cast at hdiff ⊢; linarith
    · refine ⟨m₀, m₁ + 1, m₂, by omega, ?_⟩
      simp only [QSqrt5.toReal]; push_cast at hdiff ⊢; linarith

theorem int_cast_ne_half (z : ℤ) {s : ℚ} (hs : s = 1 / 2 ∨ s = -1 / 2) : (z : ℚ) ≠ s := by
  intro h
  have h2 : ((2 * z : ℤ) : ℚ) = 2 * s := by push_cast; rw [h]
  rcases hs with rfl | rfl
  · have h2' : ((2 * z : ℤ) : ℚ) = (1 : ℚ) := by linarith
    have hz : 2 * z = 1 := by exact_mod_cast h2'
    omega
  · have h2' : ((2 * z : ℤ) : ℚ) = (-1 : ℚ) := by linarith
    have hz : 2 * z = -1 := by exact_mod_cast h2'
    omega

/-- Key arithmetic non-connection lemma via `QSqrt5.toReal_injective`:
1. `ietT^[k] x = x → k = 0`;
2. `ietT^[k] d ≠ b5CutPt i` for `d ∈ {1 / 2, (1 + φ) / 2}` and all `i : Fin 4`, `k : ℕ`;
3. `ietT^[k] (b5CutPt j) = b5CutPt i → k = 0 ∧ i = j`. -/
theorem ietT_no_connections :
    (∀ k x, ietT^[k] x = x → k = 0) ∧
    (∀ k (i : Fin 4), ietT^[k] (1 / 2) ≠ b5CutPt i ∧ ietT^[k] ((1 + φ) / 2) ≠ b5CutPt i) ∧
    (∀ k (i j : Fin 4), ietT^[k] (b5CutPt j) = b5CutPt i → k = 0 ∧ i = j) := by
  have hzero_coords : ∀ m₀ m₁ m₂ : ℕ,
      (⟨(m₀ + m₂ : ℚ), (m₂ : ℚ) - (m₁ : ℚ)⟩ : QSqrt5) = 0 → m₀ + m₁ + m₂ = 0 := by
    intro m₀ m₁ m₂ hinj
    have ha_raw := congrArg QSqrt5.a hinj
    have hb_raw := congrArg QSqrt5.b hinj
    change (m₀ : ℚ) + (m₂ : ℚ) = 0 at ha_raw
    change (m₂ : ℚ) - (m₁ : ℚ) = 0 at hb_raw
    have ha_nat : ((m₀ + m₂ : ℕ) : ℚ) = (0 : ℚ) := by push_cast; exact ha_raw
    have hb_int : (((m₂ : ℤ) - (m₁ : ℤ) : ℤ) : ℚ) = (0 : ℚ) := by push_cast; exact hb_raw
    have hm02 : m₀ + m₂ = 0 := by exact_mod_cast ha_nat
    have hm21 : (m₂ : ℤ) - (m₁ : ℤ) = 0 := by exact_mod_cast hb_int
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro k x heq
    rcases ietT_iter_coords k x with ⟨m₀, m₁, m₂, hsum, hdiff⟩
    rw [heq, sub_self, ← QSqrt5.toReal_zero] at hdiff
    have hinj := QSqrt5.toReal_injective hdiff.symm
    have h0 := hzero_coords m₀ m₁ m₂ hinj
    omega
  · intro k i
    let d0 : QSqrt5 := ⟨1 / 2, 0⟩
    let d1 : QSqrt5 := ⟨1 / 2, 1 / 2⟩
    have hd0 : d0.toReal = 1 / 2 := by simp [d0, QSqrt5.toReal]
    have hd1 : d1.toReal = (1 + φ) / 2 := by simp [d1, QSqrt5.toReal]; ring
    constructor <;> intro heq
    · rcases ietT_iter_coords k (1 / 2) with ⟨m₀, m₁, m₂, _, hdiff⟩
      rw [heq, ← b5CutPtQ_toReal i, ← hd0, ← QSqrt5.toReal_sub] at hdiff
      have hinj := QSqrt5.toReal_injective hdiff
      have ha := congrArg QSqrt5.a hinj
      have hnn : (0 : ℚ) ≤ (m₀ : ℚ) + (m₂ : ℚ) := by positivity
      fin_cases i <;> (simp only [b5CutPtQ, d0, QSqrt5.sub_a] at ha; linarith)
    · rcases ietT_iter_coords k ((1 + φ) / 2) with ⟨m₀, m₁, m₂, _, hdiff⟩
      rw [heq, ← b5CutPtQ_toReal i, ← hd1, ← QSqrt5.toReal_sub] at hdiff
      have hinj := QSqrt5.toReal_injective hdiff
      have ha := congrArg QSqrt5.a hinj
      have hnn : (0 : ℚ) ≤ (m₀ : ℚ) + (m₂ : ℚ) := by positivity
      fin_cases i <;> (simp only [b5CutPtQ, d1, QSqrt5.sub_a] at ha; linarith)
  · intro k i j heq
    by_cases hij : i = j
    · subst hij
      rcases ietT_iter_coords k (b5CutPt i) with ⟨m₀, m₁, m₂, hsum, hdiff⟩
      rw [heq, sub_self, ← QSqrt5.toReal_zero] at hdiff
      have hinj := QSqrt5.toReal_injective hdiff.symm
      have h0 := hzero_coords m₀ m₁ m₂ hinj
      exact ⟨by omega, rfl⟩
    · exfalso
      rcases ietT_iter_coords k (b5CutPt j) with ⟨m₀, m₁, m₂, _, hdiff⟩
      rw [heq, ← b5CutPtQ_toReal i, ← b5CutPtQ_toReal j, ← QSqrt5.toReal_sub] at hdiff
      have hinj := QSqrt5.toReal_injective hdiff
      have ha : (((m₀ : ℤ) + (m₂ : ℤ) : ℤ) : ℚ) = (b5CutPtQ i - b5CutPtQ j).a := by
        rw [congrArg QSqrt5.a hinj]; push_cast; ring
      have hb : (((m₂ : ℤ) - (m₁ : ℤ) : ℤ) : ℚ) = (b5CutPtQ i - b5CutPtQ j).b := by
        rw [congrArg QSqrt5.b hinj]; push_cast; ring
      have hhalf : (b5CutPtQ i - b5CutPtQ j).a = 1 / 2 ∨
          (b5CutPtQ i - b5CutPtQ j).a = -1 / 2 ∨
          (b5CutPtQ i - b5CutPtQ j).b = 1 / 2 ∨
          (b5CutPtQ i - b5CutPtQ j).b = -1 / 2 := by
        fin_cases i <;> fin_cases j <;> first
          | exact absurd rfl hij
          | (simp only [b5CutPtQ, QSqrt5.sub_a, QSqrt5.sub_b]; norm_num)
      rcases hhalf with h | h | h | h
      · exact int_cast_ne_half ((m₀ : ℤ) + (m₂ : ℤ)) (Or.inl h) ha
      · exact int_cast_ne_half ((m₀ : ℤ) + (m₂ : ℤ)) (Or.inr h) ha
      · exact int_cast_ne_half ((m₂ : ℤ) - (m₁ : ℤ)) (Or.inl h) hb
      · exact int_cast_ne_half ((m₂ : ℤ) - (m₁ : ℤ)) (Or.inr h) hb

/-- Every backward preimage `ietTInv^[k] (b5CutPt i)` stays inside `J` and returns to `b5CutPt i`. -/
theorem ietTInv_iter_cut (k : ℕ) (i : Fin 4) :
    -φ ^ 2 / 2 < ietTInv^[k] (b5CutPt i) ∧
    ietTInv^[k] (b5CutPt i) < φ ^ 3 / 2 ∧
    ietT^[k] (ietTInv^[k] (b5CutPt i)) = b5CutPt i := by
  induction k with
  | zero =>
    dsimp only [Function.iterate_zero, id_eq]
    rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
    fin_cases i <;> (dsimp only [b5CutPt]; exact ⟨by linarith, by linarith, rfl⟩)
  | succ k ih =>
    rcases ih with ⟨hlo, hhi, hret⟩
    have hne1 : ietTInv^[k] (b5CutPt i) ≠ 1 / 2 := by
      intro heq; rw [heq] at hret
      exact (ietT_no_connections.2.1 k i).1 hret
    have hne2 : ietTInv^[k] (b5CutPt i) ≠ (1 + φ) / 2 := by
      intro heq; rw [heq] at hret
      exact (ietT_no_connections.2.1 k i).2 hret
    rw [Function.iterate_succ_apply']
    rcases ietT_ietTInv hlo hhi hne1 hne2 with ⟨hlo', hhi', _, _, hinv⟩
    refine ⟨hlo', hhi', ?_⟩
    rw [Function.iterate_succ_apply, hinv, hret]

theorem ietTInv_iter_injective :
    Function.Injective (fun p : ℕ × Fin 4 => ietTInv^[p.1] (b5CutPt p.2)) := by
  rintro ⟨k₁, i₁⟩ ⟨k₂, i₂⟩ heq
  dsimp only at heq
  rcases le_total k₁ k₂ with hle | hle
  · have hret2 := (ietTInv_iter_cut k₂ i₂).2.2
    rw [← heq] at hret2
    have hsplit : k₂ = (k₂ - k₁) + k₁ := by omega
    rw [hsplit, Function.iterate_add_apply, (ietTInv_iter_cut k₁ i₁).2.2] at hret2
    rcases ietT_no_connections.2.2 (k₂ - k₁) i₂ i₁ hret2 with ⟨hd0, hi_eq⟩
    exact Prod.ext (by omega) hi_eq.symm
  · have hret1 := (ietTInv_iter_cut k₁ i₁).2.2
    rw [heq] at hret1
    have hsplit : k₁ = (k₁ - k₂) + k₂ := by omega
    rw [hsplit, Function.iterate_add_apply, (ietTInv_iter_cut k₂ i₂).2.2] at hret1
    rcases ietT_no_connections.2.2 (k₁ - k₂) i₁ i₂ hret1 with ⟨hd0, hi_eq⟩
    exact Prod.ext (by omega) hi_eq

/-- Backward preimage set `ietCutSet n` of exact cardinality `4 * n` inside `J`. -/
noncomputable def ietCutSet (n : ℕ) : Finset ℝ :=
  ((Finset.range n) ×ˢ (Finset.univ : Finset (Fin 4))).image
    (fun p : ℕ × Fin 4 => ietTInv^[p.1] (b5CutPt p.2))

theorem ietCutSet_card (n : ℕ) : (ietCutSet n).card = 4 * n := by
  unfold ietCutSet
  rw [Finset.card_image_of_injective _ ietTInv_iter_injective,
    Finset.card_product, Finset.card_range, Finset.card_fin]
  ring

theorem ietCutSet_iff (n : ℕ) {x : ℝ} (hx1 : -φ ^ 2 / 2 < x) (hx2 : x < φ ^ 3 / 2) :
    x ∈ ietCutSet n ↔ ∃ k < n, ietT^[k] x ∈ b5BaseCuts := by
  simp only [ietCutSet, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, Prod.exists, mem_b5BaseCuts_iff]
  constructor
  · rintro ⟨k, i, hkn, rfl⟩
    exact ⟨k, hkn, i, (ietTInv_iter_cut k i).2.2.symm⟩
  · rintro ⟨k, hkn, i, hhit⟩
    have hex_hit : ∃ j : ℕ, j < n ∧ ∃ c : Fin 4, ietT^[j] x = b5CutPt c :=
      ⟨k, hkn, i, hhit.symm⟩
    classical
    let j₀ := Nat.find hex_hit
    rcases Nat.find_spec hex_hit with ⟨hj0_lt, c₀, hj0_eq⟩
    have hmin : ∀ r < j₀, ∀ c : Fin 4, ietT^[r] x ≠ b5CutPt c := by
      intro r hr c hrc
      exact Nat.find_min hex_hit hr ⟨by omega, c, hrc⟩
    refine ⟨j₀, c₀, hj0_lt, ?_⟩
    have hwalk : ∀ r : ℕ, r ≤ j₀ →
        -φ ^ 2 / 2 < ietT^[r] x ∧ ietT^[r] x < φ ^ 3 / 2 ∧
        ietTInv^[r] (ietT^[r] x) = x := by
      intro r
      induction r with
      | zero =>
        intro _; simp [hx1, hx2]
      | succ r ih =>
        intro hr_le
        rcases ih (by omega) with ⟨hr1, hr2, hrinv⟩
        have hne0 : ietT^[r] x ≠ -1 / 2 := hmin r (by omega) 0
        have hne1 : ietT^[r] x ≠ (φ - 1) / 2 := hmin r (by omega) 1
        rcases ietTInv_ietT hr1 hr2 hne0 hne1 with ⟨hs1, hs2, _, _, hsinv⟩
        have hstep_eq : ietT (ietT^[r] x) = ietT^[r + 1] x :=
          (Function.iterate_succ_apply' ietT r x).symm
        rw [hstep_eq] at hs1 hs2 hsinv
        refine ⟨hs1, hs2, ?_⟩
        rw [Function.iterate_succ_apply, hsinv, hrinv]
    have hj0_inv := (hwalk j₀ (le_refl _)).2.2
    rwa [hj0_eq] at hj0_inv

/-- **Corollary A (`b5_factor_complexity`)**:
For EVERY factor length `n : ℕ` (both `n = 0` and all `n ≥ 1`), the exact number of distinct
length-`n` factors of `b_5` is **`4 * n + 1`**. -/
theorem b5_factor_complexity (n : ℕ) :
    factorComplexity b5 n = 4 * n + 1 := by
  rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h1 : 1 < φ := one_lt_phi
  have hJ : -φ ^ 2 / 2 < φ ^ 3 / 2 := by linarith
  have hinS : ∀ s ∈ ietCutSet n, -φ ^ 2 / 2 < s ∧ s < φ ^ 3 / 2 := by
    intro s hs
    simp only [ietCutSet, Finset.mem_image, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true, Prod.exists] at hs
    rcases hs with ⟨k, i, _, rfl⟩
    exact ⟨(ietTInv_iter_cut k i).1, (ietTInv_iter_cut k i).2.1⟩
  have h_trans : ∀ x₁ x₂, -φ ^ 2 / 2 < x₁ → x₁ ≤ x₂ → x₂ < φ ^ 3 / 2 →
      (∀ c ∈ b5BaseCuts, ¬ (x₁ ≤ c ∧ c ≤ x₂)) →
      ietLetter x₁ = ietLetter x₂ ∧ ietT x₂ - ietT x₁ = x₂ - x₁ ∧
      -φ ^ 2 / 2 < ietT x₁ ∧ ietT x₂ < φ ^ 3 / 2 := by
    intro x₁ x₂ hx1 h12 hx2 hno
    have hno_i : ∀ i : Fin 4, ¬ (x₁ ≤ b5CutPt i ∧ b5CutPt i ≤ x₂) :=
      fun i => hno (b5CutPt i) ((mem_b5BaseCuts_iff _).mpr ⟨i, rfl⟩)
    have h0 := hno_i 0; simp only [b5CutPt] at h0
    have h1c := hno_i 1; simp only [b5CutPt] at h1c
    have h2c := hno_i 2; simp only [b5CutPt] at h2c
    have h3c := hno_i 3; simp only [b5CutPt] at h3c
    by_cases ha : x₂ < -1 / 2
    · have ha1 : x₁ < -1 / 2 := lt_of_le_of_lt h12 ha
      have hl1 : ietLetter x₁ = 2 := by unfold ietLetter; exact ite_true_of ha1
      have hl2 : ietLetter x₂ = 2 := by unfold ietLetter; exact ite_true_of ha
      have ht1 : ietT x₁ = x₁ + (1 + φ) := by unfold ietT; exact ite_true_of ha1
      have ht2 : ietT x₂ = x₂ + (1 + φ) := by unfold ietT; exact ite_true_of ha
      rw [hl1, hl2, ht1, ht2]
      exact ⟨rfl, by ring, by linarith, by linarith⟩
    · have ha1 : -1 / 2 < x₁ := by
        by_contra hle; exact h0 ⟨le_of_not_gt hle, le_of_not_gt ha⟩
      have hna1 : ¬ (x₁ < -1 / 2) := by linarith
      by_cases hb : x₂ < (φ - 1) / 2
      · have hb1 : x₁ < (φ - 1) / 2 := lt_of_le_of_lt h12 hb
        have hl1 : ietLetter x₁ = 0 := by
          unfold ietLetter
          rw [ite_false_of hna1, ite_true_of hb1]
        have hl2 : ietLetter x₂ = 0 := by
          unfold ietLetter
          rw [ite_false_of ha, ite_true_of hb]
        have ht1 : ietT x₁ = x₁ + 1 := by
          unfold ietT
          rw [ite_false_of hna1, ite_true_of hb1]
        have ht2 : ietT x₂ = x₂ + 1 := by
          unfold ietT
          rw [ite_false_of ha, ite_true_of hb]
        rw [hl1, hl2, ht1, ht2]
        exact ⟨rfl, by ring, by linarith, by linarith⟩
      · have hb1 : (φ - 1) / 2 < x₁ := by
          by_contra hle; exact h1c ⟨le_of_not_gt hle, le_of_not_gt hb⟩
        have hnb1 : ¬ (x₁ < (φ - 1) / 2) := by linarith
        have ht1 : ietT x₁ = x₁ - φ := by
          unfold ietT
          rw [ite_false_of hna1, ite_false_of hnb1]
        have ht2 : ietT x₂ = x₂ - φ := by
          unfold ietT
          rw [ite_false_of ha, ite_false_of hb]
        rw [ht1, ht2]
        refine ⟨?_, by ring, by linarith, by linarith⟩
        by_cases hc : x₂ < φ / 2
        · have hc1 : x₁ < φ / 2 := lt_of_le_of_lt h12 hc
          unfold ietLetter
          rw [ite_false_of hna1,
              ite_false_of ha,
              ite_false_of hnb1,
              ite_false_of hb,
              ite_true_of hc1,
              ite_true_of hc]
        · have hc1 : φ / 2 < x₁ := by
            by_contra hle; exact h2c ⟨le_of_not_gt hle, le_of_not_gt hc⟩
          have hnc1 : ¬ (x₁ < φ / 2) := by linarith
          by_cases hd : x₂ < φ
          · have hd1 : x₁ < φ := lt_of_le_of_lt h12 hd
            unfold ietLetter
            rw [ite_false_of hna1,
                ite_false_of ha,
                ite_false_of hnb1,
                ite_false_of hb,
                ite_false_of hnc1,
                ite_false_of hc,
                ite_true_of hd1,
                ite_true_of hd]
          · have hd1 : φ < x₁ := by
              by_contra hle; exact h3c ⟨le_of_not_gt hle, le_of_not_gt hd⟩
            have hnd1 : ¬ (x₁ < φ) := by linarith
            unfold ietLetter
            rw [ite_false_of hna1,
                ite_false_of ha,
                ite_false_of hnb1,
                ite_false_of hb,
                ite_false_of hnc1,
                ite_false_of hc,
                ite_false_of hnd1,
                ite_false_of hd]
  have h_sep : ∀ y₁ c y₂, -φ ^ 2 / 2 < y₁ → y₁ < c → c < y₂ → y₂ < φ ^ 3 / 2 →
      c ∈ b5BaseCuts → y₁ ∉ b5BaseCuts → y₂ ∉ b5BaseCuts →
      ietLetter y₁ ≠ ietLetter y₂ := by
    intro y₁ c y₂ _ hy1 hy2 _ hc _ _ heq
    rcases (mem_b5BaseCuts_iff c).mp hc with ⟨i, rfl⟩
    fin_cases i
    · simp only [b5CutPt] at hy1 hy2
      have hl1 : ietLetter y₁ = 2 := by
        unfold ietLetter; exact ite_true_of hy1
      have hl2 : ietLetter y₂ ≠ 2 := by
        unfold ietLetter
        rw [ite_false_of (by linarith)]
        split_ifs <;> decide
      exact hl2 (hl1 ▸ heq).symm
    · simp only [b5CutPt] at hy1 hy2
      have hl1 : ietLetter y₁ = 2 ∨ ietLetter y₁ = 0 := by
        unfold ietLetter
        by_cases ha : y₁ < -1 / 2
        · rw [ite_true_of ha]; left; rfl
        · rw [ite_false_of ha, ite_true_of hy1]
          right; rfl
      have hl2 : ietLetter y₂ = 4 ∨ ietLetter y₂ = 1 ∨ ietLetter y₂ = 3 := by
        unfold ietLetter
        rw [ite_false_of (by linarith), ite_false_of (by linarith)]
        split_ifs <;> simp
      rw [heq] at hl1
      rcases hl1 with h | h <;> rcases hl2 with h' | h' | h' <;>
        exact absurd (h.symm.trans h') (by decide)
    · simp only [b5CutPt] at hy1 hy2
      have hl1 : ietLetter y₁ = 2 ∨ ietLetter y₁ = 0 ∨ ietLetter y₁ = 4 := by
        unfold ietLetter
        by_cases ha : y₁ < -1 / 2
        · rw [ite_true_of ha]; simp
        · rw [ite_false_of ha]
          by_cases hb : y₁ < (φ - 1) / 2
          · rw [ite_true_of hb]; simp
          · rw [ite_false_of hb, ite_true_of hy1]; simp
      have hl2 : ietLetter y₂ = 1 ∨ ietLetter y₂ = 3 := by
        unfold ietLetter
        rw [ite_false_of (by linarith), ite_false_of (by linarith), ite_false_of (by linarith)]
        split_ifs <;> simp
      rw [heq] at hl1
      rcases hl1 with h | h | h <;> rcases hl2 with h' | h' <;>
        exact absurd (h.symm.trans h') (by decide)
    · simp only [b5CutPt] at hy1 hy2
      have hl2 : ietLetter y₂ = 3 := by
        unfold ietLetter
        rw [ite_false_of (by linarith), ite_false_of (by linarith),
            ite_false_of (by linarith), ite_false_of (by linarith)]
      have hl1 : ietLetter y₁ ≠ 3 := by
        unfold ietLetter
        by_cases ha : y₁ < -1 / 2
        · rw [ite_true_of ha]; decide
        · rw [ite_false_of ha]
          by_cases hb : y₁ < (φ - 1) / 2
          · rw [ite_true_of hb]; decide
          · rw [ite_false_of hb]
            by_cases hc2 : y₁ < φ / 2
            · rw [ite_true_of hc2]; decide
            · rw [ite_false_of hc2, ite_true_of hy1]; decide
      exact hl1 (heq.trans hl2)
  rcases factorsOfLen_eq_range_of_iet ietT ietLetter b5BaseCuts (ietCutSet n)
    hJ (ietCutSet_card n) hinS (fun x hx1 hx2 => ietCutSet_iff n hx1 hx2) h_trans h_sep with
    ⟨hinj, hrange_of_orb⟩
  have hb5_range := hrange_of_orb b5 (fun p => lambda' (prefixOf b5 p))
    (fun p => (b5_orbit_iet_props p).1)
    (fun p => (b5_orbit_iet_props p).2.1)
    (fun p => (b5_orbit_iet_props p).2.2.1)
    (fun p => (b5_orbit_iet_props p).2.2.2)
    (fun a b ha hab hb => b5_orbit_dense_in_J a b ha hab hb)
  exact factorComplexity_eq_of_bij _ hinj hb5_range

/-- Explicit `n ≥ 1` corollary matching the printed TCS 2015 statement. -/
theorem b5_factor_complexity_ge_one (n : ℕ) (_hn : 1 ≤ n) :
    factorComplexity b5 n = 4 * n + 1 :=
  b5_factor_complexity n

end BadkobehOchemB5
