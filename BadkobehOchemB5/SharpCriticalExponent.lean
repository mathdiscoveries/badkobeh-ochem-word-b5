/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BadkobehOchemB5.Defs
public import BadkobehOchemB5.SeedsCert
public import BadkobehOchemB5.CriticalExponent
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Sharp Second-Order Critical Exponent, Exact Deficit Infimum, Asymptotic Critical Exponent, and Irrationality

This module strengthens Theorem 4 (`CriticalExponent.lean`) beyond the qualitative strict bound
`|w| / p < (5 + √5) / 4` by establishing the **exact, optimal second-order law** with sharp constant
`(7 - √5) / 8 = (2 - φ / 2) / 2`, the exact exponential closed form of the extremal deficit branch,
the asymptotic critical exponent `E*(b_5) = E(b_5) = (5 + √5) / 4`, and the irrationality of
`E(b_5)`.

Main theorems proved unconditionally (zero `sorry`, zero `native_decide`, standard 3 axioms only):
1. **`b5_sharp_deficit_gt`** & **`b5_exponent_lt_sharp_second_order`**: For EVERY factor `w` of
   `b_5` and EVERY period `p ≥ 1` of `w`,
   `φ * p - 2 * (|w| - p) > (7 - √5) / 4` and
   `|w| / p < (5 + √5) / 4 - (7 - √5) / (8 * p)`.
2. **`extremal_deficit_closed_form`**: Along the canonical extremal seed `123.010.421` at
   `k = 6 + 6 * j` (`j : ℕ`), the shifted deficit satisfies the exact Fibonacci closed form
   `2 * (φ * p_{6+6j} - 2 * m_{6+6j}) - (4 - φ) = 1 / φ ^ (11 + 6 * j)`.
3. **`b5_sharp_second_order_optimal`**, **`b5_sharp_deficit_inf_eq`**, &
   **`b5_sharp_deficit_not_attained`**: The constant `(7 - √5) / 4` is the exact infimum of
   `φ * p - 2 * (|w| - p)` over all factors and periods `p ≥ 1` (never attained), and is approached
   with arbitrarily large periods `p ≥ P₀`.
4. **`b5_asymp_critExp_eq`**: For every period threshold `L ≥ 1`,
   `sSup { |w| / p | w factor of b_5, p ≥ L period of w } = (5 + √5) / 4`,
   establishing `E*(b_5) = E(b_5) = (5 + √5) / 4`.
5. **`b5_critExp_irrational`**: `Irrational (critExp b5)`.
-/

@[expose] public section

namespace BadkobehOchemB5

/-! ## Section 1: Pure-Kernel `ℤ[φ]` Sharp-Deficit Certificate (`2 D_k - (4 - φ) > 0`) -/

/-- Shifted deficit `E(s) := 2 * D(s) - (4 - φ) = (-4 * m - 4) + (2 * p + 1) * φ ∈ ℤ[φ]`.
Note `E(s).toReal > 0 ↔ φ * p - 2 * m > 2 - φ / 2 = (7 - √5) / 4`. -/
def summarySharpE (s : SeedSummary) : ZPhi :=
  ⟨-4 * s.pz.sum - 4, 2 * s.pu.sum + 1⟩

theorem summarySharpE_toReal (s : SeedSummary) :
    (summarySharpE s).toReal = 2 * (summaryD s).toReal - (4 - φ) := by
  unfold summarySharpE summaryD ZPhi.toReal
  dsimp only
  push_cast
  ring

theorem sharp_const_eq : (4 - φ) / 2 = (7 - Real.sqrt 5) / 4 := by
  unfold φ; ring

theorem sharp_exp_const_eq : 1 + φ / 2 = (5 + Real.sqrt 5) / 4 := by
  unfold φ; ring

/-- Bounded-branch checker allowing BOTH `K > 0` and exact extremal `K = 0` (`Λ E_{j+1} = E_j`). -/
def residueBddNonnegCheck (e0 e1 e2 e3 : ZPhi) : Bool :=
  let r0 := lamZPhi * (e2 - e1) - (e1 - e0)
  let r1 := lamZPhi * (e3 - e2) - (e2 - e1)
  let k := lamZPhi * e1 - e0
  decide (r0.a = 0) && decide (r0.b = 0) &&
  decide (r1.a = 0) && decide (r1.b = 0) &&
  zphiPosFast e0 &&
  (zphiPosFast k || (decide (k.a = 0) && decide (k.b = 0)))

/-- Pure-`ℤ[φ]` 26-step sharp-deficit verifier for `summarySharpE`. -/
def checkSummarySharp (s₀ : SeedSummary) : Bool :=
  let orb := collectSummaries 26 s₀
  match orb[2]?, orb[8]? with
  | some s2, some s8 =>
    CtxState.beq s8.st s2.st &&
    let es := orb.map summarySharpE
    zphiPosFast (es.getD 0 ⟨0, 0⟩) &&
    zphiPosFast (es.getD 1 ⟨0, 0⟩) &&
    allTR (fun r =>
      let e0 := es.getD (2 + r) ⟨0, 0⟩
      let e1 := es.getD (8 + r) ⟨0, 0⟩
      let e2 := es.getD (14 + r) ⟨0, 0⟩
      let e3 := es.getD (20 + r) ⟨0, 0⟩
      checkResidueInc e0 e1 e2 e3 || residueBddNonnegCheck e0 e1 e2 e3)
      [0, 1, 2, 3, 4, 5]
  | _, _ => false

def checkListBin64Sharp (l : List SeedSummary) : Bool :=
  allRangeBin (fun i =>
    match l[i]? with
    | some s => checkSummarySharp s
    | none => true) 6 0

theorem seedBuckets_sharp_s0 (y z : Sym5) : checkListBin64Sharp (seedBucket .s0 y z) = true := by
  cases y <;> cases z <;> rfl

theorem seedBuckets_sharp_s1 (y z : Sym5) : checkListBin64Sharp (seedBucket .s1 y z) = true := by
  cases y <;> cases z <;> rfl

theorem seedBuckets_sharp_s2 (y z : Sym5) : checkListBin64Sharp (seedBucket .s2 y z) = true := by
  cases y <;> cases z <;> rfl

theorem seedBuckets_sharp_s3 (y z : Sym5) : checkListBin64Sharp (seedBucket .s3 y z) = true := by
  cases y <;> cases z <;> rfl

theorem seedBuckets_sharp_s4 (y z : Sym5) : checkListBin64Sharp (seedBucket .s4 y z) = true := by
  cases y <;> cases z <;> rfl

theorem all_seedBuckets_sharp (x y z : Sym5) {s : SeedSummary}
    (hs : s ∈ seedBucket x y z) : checkSummarySharp s = true := by
  have hbin : checkListBin64Sharp (seedBucket x y z) = true := by
    cases x
    · exact seedBuckets_sharp_s0 y z
    · exact seedBuckets_sharp_s1 y z
    · exact seedBuckets_sharp_s2 y z
    · exact seedBuckets_sharp_s3 y z
    · exact seedBuckets_sharp_s4 y z
  have hlt64 : (seedBucket x y z).length < 64 :=
    Nat.blt_eq.mp (seedBucket_len_lt_64 x y z)
  rcases List.mem_iff_getElem.mp hs with ⟨i, hi, rfl⟩
  have hall := (allRangeBin_iff _ 6 0).mp hbin i (by omega)
  simp only [Nat.zero_add, List.getElem?_eq_getElem hi] at hall
  exact hall

/-! ## Section 2: Soundness of `checkSummarySharp` & Large-Period Bound (`p₀ ≥ 41`) -/

theorem residueBddNonneg_sound {E : ℕ → ZPhi}
    (hrec : ∀ j : ℕ, E (j + 4) - ⟨20, 0⟩ * E (j + 3) + ⟨38, 0⟩ * E (j + 2) -
      ⟨20, 0⟩ * E (j + 1) + E j = 0)
    (hchk : residueBddNonnegCheck (E 0) (E 1) (E 2) (E 3) = true) :
    ∀ j : ℕ, 0 < (E j).toReal := by
  unfold residueBddNonnegCheck at hchk
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, zphiPosFast_eq_isPos,
    ZPhi.isPos_iff_toReal_pos] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hr0a, hr0b⟩, hr1a⟩, hr1b⟩, he0⟩, hk_nonneg⟩
  have hR0 : lamZPhi * (E 2 - E 1) - (E 1 - E 0) = 0 := ZPhi.ext hr0a hr0b
  have hR1 : lamZPhi * (E 3 - E 2) - (E 2 - E 1) = 0 := ZPhi.ext hr1a hr1b
  have hinv := residueBdd_inv hrec hR0 hR1
  have hK_ge : 0 ≤ (lamZPhi * E 1 - E 0).toReal := by
    rcases hk_nonneg with hpos | ⟨hka, hkb⟩
    · exact le_of_lt hpos
    · have hk0 : lamZPhi * E 1 - E 0 = 0 := ZPhi.ext hka hkb
      rw [hk0, ZPhi.toReal_zero]
  have hlam_pos : 0 < lamZPhi.toReal := by
    simp only [lamZPhi, ZPhi.toReal]; push_cast; linarith [phi_pos]
  intro j
  induction j with
  | zero => exact he0
  | succ j ih =>
    have hstep := congrArg ZPhi.toReal (hinv j)
    rw [ZPhi.toReal_sub, ZPhi.toReal_mul] at hstep
    have hpos_prod : 0 < lamZPhi.toReal * (E (j + 1)).toReal := by linarith
    exact (mul_pos_iff_of_pos_left hlam_pos).mp hpos_prod

theorem checkSummarySharp_sound {s₀ : SeedSummary} (h : checkSummarySharp s₀ = true) :
    ∀ k : ℕ, 0 < (summarySharpE ((stepSummary^[k]) s₀)).toReal := by
  unfold checkSummarySharp at h
  generalize horb : collectSummaries 26 s₀ = orb at h
  have h2 : orb[2]? = some ((stepSummary^[2]) s₀) := by
    rw [← horb]; exact collectSummaries_getElem? 26 s₀ 2 (by omega)
  have h8 : orb[8]? = some ((stepSummary^[8]) s₀) := by
    rw [← horb]; exact collectSummaries_getElem? 26 s₀ 8 (by omega)
  dsimp only at h
  rw [h2, h8] at h
  dsimp only at h
  rw [allTR_eq_all] at h
  simp only [Bool.and_eq_true, CtxState.beq_iff_eq, zphiPosFast_eq_isPos,
    ZPhi.isPos_iff_toReal_pos] at h
  rcases h with ⟨hst8, ⟨⟨he0_pos, he1_pos⟩, hall_r⟩⟩
  let s (n : ℕ) := (stepSummary^[n]) s₀
  have hes_at : ∀ n (hn : n < 26),
      (orb.map summarySharpE).getD n ⟨0, 0⟩ = summarySharpE (s n) := by
    intro n hn
    rw [← horb, List.getD_eq_getElem?_getD, List.getElem?_map,
        collectSummaries_getElem? 26 s₀ n hn]
    rfl
  -- State 6-periodicity for n ≥ 2
  have hst_per : ∀ m : ℕ, (s (2 + m + 6)).st = (s (2 + m)).st := by
    intro m
    induction m with
    | zero => exact hst8
    | succ m ih =>
      have h1 : s (2 + (m + 1) + 6) = stepSummary (s (2 + m + 6)) := by
        have hidx : 2 + (m + 1) + 6 = (2 + m + 6) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      have h2' : s (2 + (m + 1)) = stepSummary (s (2 + m)) := by
        have hidx : 2 + (m + 1) = (2 + m) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      rw [h1, h2']
      dsimp only [stepSummary]
      rw [ih]
  have hst_per_j : ∀ r j : ℕ, (s (2 + r + 6 * j)).st = (s (2 + r)).st := by
    intro r j
    induction j with
    | zero => simp
    | succ j ih =>
      have hidx : 2 + r + 6 * (j + 1) = 2 + (r + 6 * j) + 6 := by omega
      rw [hidx, hst_per (r + 6 * j)]
      have hidx2 : 2 + (r + 6 * j) = 2 + r + 6 * j := by omega
      rw [hidx2, ih]
  have h6_affine : ∀ r : ℕ, ∃ C_r : Vec5Z, ∀ j : ℕ,
      (s (2 + r + 6 * (j + 1))).pu = stepM6Z ((s (2 + r + 6 * j)).pu) ∧
      (s (2 + r + 6 * (j + 1))).pz = Vec5Z.add (stepM6Z ((s (2 + r + 6 * j)).pz)) C_r := by
    intro r
    let st_at (t : ℕ) := (s (2 + r + t)).st
    have hst_shift : ∀ j t : ℕ, (s (2 + r + 6 * j + t)).st = st_at t := by
      intro j t
      have hidx : 2 + r + 6 * j + t = 2 + (r + t) + 6 * j := by omega
      rw [hidx, hst_per_j (r + t) j]
      dsimp [st_at]; congr 2; omega
    let stepPz (t : ℕ) (v : Vec5Z) : Vec5Z :=
      Vec5Z.add (stepMZ v) (parikhSym (phiStepCtx (st_at t)).2)
    let f6 (v : Vec5Z) : Vec5Z :=
      stepPz 5 (stepPz 4 (stepPz 3 (stepPz 2 (stepPz 1 (stepPz 0 v)))))
    refine ⟨f6 Vec5Z.zero, fun j => ?_⟩
    have hstep1 : ∀ t : ℕ,
        s (2 + r + 6 * j + (t + 1)) = stepSummary (s (2 + r + 6 * j + t)) := by
      intro t
      have hidx : 2 + r + 6 * j + (t + 1) = (2 + r + 6 * j + t) + 1 := by omega
      rw [hidx]; exact Function.iterate_succ_apply' _ _ _
    have hs_step : ∀ t : ℕ,
        (s (2 + r + 6 * j + (t + 1))).pu = stepMZ ((s (2 + r + 6 * j + t)).pu) ∧
        (s (2 + r + 6 * j + (t + 1))).pz = stepPz t ((s (2 + r + 6 * j + t)).pz) := by
      intro t
      rw [hstep1 t]; dsimp only [stepSummary, stepPz]; rw [hst_shift j t]; exact ⟨rfl, rfl⟩
    have hidx6 : 2 + r + 6 * (j + 1) = 2 + r + 6 * j + 6 := by omega
    rw [hidx6]
    have hp0 := (hs_step 0).1; have hz0 := (hs_step 0).2
    have hp1 := (hs_step 1).1; have hz1 := (hs_step 1).2
    have hp2 := (hs_step 2).1; have hz2 := (hs_step 2).2
    have hp3 := (hs_step 3).1; have hz3 := (hs_step 3).2
    have hp4 := (hs_step 4).1; have hz4 := (hs_step 4).2
    have hp5 := (hs_step 5).1; have hz5 := (hs_step 5).2
    simp only [Nat.add_zero] at hp0 hz0
    constructor
    · rw [hp5, hp4, hp3, hp2, hp1, hp0]; rfl
    · rw [hz5, hz4, hz3, hz2, hz1, hz0]
      exact step6_affine_eq _ _ _ _ _ _ _
  intro k
  by_cases hk0 : k = 0
  · subst hk0; rwa [hes_at 0 (by omega)] at he0_pos
  · by_cases hk1 : k = 1
    · subst hk1; rwa [hes_at 1 (by omega)] at he1_pos
    · let r := (k - 2) % 6
      let j := (k - 2) / 6
      have hr_lt : r < 6 := Nat.mod_lt _ (by omega)
      have hk_eq : k = 2 + r + 6 * j := by
        have := Nat.div_add_mod (k - 2) 6; omega
      rw [hk_eq]
      rcases h6_affine r with ⟨C_r, haff_r⟩
      let E (n : ℕ) : ZPhi := summarySharpE (s (2 + r + 6 * n))
      have hpu_step : ∀ n : ℕ,
          (s (2 + r + 6 * (n + 1))).pu = Vec5Z.add (stepM6Z ((s (2 + r + 6 * n)).pu)) Vec5Z.zero := by
        intro n
        rw [(haff_r n).1]
        cases stepM6Z (s (2 + r + 6 * n)).pu
        simp [Vec5Z.add, Vec5Z.zero]
      have hpz_step : ∀ n : ℕ,
          (s (2 + r + 6 * (n + 1))).pz = Vec5Z.add (stepM6Z ((s (2 + r + 6 * n)).pz)) C_r :=
        fun n => (haff_r n).2
      -- Adding a constant (-4, 1) preserves the 4th-order recurrence because 1 - 20 + 38 - 20 + 1 = 0!
      have hE_rec : ∀ n : ℕ, E (n + 4) - ⟨20, 0⟩ * E (n + 3) + ⟨38, 0⟩ * E (n + 2) -
          ⟨20, 0⟩ * E (n + 1) + E n = 0 := by
        intro n
        have hpu_r := affine_stepM6Z_sum_rec
          (v := fun m => (s (2 + r + 6 * m)).pu) (C := Vec5Z.zero) hpu_step n
        have hpz_r := affine_stepM6Z_sum_rec
          (v := fun m => (s (2 + r + 6 * m)).pz) (C := C_r) hpz_step n
        dsimp only [E, summarySharpE]
        ext
        · simp only [ZPhi.add_a, ZPhi.sub_a, ZPhi.mul_a, ZPhi.zero_a]; linarith
        · simp only [ZPhi.add_b, ZPhi.sub_b, ZPhi.mul_b, ZPhi.zero_b]; linarith
      have hr_mem : r ∈ ([0, 1, 2, 3, 4, 5] : List ℕ) := by
        have hrc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
        rcases hrc with h | h | h | h | h | h <;> simp [h]
      have hr_cert := List.all_eq_true.mp hall_r r hr_mem
      rw [hes_at (2 + r) (by omega), hes_at (8 + r) (by omega),
          hes_at (14 + r) (by omega), hes_at (20 + r) (by omega)] at hr_cert
      have he0_eq : s (2 + r) = s (2 + r + 6 * 0) := rfl
      have he1_eq : s (8 + r) = s (2 + r + 6 * 1) := congrArg s (by omega)
      have he2_eq : s (14 + r) = s (2 + r + 6 * 2) := congrArg s (by omega)
      have he3_eq : s (20 + r) = s (2 + r + 6 * 3) := congrArg s (by omega)
      rw [he0_eq, he1_eq, he2_eq, he3_eq] at hr_cert
      rw [Bool.or_eq_true] at hr_cert
      rcases hr_cert with hinc | hbdd
      · exact residueInc_sound hE_rec hinc j
      · exact residueBddNonneg_sound hE_rec hbdd j

/-- Sharp bound for large-period seeds `p₀ ≥ 41`: `summarySharpE > 0` for all `k : ℕ`. -/
theorem seed_sharp_of_p_ge_41 {i₀ p₀ m₀ : ℕ}
    (hp41 : 41 ≤ p₀) (hm2 : m₀ ≤ 2) (k : ℕ) :
    0 < (summarySharpE ((stepSummary^[k]) (runSummary i₀ p₀ m₀))).toReal := by
  rw [summarySharpE_toReal]
  cases k with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    unfold summaryD ZPhi.toReal
    dsimp only
    rcases runSummary_sums i₀ p₀ m₀ with ⟨hpu, hpz⟩
    rw [hpu, hpz]
    push_cast
    have hp41R : (41 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp41
    have hm2R : (m₀ : ℝ) ≤ 2 := by exact_mod_cast hm2
    have h1 : 1 < φ := one_lt_phi
    nlinarith
  | succ k' =>
    let k := k' + 1
    let s (n : ℕ) := (stepSummary^[n]) (runSummary i₀ p₀ m₀)
    have hprops : ∀ n : ℕ,
        (s n).pu.Nonneg ∧ (s n).pz.Nonneg ∧
        nuVec (s n).pu = φ ^ n * nuVec (s 0).pu ∧
        nuVec (s n).pz + φ ^ 2 ≤ φ ^ n * (2 + φ ^ 2) := by
      intro n
      induction n with
      | zero =>
        dsimp [s, runSummary]
        have hpu_nn := parikhSym_nonneg (symSlice i₀ p₀)
        have hpz_nn := parikhSym_nonneg (symSlice (i₀ + p₀) m₀)
        have hpz_le2 : nuVec (parikhSym (symSlice (i₀ + p₀) m₀)) ≤ 2 := by
          have hb := (nuVec_bounds_of_nonneg hpz_nn).2
          rw [parikhSym_sum_eq_length, symSlice_length] at hb
          have hmR : ((m₀ : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hm2
          linarith
        exact ⟨hpu_nn, hpz_nn, by simp, by simp; linarith⟩
      | succ n ih =>
        rcases ih with ⟨hpu_nn, hpz_nn, hpu_eq, hpz_le⟩
        have hsn : s (n + 1) = stepSummary (s n) := Function.iterate_succ_apply' _ _ _
        rw [hsn]; dsimp only [stepSummary]
        refine ⟨stepMZ_nonneg hpu_nn,
          vec5Z_add_nonneg (stepMZ_nonneg hpz_nn) (parikhSym_nonneg _), ?_, ?_⟩
        · rw [nuVec_stepMZ, hpu_eq]; ring
        · rw [nuVec_add, nuVec_stepMZ]
          have hextra := nuVec_extra_le_phi (s n).st
          have hstep : φ * nuVec (s n).pz + nuVec (parikhSym (phiStepCtx (s n).st).2) + φ ^ 2 ≤
              φ * (nuVec (s n).pz + φ ^ 2) := by nlinarith [phi_sq, phi_pos]
          have hmul : φ * (nuVec (s n).pz + φ ^ 2) ≤ φ * (φ ^ n * (2 + φ ^ 2)) :=
            mul_le_mul_of_nonneg_left hpz_le (le_of_lt phi_pos)
          calc
            φ * nuVec (s n).pz + nuVec (parikhSym (phiStepCtx (s n).st).2) + φ ^ 2
              ≤ φ * (φ ^ n * (2 + φ ^ 2)) := le_trans hstep hmul
            _ = φ ^ (n + 1) * (2 + φ ^ 2) := by ring
    rcases hprops k with ⟨hpu_nn, hpz_nn, hpu_eq, hpz_le⟩
    rcases nuVec_bounds_of_nonneg hpu_nn with ⟨_, hnu_le_pk⟩
    rcases nuVec_bounds_of_nonneg hpz_nn with ⟨hmk_le_nu, _⟩
    rcases nuVec_bounds_of_nonneg (parikhSym_nonneg (symSlice i₀ p₀)) with ⟨hp0_le_nu0, _⟩
    rw [parikhSym_sum_eq_length, symSlice_length] at hp0_le_nu0
    have hphi_pos : 0 < φ := phi_pos
    have hpow_pos : 0 < φ ^ k := pow_pos hphi_pos k
    have hsq_pos : 0 < φ ^ 2 := by positivity
    have hpk_lb : φ ^ k * (p₀ : ℝ) ≤ φ ^ 2 * ((s k).pu.sum : ℝ) := by
      have h1 : φ ^ k * ((p₀ : ℤ) : ℝ) ≤ φ ^ k * (φ ^ 2 * nuVec (s 0).pu) :=
        mul_le_mul_of_nonneg_left hp0_le_nu0 (le_of_lt hpow_pos)
      have h2 : φ ^ k * (φ ^ 2 * nuVec (s 0).pu) = φ ^ 2 * nuVec (s k).pu := by
        rw [hpu_eq]; ring
      have h3 : φ ^ 2 * nuVec (s k).pu ≤ φ ^ 2 * ((s k).pu.sum : ℝ) :=
        mul_le_mul_of_nonneg_left hnu_le_pk (le_of_lt hsq_pos)
      push_cast at h1; linarith
    have hmk_ub : ((s k).pz.sum : ℝ) < φ ^ k * (φ ^ 2 * (2 + φ ^ 2)) := by
      have hnu_lt : nuVec (s k).pz < φ ^ k * (2 + φ ^ 2) := by linarith [hsq_pos]
      have hmul : φ ^ 2 * nuVec (s k).pz < φ ^ 2 * (φ ^ k * (2 + φ ^ 2)) :=
        mul_lt_mul_of_pos_left hnu_lt hsq_pos
      linarith
    -- Since k = k' + 1 ≥ 1, φ ^ k ≥ φ, so φ * φ ^ k ≥ φ ^ 2!
    have hpow_ge_phi : φ ≤ φ ^ k := by
      have h1 : (1 : ℝ) ≤ φ ^ k' := one_le_pow₀ (le_of_lt one_lt_phi)
      calc
        φ = φ * 1 := by ring
        _ ≤ φ * φ ^ k' := mul_le_mul_of_nonneg_left h1 (le_of_lt hphi_pos)
        _ = φ ^ (k' + 1) := by ring
    have hsimp : 2 * φ ^ 3 * (2 + φ ^ 2) = 18 * φ + 10 := by
      calc
        2 * φ ^ 3 * (2 + φ ^ 2) = 2 * (2 * φ + 1) * (2 + (φ + 1)) := by rw [phi_cube, phi_sq]
        _ = 4 * φ ^ 2 + 14 * φ + 6 := by ring
        _ = 4 * (φ + 1) + 14 * φ + 6 := by rw [phi_sq]
        _ = 18 * φ + 10 := by ring
    -- Key sharp numerical inequality: 2 * (31 - 18 * φ) > 4 - φ (⇔ 58 > 35 * φ ⇔ 81 > 35 * √5 ⇔ 6561 > 6125)
    have hgap : (4 - φ) / 2 < (p₀ : ℝ) - (18 * φ + 10) := by
      have hp0R : (41 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp41
      have h35s5 : 35 * Real.sqrt 5 < 81 := by
        have hsq5 : (35 * Real.sqrt 5) ^ 2 < 81 ^ 2 := by
          rw [mul_pow, sqrt5_sq]; norm_num
        nlinarith [sqrt5_pos]
      have hnum : (4 - φ) / 2 < 31 - 18 * φ := by unfold φ; linarith
      linarith
    have hgap_pos : 0 < (p₀ : ℝ) - (18 * φ + 10) := by
      have hlt2 : φ < 2 := phi_lt_two
      linarith
    have hdiff_gt : φ ^ 2 * ((4 - φ) / 2) <
        φ ^ 2 * (φ * ((s k).pu.sum : ℝ) - 2 * ((s k).pz.sum : ℝ)) := by
      have h1 : φ ^ 2 * (2 * ((s k).pz.sum : ℝ)) < φ * (φ ^ k * (18 * φ + 10)) := by
        calc
          φ ^ 2 * (2 * ((s k).pz.sum : ℝ))
            < φ ^ 2 * (2 * (φ ^ k * (φ ^ 2 * (2 + φ ^ 2)))) := by nlinarith
          _ = φ * (φ ^ k * (2 * φ ^ 3 * (2 + φ ^ 2))) := by ring
          _ = φ * (φ ^ k * (18 * φ + 10)) := by rw [hsimp]
      have h2 : φ * (φ ^ k * (p₀ : ℝ)) ≤ φ ^ 2 * (φ * ((s k).pu.sum : ℝ)) := by
        calc
          φ * (φ ^ k * (p₀ : ℝ))
            ≤ φ * (φ ^ 2 * ((s k).pu.sum : ℝ)) :=
              mul_le_mul_of_nonneg_left hpk_lb (le_of_lt hphi_pos)
          _ = φ ^ 2 * (φ * ((s k).pu.sum : ℝ)) := by ring
      have h3 : φ ^ 2 * ((4 - φ) / 2) < φ * (φ ^ k * ((p₀ : ℝ) - (18 * φ + 10))) := by
        have hphi2_le : φ ^ 2 ≤ φ * φ ^ k := by nlinarith
        calc
          φ ^ 2 * ((4 - φ) / 2)
            < φ ^ 2 * ((p₀ : ℝ) - (18 * φ + 10)) :=
              mul_lt_mul_of_pos_left hgap hsq_pos
          _ ≤ (φ * φ ^ k) * ((p₀ : ℝ) - (18 * φ + 10)) :=
              mul_le_mul_of_nonneg_right hphi2_le (le_of_lt hgap_pos)
          _ = φ * (φ ^ k * ((p₀ : ℝ) - (18 * φ + 10))) := by ring
      linarith
    have hD_gt : (4 - φ) / 2 < φ * ((s k).pu.sum : ℝ) - 2 * ((s k).pz.sum : ℝ) := by
      nlinarith
    change 0 < 2 * (summaryD (s k)).toReal - (4 - φ)
    unfold summaryD ZPhi.toReal
    dsimp only
    push_cast
    linarith

/-- Sharp bound for short seeds `1 ≤ p₀ ≤ 40` via `seedBucket` + `all_seedBuckets_sharp`. -/
theorem seed_sharp_of_p_le_40 {i₀ p₀ m₀ : ℕ}
    (hrun : ConcreteRun i₀ p₀ m₀) (hp40 : p₀ ≤ 40) (hm0 : m₀ = 1 ∨ m₀ = 2) (k : ℕ) :
    0 < (summarySharpE ((stepSummary^[k]) (runSummary i₀ p₀ m₀))).toReal := by
  rcases hrun with ⟨hi10, hp1, hper, hmisL, hmisR⟩
  have hlen48 : p₀ + m₀ + 6 ≤ 48 := by omega
  rcases symSlice_in_g10_pair (i₀ - 3) (p₀ + m₀ + 6) hlen48 with
    ⟨a, b, o, hmem, ho256, hfit, hslice⟩
  let full := g10Val a ++ g10Val b
  let suf := full.drop o
  have hsuf_len : p₀ + m₀ + 6 ≤ suf.length := by
    dsimp [suf, full]; rw [List.length_drop]; omega
  have hsuf_at : ∀ r (hr : r < p₀ + m₀ + 6), suf[r]? = some (b5Sym (i₀ - 3 + r)) := by
    intro r hr
    have h1 := congrArg (fun l : List Sym5 => l[r]?) hslice
    rw [List.getElem?_eq_getElem (by simp [hr]), symSlice_getElem,
        List.getElem?_take_of_lt hr] at h1
    exact h1.symm
  have hsum_eq : runSummary i₀ p₀ m₀ = summaryOfSuffix p₀ m₀ suf := by
    have hw3 : ∀ off (hoff : off + 3 ≤ p₀ + m₀ + 6),
        word3OfList (suf.drop off) = symWord3At (i₀ - 3 + off) := by
      intro off hoff
      have hdl : 3 ≤ (suf.drop off).length := by rw [List.length_drop]; omega
      rw [word3OfList_eq_of_ge3 hdl]
      simp only [List.getElem_drop, symWord3At, Nat.add_zero]
      have g0 := hsuf_at off (by omega)
      have g1 := hsuf_at (off + 1) (by omega)
      have g2 := hsuf_at (off + 2) (by omega)
      rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at g0 g1 g2
      rw [g0, g1, g2]; simp only [Nat.add_assoc]
    have htake_eq : ∀ off len (hlen : off + len ≤ p₀ + m₀ + 6),
        (suf.drop off).take len = symSlice (i₀ - 3 + off) len := by
      intro off len hlen
      apply List.ext_getElem
      · rw [List.length_take, List.length_drop, symSlice_length]; omega
      · intro r hr1 hr2
        rw [symSlice_length] at hr2
        rw [List.getElem_take, List.getElem_drop, symSlice_getElem]
        have g := hsuf_at (off + r) (by omega)
        rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at g
        rw [g]; congr 1; omega
    unfold runSummary summaryOfSuffix runCtxState
    have hx := hw3 0 (by omega); simp only [List.drop_zero, Nat.add_zero] at hx
    have hy := hw3 p₀ (by omega)
    have hy_idx : i₀ - 3 + p₀ = i₀ + p₀ - 3 := by omega
    rw [hy_idx] at hy
    have hs := hw3 (p₀ + m₀ + 3) (by omega)
    have hs_idx : i₀ - 3 + (p₀ + m₀ + 3) = i₀ + p₀ + m₀ := by omega
    rw [hs_idx] at hs
    have ht := hw3 (m₀ + 3) (by omega)
    have ht_idx : i₀ - 3 + (m₀ + 3) = i₀ + m₀ := by omega
    rw [ht_idx] at ht
    have hu := htake_eq 3 p₀ (by omega)
    have hu_idx : i₀ - 3 + 3 = i₀ := by omega
    rw [hu_idx] at hu
    have hz := htake_eq (3 + p₀) m₀ (by omega)
    have hz_idx : i₀ - 3 + (3 + p₀) = i₀ + p₀ := by omega
    rw [hz_idx] at hz
    rw [hx, hy, hs, ht, hu, hz]
  have hcov_pair := List.all_eq_true.mp all_twoFactor_seeds_in_buckets (a, b) hmem
  have hcov_suf := (scanDrops256_iff checkSuffixAllPM full).mp hcov_pair o ho256
  unfold checkSuffixAllPM at hcov_suf
  have hpm_raw := (allRangeBin_iff _ 6 0).mp hcov_suf (p₀ - 1) (by omega)
  have hblt : Nat.blt (p₀ - 1) 40 = true := Nat.blt_eq.mpr (by omega)
  have hp0_succ : p₀ - 1 + 1 = p₀ := by omega
  simp only [Nat.zero_add, hblt, ↓reduceIte, hp0_succ, Bool.and_eq_true] at hpm_raw
  have hseed_chk : checkSeedAtSuffix p₀ m₀ suf = true := by
    rcases hm0 with rfl | rfl
    · exact hpm_raw.1
    · exact hpm_raw.2
  unfold checkSeedAtSuffix at hseed_chk
  have hg_3 : symOptEq suf[3]? suf[3 + p₀]? = true := by
    rw [hsuf_at 3 (by omega), hsuf_at (3 + p₀) (by omega)]
    have h0 := hper 0 (by omega)
    have idx1 : i₀ - 3 + 3 = i₀ := by omega
    have idx2 : i₀ - 3 + (3 + p₀) = i₀ + 0 + p₀ := by omega
    rw [idx1, idx2]; exact (Sym5.beq_iff_eq _ _).mpr h0
  have hg_len : hasLenAtLeast (p₀ + m₀ + 6) suf = true := (hasLenAtLeast_iff _ _).mpr hsuf_len
  have hg_m : (Nat.beq m₀ 1 || symOptEq suf[4]? suf[4 + p₀]?) = true := by
    rcases hm0 with rfl | rfl
    · rfl
    · simp only [Nat.beq, Bool.false_or]
      rw [hsuf_at 4 (by omega), hsuf_at (4 + p₀) (by omega)]
      have h1 := hper 1 (by omega)
      have idx1 : i₀ - 3 + 4 = i₀ + 1 := by omega
      have idx2 : i₀ - 3 + (4 + p₀) = i₀ + 1 + p₀ := by omega
      rw [idx1, idx2]; exact (Sym5.beq_iff_eq _ _).mpr h1
  have hg_L : symOptNe suf[2]? suf[2 + p₀]? = true := by
    rw [hsuf_at 2 (by omega), hsuf_at (2 + p₀) (by omega)]
    have idx1 : i₀ - 3 + 2 = i₀ - 1 := by omega
    have idx2 : i₀ - 3 + (2 + p₀) = i₀ + p₀ - 1 := by omega
    rw [idx1, idx2]; simp only [symOptNe, Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr (mt (Sym5.beq_iff_eq _ _).mp hmisL)
  have hg_R : symOptNe suf[3 + p₀ + m₀]? suf[3 + m₀]? = true := by
    rw [hsuf_at (3 + p₀ + m₀) (by omega), hsuf_at (3 + m₀) (by omega)]
    have idx1 : i₀ - 3 + (3 + p₀ + m₀) = i₀ + p₀ + m₀ := by omega
    have idx2 : i₀ - 3 + (3 + m₀) = i₀ + m₀ := by omega
    rw [idx1, idx2]; simp only [symOptNe, Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr (mt (Sym5.beq_iff_eq _ _).mp hmisR)
  simp only [hg_3, hg_len, hg_m, hg_L, hg_R, Bool.and_self, ↓reduceIte] at hseed_chk
  rw [← hsum_eq] at hseed_chk
  unfold inSeedBuckets at hseed_chk
  have hmem_bkt := (memSummaryList_iff _ _).mp hseed_chk
  have hvalid_s0 := all_seedBuckets_sharp _ _ _ hmem_bkt
  exact checkSummarySharp_sound hvalid_s0 k

/-! ## Section 3: Universal Sharp Second-Order Deficit & Exponent Bounds -/

theorem concreteRun_sharp_deficit_gt {i p m : ℕ} (hrun : ConcreteRun i p m) :
    (7 - Real.sqrt 5) / 4 < φ * (p : ℝ) - 2 * (m : ℝ) := by
  by_cases hm0 : m = 0
  · subst hm0
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hrun.2.1
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    have hphi_gt : (7 - Real.sqrt 5) / 4 < φ := by
      unfold φ; linarith [two_lt_sqrt5]
    nlinarith [phi_pos]
  · rcases concreteRun_from_seed p i m hrun (by omega) with ⟨k, i₀, p₀, m₀, hseed, hm0_12, hiter⟩
    have hE_pos : 0 < (summarySharpE ((stepSummary^[k]) (runSummary i₀ p₀ m₀))).toReal := by
      by_cases hp40 : p₀ ≤ 40
      · exact seed_sharp_of_p_le_40 hseed hp40 hm0_12 k
      · exact seed_sharp_of_p_ge_41 (by omega) (by omega) k
    rw [hiter, summarySharpE_toReal] at hE_pos
    rcases runSummary_sums i p m with ⟨hpu, hpz⟩
    unfold summaryD ZPhi.toReal at hE_pos
    dsimp only at hE_pos
    rw [hpu, hpz] at hE_pos
    push_cast at hE_pos
    have hconst := sharp_const_eq
    linarith

/-- **Sharp Universal Deficit Lower Bound (`b5_sharp_deficit_gt`)**:
For EVERY factor `w` of `b_5` and EVERY period `p ≥ 1` of `w`,
`(7 - √5) / 4 < φ * p - 2 * (|w| - p)` strictly (never attained). -/
theorem b5_sharp_deficit_gt (w : List (Fin 5)) (p : ℕ)
    (hfac : IsFactorInf w b5) (hp : 1 ≤ p) (hper : IsPeriod w p) :
    (7 - Real.sqrt 5) / 4 < φ * (p : ℝ) - 2 * ((w.length : ℝ) - (p : ℝ)) := by
  by_cases hle : w.length ≤ p
  · have hleR : (w.length : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
    have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hphi_gt : (7 - Real.sqrt 5) / 4 < φ := by
      unfold φ; linarith [two_lt_sqrt5]
    nlinarith [phi_pos]
  · have hlt : p < w.length := by omega
    let m₀ := w.length - p
    have hm₀_pos : 1 ≤ m₀ := by omega
    rcases hfac with ⟨pos₀, hocc₀⟩
    rcases exists_sym_occ_ge pos₀ w.length (maxOverlap p + 20) with ⟨q, hq_ge, hq_eq⟩
    have hper_q : ∀ j < m₀, b5Sym (q + j) = b5Sym (q + j + p) := by
      intro j hj
      have hj1 : j < w.length := by omega
      have hj2 : j + p < w.length := by omega
      have hq1 : b5Sym (q + j) = b5Sym (pos₀ + j) := by
        have hget := congrArg (fun l => l[j]?) hq_eq
        rw [List.getElem?_eq_getElem (by rw [symSlice_length]; exact hj1),
            List.getElem?_eq_getElem (by rw [symSlice_length]; exact hj1),
            symSlice_getElem, symSlice_getElem] at hget
        exact Option.some.inj hget
      have hq2 : b5Sym (q + j + p) = b5Sym (pos₀ + (j + p)) := by
        have hget := congrArg (fun l => l[j + p]?) hq_eq
        rw [List.getElem?_eq_getElem (by rw [symSlice_length]; exact hj2),
            List.getElem?_eq_getElem (by rw [symSlice_length]; exact hj2),
            symSlice_getElem, symSlice_getElem] at hget
        have hidx : q + (j + p) = q + j + p := by omega
        rw [hidx] at hget
        exact Option.some.inj hget
      rw [hq1, hq2]
      simp only [b5Sym]
      congr 1
      rw [hocc₀ j hj1, hocc₀ (j + p) hj2]
      exact hper j hj2
    rcases extend_to_concreteRun hp hq_ge with ⟨i, r, hrun, hi_le, hq_le_ir⟩
    have hm_le_r : m₀ ≤ r := by
      have hq_plus_m : q + m₀ ≤ i + r := by
        by_contra hlt_ir
        have hlt_ir' : i + r < q + m₀ := by omega
        have hj_lt : i + r - q < m₀ := by omega
        have heq_mis := hper_q (i + r - q) hj_lt
        have hidx1 : q + (i + r - q) = i + r := by omega
        have hidx2 : i + r + p = i + p + r := by omega
        rw [hidx1, hidx2] at heq_mis
        exact hrun.2.2.2.2 heq_mis.symm
      omega
    have hD := concreteRun_sharp_deficit_gt hrun
    have hm_le_rR : (m₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hm_le_r
    have hm0R : (m₀ : ℝ) = (w.length : ℝ) - (p : ℝ) := by
      have hcast : (m₀ : ℝ) + (p : ℝ) = (w.length : ℝ) := by
        exact_mod_cast (show m₀ + p = w.length by omega)
      linarith
    linarith

/-- **Sharp Second-Order Critical Exponent Upper Bound (`b5_exponent_lt_sharp_second_order`)**:
For EVERY factor `w` of `b_5` and EVERY period `p ≥ 1` of `w`,
`|w| / p < (5 + √5) / 4 - (7 - √5) / (8 * p)`. -/
theorem b5_exponent_lt_sharp_second_order (w : List (Fin 5)) (p : ℕ)
    (hfac : IsFactorInf w b5) (hp : 1 ≤ p) (hper : IsPeriod w p) :
    (w.length : ℝ) / (p : ℝ) < (5 + Real.sqrt 5) / 4 - (7 - Real.sqrt 5) / (8 * (p : ℝ)) := by
  have hdef := b5_sharp_deficit_gt w p hfac hp hper
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h8p_pos : (0 : ℝ) < 8 * (p : ℝ) := by positivity
  rw [div_lt_iff₀ hp_pos]
  have hmul : ((5 + Real.sqrt 5) / 4 - (7 - Real.sqrt 5) / (8 * (p : ℝ))) * (p : ℝ) =
      (5 + Real.sqrt 5) / 4 * (p : ℝ) - (7 - Real.sqrt 5) / 8 := by
    field_simp
  rw [hmul]
  have hphi_eq : (5 + Real.sqrt 5) / 4 = 1 + φ / 2 := by unfold φ; ring
  rw [hphi_eq]
  linarith

/-! ## Section 4: Exact Fibonacci Closed Form on `k = 6 + 6j`, Infimum Sharpness & `E*(b_5)` -/

/-- Pure-kernel `rfl` certificate for residue class `r = 4` (`k = 6 + 6*j`) of `extremalSeedSummary`:
`E_0 = ⟨-144, 89⟩`, `E_1 = ⟨-2584, 1597⟩`, `R_0 = R_1 = 0`, `K = Λ E_1 - E_0 = 0`. -/
def checkExtremalSharpCert : Bool :=
  let orb := collectSummaries 26 extremalSeedSummary
  match orb[2]?, orb[8]? with
  | some s2, some s8 =>
    CtxState.beq s8.st s2.st &&
    let es := orb.map summarySharpE
    let e0 := es.getD 6 ⟨0, 0⟩
    let e1 := es.getD 12 ⟨0, 0⟩
    let e2 := es.getD 18 ⟨0, 0⟩
    let e3 := es.getD 24 ⟨0, 0⟩
    decide (e0.a = -144) && decide (e0.b = 89) &&
    decide (e1.a = -2584) && decide (e1.b = 1597) &&
    decide ((lamZPhi * (e2 - e1) - (e1 - e0)).a = 0) &&
    decide ((lamZPhi * (e2 - e1) - (e1 - e0)).b = 0) &&
    decide ((lamZPhi * (e3 - e2) - (e2 - e1)).a = 0) &&
    decide ((lamZPhi * (e3 - e2) - (e2 - e1)).b = 0) &&
    decide ((lamZPhi * e1 - e0).a = 0) &&
    decide ((lamZPhi * e1 - e0).b = 0)
  | _, _ => false

theorem extremalSharp_cert : checkExtremalSharpCert = true := rfl

theorem phi_pow_six_eq : φ ^ 6 = 5 + 8 * φ := by
  have h2 : φ ^ 2 = φ + 1 := phi_sq
  have h3 : φ ^ 3 = 2 * φ + 1 := phi_cube
  calc
    φ ^ 6 = (φ ^ 3) ^ 2 := by ring
    _ = (2 * φ + 1) ^ 2 := by rw [h3]
    _ = 4 * φ ^ 2 + 4 * φ + 1 := by ring
    _ = 4 * (φ + 1) + 4 * φ + 1 := by rw [h2]
    _ = 5 + 8 * φ := by ring

theorem phi_pow_eleven_eq : φ ^ 11 = 55 + 89 * φ := by
  have h2 : φ ^ 2 = φ + 1 := phi_sq
  have h3 : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h6 : φ ^ 6 = 5 + 8 * φ := phi_pow_six_eq
  calc
    φ ^ 11 = φ ^ 6 * φ ^ 3 * φ ^ 2 := by ring
    _ = (5 + 8 * φ) * (2 * φ + 1) * (φ + 1) := by rw [h6, h3, h2]
    _ = 16 * φ ^ 3 + 34 * φ ^ 2 + 23 * φ + 5 := by ring
    _ = 16 * (2 * φ + 1) + 34 * (φ + 1) + 23 * φ + 5 := by rw [h3, h2]
    _ = 55 + 89 * φ := by ring

theorem zphi_144_89_eq_inv_phi_pow_eleven :
    (⟨-144, 89⟩ : ZPhi).toReal = 1 / φ ^ 11 := by
  have hpos : 0 < φ ^ 11 := pow_pos phi_pos 11
  rw [eq_div_iff (ne_of_gt hpos)]
  simp only [ZPhi.toReal]
  push_cast
  rw [phi_pow_eleven_eq]
  have h2 : φ ^ 2 = φ + 1 := phi_sq
  calc
    (-144 + 89 * φ) * (55 + 89 * φ)
      = 7921 * φ ^ 2 - 7921 * φ - 7920 := by ring
    _ = 7921 * (φ + 1) - 7921 * φ - 7920 := by rw [h2]
    _ = 1 := by ring

/-- **Exact Fibonacci Closed Form of the Extremal Deficit Branch (`extremal_deficit_closed_form`)**:
Along `k = 6 + 6 * j` (`j : ℕ`) of the canonical extremal seed `123.010.421`,
`2 * (summaryD (stepSummary^[6 + 6 * j] extremalSeedSummary)).toReal - (4 - φ) = 1 / φ ^ (11 + 6 * j)`. -/
theorem extremal_deficit_closed_form (j : ℕ) :
    (summarySharpE ((stepSummary^[6 + 6 * j]) extremalSeedSummary)).toReal =
    1 / φ ^ (11 + 6 * j) := by
  have hcert := extremalSharp_cert
  unfold checkExtremalSharpCert at hcert
  generalize horb : collectSummaries 26 extremalSeedSummary = orb at hcert
  have h2 : orb[2]? = some ((stepSummary^[2]) extremalSeedSummary) := by
    rw [← horb]; exact collectSummaries_getElem? 26 extremalSeedSummary 2 (by omega)
  have h8 : orb[8]? = some ((stepSummary^[8]) extremalSeedSummary) := by
    rw [← horb]; exact collectSummaries_getElem? 26 extremalSeedSummary 8 (by omega)
  dsimp only at hcert
  rw [h2, h8] at hcert
  dsimp only at hcert
  simp only [Bool.and_eq_true, CtxState.beq_iff_eq, decide_eq_true_eq] at hcert
  rcases hcert with ⟨hst8, ⟨⟨⟨⟨⟨⟨⟨⟨⟨he0a, he0b⟩, he1a⟩, he1b⟩, hR0a⟩, hR0b⟩, hR1a⟩, hR1b⟩, hKa⟩, hKb⟩⟩
  let s (n : ℕ) := (stepSummary^[n]) extremalSeedSummary
  have hes_at : ∀ n (hn : n < 26),
      (orb.map summarySharpE).getD n ⟨0, 0⟩ = summarySharpE (s n) := by
    intro n hn
    rw [← horb, List.getD_eq_getElem?_getD, List.getElem?_map,
        collectSummaries_getElem? 26 extremalSeedSummary n hn]
    rfl
  rw [hes_at 6 (by omega)] at he0a he0b hR0a hR0b hKa hKb
  rw [hes_at 12 (by omega)] at he1a he1b hR0a hR0b hR1a hR1b hKa hKb
  rw [hes_at 18 (by omega)] at hR0a hR0b hR1a hR1b
  rw [hes_at 24 (by omega)] at hR1a hR1b
  have hst_per : ∀ m : ℕ, (s (2 + m + 6)).st = (s (2 + m)).st := by
    intro m
    induction m with
    | zero => exact hst8
    | succ m ih =>
      have h1 : s (2 + (m + 1) + 6) = stepSummary (s (2 + m + 6)) := by
        have hidx : 2 + (m + 1) + 6 = (2 + m + 6) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      have h2' : s (2 + (m + 1)) = stepSummary (s (2 + m)) := by
        have hidx : 2 + (m + 1) = (2 + m) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      rw [h1, h2']; dsimp only [stepSummary]; rw [ih]
  have hst_per_j : ∀ t n : ℕ, (s (2 + t + 6 * n)).st = (s (2 + t)).st := by
    intro t n
    induction n with
    | zero => simp
    | succ n ih =>
      have hidx : 2 + t + 6 * (n + 1) = 2 + (t + 6 * n) + 6 := by omega
      rw [hidx, hst_per (t + 6 * n)]
      have hidx2 : 2 + (t + 6 * n) = 2 + t + 6 * n := by omega
      rw [hidx2, ih]
  let st_at (t : ℕ) := (s (6 + t)).st
  let stepPz (t : ℕ) (v : Vec5Z) : Vec5Z :=
    Vec5Z.add (stepMZ v) (parikhSym (phiStepCtx (st_at t)).2)
  let C4 : Vec5Z :=
    stepPz 5 (stepPz 4 (stepPz 3 (stepPz 2 (stepPz 1 (stepPz 0 Vec5Z.zero)))))
  have haff4 : ∀ n : ℕ,
      (s (6 + 6 * (n + 1))).pu = Vec5Z.add (stepM6Z ((s (6 + 6 * n)).pu)) Vec5Z.zero ∧
      (s (6 + 6 * (n + 1))).pz = Vec5Z.add (stepM6Z ((s (6 + 6 * n)).pz)) C4 := by
    intro n
    have hs_step : ∀ t : ℕ,
        (s (6 + 6 * n + (t + 1))).pu = stepMZ ((s (6 + 6 * n + t)).pu) ∧
        (s (6 + 6 * n + (t + 1))).pz = stepPz t ((s (6 + 6 * n + t)).pz) := by
      intro t
      have h1 : s (6 + 6 * n + (t + 1)) = stepSummary (s (6 + 6 * n + t)) := by
        have hidx : 6 + 6 * n + (t + 1) = (6 + 6 * n + t) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      rw [h1]; dsimp only [stepSummary, stepPz]
      have hsh : (s (6 + 6 * n + t)).st = st_at t := by
        have hidx : 6 + 6 * n + t = 2 + (4 + t) + 6 * n := by omega
        rw [hidx, hst_per_j (4 + t) n]
        dsimp [st_at]; congr 2; omega
      rw [hsh]; exact ⟨rfl, rfl⟩
    have hidx6 : 6 + 6 * (n + 1) = 6 + 6 * n + 6 := by omega
    rw [hidx6]
    have hp0 := (hs_step 0).1; have hz0 := (hs_step 0).2
    have hp1 := (hs_step 1).1; have hz1 := (hs_step 1).2
    have hp2 := (hs_step 2).1; have hz2 := (hs_step 2).2
    have hp3 := (hs_step 3).1; have hz3 := (hs_step 3).2
    have hp4 := (hs_step 4).1; have hz4 := (hs_step 4).2
    have hp5 := (hs_step 5).1; have hz5 := (hs_step 5).2
    simp only [Nat.add_zero] at hp0 hz0
    constructor
    · rw [hp5, hp4, hp3, hp2, hp1, hp0]
      change stepM6Z (s (6 + 6 * n)).pu = Vec5Z.add (stepM6Z (s (6 + 6 * n)).pu) Vec5Z.zero
      cases stepM6Z (s (6 + 6 * n)).pu
      simp [Vec5Z.add, Vec5Z.zero]
    · rw [hz5, hz4, hz3, hz2, hz1, hz0]
      exact step6_affine_eq _ _ _ _ _ _ _
  let E (n : ℕ) : ZPhi := summarySharpE (s (6 + 6 * n))
  have hE_rec : ∀ n : ℕ, E (n + 4) - ⟨20, 0⟩ * E (n + 3) + ⟨38, 0⟩ * E (n + 2) -
      ⟨20, 0⟩ * E (n + 1) + E n = 0 := by
    intro n
    have hpu_r := affine_stepM6Z_sum_rec
      (v := fun m => (s (6 + 6 * m)).pu) (C := Vec5Z.zero) (fun m => (haff4 m).1) n
    have hpz_r := affine_stepM6Z_sum_rec
      (v := fun m => (s (6 + 6 * m)).pz) (C := C4) (fun m => (haff4 m).2) n
    dsimp only [E, summarySharpE]
    ext
    · simp only [ZPhi.add_a, ZPhi.sub_a, ZPhi.mul_a, ZPhi.zero_a]; linarith
    · simp only [ZPhi.add_b, ZPhi.sub_b, ZPhi.mul_b, ZPhi.zero_b]; linarith
  have hE0 : E 0 = summarySharpE (s 6) := congrArg (fun n => summarySharpE (s n)) (by omega)
  have hE1 : E 1 = summarySharpE (s 12) := congrArg (fun n => summarySharpE (s n)) (by omega)
  have hE2 : E 2 = summarySharpE (s 18) := congrArg (fun n => summarySharpE (s n)) (by omega)
  have hE3 : E 3 = summarySharpE (s 24) := congrArg (fun n => summarySharpE (s n)) (by omega)
  have hR0 : lamZPhi * (E 2 - E 1) - (E 1 - E 0) = 0 := by
    rw [hE2, hE1, hE0]; exact ZPhi.ext hR0a hR0b
  have hR1 : lamZPhi * (E 3 - E 2) - (E 2 - E 1) = 0 := by
    rw [hE3, hE2, hE1]; exact ZPhi.ext hR1a hR1b
  have hK0 : lamZPhi * E 1 - E 0 = 0 := by
    rw [hE1, hE0]; exact ZPhi.ext hKa hKb
  have hE0_eq : E 0 = ⟨-144, 89⟩ := by
    rw [hE0]; exact ZPhi.ext he0a he0b
  have hinv := residueBdd_inv hE_rec hR0 hR1
  change (E j).toReal = 1 / φ ^ (11 + 6 * j)
  induction j with
  | zero =>
    rw [hE0_eq, zphi_144_89_eq_inv_phi_pow_eleven]
  | succ j ih =>
    have hstep := congrArg ZPhi.toReal (hinv j)
    rw [hK0, ZPhi.toReal_zero, ZPhi.toReal_sub, ZPhi.toReal_mul] at hstep
    have hlamR : lamZPhi.toReal = φ ^ 6 := by
      simp only [lamZPhi, ZPhi.toReal]; push_cast; exact phi_pow_six_eq.symm
    rw [hlamR, ih] at hstep
    have hlam_pos : 0 < φ ^ 6 := pow_pos phi_pos 6
    have hphi_ne : φ ≠ 0 := ne_of_gt phi_pos
    have hpow_ne : φ ^ (11 + 6 * j) ≠ 0 := ne_of_gt (pow_pos phi_pos _)
    have hpow_eq : φ ^ 6 * φ ^ (11 + 6 * j) = φ ^ (11 + 6 * (j + 1)) := by
      rw [← pow_add]; congr 1; omega
    have hmul : φ ^ 6 * (E (j + 1)).toReal = φ ^ 6 * (1 / φ ^ (11 + 6 * (j + 1))) := by
      rw [← hpow_eq]
      have : φ ^ 6 * (1 / (φ ^ 6 * φ ^ (11 + 6 * j))) = 1 / φ ^ (11 + 6 * j) := by
        field_simp [hphi_ne]
      linarith
    exact mul_left_cancel₀ (ne_of_gt hlam_pos) hmul

/-- **Sharp Second-Order Optimality with Arbitrarily Large Periods (`b5_sharp_second_order_optimal`)**:
For EVERY `ε > 0` and EVERY period lower bound `P₀ : ℕ`, there exist a non-empty factor `w` of
`b_5` and a period `p ≥ max 1 P₀` of `w` such that BOTH:
1. `φ * p - 2 * (|w| - p) < (7 - √5) / 4 + ε`;
2. `(5 + √5) / 4 - (7 - √5 + ε) / (8 * p) < |w| / p`. -/
theorem b5_sharp_second_order_optimal (ε : ℝ) (hε : 0 < ε) (P₀ : ℕ) :
    ∃ w : List (Fin 5), ∃ p : ℕ,
      w ≠ [] ∧ IsFactorInf w b5 ∧ 1 ≤ p ∧ P₀ ≤ p ∧ IsPeriod w p ∧
      φ * (p : ℝ) - 2 * ((w.length : ℝ) - (p : ℝ)) < (7 - Real.sqrt 5) / 4 + ε ∧
      (5 + Real.sqrt 5) / 4 - (7 - Real.sqrt 5 + ε) / (8 * (p : ℝ)) < (w.length : ℝ) / (p : ℝ) := by
  rcases extremalSeed_concreteRun with ⟨hrun0, hsum0⟩
  let s (n : ℕ) := (stepSummary^[n]) extremalSeedSummary
  -- Unbounded growth of period p_k ≥ φ ^ k
  have hpk_ge_pow : ∀ k : ℕ, φ ^ k ≤ ((s k).pu.sum : ℝ) := by
    have hnn_all : ∀ k : ℕ, (s k).pu.Nonneg ∧ nuVec (s k).pu = φ ^ k * nuVec (s 0).pu := by
      intro k
      induction k with
      | zero =>
        have hs0_eq : s 0 = extremalSeedSummary := rfl
        rw [hs0_eq, ← hsum0]
        exact ⟨parikhSym_nonneg _, by simp⟩
      | succ k ih =>
        have hs1 : s (k + 1) = stepSummary (s k) := Function.iterate_succ_apply' _ _ _
        rw [hs1]; dsimp only [stepSummary]
        exact ⟨stepMZ_nonneg ih.1, by rw [nuVec_stepMZ, ih.2]; ring⟩
    intro k
    rcases hnn_all k with ⟨hnn, hnu_eq⟩
    have hle_sum := (nuVec_bounds_of_nonneg hnn).2
    have hnu0_ge1 : (1 : ℝ) ≤ nuVec (s 0).pu := by
      have hs0 : (s 0).pu = ⟨1, 1, 0, 0, 0⟩ := rfl
      rw [hs0]; simp only [nuVec]; push_cast
      have : 0 ≤ 1 / φ := by positivity [phi_pos]
      linarith
    have hpow_le : φ ^ k * 1 ≤ φ ^ k * nuVec (s 0).pu :=
      mul_le_mul_of_nonneg_left hnu0_ge1 (pow_nonneg (le_of_lt phi_pos) k)
    linarith
  have hphi_ge_linear : ∀ j : ℕ, (j + 1 : ℝ) ≤ φ ^ (6 + 6 * j) := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, Nat.cast_zero, zero_add]
      rw [phi_pow_six_eq]; linarith [one_lt_phi]
    | succ j ih =>
      have hpow : φ ^ (6 + 6 * (j + 1)) = φ ^ 6 * φ ^ (6 + 6 * j) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow, phi_pow_six_eq]
      push_cast
      nlinarith [one_lt_phi]
  have hphi_ge_linear11 : ∀ j : ℕ, (j + 1 : ℝ) ≤ φ ^ (11 + 6 * j) := by
    intro j
    have h1 := hphi_ge_linear j
    have h5 : (1 : ℝ) ≤ φ ^ 5 := one_le_pow₀ (le_of_lt one_lt_phi)
    have hpow : φ ^ (11 + 6 * j) = φ ^ 5 * φ ^ (6 + 6 * j) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    nlinarith [pow_pos phi_pos (6 + 6 * j)]
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
  let j₀ := max N P₀
  let k₀ := 6 + 6 * j₀
  rcases exists_concreteRun_iter_summary k₀ hrun0 with ⟨i_k, p_k, m_k, hr_k, hsum_k⟩
  rw [hsum0] at hsum_k
  have hsums := runSummary_sums i_k p_k m_k
  have hp_eq : (p_k : ℤ) = (s k₀).pu.sum := by
    rw [← hsums.1, hsum_k]
  have hm_eq : (m_k : ℤ) = (s k₀).pz.sum := by
    rw [← hsums.2, hsum_k]
  have hpk_ge_j : (j₀ + 1 : ℝ) ≤ (p_k : ℝ) := by
    have h1 := hpk_ge_pow k₀
    have h2 := hphi_ge_linear j₀
    have hpR : ((s k₀).pu.sum : ℝ) = (p_k : ℝ) := by exact_mod_cast hp_eq.symm
    linarith
  have hpk_ge_P0 : P₀ ≤ p_k := by
    have hj_ge : (P₀ : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast le_max_right N P₀
    have hlt : (P₀ : ℝ) ≤ (p_k : ℝ) := by linarith
    exact_mod_cast hlt
  have hclosed := extremal_deficit_closed_form j₀
  have hinv_small : 1 / φ ^ (11 + 6 * j₀) < ε / 4 := by
    have hpow_pos : 0 < φ ^ (11 + 6 * j₀) := pow_pos phi_pos _
    have hlin := hphi_ge_linear11 j₀
    have hjN : (N : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast le_max_left N P₀
    have hgt : 4 / ε < φ ^ (11 + 6 * j₀) := by linarith
    rw [div_lt_div_iff₀ hpow_pos (by norm_num : (0 : ℝ) < 4)]
    have hmul := (div_lt_iff₀ hε).mp hgt
    linarith
  -- Construct factor w := (symSlice i_k (p_k + m_k)).map Sym5.toFin
  let w : List (Fin 5) := (symSlice i_k (p_k + m_k)).map Sym5.toFin
  have hw_len : w.length = p_k + m_k := by
    simp [w, symSlice_length]
  have hw_ne : w ≠ [] := by
    intro hnil
    have h0 := congrArg List.length hnil
    simp only [hw_len, List.length_nil] at h0
    have hp1 := hr_k.2.1
    omega
  have hw_fac : IsFactorInf w b5 := by
    refine ⟨i_k, fun j hj => ?_⟩
    rw [hw_len] at hj
    simp only [w, List.getElem_map, symSlice_getElem]
    exact (Sym5.toFin_ofFin (b5 (i_k + j))).symm
  have hw_per : IsPeriod w p_k := by
    intro j hj
    rw [hw_len] at hj
    simp only [w, List.getElem_map, symSlice_getElem]
    have hsym := hr_k.2.2.1 j (by omega)
    have hfin := congrArg Sym5.toFin hsym
    simp only [b5Sym, Sym5.toFin_ofFin] at hfin ⊢
    have hidx : i_k + (j + p_k) = i_k + j + p_k := by omega
    rw [hidx]
    exact hfin
  have hD_val : 2 * (φ * (p_k : ℝ) - 2 * (m_k : ℝ)) - (4 - φ) = 1 / φ ^ (11 + 6 * j₀) := by
    rw [← hclosed, summarySharpE_toReal]
    unfold summaryD ZPhi.toReal
    dsimp only
    have hpR : ((s k₀).pu.sum : ℝ) = (p_k : ℝ) := by exact_mod_cast hp_eq.symm
    have hmR : ((s k₀).pz.sum : ℝ) = (m_k : ℝ) := by exact_mod_cast hm_eq.symm
    push_cast
    rw [hpR, hmR]
    ring
  have hlenR : (w.length : ℝ) - (p_k : ℝ) = (m_k : ℝ) := by
    rw [hw_len]; push_cast; ring
  have hdef_lt : φ * (p_k : ℝ) - 2 * ((w.length : ℝ) - (p_k : ℝ)) < (7 - Real.sqrt 5) / 4 + ε := by
    rw [hlenR]
    have hconst := sharp_const_eq
    linarith
  have hexp_gt : (5 + Real.sqrt 5) / 4 - (7 - Real.sqrt 5 + ε) / (8 * (p_k : ℝ)) <
      (w.length : ℝ) / (p_k : ℝ) := by
    have hp_pos : (0 : ℝ) < (p_k : ℝ) := by exact_mod_cast hr_k.2.1
    rw [lt_div_iff₀ hp_pos]
    have hmul : ((5 + Real.sqrt 5) / 4 - (7 - Real.sqrt 5 + ε) / (8 * (p_k : ℝ))) * (p_k : ℝ) =
        (5 + Real.sqrt 5) / 4 * (p_k : ℝ) - (7 - Real.sqrt 5 + ε) / 8 := by
      field_simp
    rw [hmul, hw_len]
    push_cast
    have hphi_eq : (5 + Real.sqrt 5) / 4 = 1 + φ / 2 := by unfold φ; ring
    have hconst := sharp_const_eq
    rw [hphi_eq]
    linarith
  exact ⟨w, p_k, hw_ne, hw_fac, hr_k.2.1, hpk_ge_P0, hw_per, hdef_lt, hexp_gt⟩

/-- Set of all repetition deficits `φ * p - 2 * (|w| - p)` over factors `w` of `b_5` and periods `p ≥ 1`. -/
def DeficitSet (W : ℕ → Fin 5) : Set ℝ :=
  { d : ℝ | ∃ w : List (Fin 5), ∃ p : ℕ,
      IsFactorInf w W ∧ 1 ≤ p ∧ IsPeriod w p ∧
      d = φ * (p : ℝ) - 2 * ((w.length : ℝ) - (p : ℝ)) }

/-- **Exact Deficit Infimum (`b5_sharp_deficit_inf_eq`)**:
`sInf (DeficitSet b5) = (7 - √5) / 4 = 2 - φ / 2`. -/
theorem b5_sharp_deficit_inf_eq :
    sInf (DeficitSet b5) = (7 - Real.sqrt 5) / 4 := by
  have hne : (DeficitSet b5).Nonempty := by
    refine ⟨φ + 2, [], 1, isFactorInf_nil b5, le_refl 1, fun i hi => by simp at hi, by simp⟩
  have hlb : ∀ d ∈ DeficitSet b5, (7 - Real.sqrt 5) / 4 ≤ d := by
    rintro d ⟨w, p, hfac, hp, hper, rfl⟩
    exact le_of_lt (b5_sharp_deficit_gt w p hfac hp hper)
  apply le_antisymm
  · by_contra hgt
    push Not at hgt
    set ε := sInf (DeficitSet b5) - (7 - Real.sqrt 5) / 4 with hε_def
    have hε : 0 < ε := sub_pos.mpr hgt
    rcases b5_sharp_second_order_optimal ε hε 1 with ⟨w, p, _, hfac, hp, _, hper, hdef_lt, _⟩
    have hmem : φ * (p : ℝ) - 2 * ((w.length : ℝ) - (p : ℝ)) ∈ DeficitSet b5 :=
      ⟨w, p, hfac, hp, hper, rfl⟩
    have hle := csInf_le ⟨(7 - Real.sqrt 5) / 4, hlb⟩ hmem
    linarith
  · exact le_csInf hne hlb

/-- **Non-Attainment of the Sharp Deficit Infimum (`b5_sharp_deficit_not_attained`)**. -/
theorem b5_sharp_deficit_not_attained :
    ¬ ∃ w : List (Fin 5), ∃ p : ℕ,
      IsFactorInf w b5 ∧ 1 ≤ p ∧ IsPeriod w p ∧
      φ * (p : ℝ) - 2 * ((w.length : ℝ) - (p : ℝ)) = (7 - Real.sqrt 5) / 4 := by
  rintro ⟨w, p, hfac, hp, hper, heq⟩
  have hgt := b5_sharp_deficit_gt w p hfac hp hper
  linarith

/-- Set of repetition exponents restricted to periods `p ≥ L`. -/
def AsympExponentSet (W : ℕ → Fin 5) (L : ℕ) : Set ℝ :=
  { r : ℝ | ∃ w : List (Fin 5), ∃ p : ℕ,
      IsFactorInf w W ∧ L ≤ p ∧ 1 ≤ p ∧ IsPeriod w p ∧ r = (w.length : ℝ) / (p : ℝ) }

/-- **Exact Asymptotic Critical Exponent (`b5_asymp_critExp_eq`)**:
For EVERY period lower bound `L : ℕ`, `sSup (AsympExponentSet b5 L) = (5 + √5) / 4`, establishing
`E*(b_5) = E(b_5) = (5 + √5) / 4`. -/
theorem b5_asymp_critExp_eq (L : ℕ) :
    sSup (AsympExponentSet b5 L) = (5 + Real.sqrt 5) / 4 := by
  have hub : ∀ r ∈ AsympExponentSet b5 L, r ≤ (5 + Real.sqrt 5) / 4 := by
    rintro r ⟨w, p, hfac, _, hp, hper, rfl⟩
    exact le_of_lt (b5_exponent_lt_crit w p hfac hp hper)
  have hne : (AsympExponentSet b5 L).Nonempty := by
    rcases b5_sharp_second_order_optimal 1 one_pos L with ⟨w, p, _, hfac, hp, hpL, hper, _, _⟩
    exact ⟨(w.length : ℝ) / (p : ℝ), w, p, hfac, hpL, hp, hper, rfl⟩
  apply le_antisymm
  · exact csSup_le hne hub
  · by_contra hlt
    push Not at hlt
    set δ := (5 + Real.sqrt 5) / 4 - sSup (AsympExponentSet b5 L) with hδ_def
    have hδ : 0 < δ := sub_pos.mpr hlt
    -- Pick P₀ ≥ max L 1 large enough that (7 - √5 + 1) / (8 * P₀) < δ (e.g. P₀ > 1 / δ)
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
    let P₀ := max L (M + 1)
    rcases b5_sharp_second_order_optimal 1 one_pos P₀ with ⟨w, p, _, hfac, hp, hpP0, hper, _, hexp_gt⟩
    have hpL : L ≤ p := le_trans (le_max_left L (M + 1)) hpP0
    have hmem : (w.length : ℝ) / (p : ℝ) ∈ AsympExponentSet b5 L :=
      ⟨w, p, hfac, hpL, hp, hper, rfl⟩
    have hle := le_csSup ⟨(5 + Real.sqrt 5) / 4, hub⟩ hmem
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    have hp_gt : 1 / δ < (p : ℝ) := by
      have h1 : (M + 1 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast le_trans (le_max_right L (M + 1)) hpP0
      linarith
    have hnum_lt8 : 7 - Real.sqrt 5 + 1 < 8 := by linarith [sqrt5_pos]
    have hterm_lt : (7 - Real.sqrt 5 + 1) / (8 * (p : ℝ)) < δ := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 8 * (p : ℝ))]
      have hmul : 1 < (p : ℝ) * δ := (div_lt_iff₀ hδ).mp hp_gt
      nlinarith
    linarith

/-- **Irrationality of `E(b_5)` (`b5_critExp_irrational`)**:
`E(b_5) = (5 + √5) / 4` is irrational. -/
theorem b5_critExp_irrational : Irrational (critExp b5) := by
  rw [b5_critical_exponent_eq]
  intro ⟨q, hq⟩
  -- (q : ℝ) = (5 + √5) / 4 = 1 + φ / 2 ⇔ (q - 1) + (-1/2) * φ = 0
  have hlin : ((q - 1 : ℚ) : ℝ) + ((-1 / 2 : ℚ) : ℝ) * φ = 0 := by
    push_cast
    unfold φ
    linarith
  have hzero := rat_add_rat_mul_phi_eq_zero hlin
  norm_num at hzero

end BadkobehOchemB5
