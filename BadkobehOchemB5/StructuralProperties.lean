module

public import BadkobehOchemB5.Defs
public import BadkobehOchemB5.ComplexityAndSturmian
public import BadkobehOchemB5.SeedsCert
public import BadkobehOchemB5.CriticalExponent
import Mathlib.Tactic

/-!
# Structural Properties of `b_5`: Reversal–Swap Symmetry, 3-IET Collapse (`2n + 1`),
# Unbounded Balance Defect, Badkobeh–Ochem `F_5` Avoidance, and Exact `A005252` Recurrence

This module establishes five structural theorems for `b_5 = f_5^ω(0)` beyond the baseline library:

1. **Geometric Reversal + `(3 ↔ 4)` Symmetry (`b5_language_rev_swap34_invariant`)**:
   Using the exact affine involution `S(x) = φ / 2 - x` on `J = (-φ^2 / 2, φ^3 / 2)` satisfying
   `S(T(P_a)) = P_{swap34(a)}` and `T(S(T(x))) = S(x)`, we prove
   `IsFactorInf w b5 ↔ IsFactorInf (revSwap34 w) b5` for every finite word `w : List (Fin 5)`.
2. **Ternary 3-IET Collapse & Lenz–Masáková–Pelantová Factorization (`gFib_eq_sigma01_comp_pi3`,
   `pi3B5_factor_complexity`)**:
   Under `π_3 : {1,3,4} ↦ 0, 0 ↦ 1, 2 ↦ 2` and `σ_{01} : 0 ↦ 0, 1 ↦ 01, 2 ↦ 1`, Badkobeh–Ochem's
   Sturmian projection factors identically as `g_fib = σ_{01} ∘ π_3` (matching Lenz–Masáková–
   Pelantová, *TCS* 412 (2011), Theorem 3), and the ternary 3-IET word `π_3(b_5)` has exact factor
   complexity `factorComplexity pi3B5 n = 2 * n + 1` for every `n : ℕ`.
3. **Unbounded Balance Defect (`b5_not_C_balanced`, `b5_not_balanced`)**:
   Via the exact integer `(-1)`-eigenvector functional
   `ψ(w) = |w|_0 - 2|w|_1 + |w|_2 + |w|_3 - |w|_4` satisfying `ψ(f_5(w)) = -ψ(w)` and the explicit
   factor family `unbalWord (k + 1) = 423 · f_5^4(unbalWord k)` with `ψ(unbalWord k) = k`, we prove
   that `b_5` is **not `C`-balanced for any `C : ℕ`**, completely separating `b_5` from balanced
   words (such as Rampersad–Shallit–Vandomme's 4-letter word `x_4`).
4. **Badkobeh–Ochem (2015) Theorem 1 Avoidance (`b5_avoids_F5`, `badkobehOchemF5_rev_swap34_invariant`)**:
   Every one of the 16 forbidden factors in Badkobeh–Ochem's set `F_5` is avoided by `b_5`, and
   `F_5` is closed under `revSwap34`.
5. **Exact 5th-Order Prefix-Length Recurrence (`stepMZ_charpoly`, `fB5_iter_length_rec`)**:
   From the exact characteristic polynomial `x^5 - x^4 - x^3 + x^2 - x - 1` of the incidence matrix
   `M` of `f_5`, every iterate length sequence `|f_5^k(w)|` (in particular OEIS `A005252` for
   `w = [0]`) satisfies
   `|f_5^{k+5}(w)| + |f_5^{k+2}(w)| = |f_5^{k+4}(w)| + |f_5^{k+3}(w)| + |f_5^{k+1}(w)| + |f_5^k(w)|`.
-/

@[expose] public section

namespace BadkobehOchemB5

/-! ## Section 1: Geometric Reversal + `(3 ↔ 4)` Symmetry of `b_5` -/

/-- Letter involution swapping `3 ↔ 4` and fixing `0, 1, 2`. -/
def swap34 : Fin 5 → Fin 5
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 3

/-- Reversal composed with `(3 ↔ 4)` swap (Badkobeh–Ochem 2015, Section 3). -/
def revSwap34 (w : List (Fin 5)) : List (Fin 5) :=
  w.reverse.map swap34

theorem swap34_involutive (a : Fin 5) : swap34 (swap34 a) = a := by
  rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem revSwap34_involutive (w : List (Fin 5)) : revSwap34 (revSwap34 w) = w := by
  unfold revSwap34
  rw [← List.map_reverse, List.reverse_reverse, List.map_map]
  have hcomp : swap34 ∘ swap34 = id := funext swap34_involutive
  rw [hcomp, List.map_id]

theorem revSwap34_length (w : List (Fin 5)) : (revSwap34 w).length = w.length := by
  simp [revSwap34]

/-- Exact affine involution `S(x) := φ / 2 - x` on `J = (-φ^2 / 2, φ^3 / 2)`. -/
noncomputable def invS (x : ℝ) : ℝ :=
  φ / 2 - x

theorem ietT_of_inLetterInterval {a : Fin 5} {x : ℝ} (hx : InLetterInterval a x) :
    ietT x = x + l' a := by
  rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
  rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl
  · unfold InLetterInterval intervalLo intervalHi at hx
    unfold ietT l'
    rw [ite_false_of (by linarith), ite_true_of hx.2]
  · unfold InLetterInterval intervalLo intervalHi at hx
    unfold ietT l'
    rw [ite_false_of (by linarith), ite_false_of (by linarith)]
    ring
  · unfold InLetterInterval intervalLo intervalHi at hx
    unfold ietT l'
    rw [ite_true_of hx.2]
  · unfold InLetterInterval intervalLo intervalHi at hx
    unfold ietT l'
    rw [ite_false_of (by linarith), ite_false_of (by linarith)]
    ring
  · unfold InLetterInterval intervalLo intervalHi at hx
    unfold ietT l'
    rw [ite_false_of (by linarith), ite_false_of (by linarith)]
    ring

/-- **Key Geometric Symmetry Lemma (`invS_ietT_inLetterInterval`)**:
For every letter `a : Fin 5` and `x ∈ P_a`:
1. `invS (ietT x) ∈ P_{swap34 a}`;
2. `ietT (invS (ietT x)) = invS x`. -/
theorem invS_ietT_inLetterInterval {a : Fin 5} {x : ℝ} (hx : InLetterInterval a x) :
    InLetterInterval (swap34 a) (invS (ietT x)) ∧ ietT (invS (ietT x)) = invS x := by
  have hT := ietT_of_inLetterInterval hx
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h1 : 1 < φ := one_lt_phi
  have hin : InLetterInterval (swap34 a) (invS (ietT x)) := by
    rw [hT]
    rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;>
      simp only [swap34, InLetterInterval, intervalLo, intervalHi, invS, l'] at hx ⊢ <;>
      constructor <;> linarith
  refine ⟨hin, ?_⟩
  rw [ietT_of_inLetterInterval hin, hT]
  have hl_eq : l' (swap34 a) = l' a := by
    rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hl_eq]
  unfold invS
  ring

theorem inLetterInterval_subset_J {a : Fin 5} {x : ℝ} (hx : InLetterInterval a x) :
    -φ ^ 2 / 2 < x ∧ x < φ ^ 3 / 2 := by
  rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
  rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;>
    unfold InLetterInterval intervalLo intervalHi at hx <;> constructor <;> linarith

/-- Every open letter interval `P_a` contains an open ball around each of its points. -/
theorem exists_ball_inLetterInterval {a : Fin 5} {x : ℝ} (hx : InLetterInterval a x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| < δ → InLetterInterval a y := by
  unfold InLetterInterval at hx ⊢
  refine ⟨min (x - intervalLo a) (intervalHi a - x), lt_min (by linarith) (by linarith), fun y hy => ?_⟩
  rw [abs_lt] at hy
  have h1 := min_le_left (x - intervalLo a) (intervalHi a - x)
  have h2 := min_le_right (x - intervalLo a) (intervalHi a - x)
  constructor <;> linarith

/-- Along a finite open itinerary `ietT^[j] y₀ ∈ P_{v[j]}`, there is a `δ > 0` open ball around
`y₀` whose points share the exact same length-`|v|` `ietT`-itinerary. -/
theorem exists_ball_same_itinerary (v : List (Fin 5)) (y₀ : ℝ)
    (hit : ∀ j (hj : j < v.length), InLetterInterval (v[j]'hj) (ietT^[j] y₀)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - y₀| < δ →
      ∀ j (hj : j < v.length), InLetterInterval (v[j]'hj) (ietT^[j] y) := by
  induction v generalizing y₀ with
  | nil =>
    exact ⟨1, one_pos, fun _ _ j hj => by simp at hj⟩
  | cons a rest ih =>
    have h0 : InLetterInterval a y₀ := hit 0 (by simp)
    rcases exists_ball_inLetterInterval h0 with ⟨δ₀, hδ0_pos, hball0⟩
    have hrest : ∀ j (hj : j < rest.length),
        InLetterInterval (rest[j]'hj) (ietT^[j] (ietT y₀)) := by
      intro j hj
      have h := hit (j + 1) (by simp; omega)
      rw [Function.iterate_succ_apply] at h
      exact h
    rcases ih (ietT y₀) hrest with ⟨δ₁, hδ1_pos, hball1⟩
    refine ⟨min δ₀ δ₁, lt_min hδ0_pos hδ1_pos, fun y hy j hj => ?_⟩
    have hy0 : |y - y₀| < δ₀ := lt_of_lt_of_le hy (min_le_left _ _)
    have hy1 : |y - y₀| < δ₁ := lt_of_lt_of_le hy (min_le_right _ _)
    have hya : InLetterInterval a y := hball0 y hy0
    have hTy : ietT y - ietT y₀ = y - y₀ := by
      rw [ietT_of_inLetterInterval hya, ietT_of_inLetterInterval h0]; ring
    cases j with
    | zero => exact hya
    | succ j' =>
      rw [Function.iterate_succ_apply]
      apply hball1 (ietT y) (by rw [hTy]; exact hy1) j' (by simp at hj; omega)

theorem b5_orbit_ietT_iter (p j : ℕ) :
    ietT^[j] (lambda' (prefixOf b5 p)) = lambda' (prefixOf b5 (p + j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 := (b5_orbit_iet_props (p + j)).2.2.1
    have hidx : p + (j + 1) = p + j + 1 := by omega
    rw [hidx, h1]

theorem isFactorInf_revSwap34_of_isFactorInf {w : List (Fin 5)} (h : IsFactorInf w b5) :
    IsFactorInf (revSwap34 w) b5 := by
  cases w with
  | nil => exact isFactorInf_nil b5
  | cons a rest =>
    let u := a :: rest
    rcases h with ⟨p, hp⟩
    let n := u.length
    have hn_eq : n = u.length := rfl
    have hn_pos : 1 ≤ n := by simp [n, u]
    let y₀ : ℝ := invS (lambda' (prefixOf b5 (p + n)))
    -- Show ietT^[j] y₀ = invS (lambda' (prefixOf b5 (p + n - j))) and lies in P_{(revSwap34 u)[j]}!
    have hwalk : ∀ j : ℕ, j ≤ n →
        ietT^[j] y₀ = invS (lambda' (prefixOf b5 (p + n - j))) ∧
        (∀ hj : j < n, InLetterInterval ((revSwap34 u)[j]'(by rw [revSwap34_length]; exact hj))
          (ietT^[j] y₀)) := by
      intro j hj_le
      induction j with
      | zero =>
        refine ⟨by simp [y₀], fun hj => ?_⟩
        simp only [Function.iterate_zero, id_eq, y₀]
        have hstep_pos : p + n = p + (n - 1) + 1 := by omega
        have hT_last : lambda' (prefixOf b5 (p + n)) = ietT (lambda' (prefixOf b5 (p + (n - 1)))) := by
          rw [hstep_pos, ← (b5_orbit_iet_props (p + (n - 1))).2.2.1]
        rw [hT_last]
        have hlast_in : InLetterInterval (u[n - 1]'(by omega)) (lambda' (prefixOf b5 (p + (n - 1)))) := by
          have hb := b5_prefix_in_letter_interval (p + (n - 1))
          rw [hp (n - 1) (by rw [← hn_eq]; omega)] at hb
          exact hb
        have hrev0 : (revSwap34 u)[0]'(by rw [revSwap34_length]; exact hj) = swap34 (u[n - 1]'(by omega)) := by
          simp [revSwap34, List.getElem_reverse, n]
        rw [hrev0]
        exact (invS_ietT_inLetterInterval hlast_in).1
      | succ j ih =>
        rcases ih (by omega) with ⟨hiter_j, hmem_j⟩
        have hstep_pos : p + n - j = (p + (n - 1 - j)) + 1 := by omega
        have hT_prev : lambda' (prefixOf b5 (p + n - j)) =
            ietT (lambda' (prefixOf b5 (p + (n - 1 - j)))) := by
          rw [hstep_pos, ← (b5_orbit_iet_props (p + (n - 1 - j))).2.2.1]
        have hprev_in : InLetterInterval (u[n - 1 - j]'(by omega))
            (lambda' (prefixOf b5 (p + (n - 1 - j)))) := by
          have hb := b5_prefix_in_letter_interval (p + (n - 1 - j))
          rw [hp (n - 1 - j) (by rw [← hn_eq]; omega)] at hb
          exact hb
        have hnext_eq : ietT^[j + 1] y₀ = invS (lambda' (prefixOf b5 (p + n - (j + 1)))) := by
          rw [Function.iterate_succ_apply', hiter_j, hT_prev]
          have hinv := (invS_ietT_inLetterInterval hprev_in).2
          rw [hinv]
          have hidx_eq : p + (n - 1 - j) = p + n - (j + 1) := by omega
          rw [hidx_eq]
        refine ⟨hnext_eq, fun hj_lt => ?_⟩
        rw [hnext_eq]
        have hstep2 : p + n - (j + 1) = (p + (n - 1 - (j + 1))) + 1 := by omega
        have hT2 : lambda' (prefixOf b5 (p + n - (j + 1))) =
            ietT (lambda' (prefixOf b5 (p + (n - 1 - (j + 1))))) := by
          rw [hstep2, ← (b5_orbit_iet_props (p + (n - 1 - (j + 1)))).2.2.1]
        rw [hT2]
        have hin2 : InLetterInterval (u[n - 1 - (j + 1)]'(by omega))
            (lambda' (prefixOf b5 (p + (n - 1 - (j + 1))))) := by
          have hb := b5_prefix_in_letter_interval (p + (n - 1 - (j + 1)))
          rw [hp (n - 1 - (j + 1)) (by rw [← hn_eq]; omega)] at hb
          exact hb
        have hrev_j : (revSwap34 u)[j + 1]'(by rw [revSwap34_length]; exact hj_lt) =
            swap34 (u[n - 1 - (j + 1)]'(by omega)) := by
          simp only [revSwap34, List.getElem_map, List.getElem_reverse]
          congr 2
        rw [hrev_j]
        exact (invS_ietT_inLetterInterval hin2).1
    have hit : ∀ j (hj : j < (revSwap34 u).length),
        InLetterInterval ((revSwap34 u)[j]'hj) (ietT^[j] y₀) := by
      intro j hj
      rw [revSwap34_length] at hj
      exact (hwalk j (by omega)).2 hj
    rcases exists_ball_same_itinerary (revSwap34 u) y₀ hit with ⟨δ, hδ_pos, hball⟩
    -- Note y₀ ∈ P_{(revSwap34 u)[0]} ⊂ J!
    have hy0_J : -φ ^ 2 / 2 < y₀ ∧ y₀ < φ ^ 3 / 2 :=
      inLetterInterval_subset_J (hit 0 (by rw [revSwap34_length]; simp [u]))
    let lo := max (-φ ^ 2 / 2) (y₀ - δ)
    let hi := min (φ ^ 3 / 2) (y₀ + δ)
    have hlo_ge : -φ ^ 2 / 2 ≤ lo := le_max_left _ _
    have hhi_le : hi ≤ φ ^ 3 / 2 := min_le_left _ _
    have hlo_lt_hi : lo < hi := by
      dsimp [lo, hi]
      exact max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
    rcases b5_orbit_dense_in_J lo hi hlo_ge hlo_lt_hi hhi_le with ⟨q, hq_lo, hq_hi⟩
    have hq_dist : |lambda' (prefixOf b5 q) - y₀| < δ := by
      rw [abs_lt]
      have h1 : y₀ - δ ≤ lo := le_max_right _ _
      have h2 : hi ≤ y₀ + δ := min_le_right _ _
      constructor <;> linarith
    refine ⟨q, fun j hj => ?_⟩
    have hin_j := hball (lambda' (prefixOf b5 q)) hq_dist j hj
    rw [b5_orbit_ietT_iter] at hin_j
    exact inLetterInterval_unique (b5_prefix_in_letter_interval (q + j)) hin_j

/-- **Badkobeh–Ochem (2015, Section 3) Reversal + `(3 ↔ 4)` Symmetry Theorem
(`b5_language_rev_swap34_invariant`)**:
For EVERY finite word `w : List (Fin 5)`, `w` is a factor of `b_5` iff `revSwap34 w` is. -/
theorem b5_language_rev_swap34_invariant (w : List (Fin 5)) :
    IsFactorInf w b5 ↔ IsFactorInf (revSwap34 w) b5 := by
  constructor
  · exact isFactorInf_revSwap34_of_isFactorInf
  · intro h
    have h2 := isFactorInf_revSwap34_of_isFactorInf h
    rwa [revSwap34_involutive] at h2

/-! ## Section 2: Ternary 3-IET Collapse `π_3(b_5)` (`2n + 1`) & Lenz–Masáková–Pelantová Factorization -/

/-- The 3-interval collapse `π_3 : {1,3,4} ↦ 0 (A), 0 ↦ 1 (B), 2 ↦ 2 (C)`. -/
def pi3 : Fin 5 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 0

/-- Canonical Lenz–Masáková–Pelantová (2011, Theorem 3) 3-IET-to-Sturmian morphism
`σ_{01} : 0 (A) ↦ 0, 1 (B) ↦ 01, 2 (C) ↦ 1`. -/
def sigma01 : Fin 3 → List Bool
  | ⟨0, _⟩ => [false]
  | ⟨1, _⟩ => [false, true]
  | ⟨2, _⟩ => [true]

theorem sigma01_nonempty : ∀ a : Fin 3, sigma01 a ≠ [] := by
  intro a
  fin_cases a <;> decide

/-- The ternary 3-IET word `π_3(b_5)`. -/
def pi3B5 (p : ℕ) : Fin 3 :=
  pi3 (b5 p)

/-- **Lenz–Masáková–Pelantová (2011, Theorem 3) Factorization (`gFib_eq_sigma01_comp_pi3`)**:
Badkobeh–Ochem's Sturmian projection factors identically as `g_fib = σ_{01} ∘ π_3`. -/
theorem gFib_eq_sigma01_comp_pi3 (w : List (Fin 5)) :
    applyMorph gFib w = applyMorph sigma01 (w.map pi3) := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    change gFib a ++ applyMorph gFib rest = sigma01 (pi3 a) ++ applyMorph sigma01 (rest.map pi3)
    have hletter : gFib a = sigma01 (pi3 a) := by
      rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hletter, ih]

theorem gFibB5_eq_sigma01_pi3B5 (k : ℕ) :
    gFibB5 k = applyMorphInf sigma01 sigma01_nonempty pi3B5 k := by
  let N := k + 1
  have hk_g : k < (applyMorph gFib (prefixOf b5 N)).length :=
    lt_applyMorph_prefix_length gFib gFib_nonempty b5 k
  have hmap : (prefixOf b5 N).map pi3 = prefixOf pi3B5 N := by
    apply List.ext_getElem
    · simp [prefixOf_length]
    · intro i hi1 hi2
      simp [prefixOf_getElem, pi3B5]
  have heq : applyMorph gFib (prefixOf b5 N) = applyMorph sigma01 (prefixOf pi3B5 N) := by
    rw [gFib_eq_sigma01_comp_pi3, hmap]
  have hk_s : k < (applyMorph sigma01 (prefixOf pi3B5 N)).length := by
    rw [← heq]; exact hk_g
  have h1 := applyMorphInf_eq_getElem gFib gFib_nonempty b5 N k hk_g
  have h2 := applyMorphInf_eq_getElem sigma01 sigma01_nonempty pi3B5 N k hk_s
  unfold gFibB5
  rw [h1, h2]
  congr 1

/-- Ternary readout `ietLetter3` on `J` with only the 2 base discontinuities `{-1/2, (φ-1)/2}`. -/
noncomputable def ietLetter3 (x : ℝ) : Fin 3 :=
  if x < -1 / 2 then 2
  else if x < (φ - 1) / 2 then 1
  else 0

theorem pi3_ietLetter_eq (x : ℝ) : pi3 (ietLetter x) = ietLetter3 x := by
  unfold ietLetter ietLetter3
  split_ifs <;> rfl

/-- The 2 base cut points `{-1/2, (φ-1)/2}` of the 3-IET `ietT`. -/
noncomputable def pi3BaseCuts : Finset ℝ :=
  {-1 / 2, (φ - 1) / 2}

theorem mem_pi3BaseCuts_iff (x : ℝ) :
    x ∈ pi3BaseCuts ↔ ∃ i : Fin 2, x = b5CutPt ⟨i.val, by omega⟩ := by
  simp only [pi3BaseCuts, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · left; rfl
    · right; rfl

/-- Backward preimage set of the 2 base cuts, of exact cardinality `2 * n`. -/
noncomputable def ietCutSet3 (n : ℕ) : Finset ℝ :=
  ((Finset.range n) ×ˢ (Finset.univ : Finset (Fin 2))).image
    (fun p : ℕ × Fin 2 => ietTInv^[p.1] (b5CutPt ⟨p.2.val, by omega⟩))

theorem ietCutSet3_card (n : ℕ) : (ietCutSet3 n).card = 2 * n := by
  unfold ietCutSet3
  have hinj : Function.Injective
      (fun p : ℕ × Fin 2 => ietTInv^[p.1] (b5CutPt ⟨p.2.val, by omega⟩)) := by
    intro p1 p2 heq
    have h4 := ietTInv_iter_injective (a₁ := (p1.1, ⟨p1.2.val, by omega⟩))
      (a₂ := (p2.1, ⟨p2.2.val, by omega⟩)) heq
    cases p1; cases p2
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h4
    exact Prod.ext h4.1 (Fin.ext h4.2)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_range,
      Finset.card_fin]
  ring

theorem ietCutSet3_iff (n : ℕ) {x : ℝ} (hx1 : -φ ^ 2 / 2 < x) (hx2 : x < φ ^ 3 / 2) :
    x ∈ ietCutSet3 n ↔ ∃ k < n, ietT^[k] x ∈ pi3BaseCuts := by
  simp only [ietCutSet3, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, Prod.exists, mem_pi3BaseCuts_iff]
  constructor
  · rintro ⟨k, i, hkn, rfl⟩
    exact ⟨k, hkn, i, (ietTInv_iter_cut k ⟨i.val, by omega⟩).2.2⟩
  · rintro ⟨k, hkn, i, hhit⟩
    have hex_hit : ∃ j : ℕ, j < n ∧ ∃ c : Fin 2, ietT^[j] x = b5CutPt ⟨c.val, by omega⟩ :=
      ⟨k, hkn, i, hhit⟩
    classical
    let j₀ := Nat.find hex_hit
    rcases Nat.find_spec hex_hit with ⟨hj0_lt, c₀, hj0_eq⟩
    have hmin : ∀ r < j₀, ∀ c : Fin 2, ietT^[r] x ≠ b5CutPt ⟨c.val, by omega⟩ := by
      intro r hr c hrc
      exact Nat.find_min hex_hit hr ⟨by omega, c, hrc⟩
    refine ⟨j₀, c₀, hj0_lt, ?_⟩
    have hwalk : ∀ r : ℕ, r ≤ j₀ →
        -φ ^ 2 / 2 < ietT^[r] x ∧ ietT^[r] x < φ ^ 3 / 2 ∧
        ietTInv^[r] (ietT^[r] x) = x := by
      intro r
      induction r with
      | zero => intro _; simp [hx1, hx2]
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

/-- **Exact Ternary 3-IET Factor Complexity (`pi3B5_factor_complexity`)**:
For EVERY `n : ℕ`, the 3-interval collapse `π_3(b_5)` has exact factor complexity `2 * n + 1`. -/
theorem pi3B5_factor_complexity (n : ℕ) :
    factorComplexity pi3B5 n = 2 * n + 1 := by
  rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have h1 : 1 < φ := one_lt_phi
  have hJ : -φ ^ 2 / 2 < φ ^ 3 / 2 := by linarith
  have hinS : ∀ s ∈ ietCutSet3 n, -φ ^ 2 / 2 < s ∧ s < φ ^ 3 / 2 := by
    intro s hs
    simp only [ietCutSet3, Finset.mem_image, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true, Prod.exists] at hs
    rcases hs with ⟨k, i, _, rfl⟩
    exact ⟨(ietTInv_iter_cut k ⟨i.val, by omega⟩).1,
           (ietTInv_iter_cut k ⟨i.val, by omega⟩).2.1⟩
  have h_trans : ∀ x₁ x₂, -φ ^ 2 / 2 < x₁ → x₁ ≤ x₂ → x₂ < φ ^ 3 / 2 →
      (∀ c ∈ pi3BaseCuts, ¬ (x₁ ≤ c ∧ c ≤ x₂)) →
      ietLetter3 x₁ = ietLetter3 x₂ ∧ ietT x₂ - ietT x₁ = x₂ - x₁ ∧
      -φ ^ 2 / 2 < ietT x₁ ∧ ietT x₂ < φ ^ 3 / 2 := by
    intro x₁ x₂ hx1 h12 hx2 hno
    have h0 : ¬ (x₁ ≤ -1 / 2 ∧ -1 / 2 ≤ x₂) :=
      hno (-1 / 2) (by simp [pi3BaseCuts])
    have h1c : ¬ (x₁ ≤ (φ - 1) / 2 ∧ (φ - 1) / 2 ≤ x₂) :=
      hno ((φ - 1) / 2) (by simp [pi3BaseCuts])
    by_cases ha : x₂ < -1 / 2
    · have ha1 : x₁ < -1 / 2 := lt_of_le_of_lt h12 ha
      have hl1 : ietLetter3 x₁ = 2 := by unfold ietLetter3; exact ite_true_of ha1
      have hl2 : ietLetter3 x₂ = 2 := by unfold ietLetter3; exact ite_true_of ha
      have ht1 : ietT x₁ = x₁ + (1 + φ) := by unfold ietT; exact ite_true_of ha1
      have ht2 : ietT x₂ = x₂ + (1 + φ) := by unfold ietT; exact ite_true_of ha
      rw [hl1, hl2, ht1, ht2]
      exact ⟨rfl, by ring, by linarith, by linarith⟩
    · have ha1 : -1 / 2 < x₁ := by
        by_contra hle; exact h0 ⟨le_of_not_gt hle, le_of_not_gt ha⟩
      have hna1 : ¬ (x₁ < -1 / 2) := by linarith
      by_cases hb : x₂ < (φ - 1) / 2
      · have hb1 : x₁ < (φ - 1) / 2 := lt_of_le_of_lt h12 hb
        have hl1 : ietLetter3 x₁ = 1 := by
          unfold ietLetter3; rw [ite_false_of hna1, ite_true_of hb1]
        have hl2 : ietLetter3 x₂ = 1 := by
          unfold ietLetter3; rw [ite_false_of ha, ite_true_of hb]
        have ht1 : ietT x₁ = x₁ + 1 := by
          unfold ietT; rw [ite_false_of hna1, ite_true_of hb1]
        have ht2 : ietT x₂ = x₂ + 1 := by
          unfold ietT; rw [ite_false_of ha, ite_true_of hb]
        rw [hl1, hl2, ht1, ht2]
        exact ⟨rfl, by ring, by linarith, by linarith⟩
      · have hb1 : (φ - 1) / 2 < x₁ := by
          by_contra hle; exact h1c ⟨le_of_not_gt hle, le_of_not_gt hb⟩
        have hnb1 : ¬ (x₁ < (φ - 1) / 2) := by linarith
        have hl1 : ietLetter3 x₁ = 0 := by
          unfold ietLetter3; rw [ite_false_of hna1, ite_false_of hnb1]
        have hl2 : ietLetter3 x₂ = 0 := by
          unfold ietLetter3; rw [ite_false_of ha, ite_false_of hb]
        have ht1 : ietT x₁ = x₁ - φ := by
          unfold ietT; rw [ite_false_of hna1, ite_false_of hnb1]
        have ht2 : ietT x₂ = x₂ - φ := by
          unfold ietT; rw [ite_false_of ha, ite_false_of hb]
        rw [hl1, hl2, ht1, ht2]
        exact ⟨rfl, by ring, by linarith, by linarith⟩
  have h_sep : ∀ x₁ x₂, -φ ^ 2 / 2 < x₁ → x₁ < x₂ → x₂ < φ ^ 3 / 2 →
      (∃ c ∈ pi3BaseCuts, x₁ < c ∧ c < x₂) → ietLetter3 x₁ ≠ ietLetter3 x₂ := by
    intro x₁ x₂ _ _ _ hsep
    rcases hsep with ⟨c, hc_mem, hc1, hc2⟩
    simp only [pi3BaseCuts, Finset.mem_insert, Finset.mem_singleton] at hc_mem
    rcases hc_mem with rfl | rfl
    · have hl1 : ietLetter3 x₁ = 2 := by unfold ietLetter3; exact ite_true_of hc1
      have hna2 : ¬ (x₂ < -1 / 2) := by linarith
      unfold ietLetter3; rw [ite_true_of hc1, ite_false_of hna2]
      split_ifs <;> decide
    · have hl2 : ietLetter3 x₂ = 0 := by
        unfold ietLetter3; rw [ite_false_of (by linarith), ite_false_of (by linarith)]
      rw [hl2]
      unfold ietLetter3
      split_ifs with hlt1
      · decide
      · decide
  have h_orbit_nocut : ∀ p : ℕ, lambda' (prefixOf b5 p) ∉ pi3BaseCuts := by
    intro p hmem
    have hno := (b5_orbit_iet_props p).2.1
    apply hno
    rw [mem_pi3BaseCuts_iff] at hmem
    rw [mem_b5BaseCuts_iff]
    rcases hmem with ⟨i, hi⟩
    exact ⟨⟨i.val, by omega⟩, hi.symm⟩
  have h_orbit_read : ∀ p : ℕ, pi3B5 p = ietLetter3 (lambda' (prefixOf b5 p)) := by
    intro p
    unfold pi3B5
    rw [(b5_orbit_iet_props p).2.2.2, pi3_ietLetter_eq]
  rcases factorsOfLen_eq_range_of_iet ietT ietLetter3 pi3BaseCuts (ietCutSet3 n)
      hJ (ietCutSet3_card n) hinS (fun x hx1 hx2 => ietCutSet3_iff n hx1 hx2) h_trans
      (fun y₁ c y₂ hy1 h1c hc2 hy2 hc _ _ => h_sep y₁ y₂ hy1 (lt_trans h1c hc2) hy2 ⟨c, hc, h1c, hc2⟩) with
    ⟨hinj, hrange_of_orb⟩
  have hpi3_range := hrange_of_orb pi3B5 (fun p => lambda' (prefixOf b5 p))
    (fun p => (b5_orbit_iet_props p).1)
    h_orbit_nocut
    (fun p => (b5_orbit_iet_props p).2.2.1)
    h_orbit_read
    (fun a b ha hab hb => b5_orbit_dense_in_J a b ha hab hb)
  exact factorComplexity_eq_of_bij _ hinj hpi3_range

/-! ## Section 3: Unbounded Balance Defect of `b_5` (Exact Integer `(-1)`-Eigenvector Proof) -/

/-- Exact integer `(-1)`-eigenvector weights `(1, -2, 1, 1, -1)` of `M_{f_5}`. -/
def psiWeight : Fin 5 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => -1

/-- Additive integer functional `ψ(w) = |w|_0 - 2|w|_1 + |w|_2 + |w|_3 - |w|_4`. -/
def psiB5 (w : List (Fin 5)) : ℤ :=
  (w.map psiWeight).sum

theorem psiB5_nil : psiB5 [] = 0 := rfl

theorem psiB5_append (u v : List (Fin 5)) :
    psiB5 (u ++ v) = psiB5 u + psiB5 v := by
  simp [psiB5, List.map_append, List.sum_append]

theorem psiB5_eq_counts (w : List (Fin 5)) :
    psiB5 w = (w.count 0 : ℤ) - 2 * (w.count 1 : ℤ) + (w.count 2 : ℤ) +
      (w.count 3 : ℤ) - (w.count 4 : ℤ) := by
  induction w with
  | nil => simp [psiB5]
  | cons a rest ih =>
    simp only [psiB5, List.map_cons, List.sum_cons, List.count_cons] at ih ⊢
    rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;>
      simp [psiWeight] <;> omega

theorem psiB5_abs_le_two_mul_length (w : List (Fin 5)) :
    -2 * (w.length : ℤ) ≤ psiB5 w ∧ psiB5 w ≤ 2 * (w.length : ℤ) := by
  induction w with
  | nil => simp [psiB5]
  | cons a rest ih =>
    simp only [psiB5, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at ih ⊢
    rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;>
      simp only [psiWeight] <;> omega

/-- Exact `(-1)`-eigenvector scaling: `ψ(f_5(w)) = -ψ(w)` for EVERY finite word `w`. -/
theorem psiB5_applyMorph_fB5 (w : List (Fin 5)) :
    psiB5 (applyMorph fB5 w) = -psiB5 w := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    change psiB5 (fB5 a ++ applyMorph fB5 rest) = -psiB5 (a :: rest)
    have hlet : psiB5 (fB5 a) = -psiWeight a := by
      rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [psiB5_append, ih, hlet]
    simp only [psiB5, List.map_cons, List.sum_cons]
    ring

theorem psiB5_iter_fB5_even (m : ℕ) (w : List (Fin 5)) :
    psiB5 (iterMorph fB5 (2 * m) w) = psiB5 w := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [h]
    simp only [iterMorph]
    rw [psiB5_applyMorph_fB5, psiB5_applyMorph_fB5, neg_neg, ih]

/-- Explicit factor family `unbalWord k` satisfying `0 :: unbalWord k ∈ L(b_5)` and
`ψ(unbalWord k) = k`. -/
def unbalWord : ℕ → List (Fin 5)
  | 0 => []
  | k + 1 => [4, 2, 3] ++ iterMorph fB5 4 (unbalWord k)

theorem fB5_iter4_zero :
    iterMorph fB5 4 [0] = [0, 1, 2, 3, 4, 2, 1, 0, 4, 2, 3] := rfl

theorem isFactorInf_applyMorph_fB5 {u : List (Fin 5)} (hu : IsFactorInf u b5) :
    IsFactorInf (applyMorph fB5 u) b5 := by
  rcases isFactorInf_iff_exists_prefix.mp hu with ⟨n, hfac⟩
  have hfac' : IsFactor (applyMorph fB5 u) (applyMorph fB5 (prefixOf b5 n)) :=
    applyMorph_isFactor fB5 hfac
  rw [← b5_prefix_blockStart n] at hfac'
  exact isFactorInf_of_prefix hfac'

theorem isFactorInf_iter_fB5 (r : ℕ) {u : List (Fin 5)} (hu : IsFactorInf u b5) :
    IsFactorInf (iterMorph fB5 r u) b5 := by
  induction r with
  | zero => exact hu
  | succ r ih => exact isFactorInf_applyMorph_fB5 ih

theorem unbalWord_isFactor (k : ℕ) :
    IsFactorInf (0 :: unbalWord k) b5 := by
  induction k with
  | zero =>
    refine ⟨0, fun j hj => ?_⟩
    simp only [unbalWord, List.length_singleton] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact fixedPoint_eq_iterMorph_getElem fB5 0 fB5_nonempty fB5_prolongable 1 0 (by decide)
  | succ k ih =>
    have h4 := isFactorInf_iter_fB5 4 ih
    have hsplit : iterMorph fB5 4 (0 :: unbalWord k) =
        [0, 1, 2, 3, 4, 2, 1] ++ (0 :: unbalWord (k + 1)) := by
      have hcons : 0 :: unbalWord k = [0] ++ unbalWord k := rfl
      rw [hcons, iterMorph_append, fB5_iter4_zero]
      simp [unbalWord]
    rw [hsplit] at h4
    exact isFactorInf_trans ⟨[0, 1, 2, 3, 4, 2, 1], [], by simp⟩ h4

theorem psiB5_unbalWord (k : ℕ) : psiB5 (unbalWord k) = (k : ℤ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unbalWord, psiB5_append]
    have h423 : psiB5 [4, 2, 3] = 1 := rfl
    have h4 : psiB5 (iterMorph fB5 4 (unbalWord k)) = psiB5 (unbalWord k) :=
      psiB5_iter_fB5_even 2 (unbalWord k)
    rw [h423, h4, ih]
    push_cast; ring

/-- Splitting a list into consecutive blocks of length `L ≥ 1` gives `psiB5` ≥ `q` if every
length-`L` factor has `psiB5 ≥ 1`. -/
theorem psiB5_ge_div_of_all_blocks_pos {L : ℕ} (hL : 1 ≤ L) (w : List (Fin 5))
    (hblock : ∀ u : List (Fin 5), u.length = L → IsFactor u w → 1 ≤ psiB5 u) :
    ((w.length / L : ℕ) : ℤ) - 2 * (L : ℤ) ≤ psiB5 w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hlt : w.length < L
    · have hdiv : n / L = 0 := by rw [← hn]; exact Nat.div_eq_of_lt hlt
      rw [hdiv, Nat.cast_zero]
      have hbd := (psiB5_abs_le_two_mul_length w).1
      have hltZ : (w.length : ℤ) ≤ (L : ℤ) := by exact_mod_cast le_of_lt hlt
      linarith
    · have hge : L ≤ w.length := by omega
      have hsplit : w = w.take L ++ w.drop L := (List.take_append_drop L w).symm
      have htake_len : (w.take L).length = L := by rw [List.length_take]; omega
      have htake_fac : IsFactor (w.take L) w := ⟨[], w.drop L, by simp⟩
      have h1 : 1 ≤ psiB5 (w.take L) := hblock (w.take L) htake_len htake_fac
      have hdrop_len : (w.drop L).length < n := by rw [List.length_drop, ← hn]; omega
      have hdrop_fac : ∀ u : List (Fin 5), u.length = L → IsFactor u (w.drop L) → 1 ≤ psiB5 u :=
        fun u hu hfu => hblock u hu (isFactor_trans hfu ⟨w.take L, [], by simp⟩)
      have hih := ih (w.drop L).length hdrop_len (w.drop L) hdrop_fac rfl
      have hpsi : psiB5 w = psiB5 (w.take L) + psiB5 (w.drop L) := by
        conv_lhs => rw [hsplit]
        exact psiB5_append _ _
      have hdiv_step : n / L = (w.drop L).length / L + 1 := by
        rw [← hn, List.length_drop]
        have heq : w.length = (w.length - L) + L := by omega
        conv_lhs => rw [heq]
        rw [Nat.add_div_right _ (by omega)]
      rw [hdiv_step, Nat.cast_add, Nat.cast_one, hpsi]
      linarith

/-- **Unbounded Balance Defect Theorem (`b5_not_C_balanced`)**:
For EVERY constant `C : ℕ`, `b_5` is NOT `C`-balanced: there exist a length `n`, a letter
`a : Fin 5`, and two length-`n` factors `u, v` of `b_5` whose counts of `a` differ by strictly
more than `C`. -/
theorem b5_not_C_balanced (C : ℕ) :
    ∃ n : ℕ, ∃ u v : List (Fin 5), ∃ a : Fin 5,
      u.length = n ∧ v.length = n ∧ IsFactorInf u b5 ∧ IsFactorInf v b5 ∧
      (C : ℤ) < |(u.count a : ℤ) - (v.count a : ℤ)| := by
  by_contra hbal
  push Not at hbal
  let k := 6 * C + 1
  let u := unbalWord k
  have hu_fac : IsFactorInf u b5 :=
    isFactorInf_trans ⟨[0], [], by simp [u]⟩ (unbalWord_isFactor k)
  let L := u.length
  have hL_pos : 1 ≤ L := by
    dsimp [L, u, k, unbalWord]; simp
  -- Every length-L factor v of b_5 satisfies |psiB5 u - psiB5 v| ≤ 6 * C, hence psiB5 v ≥ 1!
  have hv_pos : ∀ v : List (Fin 5), v.length = L → IsFactorInf v b5 → 1 ≤ psiB5 v := by
    intro v hv_len hv_fac
    have hdiff_le : ∀ a : Fin 5, |(u.count a : ℤ) - (v.count a : ℤ)| ≤ (C : ℤ) :=
      fun a => hbal L u v a rfl hv_len hu_fac hv_fac
    have h0 := abs_le.mp (hdiff_le 0)
    have h1 := abs_le.mp (hdiff_le 1)
    have h2 := abs_le.mp (hdiff_le 2)
    have h3 := abs_le.mp (hdiff_le 3)
    have h4 := abs_le.mp (hdiff_le 4)
    have hpu : psiB5 u = (6 * C + 1 : ℤ) := by
      dsimp [u, k]; rw [psiB5_unbalWord]; push_cast; ring
    rw [psiB5_eq_counts] at hpu ⊢
    omega
  -- Choose m := (L + 1) * L so |f_5^{2*m}(0)| ≥ 2 * (L + 1) * L = (2*L + 2) * L!
  let m := (L + 1) * L
  let pref := iterMorph fB5 (2 * m) [0]
  have hpref_len : (2 * L + 2) * L ≤ pref.length := by
    have h := lt_iterMorph_length fB5 0 fB5_nonempty fB5_prolongable (2 * m)
    dsimp [pref, m] at h ⊢
    nlinarith
  have hpref_fac : ∀ v : List (Fin 5), v.length = L → IsFactor v pref → 1 ≤ psiB5 v := by
    intro v hv_len hfv
    exact hv_pos v hv_len (fixedPoint_isFactorInf_of_iter fB5 0 fB5_nonempty fB5_prolongable hfv)
  have hlb := psiB5_ge_div_of_all_blocks_pos hL_pos pref hpref_fac
  have hdiv_ge : 2 * L + 2 ≤ pref.length / L := by
    exact (Nat.le_div_iff_mul_le (by omega)).mpr hpref_len
  have hpsi_pref : psiB5 pref = 1 := by
    dsimp [pref]
    rw [psiB5_iter_fB5_even]
    rfl
  rw [hpsi_pref] at hlb
  have hdivZ : (2 * (L : ℤ) + 2) ≤ ((pref.length / L : ℕ) : ℤ) := by exact_mod_cast hdiv_ge
  omega

/-- Immediate explicit witness (`010` vs `123` of length `3`) that `b_5` is not 1-balanced. -/
theorem b5_not_balanced :
    ∃ n : ℕ, ∃ u v : List (Fin 5), ∃ a : Fin 5,
      u.length = n ∧ v.length = n ∧ IsFactorInf u b5 ∧ IsFactorInf v b5 ∧
      (1 : ℤ) < |(u.count a : ℤ) - (v.count a : ℤ)| :=
  b5_not_C_balanced 1

/-! ## Section 4: Badkobeh–Ochem (2015) Theorem 1 — Exact `F_5` Avoidance -/

/-- Exact 16-element forbidden factor set `F_5` of Badkobeh & Ochem (*TCS* 588, 2015, Thm. 1). -/
def badkobehOchemF5 : List (List (Fin 5)) :=
  [[0, 2], [0, 3], [1, 3], [1, 4], [2, 0], [2, 4], [3, 1], [3, 2],
   [4, 0], [4, 1], [4, 3], [1, 2, 1], [2, 1, 2], [3, 0, 4],
   [3, 4, 2, 3], [4, 2, 3, 4]]

/-- `F_5` is invariant under reversal + `(3 ↔ 4)` swap (Badkobeh–Ochem 2015, Sec. 3). -/
theorem badkobehOchemF5_rev_swap34_invariant :
    ∀ w ∈ badkobehOchemF5, revSwap34 w ∈ badkobehOchemF5 := by
  decide

/-- Sym5-encoded copy of `F_5` for fast pure-kernel `rfl` avoidance verification on `g10Val`. -/
def badkobehOchemF5Sym : List (List Sym5) :=
  badkobehOchemF5.map (List.map Sym5.ofFin)

def listEqSym : List Sym5 → List Sym5 → Bool
  | [], [] => true
  | x :: xs, y :: ys => Sym5.beq x y && listEqSym xs ys
  | _, _ => false

theorem listEqSym_iff (u v : List Sym5) : listEqSym u v = true ↔ u = v := by
  induction u generalizing v with
  | nil => cases v <;> simp [listEqSym]
  | cons x xs ih =>
    cases v with
    | nil => simp [listEqSym]
    | cons y ys =>
      simp only [listEqSym, Bool.and_eq_true, Sym5.beq_iff_eq, ih, List.cons.injEq]

def notPrefixSym (pat s : List Sym5) : Bool :=
  !(hasLenAtLeast pat.length s && listEqSym (s.take pat.length) pat)

def checkNoF5AtSuffix (s : List Sym5) : Bool :=
  allTR (fun pat => notPrefixSym pat s) badkobehOchemF5Sym

theorem twoFactor_avoids_F5_0 :
    scanDrops256 checkNoF5AtSuffix (g10Val .s0 ++ g10Val .s1) = true := rfl
theorem twoFactor_avoids_F5_1 :
    scanDrops256 checkNoF5AtSuffix (g10Val .s0 ++ g10Val .s4) = true := rfl
theorem twoFactor_avoids_F5_2 :
    scanDrops256 checkNoF5AtSuffix (g10Val .s1 ++ g10Val .s0) = true := rfl
theorem twoFactor_avoids_F5_3 :
    scanDrops256 checkNoF5AtSuffix (g10Val .s1 ++ g10Val .s2) = true := rfl
theorem twoFactor_avoids_F5_4 :
    scanDrops256 checkNoF5AtSuffix (g10Val .s2 ++ g10Val .s1) = true := rfl
theorem twoFactor_avoids_F5_5 :
    scanDrops256 checkNoF5AtSuffix (g10Val .s2 ++ g10Val .s3) = true := rfl
theorem twoFactor_avoids_F5_6 :
    scanDrops256 checkNoF5AtSuffix (g10Val .s3 ++ g10Val .s0) = true := rfl
theorem twoFactor_avoids_F5_7 :
    scanDrops256 checkNoF5AtSuffix (g10Val .s3 ++ g10Val .s4) = true := rfl
theorem twoFactor_avoids_F5_8 :
    scanDrops256 checkNoF5AtSuffix (g10Val .s4 ++ g10Val .s2) = true := rfl

theorem all_twoFactor_avoids_F5 :
    twoFactorSymList.all (fun p => scanDrops256 checkNoF5AtSuffix (g10Val p.1 ++ g10Val p.2)) = true := by
  simp only [twoFactorSymList, List.all_cons, List.all_nil, Bool.and_true]
  rw [twoFactor_avoids_F5_0, twoFactor_avoids_F5_1, twoFactor_avoids_F5_2,
      twoFactor_avoids_F5_3, twoFactor_avoids_F5_4, twoFactor_avoids_F5_5,
      twoFactor_avoids_F5_6, twoFactor_avoids_F5_7, twoFactor_avoids_F5_8]
  rfl

/-- **Badkobeh–Ochem (2015, Theorem 1) Avoidance Theorem (`b5_avoids_F5`)**:
Every one of the 16 forbidden factors in `F_5` is avoided by `b_5`. Combined with
`b5_squarefree`, this verifies the full avoidance half of Badkobeh–Ochem Theorem 1. -/
theorem b5_avoids_F5 : ∀ w ∈ badkobehOchemF5, ¬ IsFactorInf w b5 := by
  intro w hw ⟨q, hocc⟩
  have hlen48 : w.length ≤ 48 := by
    have : ∀ u ∈ badkobehOchemF5, u.length ≤ 48 := by decide
    exact this w hw
  rcases symSlice_in_g10_pair q w.length hlen48 with ⟨a, b, o, hmem, ho256, hfit, hslice⟩
  have hpair := List.all_eq_true.mp all_twoFactor_avoids_F5 (a, b) hmem
  have hsuf := (scanDrops256_iff checkNoF5AtSuffix (g10Val a ++ g10Val b)).mp hpair o ho256
  unfold checkNoF5AtSuffix at hsuf
  rw [allTR_eq_all] at hsuf
  have hpat_mem : w.map Sym5.ofFin ∈ badkobehOchemF5Sym := List.mem_map_of_mem hw
  have hnot := List.all_eq_true.mp hsuf (w.map Sym5.ofFin) hpat_mem
  unfold notPrefixSym at hnot
  have hpat_len : (w.map Sym5.ofFin).length = w.length := List.length_map _
  have hhas : hasLenAtLeast (w.map Sym5.ofFin).length ((g10Val a ++ g10Val b).drop o) = true := by
    rw [hpat_len]
    exact (hasLenAtLeast_iff _ _).mpr (by rw [List.length_drop]; omega)
  have htake_eq : ((g10Val a ++ g10Val b).drop o).take (w.map Sym5.ofFin).length =
      w.map Sym5.ofFin := by
    rw [hpat_len, ← hslice]
    apply List.ext_getElem
    · simp [symSlice_length]
    · intro j hj1 hj2
      simp only [symSlice_getElem, List.getElem_map, b5Sym]
      rw [hocc j (by simp [symSlice_length] at hj1; exact hj1)]
  have heq_true : listEqSym (((g10Val a ++ g10Val b).drop o).take (w.map Sym5.ofFin).length)
      (w.map Sym5.ofFin) = true := (listEqSym_iff _ _).mpr htake_eq
  rw [hhas, heq_true] at hnot
  exact Bool.noConfusion hnot

/-! ## Section 5: Characteristic Polynomial of `M` & Exact `A005252` Prefix-Length Recurrence -/

/-- Exact Cayley–Hamilton identity for the `5 × 5` incidence matrix `M` of `f_5`:
`M^5 v + M^2 v = M^4 v + M^3 v + M v + v` (characteristic polynomial
`x^5 - x^4 - x^3 + x^2 - x - 1 = (x + 1)(x^2 - x - 1)(x^2 - x + 1)`). -/
theorem stepMZ_charpoly (v : Vec5Z) :
    (stepMZ (stepMZ (stepMZ (stepMZ (stepMZ v))))).sum + (stepMZ (stepMZ v)).sum =
    (stepMZ (stepMZ (stepMZ (stepMZ v)))).sum + (stepMZ (stepMZ (stepMZ v))).sum +
    (stepMZ v).sum + v.sum := by
  cases v
  simp only [stepMZ, Vec5Z.sum]
  ring

theorem parikhSym_iterSym5 (k : ℕ) (w : List Sym5) :
    parikhSym (iterSym5 k w) = (stepMZ^[k]) (parikhSym w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change parikhSym (morphSym5 (iterSym5 k w)) = stepMZ ((stepMZ^[k]) (parikhSym w))
    rw [parikhSym_morphSym5, ih]

theorem iterSym5_length_eq_iterMorph_fB5 (k : ℕ) (w : List (Fin 5)) :
    (iterSym5 k (w.map Sym5.ofFin)).length = (iterMorph fB5 k w).length := by
  have h : iterSym5 k (w.map Sym5.ofFin) = (iterMorph fB5 k w).map Sym5.ofFin := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change morphSym5 (iterSym5 k (w.map Sym5.ofFin)) =
        (applyMorph fB5 (iterMorph fB5 k w)).map Sym5.ofFin
      rw [ih]
      have hmorph : ∀ u : List (Fin 5), morphSym5 (u.map Sym5.ofFin) =
          (applyMorph fB5 u).map Sym5.ofFin := by
        intro u
        induction u with
        | nil => rfl
        | cons a rest ihu =>
          change fSym5 (Sym5.ofFin a) ++ morphSym5 (rest.map Sym5.ofFin) =
            (fB5 a ++ applyMorph fB5 rest).map Sym5.ofFin
          have hlet : fSym5 (Sym5.ofFin a) = (fB5 a).map Sym5.ofFin := by
            rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;> rfl
          rw [List.map_append, hlet, ihu]
      exact hmorph (iterMorph fB5 k w)
  rw [h, List.length_map]

/-- **Exact 5th-Order Prefix-Length Recurrence (`fB5_iter_length_rec`, OEIS `A005252`)**:
For EVERY starting word `w : List (Fin 5)` and EVERY `k : ℕ`:
`|f_5^{k+5}(w)| + |f_5^{k+2}(w)| = |f_5^{k+4}(w)| + |f_5^{k+3}(w)| + |f_5^{k+1}(w)| + |f_5^k(w)|`. -/
theorem fB5_iter_length_rec (w : List (Fin 5)) (k : ℕ) :
    (iterMorph fB5 (k + 5) w).length + (iterMorph fB5 (k + 2) w).length =
    (iterMorph fB5 (k + 4) w).length + (iterMorph fB5 (k + 3) w).length +
    (iterMorph fB5 (k + 1) w).length + (iterMorph fB5 k w).length := by
  have hlen : ∀ n : ℕ, ((iterMorph fB5 n w).length : ℤ) =
      ((stepMZ^[n]) (parikhSym (w.map Sym5.ofFin))).sum := by
    intro n
    rw [← iterSym5_length_eq_iterMorph_fB5, ← parikhSym_sum_eq_length, parikhSym_iterSym5]
  have hch := stepMZ_charpoly ((stepMZ^[k]) (parikhSym (w.map Sym5.ofFin)))
  have h1 : stepMZ ((stepMZ^[k]) (parikhSym (w.map Sym5.ofFin))) =
      (stepMZ^[k + 1]) (parikhSym (w.map Sym5.ofFin)) := (Function.iterate_succ_apply' _ _ _).symm
  have h2 : stepMZ ((stepMZ^[k + 1]) (parikhSym (w.map Sym5.ofFin))) =
      (stepMZ^[k + 2]) (parikhSym (w.map Sym5.ofFin)) := (Function.iterate_succ_apply' _ _ _).symm
  have h3 : stepMZ ((stepMZ^[k + 2]) (parikhSym (w.map Sym5.ofFin))) =
      (stepMZ^[k + 3]) (parikhSym (w.map Sym5.ofFin)) := (Function.iterate_succ_apply' _ _ _).symm
  have h4 : stepMZ ((stepMZ^[k + 3]) (parikhSym (w.map Sym5.ofFin))) =
      (stepMZ^[k + 4]) (parikhSym (w.map Sym5.ofFin)) := (Function.iterate_succ_apply' _ _ _).symm
  have h5 : stepMZ ((stepMZ^[k + 4]) (parikhSym (w.map Sym5.ofFin))) =
      (stepMZ^[k + 5]) (parikhSym (w.map Sym5.ofFin)) := (Function.iterate_succ_apply' _ _ _).symm
  rw [h1, h2, h3, h4, h5] at hch
  rw [← hlen (k + 5), ← hlen (k + 2), ← hlen (k + 4), ← hlen (k + 3), ← hlen (k + 1), ← hlen k] at hch
  exact_mod_cast hch

/-- Initial prefix lengths `|f_5^k(0)|` for `k = 0..7` (`1, 2, 4, 7, 11, 17, 27, 44`). -/
theorem fB5_prefix_lengths_0_to_7 :
    (List.range 8).map (fun k => (iterMorph fB5 k [0]).length) = [1, 2, 4, 7, 11, 17, 27, 44] := rfl

end BadkobehOchemB5
