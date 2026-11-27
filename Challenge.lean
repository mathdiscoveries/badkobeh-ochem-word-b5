/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Palomar Challenge: Badkobeh–Ochem's 5-Letter Word `b₅`

Self-contained Lean 4 + Mathlib statements resolving all four questions and
observations (Q1, Q2, O1, O2) from Badkobeh and Ochem (*Theoret. Comput. Sci.*
588, 2015) for the fixed point `b₅ = f₅^ω(0)` of
`0 ↦ 01, 1 ↦ 23, 2 ↦ 4, 3 ↦ 21, 4 ↦ 0`, together with sharp second-order
critical-exponent bounds, asymptotic critical exponent, irrationality, reversal-
swap symmetry, ternary 3-IET projection, unbounded balance defect, `F₅`
avoidance, and the 5th-order `A005252` length recurrence.
-/

@[expose] public section

namespace BadkobehOchemB5Challenge

/-- The golden ratio `φ = (1 + √5) / 2`. -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- Prefix of length `n` of an infinite word `W : ℕ → α`. -/
def prefixOf {α : Type*} (W : ℕ → α) (n : ℕ) : List α :=
  List.ofFn fun i : Fin n => W i.val

/-- `u` occurs as a contiguous factor of the infinite word `W : ℕ → α`. -/
def IsFactorInf {α : Type*} (u : List α) (W : ℕ → α) : Prop :=
  ∃ i : ℕ, ∀ j (hj : j < u.length), W (i + j) = u[j]

/-- Apply a morphism `f : α → List β` to a finite word `w : List α`. -/
def applyMorph {α β : Type*} (f : α → List β) (w : List α) : List β :=
  w.flatMap f

/-- Iterate an endomorphism `f : α → List α` `n` times on `w`. -/
def iterMorph {α : Type*} (f : α → List α) : ℕ → List α → List α
  | 0, w => w
  | n + 1, w => applyMorph f (iterMorph f n w)

/-- Badkobeh and Ochem's 5-letter morphism `f₅ : {0,1,2,3,4} → {0,1,2,3,4}^*`:
`0 ↦ 01`, `1 ↦ 23`, `2 ↦ 4`, `3 ↦ 21`, `4 ↦ 0`. -/
def fB5 : Fin 5 → List (Fin 5)
  | 0 => [0, 1]
  | 1 => [2, 3]
  | 2 => [4]
  | 3 => [2, 1]
  | 4 => [0]

/-- The infinite fixed point `b₅ = f₅^ω(0)`. Since `|f₅^i(0)| > i` for every `i`,
`.getD i 0` extracts the exact `i`-th letter. -/
def b5 (i : ℕ) : Fin 5 :=
  (iterMorph fB5 i [0]).getD i 0

/-- Left eigenvector weights for `-1 / φ` giving the 3-interval exchange translations. -/
noncomputable def l' : Fin 5 → ℝ
  | 0 => 1
  | 1 => -φ
  | 2 => 1 + φ
  | 3 => -φ
  | 4 => -φ

/-- Cumulative orbit coordinate `λ'(w) = ∑_{a ∈ w} l'(a)` along a finite prefix `w`. -/
noncomputable def lambda' (w : List (Fin 5)) : ℝ :=
  (w.map l').sum

/-- Set of length-`n` factors of an infinite word `W : ℕ → α`. -/
def FactorsOfLen {α : Type*} (W : ℕ → α) (n : ℕ) : Set (List α) :=
  { w : List α | w.length = n ∧ IsFactorInf w W }

/-- Factor complexity `p_W(n) = |L_n(W)|`. -/
noncomputable def factorComplexity {α : Type*} (W : ℕ → α) (n : ℕ) : ℕ :=
  (FactorsOfLen W n).ncard

/-- Fibonacci morphism `0 ↦ 01, 1 ↦ 0` on `Bool` (`false = 0`, `true = 1`). -/
def fibMorph : Bool → List Bool
  | false => [false, true]
  | true => [false]

/-- The infinite Fibonacci word `f = fibMorph^ω(0)`. -/
def fibWord (i : ℕ) : Bool :=
  (iterMorph fibMorph i [false]).getD i false

/-- Badkobeh and Ochem's binary projection `g_fib : 0 ↦ 01, 1 ↦ 0, 2 ↦ 1, 3 ↦ 0, 4 ↦ 0`. -/
def gFib : Fin 5 → List Bool
  | 0 => [false, true]
  | 1 => [false]
  | 2 => [true]
  | 3 => [false]
  | 4 => [false]

/-- The infinite binary image `g_fib(b₅)`. -/
def gFibB5 (i : ℕ) : Bool :=
  (applyMorph gFib (prefixOf b5 (i + 1))).getD i false

/-- Badkobeh and Ochem's erasing binary projection
`g_rf : 0 ↦ 01, 1 ↦ 10, 2 ↦ ε, 3 ↦ 11, 4 ↦ 00`. -/
def gRf : Fin 5 → List Bool
  | ⟨0, _⟩ => [false, true]
  | ⟨1, _⟩ => [true, false]
  | ⟨2, _⟩ => []
  | ⟨3, _⟩ => [true, true]
  | ⟨4, _⟩ => [false, false]

/-- The infinite binary image `g_rf(b₅)`. Every prefix of length `2(k + 1)` of `b₅`
maps under `g_rf` to a binary word of length strictly exceeding `k`. -/
def gRfB5 (k : ℕ) : Bool :=
  (applyMorph gRf (prefixOf b5 (2 * (k + 1)))).getD k false

/-- The Rote–Fibonacci word `r`: `r(0) = 0`, `r(k + 1) = r(k) ⊕ ¬f(k + 1)`. -/
def roteFib : ℕ → Bool
  | 0 => false
  | k + 1 => xor (roteFib k) (!(fibWord (k + 1)))

/-- `p` is a period of the finite word `w`. -/
def IsPeriod {α : Type*} (w : List α) (p : ℕ) : Prop :=
  ∀ i : ℕ, ∀ hi : i + p < w.length, w[i]'(Nat.lt_of_le_of_lt (Nat.le_add_right i p) hi) = w[i + p]'hi

/-- Set of fractional repetition exponents `|w| / p` over factors `w` of `W` and periods `p ≥ 1`. -/
def ExponentSet {α : Type*} (W : ℕ → α) : Set ℝ :=
  { e : ℝ | ∃ w p, IsFactorInf w W ∧ 1 ≤ p ∧ IsPeriod w p ∧ e = (w.length : ℝ) / (p : ℝ) }

/-- Critical exponent `E(W) = sup {|w| / p}`. -/
noncomputable def critExp {α : Type*} (W : ℕ → α) : ℝ :=
  sSup (ExponentSet W)

/-- Set of repetition deficits `φ p - 2(|w| - p)` over factors `w` of `W` and periods `p ≥ 1`. -/
def DeficitSet (W : ℕ → Fin 5) : Set ℝ :=
  { d : ℝ | ∃ w : List (Fin 5), ∃ p : ℕ,
      IsFactorInf w W ∧ 1 ≤ p ∧ IsPeriod w p ∧
      d = φ * (p : ℝ) - 2 * ((w.length : ℝ) - (p : ℝ)) }

/-- Set of repetition exponents with period `p ≥ max 1 L`. -/
def AsympExponentSet (W : ℕ → Fin 5) (L : ℕ) : Set ℝ :=
  { r : ℝ | ∃ w : List (Fin 5), ∃ p : ℕ,
      IsFactorInf w W ∧ L ≤ p ∧ 1 ≤ p ∧ IsPeriod w p ∧ r = (w.length : ℝ) / (p : ℝ) }

/-- Letter involution swapping `3 ↔ 4` and fixing `0, 1, 2`. -/
def swap34 : Fin 5 → Fin 5
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 3

/-- Word reversal composed with the `3 ↔ 4` involution. -/
def revSwap34 (w : List (Fin 5)) : List (Fin 5) :=
  w.reverse.map swap34

/-- Ternary 3-IET coding collapse `π₃ : 0 ↦ 1, 1 ↦ 0, 2 ↦ 2, 3 ↦ 0, 4 ↦ 0`. -/
def pi3 : Fin 5 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 0

/-- The ternary 3-interval exchange image `π₃(b₅)`. -/
def pi3B5 (p : ℕ) : Fin 3 :=
  pi3 (b5 p)

/-- **5-Interval Exchange Coding**: For every `p : ℕ`, the cumulative weight
`x_p = λ'(b₅[0..p))` lies strictly in `(-φ²/2, φ³/2)` and `b₅(p)` is uniquely
determined by which of the five open subintervals `P₂, P₀, P₄, P₁, P₃` contains `x_p`. -/
theorem b5_codes_interval_translation (p : ℕ) :
    let x_p := lambda' (prefixOf b5 p)
    (-φ ^ 2 / 2 < x_p ∧ x_p < φ ^ 3 / 2) ∧
    (b5 p = 2 ↔ -φ ^ 2 / 2 < x_p ∧ x_p < -1 / 2) ∧
    (b5 p = 0 ↔ -1 / 2 < x_p ∧ x_p < (φ - 1) / 2) ∧
    (b5 p = 4 ↔ (φ - 1) / 2 < x_p ∧ x_p < φ / 2) ∧
    (b5 p = 1 ↔ φ / 2 < x_p ∧ x_p < φ) ∧
    (b5 p = 3 ↔ φ < x_p ∧ x_p < φ ^ 3 / 2) := by
  sorry

/-- **Question (Q1)**: For every `n : ℕ`, `b₅` has exact factor complexity `4n + 1`. -/
theorem b5_factor_complexity (n : ℕ) :
    factorComplexity b5 n = 4 * n + 1 := by
  sorry

/-- **Observation (O1)**: `g_fib(b₅)` has the exact same length-`n` factors as
the Fibonacci word `f` for every `n : ℕ`, with complexity `n + 1`. -/
theorem b5_sturmian_projection (n : ℕ) :
    FactorsOfLen gFibB5 n = FactorsOfLen fibWord n ∧
    factorComplexity gFibB5 n = n + 1 := by
  sorry

/-- **Observation (O2)**: `g_rf(b₅)` has the exact same length-`n` factors as
the Rote–Fibonacci word `r` for every `n : ℕ`, with complexity `2n` for `n ≥ 1`. -/
theorem b5_rote_fibonacci_projection (n : ℕ) :
    FactorsOfLen gRfB5 n = FactorsOfLen roteFib n ∧
    (1 ≤ n → factorComplexity gRfB5 n = 2 * n) := by
  sorry

/-- **Question (Q2)**: The critical exponent of `b₅` is exactly `(5 + √5) / 4`
and is strictly unattained by any factor. -/
theorem b5_critical_exponent :
    critExp b5 = (5 + Real.sqrt 5) / 4 ∧
    ¬ ∃ w p, IsFactorInf w b5 ∧ 1 ≤ p ∧ IsPeriod w p ∧
      (w.length : ℝ) / (p : ℝ) = (5 + Real.sqrt 5) / 4 := by
  sorry

/-- **Sharp Second-Order Critical-Exponent Bound and Deficit Infimum**:
Every factor `w` of `b₅` with period `p ≥ 1` satisfies
`|w|/p < (5 + √5)/4 - (7 - √5)/(8p)`, and the infimum of `φp - 2(|w| - p)` is
exactly `(7 - √5)/4` and is never attained. -/
theorem b5_sharp_second_order_and_deficit :
    sInf (DeficitSet b5) = (7 - Real.sqrt 5) / 4 ∧
    (∀ w p, IsFactorInf w b5 → 1 ≤ p → IsPeriod w p →
      (w.length : ℝ) / (p : ℝ) < (5 + Real.sqrt 5) / 4 - (7 - Real.sqrt 5) / (8 * (p : ℝ))) ∧
    ¬ ∃ w p, IsFactorInf w b5 ∧ 1 ≤ p ∧ IsPeriod w p ∧
      φ * (p : ℝ) - 2 * ((w.length : ℝ) - (p : ℝ)) = (7 - Real.sqrt 5) / 4 := by
  sorry

/-- **Asymptotic Critical Exponent and Irrationality**:
`E*(b₅) = (5 + √5) / 4` (for every period threshold `L`) and `E(b₅)` is irrational. -/
theorem b5_asymp_critExp_and_irrational :
    (∀ L : ℕ, sSup (AsympExponentSet b5 L) = (5 + Real.sqrt 5) / 4) ∧
    Irrational (critExp b5) := by
  sorry

/-- **Reversal–Swap Symmetry**: The factor language of `b₅` is invariant under
reversal composed with swapping `3 ↔ 4`. -/
theorem b5_language_rev_swap34_invariant (w : List (Fin 5)) :
    IsFactorInf w b5 ↔ IsFactorInf (revSwap34 w) b5 := by
  sorry

/-- **Ternary 3-IET Complexity**: The 3-letter collapse `π₃(b₅)` has exact
factor complexity `2n + 1` for every `n : ℕ`. -/
theorem pi3B5_factor_complexity (n : ℕ) :
    factorComplexity pi3B5 n = 2 * n + 1 := by
  sorry

/-- **Unbounded Balance Defect**: `b₅` is not `C`-balanced for any `C : ℕ`. -/
theorem b5_not_C_balanced (C : ℕ) :
    ∃ n : ℕ, ∃ u v : List (Fin 5), ∃ a : Fin 5,
      u.length = n ∧ v.length = n ∧ IsFactorInf u b5 ∧ IsFactorInf v b5 ∧
      (C : ℤ) < |(u.count a : ℤ) - (v.count a : ℤ)| := by
  sorry

/-- **5th-Order `A005252` Length Recurrence**:
`|f₅^{k+5}(w)| + |f₅^{k+2}(w)| = |f₅^{k+4}(w)| + |f₅^{k+3}(w)| + |f₅^{k+1}(w)| + |f₅^k(w)|`
for every finite word `w` and `k : ℕ`. -/
theorem fB5_iter_length_rec (w : List (Fin 5)) (k : ℕ) :
    (iterMorph fB5 (k + 5) w).length + (iterMorph fB5 (k + 2) w).length =
    (iterMorph fB5 (k + 4) w).length + (iterMorph fB5 (k + 3) w).length +
    (iterMorph fB5 (k + 1) w).length + (iterMorph fB5 k w).length := by
  sorry

end BadkobehOchemB5Challenge
