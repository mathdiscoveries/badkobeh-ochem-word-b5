/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic

/-!
# Fixed Point `b_5`, Exact `ℚ(√5)` / `ℤ[φ]` Arithmetic, and 5-Interval Coding (`R18-2-1`)

This module formalizes the foundational objects for Badkobeh & Ochem's (*Theoret. Comput. Sci.*
588, 2015) infinite 5-letter morphic word `b_5 = f_5^ω(0)` (`0 ↦ 01, 1 ↦ 23, 2 ↦ 4, 3 ↦ 21,
4 ↦ 0`; also Ochem & Rosenfeld's `b_5` in *Electron. J. Combin.* 28(1) #P1.4, 2021):

1. **Golden ratio `φ = (1 + √5) / 2` and exact quadratic arithmetic** (`QSqrt5` for `a + b φ`
   with `a, b : ℚ`, and `ZPhi` for `a + b φ` with `a, b : ℤ`), with pure-rational/integer
   decidable positivity (`QSqrt5.isPos_iff_toReal_pos`, `ZPhi.isPos_iff_toReal_pos`) and
   injectivity into `ℝ` via elementary irrationality of `√5` (`rat_add_rat_mul_phi_eq_zero`).
2. **Prolongable morphism framework and fixed point `b5 : ℕ → Fin 5`**, together with the
   monotone block-boundary sequence `blockStart` and exact unique decomposition
   `exists_block_decomp` of every position `q` in `b5 = fB5(b5)`.
3. **Conjugate letter lengths `l'` and word sum `lambda'`**, proving unconditional
   non-vanishing `lambdaPrime_ne_zero_of_ne_nil` for every non-empty word `w : List (Fin 5)` and
   the exact left-eigenvector scaling law `lambdaPrime_applyMorph_fB5`:
   `lambda' (applyMorph fB5 w) = (-1 / φ) * lambda' w`.
4. **Theorem `R18-2-1` Part (1) (`b5_codes_interval_translation`)**: proved 100% unconditionally
   by strong induction on `p : ℕ` — `x_p = lambda' (prefixOf b5 p)` always lies in
   `(-φ^2 / 2, φ^3 / 2)` and determines `b5 p` via the five open intervals
   `P_2, P_0, P_4, P_1, P_3`.
5. **General Interval-Coding Convexity Sign Law (`b5_uvu_opposite_signs_of_not_square`)** and
   XYX digraph definitions (`LooplessDigraph`, `OccursDigraphInf`, `AvoidsDigraphInf`,
   `HasOddCycle`, `C3`, `TT`, `Kn`, `RelB5`).
-/

@[expose] public section

namespace BadkobehOchemB5

/-! ## Section 1: Golden Ratio `φ`, Irrationality of `√5`, and Exact `ℚ(√5)` / `ℤ[φ]` -/

/-- The golden ratio `φ = (1 + √5) / 2`. -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

theorem sqrt5_pos : 0 < Real.sqrt 5 :=
  Real.sqrt_pos.mpr (by norm_num)

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num)

theorem two_lt_sqrt5 : 2 < Real.sqrt 5 := by
  have h : (2 : ℝ) ^ 2 < Real.sqrt 5 ^ 2 := by rw [sqrt5_sq]; norm_num
  nlinarith [sqrt5_pos]

theorem sqrt5_lt_three : Real.sqrt 5 < 3 := by
  have h : Real.sqrt 5 ^ 2 < (3 : ℝ) ^ 2 := by rw [sqrt5_sq]; norm_num
  nlinarith [sqrt5_pos]

theorem phi_pos : 0 < φ := by
  unfold φ; linarith [sqrt5_pos]

theorem one_lt_phi : 1 < φ := by
  unfold φ; linarith [two_lt_sqrt5]

theorem phi_lt_two : φ < 2 := by
  unfold φ; linarith [sqrt5_lt_three]

theorem phi_sq : φ ^ 2 = φ + 1 := by
  unfold φ
  nlinarith [sqrt5_sq]

theorem phi_cube : φ ^ 3 = 2 * φ + 1 := by
  calc
    φ ^ 3 = φ ^ 2 * φ := by ring
    _ = (φ + 1) * φ := by rw [phi_sq]
    _ = φ ^ 2 + φ := by ring
    _ = 2 * φ + 1 := by rw [phi_sq]; ring

theorem inv_phi : 1 / φ = φ - 1 := by
  have hne : φ ≠ 0 := ne_of_gt phi_pos
  rw [div_eq_iff hne]
  nlinarith [phi_sq]

theorem neg_inv_phi : -1 / φ = 1 - φ := by
  have hne : φ ≠ 0 := ne_of_gt phi_pos
  rw [div_eq_iff hne]
  nlinarith [phi_sq]

/-- Prime divisibility mod 5: if `5 ∣ k^2` in `ℤ`, then `5 ∣ k`. -/
theorem five_dvd_of_five_dvd_sq {k : ℤ} (h : 5 ∣ k ^ 2) : 5 ∣ k := by
  have hmod : k ^ 2 % 5 = 0 := Int.emod_eq_zero_of_dvd h
  have hsq : k ^ 2 % 5 = (k % 5) * (k % 5) % 5 := by
    rw [sq, Int.mul_emod]
  rw [hsq] at hmod
  set r := k % 5
  have hr0 : 0 ≤ r := Int.emod_nonneg k (by decide)
  have hr5 : r < 5 := Int.emod_lt_of_pos k (by decide)
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hcases with hr | hr | hr | hr | hr
  · exact Int.dvd_of_emod_eq_zero hr
  all_goals
    rw [hr] at hmod
    norm_num at hmod

/-- Elementary infinite descent in `ℤ`: `m^2 = 5 n^2` has only the trivial solution `(0, 0)`. -/
theorem int_sq_eq_five_mul_sq_aux :
    ∀ K : ℕ, ∀ m n : ℤ, m.natAbs ≤ K → m ^ 2 = 5 * n ^ 2 → m = 0 ∧ n = 0 := by
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro m n hm hsq
    by_cases hm0 : m = 0
    · subst hm0
      have hn2 : n ^ 2 = 0 := by omega
      exact ⟨rfl, sq_eq_zero_iff.mp hn2⟩
    · have hdvd_m : 5 ∣ m := five_dvd_of_five_dvd_sq ⟨n ^ 2, hsq⟩
      rcases hdvd_m with ⟨m₁, rfl⟩
      have hn_sq : n ^ 2 = 5 * m₁ ^ 2 := by linarith
      have hdvd_n : 5 ∣ n := five_dvd_of_five_dvd_sq ⟨m₁ ^ 2, hn_sq⟩
      rcases hdvd_n with ⟨n₁, rfl⟩
      have hm1_sq : m₁ ^ 2 = 5 * n₁ ^ 2 := by linarith
      have hm1_ne : m₁ ≠ 0 := by omega
      have hpos : 0 < m₁.natAbs := Int.natAbs_pos.mpr hm1_ne
      have habs : (5 * m₁).natAbs = 5 * m₁.natAbs := by
        rw [Int.natAbs_mul]; rfl
      have hlt : m₁.natAbs < K := by omega
      rcases ih m₁.natAbs hlt m₁ n₁ (le_refl _) hm1_sq with ⟨rfl, rfl⟩
      simp

theorem int_sq_eq_five_mul_sq {m n : ℤ} (h : m ^ 2 = 5 * n ^ 2) : m = 0 ∧ n = 0 :=
  int_sq_eq_five_mul_sq_aux m.natAbs m n (le_refl _) h

theorem rat_sq_eq_five_mul_sq {p q : ℚ} (h : p ^ 2 = 5 * q ^ 2) : p = 0 ∧ q = 0 := by
  let D : ℤ := (p.den : ℤ) * (q.den : ℤ)
  have hp : (p * (D : ℚ)) = ((p.num * (q.den : ℤ) : ℤ) : ℚ) := by
    dsimp [D]
    push_cast
    calc
      p * ((p.den : ℚ) * (q.den : ℚ)) = (p * (p.den : ℚ)) * (q.den : ℚ) := by ring
      _ = (p.num : ℚ) * (q.den : ℚ) := by rw [Rat.mul_den_eq_num]
  have hq : (q * (D : ℚ)) = ((q.num * (p.den : ℤ) : ℤ) : ℚ) := by
    dsimp [D]
    push_cast
    calc
      q * ((p.den : ℚ) * (q.den : ℚ)) = (q * (q.den : ℚ)) * (p.den : ℚ) := by ring
      _ = (q.num : ℚ) * (p.den : ℚ) := by rw [Rat.mul_den_eq_num]
  have hmul : (p * (D : ℚ)) ^ 2 = 5 * (q * (D : ℚ)) ^ 2 := by
    linear_combination (D : ℚ) ^ 2 * h
  rw [hp, hq] at hmul
  have hint : (p.num * (q.den : ℤ)) ^ 2 = 5 * (q.num * (p.den : ℤ)) ^ 2 := by
    exact_mod_cast hmul
  rcases int_sq_eq_five_mul_sq hint with ⟨h1, h2⟩
  have hqden : (q.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr q.pos.ne'
  have hpden : (p.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr p.pos.ne'
  have hpnum : p.num = 0 := (mul_eq_zero.mp h1).resolve_right hqden
  have hqnum : q.num = 0 := (mul_eq_zero.mp h2).resolve_right hpden
  exact ⟨Rat.num_eq_zero.mp hpnum, Rat.num_eq_zero.mp hqnum⟩

/-- `1` and `√5` are `ℚ`-linearly independent in `ℝ`. -/
theorem rat_add_rat_mul_sqrt5_eq_zero {p q : ℚ}
    (h : (p : ℝ) + (q : ℝ) * Real.sqrt 5 = 0) : p = 0 ∧ q = 0 := by
  have hsqR : ((p : ℝ)) ^ 2 = 5 * ((q : ℝ)) ^ 2 := by
    have h1 : (p : ℝ) = -(q : ℝ) * Real.sqrt 5 := by linarith
    calc
      (p : ℝ) ^ 2 = (-(q : ℝ) * Real.sqrt 5) ^ 2 := by rw [h1]
      _ = (q : ℝ) ^ 2 * Real.sqrt 5 ^ 2 := by ring
      _ = 5 * (q : ℝ) ^ 2 := by rw [sqrt5_sq]; ring
  have hsqQ : p ^ 2 = 5 * q ^ 2 := by exact_mod_cast hsqR
  exact rat_sq_eq_five_mul_sq hsqQ

/-- `1` and `φ` are `ℚ`-linearly independent in `ℝ`. -/
theorem rat_add_rat_mul_phi_eq_zero {a b : ℚ}
    (h : (a : ℝ) + (b : ℝ) * φ = 0) : a = 0 ∧ b = 0 := by
  have h2 : ((a + b / 2 : ℚ) : ℝ) + ((b / 2 : ℚ) : ℝ) * Real.sqrt 5 = 0 := by
    push_cast
    unfold φ at h
    linarith
  rcases rat_add_rat_mul_sqrt5_eq_zero h2 with ⟨ha, hb⟩
  exact ⟨by linarith, by linarith⟩

/-- Exact quadratic field element `a + b φ ∈ ℚ(√5)`. -/
@[ext]
structure QSqrt5 where
  a : ℚ
  b : ℚ
  deriving DecidableEq, Repr

namespace QSqrt5

/-- Canonical embedding `QSqrt5 → ℝ` sending `⟨a, b⟩` to `a + b φ`. -/
noncomputable def toReal (z : QSqrt5) : ℝ :=
  (z.a : ℝ) + (z.b : ℝ) * φ

instance : Zero QSqrt5 := ⟨⟨0, 0⟩⟩
instance : One QSqrt5 := ⟨⟨1, 0⟩⟩
instance : Add QSqrt5 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg QSqrt5 := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub QSqrt5 := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Mul QSqrt5 :=
  ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

/-- Field norm `N(a + b φ) = a^2 + a b - b^2` over `ℚ`. -/
def norm (z : QSqrt5) : ℚ :=
  z.a ^ 2 + z.a * z.b - z.b ^ 2

instance : Inv QSqrt5 :=
  ⟨fun z => ⟨(z.a + z.b) / z.norm, -z.b / z.norm⟩⟩

instance : Div QSqrt5 := ⟨fun x y => x * y⁻¹⟩

/-- The golden ratio element `0 + 1·φ` in `QSqrt5`. -/
def phi : QSqrt5 := ⟨0, 1⟩

/-- Rational scalar embedding `ℚ → QSqrt5`. -/
def ofRat (q : ℚ) : QSqrt5 := ⟨q, 0⟩

/-- Whether `z = a + b φ` lies in the ring of integers `ℤ[φ]`. -/
def isInt (z : QSqrt5) : Bool :=
  (z.a.den == 1) && (z.b.den == 1)

@[simp] theorem zero_a : (0 : QSqrt5).a = 0 := rfl
@[simp] theorem zero_b : (0 : QSqrt5).b = 0 := rfl
@[simp] theorem one_a : (1 : QSqrt5).a = 1 := rfl
@[simp] theorem one_b : (1 : QSqrt5).b = 0 := rfl
@[simp] theorem add_a (x y : QSqrt5) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : QSqrt5) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : QSqrt5) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : QSqrt5) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : QSqrt5) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : QSqrt5) : (x - y).b = x.b - y.b := rfl
@[simp] theorem mul_a (x y : QSqrt5) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : QSqrt5) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

@[simp] theorem toReal_zero : (0 : QSqrt5).toReal = 0 := by simp [toReal]
@[simp] theorem toReal_one : (1 : QSqrt5).toReal = 1 := by simp [toReal]
@[simp] theorem toReal_phi : phi.toReal = φ := by simp [toReal, phi]
@[simp] theorem toReal_ofRat (q : ℚ) : (ofRat q).toReal = (q : ℝ) := by simp [toReal, ofRat]

@[simp] theorem toReal_add (x y : QSqrt5) : (x + y).toReal = x.toReal + y.toReal := by
  simp only [toReal, add_a, add_b]; push_cast; ring

@[simp] theorem toReal_neg (x : QSqrt5) : (-x).toReal = -x.toReal := by
  simp only [toReal, neg_a, neg_b]; push_cast; ring

@[simp] theorem toReal_sub (x y : QSqrt5) : (x - y).toReal = x.toReal - y.toReal := by
  simp only [toReal, sub_a, sub_b]; push_cast; ring

@[simp] theorem toReal_mul (x y : QSqrt5) : (x * y).toReal = x.toReal * y.toReal := by
  simp only [toReal, mul_a, mul_b]
  push_cast
  linear_combination (x.b : ℝ) * (y.b : ℝ) * phi_sq.symm

theorem toReal_eq_zero_iff {z : QSqrt5} : z.toReal = 0 ↔ z = 0 := by
  constructor
  · intro h
    rcases rat_add_rat_mul_phi_eq_zero h with ⟨ha, hb⟩
    ext <;> simp [ha, hb]
  · rintro rfl
    exact toReal_zero

theorem toReal_injective : Function.Injective toReal := by
  intro x y h
  have hsub : (x - y).toReal = 0 := by rw [toReal_sub, h, sub_self]
  have hz : x - y = 0 := toReal_eq_zero_iff.mp hsub
  ext
  · have := congrArg QSqrt5.a hz; simp at this; linarith
  · have := congrArg QSqrt5.b hz; simp at this; linarith

theorem norm_eq_zero_iff {z : QSqrt5} : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro hn
    have h4 : (2 * z.a + z.b) ^ 2 = 5 * z.b ^ 2 := by
      unfold norm at hn
      linarith
    rcases rat_sq_eq_five_mul_sq h4 with ⟨h1, h2⟩
    have ha : z.a = 0 := by linarith
    ext <;> simp [ha, h2]
  · rintro rfl
    simp [norm]

@[simp] theorem toReal_inv (z : QSqrt5) : (z⁻¹).toReal = (z.toReal)⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    change (⟨(0 + 0) / (0 : QSqrt5).norm, -0 / (0 : QSqrt5).norm⟩ : QSqrt5).toReal =
      ((0 : QSqrt5).toReal)⁻¹
    simp [norm, toReal]
  · have hnorm : z.norm ≠ 0 := mt norm_eq_zero_iff.mp hz
    have hmul : z * z⁻¹ = 1 := by
      ext
      · change z.a * ((z.a + z.b) / z.norm) + z.b * (-z.b / z.norm) = 1
        have h1 : z.a * ((z.a + z.b) / z.norm) + z.b * (-z.b / z.norm) =
            (z.a * (z.a + z.b) + z.b * (-z.b)) / z.norm := by ring
        rw [h1, div_eq_iff hnorm]
        unfold norm
        ring
      · change z.a * (-z.b / z.norm) + z.b * ((z.a + z.b) / z.norm) +
          z.b * (-z.b / z.norm) = 0
        ring
    have hR := congrArg toReal hmul
    rw [toReal_mul, toReal_one] at hR
    exact eq_inv_of_mul_eq_one_right hR

@[simp] theorem toReal_div (x y : QSqrt5) : (x / y).toReal = x.toReal / y.toReal := by
  change (x * y⁻¹).toReal = x.toReal / y.toReal
  rw [toReal_mul, toReal_inv, div_eq_mul_inv]

/-- Pure-rational decidable strict positivity test on `QSqrt5`:
`a + b φ = ((2a + b) + b √5) / 2 > 0`. -/
def isPos (z : QSqrt5) : Bool :=
  let p : ℚ := 2 * z.a + z.b
  let q : ℚ := z.b
  if 0 ≤ p ∧ 0 ≤ q then decide (0 < p ∨ 0 < q)
  else if p ≤ 0 ∧ q ≤ 0 then false
  else if 0 < p then decide (5 * q ^ 2 < p ^ 2)
  else decide (p ^ 2 < 5 * q ^ 2)

/-- Decidable strict order `<` on `QSqrt5`. -/
def ltB (x y : QSqrt5) : Bool :=
  (y - x).isPos

theorem isPos_iff_toReal_pos (z : QSqrt5) : z.isPos = true ↔ 0 < z.toReal := by
  dsimp only [isPos, toReal, φ]
  have hrew : (z.a : ℝ) + (z.b : ℝ) * ((1 + Real.sqrt 5) / 2) =
      (((2 * z.a + z.b : ℚ) : ℝ) + (z.b : ℝ) * Real.sqrt 5) / 2 := by
    push_cast; ring
  rw [hrew]
  set p : ℚ := 2 * z.a + z.b
  set q : ℚ := z.b
  have h5 : 0 < Real.sqrt 5 := sqrt5_pos
  split_ifs with h1 h2 h3
  · simp only [decide_eq_true_eq]
    rcases h1 with ⟨hp, hq⟩
    have hpR : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    constructor
    · rintro (hp' | hq')
      · have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp'
        nlinarith
      · have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq'
        nlinarith
    · intro hpos
      by_contra hnot
      have hp0 : p ≤ 0 := le_of_not_gt (fun hp' => hnot (Or.inl hp'))
      have hq0 : q ≤ 0 := le_of_not_gt (fun hq' => hnot (Or.inr hq'))
      have hpe : p = 0 := le_antisymm hp0 hp
      have hqe : q = 0 := le_antisymm hq0 hq
      rw [hpe, hqe] at hpos
      norm_num at hpos
  · simp only [false_iff]
    rcases h2 with ⟨hp, hq⟩
    have hpR : (p : ℝ) ≤ 0 := by exact_mod_cast hp
    have hqR : (q : ℝ) ≤ 0 := by exact_mod_cast hq
    nlinarith
  · simp only [decide_eq_true_eq]
    have hq_neg : q < 0 := lt_of_not_ge (fun hqn => h1 ⟨le_of_lt h3, hqn⟩)
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast h3
    have hqR : (q : ℝ) < 0 := by exact_mod_cast hq_neg
    have hposL : 0 < -(q : ℝ) * Real.sqrt 5 := by nlinarith
    constructor
    · intro hsq
      have hsqR : 5 * (q : ℝ) ^ 2 < (p : ℝ) ^ 2 := by exact_mod_cast hsq
      have hsq5 : (-(q : ℝ) * Real.sqrt 5) ^ 2 < (p : ℝ) ^ 2 := by nlinarith [sqrt5_sq]
      nlinarith
    · intro hpos
      have hlt : -(q : ℝ) * Real.sqrt 5 < (p : ℝ) := by linarith
      have hsqR : 5 * (q : ℝ) ^ 2 < (p : ℝ) ^ 2 := by
        have : (-(q : ℝ) * Real.sqrt 5) ^ 2 < (p : ℝ) ^ 2 := by nlinarith
        nlinarith [sqrt5_sq]
      exact_mod_cast hsqR
  · simp only [decide_eq_true_eq]
    have hp_le : p ≤ 0 := le_of_not_gt h3
    have hq_pos : 0 < q := lt_of_not_ge (fun hqn => h2 ⟨hp_le, hqn⟩)
    have hp_neg : p < 0 := lt_of_not_ge (fun hp0 => h1 ⟨hp0, le_of_lt hq_pos⟩)
    have hpR : (p : ℝ) < 0 := by exact_mod_cast hp_neg
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    have hposR : 0 < (q : ℝ) * Real.sqrt 5 := by nlinarith
    constructor
    · intro hsq
      have hsqR : (p : ℝ) ^ 2 < 5 * (q : ℝ) ^ 2 := by exact_mod_cast hsq
      have hsq5 : (-(p : ℝ)) ^ 2 < ((q : ℝ) * Real.sqrt 5) ^ 2 := by nlinarith [sqrt5_sq]
      nlinarith
    · intro hpos
      have hlt : -(p : ℝ) < (q : ℝ) * Real.sqrt 5 := by linarith
      have hsqR : (p : ℝ) ^ 2 < 5 * (q : ℝ) ^ 2 := by
        have : (-(p : ℝ)) ^ 2 < ((q : ℝ) * Real.sqrt 5) ^ 2 := by nlinarith
        nlinarith [sqrt5_sq]
      exact_mod_cast hsqR

theorem ltB_iff_toReal_lt (x y : QSqrt5) : ltB x y = true ↔ x.toReal < y.toReal := by
  rw [ltB, isPos_iff_toReal_pos, toReal_sub, sub_pos]

end QSqrt5

/-- Pure-integer quadratic ring element `a + b φ ∈ ℤ[φ]` for fast kernel reduction via `decide`. -/
@[ext]
structure ZPhi where
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

namespace ZPhi

noncomputable def toReal (z : ZPhi) : ℝ :=
  (z.a : ℝ) + (z.b : ℝ) * φ

def toQSqrt5 (z : ZPhi) : QSqrt5 :=
  ⟨(z.a : ℚ), (z.b : ℚ)⟩

instance : Zero ZPhi := ⟨⟨0, 0⟩⟩
instance : One ZPhi := ⟨⟨1, 0⟩⟩
instance : Add ZPhi := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg ZPhi := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub ZPhi := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Mul ZPhi :=
  ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

@[simp] theorem zero_a : (0 : ZPhi).a = 0 := rfl
@[simp] theorem zero_b : (0 : ZPhi).b = 0 := rfl
@[simp] theorem one_a : (1 : ZPhi).a = 1 := rfl
@[simp] theorem one_b : (1 : ZPhi).b = 0 := rfl
@[simp] theorem add_a (x y : ZPhi) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : ZPhi) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : ZPhi) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : ZPhi) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : ZPhi) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : ZPhi) : (x - y).b = x.b - y.b := rfl
@[simp] theorem mul_a (x y : ZPhi) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : ZPhi) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

def isPos (z : ZPhi) : Bool :=
  let p : ℤ := 2 * z.a + z.b
  let q : ℤ := z.b
  if 0 ≤ p ∧ 0 ≤ q then decide (0 < p ∨ 0 < q)
  else if p ≤ 0 ∧ q ≤ 0 then false
  else if 0 < p then decide (5 * q ^ 2 < p ^ 2)
  else decide (p ^ 2 < 5 * q ^ 2)

@[simp] theorem toQSqrt5_toReal (z : ZPhi) : z.toQSqrt5.toReal = z.toReal := by
  simp [toQSqrt5, QSqrt5.toReal, toReal]

@[simp] theorem toReal_zero : (0 : ZPhi).toReal = 0 := by simp [toReal]
@[simp] theorem toReal_one : (1 : ZPhi).toReal = 1 := by simp [toReal]

@[simp] theorem toReal_add (x y : ZPhi) : (x + y).toReal = x.toReal + y.toReal := by
  simp only [toReal, add_a, add_b]; push_cast; ring

@[simp] theorem toReal_neg (x : ZPhi) : (-x).toReal = -x.toReal := by
  simp only [toReal, neg_a, neg_b]; push_cast; ring

@[simp] theorem toReal_sub (x y : ZPhi) : (x - y).toReal = x.toReal - y.toReal := by
  simp only [toReal, sub_a, sub_b]; push_cast; ring

@[simp] theorem toReal_mul (x y : ZPhi) : (x * y).toReal = x.toReal * y.toReal := by
  simp only [toReal, mul_a, mul_b]
  push_cast
  linear_combination (x.b : ℝ) * (y.b : ℝ) * phi_sq.symm

theorem toReal_eq_zero_iff {z : ZPhi} : z.toReal = 0 ↔ z = 0 := by
  rw [← toQSqrt5_toReal, QSqrt5.toReal_eq_zero_iff]
  constructor
  · intro h
    have ha : (z.a : ℚ) = 0 := congrArg QSqrt5.a h
    have hb : (z.b : ℚ) = 0 := congrArg QSqrt5.b h
    ext
    · exact_mod_cast ha
    · exact_mod_cast hb
  · rintro rfl
    rfl

theorem isPos_iff_toReal_pos (z : ZPhi) : z.isPos = true ↔ 0 < z.toReal := by
  dsimp only [isPos, toReal, φ]
  have hrew : (z.a : ℝ) + (z.b : ℝ) * ((1 + Real.sqrt 5) / 2) =
      (((2 * z.a + z.b : ℤ) : ℝ) + (z.b : ℝ) * Real.sqrt 5) / 2 := by
    push_cast; ring
  rw [hrew]
  set p : ℤ := 2 * z.a + z.b
  set q : ℤ := z.b
  have h5 : 0 < Real.sqrt 5 := sqrt5_pos
  split_ifs with h1 h2 h3
  · simp only [decide_eq_true_eq]
    rcases h1 with ⟨hp, hq⟩
    have hpR : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    constructor
    · rintro (hp' | hq')
      · have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp'
        nlinarith
      · have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq'
        nlinarith
    · intro hpos
      by_contra hnot
      have hp0 : p ≤ 0 := le_of_not_gt (fun hp' => hnot (Or.inl hp'))
      have hq0 : q ≤ 0 := le_of_not_gt (fun hq' => hnot (Or.inr hq'))
      have hpe : p = 0 := le_antisymm hp0 hp
      have hqe : q = 0 := le_antisymm hq0 hq
      rw [hpe, hqe] at hpos
      norm_num at hpos
  · simp only [false_iff]
    rcases h2 with ⟨hp, hq⟩
    have hpR : (p : ℝ) ≤ 0 := by exact_mod_cast hp
    have hqR : (q : ℝ) ≤ 0 := by exact_mod_cast hq
    nlinarith
  · simp only [decide_eq_true_eq]
    have hq_neg : q < 0 := lt_of_not_ge (fun hqn => h1 ⟨le_of_lt h3, hqn⟩)
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast h3
    have hqR : (q : ℝ) < 0 := by exact_mod_cast hq_neg
    have hposL : 0 < -(q : ℝ) * Real.sqrt 5 := by nlinarith
    constructor
    · intro hsq
      have hsqR : 5 * (q : ℝ) ^ 2 < (p : ℝ) ^ 2 := by exact_mod_cast hsq
      have hsq5 : (-(q : ℝ) * Real.sqrt 5) ^ 2 < (p : ℝ) ^ 2 := by nlinarith [sqrt5_sq]
      nlinarith
    · intro hpos
      have hlt : -(q : ℝ) * Real.sqrt 5 < (p : ℝ) := by linarith
      have hsqR : 5 * (q : ℝ) ^ 2 < (p : ℝ) ^ 2 := by
        have : (-(q : ℝ) * Real.sqrt 5) ^ 2 < (p : ℝ) ^ 2 := by nlinarith
        nlinarith [sqrt5_sq]
      exact_mod_cast hsqR
  · simp only [decide_eq_true_eq]
    have hp_le : p ≤ 0 := le_of_not_gt h3
    have hq_pos : 0 < q := lt_of_not_ge (fun hqn => h2 ⟨hp_le, hqn⟩)
    have hp_neg : p < 0 := lt_of_not_ge (fun hp0 => h1 ⟨hp0, le_of_lt hq_pos⟩)
    have hpR : (p : ℝ) < 0 := by exact_mod_cast hp_neg
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    have hposR : 0 < (q : ℝ) * Real.sqrt 5 := by nlinarith
    constructor
    · intro hsq
      have hsqR : (p : ℝ) ^ 2 < 5 * (q : ℝ) ^ 2 := by exact_mod_cast hsq
      have hsq5 : (-(p : ℝ)) ^ 2 < ((q : ℝ) * Real.sqrt 5) ^ 2 := by nlinarith [sqrt5_sq]
      nlinarith
    · intro hpos
      have hlt : -(p : ℝ) < (q : ℝ) * Real.sqrt 5 := by linarith
      have hsqR : (p : ℝ) ^ 2 < 5 * (q : ℝ) ^ 2 := by
        have : (-(p : ℝ)) ^ 2 < ((q : ℝ) * Real.sqrt 5) ^ 2 := by nlinarith
        nlinarith [sqrt5_sq]
      exact_mod_cast hsqR

end ZPhi

/-! ## Section 2: Words, Non-Erasing Prolongable Morphisms, and Fixed Point `b_5` -/

section WordsAndMorphisms

variable {α β : Type*}

/-- `IsFactor u w` means `u` occurs as a contiguous factor (infix) of the finite word `w`. -/
def IsFactor (u w : List α) : Prop :=
  ∃ p s : List α, w = p ++ u ++ s

theorem isFactor_refl (w : List α) : IsFactor w w :=
  ⟨[], [], by simp⟩

theorem isFactor_trans {u v w : List α} (h1 : IsFactor u v) (h2 : IsFactor v w) :
    IsFactor u w := by
  rcases h1 with ⟨p1, s1, rfl⟩
  rcases h2 with ⟨p2, s2, rfl⟩
  exact ⟨p2 ++ p1, s1 ++ s2, by simp [List.append_assoc]⟩

theorem isFactor_of_prefix {u v w : List α} (h : IsFactor u v) (hp : v <+: w) :
    IsFactor u w := by
  rcases hp with ⟨t, rfl⟩
  exact isFactor_trans h ⟨[], t, by simp⟩

theorem isFactor_iff_exists_idx {u w : List α} :
    IsFactor u w ↔
      ∃ i : ℕ, ∃ _ : i + u.length ≤ w.length,
        ∀ j (hj : j < u.length), w[i + j]'(by omega) = u[j] := by
  constructor
  · rintro ⟨p, s, rfl⟩
    refine ⟨p.length, by simp, ?_⟩
    intro j hj
    rw [List.getElem_append_left (by simp; omega)]
    rw [List.getElem_append_right (by omega)]
    have h2 : p.length + j - p.length = j := by omega
    simp [h2]
  · rintro ⟨i, hi, hget⟩
    refine ⟨w.take i, w.drop (i + u.length), ?_⟩
    apply List.ext_getElem
    · simp only [List.length_append, List.length_take, List.length_drop]; omega
    · intro k hk1 hk2
      have htake : (w.take i).length = i := by simp; omega
      by_cases h1 : k < i
      · rw [List.getElem_append_left (by simp; omega)]
        rw [List.getElem_append_left (by omega)]
        simp
      · by_cases h2 : k < i + u.length
        · rw [List.getElem_append_left (by simp; omega)]
          rw [List.getElem_append_right (by omega)]
          simp only [htake]
          have hsub : i + (k - i) = k := by omega
          have hlt : k - i < u.length := by omega
          simpa [hsub] using hget (k - i) hlt
        · rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_append, htake, List.getElem_drop]
          congr 1; omega

/-- Finite prefix of length `n` of an infinite word `W : ℕ → α`. -/
def prefixOf (W : ℕ → α) (n : ℕ) : List α :=
  List.ofFn fun i : Fin n => W i.val

@[simp] theorem prefixOf_zero (W : ℕ → α) : prefixOf W 0 = [] := rfl

@[simp] theorem prefixOf_length (W : ℕ → α) (n : ℕ) : (prefixOf W n).length = n := by
  simp [prefixOf]

@[simp] theorem prefixOf_getElem (W : ℕ → α) (n i : ℕ) (hi : i < (prefixOf W n).length) :
    (prefixOf W n)[i] = W i := by
  simp [prefixOf]

theorem prefixOf_succ (W : ℕ → α) (n : ℕ) :
    prefixOf W (n + 1) = prefixOf W n ++ [W n] := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    by_cases h : i < n
    · rw [List.getElem_append_left (by simp [h])]
      simp
    · have hi : i = n := by simp at hi1; omega
      subst hi
      rw [List.getElem_append_right (by simp)]
      simp

theorem prefixOf_add (W : ℕ → α) (m n : ℕ) :
    prefixOf W (m + n) = prefixOf W m ++ List.ofFn (fun i : Fin n => W (m + i.val)) := by
  apply List.ext_getElem
  · simp
  · intro k hk1 hk2
    by_cases h : k < m
    · rw [List.getElem_append_left (by simp [h])]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [prefixOf_length, prefixOf_getElem, List.getElem_ofFn]
      congr 1; omega

theorem prefixOf_prefix_of_le (W : ℕ → α) {m n : ℕ} (h : m ≤ n) :
    prefixOf W m <+: prefixOf W n := by
  refine ⟨List.ofFn (fun i : Fin (n - m) => W (m + i.val)), ?_⟩
  have hm : m + (n - m) = n := by omega
  simpa [hm] using (prefixOf_add W m (n - m)).symm

/-- `IsFactorInf u W` means the finite word `u` occurs as a contiguous factor of `W : ℕ → α`. -/
def IsFactorInf (u : List α) (W : ℕ → α) : Prop :=
  ∃ i : ℕ, ∀ j (hj : j < u.length), W (i + j) = u[j]

theorem isFactorInf_nil (W : ℕ → α) : IsFactorInf [] W :=
  ⟨0, fun _ hj => by simp at hj⟩

theorem isFactorInf_iff_exists_prefix {u : List α} {W : ℕ → α} :
    IsFactorInf u W ↔ ∃ n : ℕ, IsFactor u (prefixOf W n) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i + u.length, ?_⟩
    rw [isFactor_iff_exists_idx]
    exact ⟨i, by simp, fun j hj => by simp [hi j hj]⟩
  · rintro ⟨n, hn⟩
    rw [isFactor_iff_exists_idx] at hn
    rcases hn with ⟨i, hi, hget⟩
    refine ⟨i, fun j hj => ?_⟩
    have hlt : i + j < (prefixOf W n).length := by simp at hi ⊢; omega
    simpa [prefixOf_getElem] using hget j hj

theorem isFactorInf_of_prefix {u : List α} {W : ℕ → α} {n : ℕ}
    (h : IsFactor u (prefixOf W n)) : IsFactorInf u W :=
  isFactorInf_iff_exists_prefix.mpr ⟨n, h⟩

theorem isFactorInf_trans {u v : List α} {W : ℕ → α}
    (huv : IsFactor u v) (hv : IsFactorInf v W) : IsFactorInf u W := by
  rcases isFactorInf_iff_exists_prefix.mp hv with ⟨n, hn⟩
  exact isFactorInf_of_prefix (isFactor_trans huv hn)

/-- Apply a letter-to-word morphism `f : α → List β` to a finite word `w : List α`. -/
def applyMorph (f : α → List β) (w : List α) : List β :=
  w.flatMap f

@[simp] theorem applyMorph_nil (f : α → List β) : applyMorph f [] = [] := rfl

@[simp] theorem applyMorph_cons (f : α → List β) (a : α) (w : List α) :
    applyMorph f (a :: w) = f a ++ applyMorph f w := rfl

@[simp] theorem applyMorph_singleton (f : α → List β) (a : α) :
    applyMorph f [a] = f a := by simp [applyMorph]

theorem applyMorph_append (f : α → List β) (u v : List α) :
    applyMorph f (u ++ v) = applyMorph f u ++ applyMorph f v := by
  simp [applyMorph, List.flatMap_append]

theorem applyMorph_ne_nil (f : α → List β) (hne : ∀ a, f a ≠ []) {w : List α} (hw : w ≠ []) :
    applyMorph f w ≠ [] := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a t =>
    simp only [applyMorph_cons, ne_eq, List.append_eq_nil_iff, not_and]
    exact fun h => (hne a h).elim

theorem applyMorph_length_ge (f : α → List β) (hne : ∀ a, f a ≠ []) (w : List α) :
    w.length ≤ (applyMorph f w).length := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have ha : 1 ≤ (f a).length := List.length_pos_of_ne_nil (hne a)
    simp only [applyMorph_cons, List.length_cons, List.length_append]
    omega

theorem applyMorph_prefix_of_prefix (f : α → List β) {u v : List α} (hp : u <+: v) :
    applyMorph f u <+: applyMorph f v := by
  rcases hp with ⟨t, rfl⟩
  exact ⟨applyMorph f t, (applyMorph_append f u t).symm⟩

theorem applyMorph_isFactor (f : α → List β) {u w : List α} (h : IsFactor u w) :
    IsFactor (applyMorph f u) (applyMorph f w) := by
  rcases h with ⟨p, s, rfl⟩
  exact ⟨applyMorph f p, applyMorph f s, by simp [applyMorph_append]⟩

/-- Iterate an endomorphism `f : α → List α` `n` times on `w`. -/
def iterMorph (f : α → List α) : ℕ → List α → List α
  | 0, w => w
  | n + 1, w => applyMorph f (iterMorph f n w)

@[simp] theorem iterMorph_zero (f : α → List α) (w : List α) : iterMorph f 0 w = w := rfl

@[simp] theorem iterMorph_succ (f : α → List α) (n : ℕ) (w : List α) :
    iterMorph f (n + 1) w = applyMorph f (iterMorph f n w) := rfl

theorem iterMorph_append (f : α → List α) (n : ℕ) (u v : List α) :
    iterMorph f n (u ++ v) = iterMorph f n u ++ iterMorph f n v := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterMorph_succ, ih, applyMorph_append]

theorem iterMorph_comm (f : α → List α) (n : ℕ) (w : List α) :
    iterMorph f (n + 1) w = iterMorph f n (applyMorph f w) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterMorph_succ, ih, ← iterMorph_succ]

theorem iterMorph_add (f : α → List α) (m n : ℕ) (w : List α) :
    iterMorph f (m + n) w = iterMorph f m (iterMorph f n w) := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_add, iterMorph_succ, ih]

theorem iterMorph_ne_nil (f : α → List α) (hne : ∀ a, f a ≠ []) (n : ℕ)
    {w : List α} (hw : w ≠ []) : iterMorph f n w ≠ [] := by
  induction n with
  | zero => exact hw
  | succ n ih => exact applyMorph_ne_nil f hne ih

theorem iterMorph_prefix_step (f : α → List α) (a₀ : α)
    (hprol : ∃ t, f a₀ = a₀ :: t ∧ t ≠ []) (n : ℕ) :
    iterMorph f n [a₀] <+: iterMorph f (n + 1) [a₀] := by
  rcases hprol with ⟨t, ht, _⟩
  refine ⟨iterMorph f n t, ?_⟩
  rw [iterMorph_comm, applyMorph_singleton, ht]
  change iterMorph f n [a₀] ++ iterMorph f n t = iterMorph f n ([a₀] ++ t)
  rw [iterMorph_append]

theorem iterMorph_prefix_le (f : α → List α) (a₀ : α)
    (hprol : ∃ t, f a₀ = a₀ :: t ∧ t ≠ []) {m n : ℕ} (hmn : m ≤ n) :
    iterMorph f m [a₀] <+: iterMorph f n [a₀] := by
  induction hmn with
  | refl => exact List.prefix_refl _
  | @step k _ ih => exact ih.trans (iterMorph_prefix_step f a₀ hprol k)

theorem iterMorph_length_lt_succ (f : α → List α) (a₀ : α) (hne : ∀ a, f a ≠ [])
    (hprol : ∃ t, f a₀ = a₀ :: t ∧ t ≠ []) (n : ℕ) :
    (iterMorph f n [a₀]).length < (iterMorph f (n + 1) [a₀]).length := by
  rcases hprol with ⟨t, ht, htne⟩
  have hstep : iterMorph f (n + 1) [a₀] = iterMorph f n [a₀] ++ iterMorph f n t := by
    rw [iterMorph_comm, applyMorph_singleton, ht]
    change iterMorph f n ([a₀] ++ t) = _
    rw [iterMorph_append]
  rw [hstep, List.length_append]
  have hpos : 0 < (iterMorph f n t).length :=
    List.length_pos_of_ne_nil (iterMorph_ne_nil f hne n htne)
  omega

theorem lt_iterMorph_length (f : α → List α) (a₀ : α) (hne : ∀ a, f a ≠ [])
    (hprol : ∃ t, f a₀ = a₀ :: t ∧ t ≠ []) (n : ℕ) :
    n < (iterMorph f n [a₀]).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt := iterMorph_length_lt_succ f a₀ hne hprol n
    omega

theorem getElem_eq_of_prefix {u v : List α} (hp : u <+: v) {i : ℕ}
    (hu : i < u.length) (hv : i < v.length) : u[i] = v[i] := by
  rcases hp with ⟨t, rfl⟩
  rw [List.getElem_append_left hu]

/-- Infinite fixed point `f^ω(a₀) : ℕ → α` of a prolongable non-erasing morphism `f`. -/
def fixedPoint (f : α → List α) (a₀ : α) (hne : ∀ a, f a ≠ [])
    (hprol : ∃ t, f a₀ = a₀ :: t ∧ t ≠ []) (i : ℕ) : α :=
  (iterMorph f i [a₀])[i]'(lt_iterMorph_length f a₀ hne hprol i)

theorem fixedPoint_eq_iterMorph_getElem (f : α → List α) (a₀ : α) (hne : ∀ a, f a ≠ [])
    (hprol : ∃ t, f a₀ = a₀ :: t ∧ t ≠ []) (n i : ℕ)
    (hi : i < (iterMorph f n [a₀]).length) :
    fixedPoint f a₀ hne hprol i = (iterMorph f n [a₀])[i] := by
  unfold fixedPoint
  by_cases h : i ≤ n
  · exact getElem_eq_of_prefix (iterMorph_prefix_le f a₀ hprol h)
      (lt_iterMorph_length f a₀ hne hprol i) hi
  · exact (getElem_eq_of_prefix (iterMorph_prefix_le f a₀ hprol (Nat.le_of_not_le h))
      hi (lt_iterMorph_length f a₀ hne hprol i)).symm

theorem fixedPoint_prefix_eq (f : α → List α) (a₀ : α) (hne : ∀ a, f a ≠ [])
    (hprol : ∃ t, f a₀ = a₀ :: t ∧ t ≠ []) (n : ℕ) :
    prefixOf (fixedPoint f a₀ hne hprol) (iterMorph f n [a₀]).length = iterMorph f n [a₀] := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [prefixOf_getElem]
    exact fixedPoint_eq_iterMorph_getElem f a₀ hne hprol n i hi2

theorem fixedPoint_isFactorInf_of_iter (f : α → List α) (a₀ : α) (hne : ∀ a, f a ≠ [])
    (hprol : ∃ t, f a₀ = a₀ :: t ∧ t ≠ []) {u : List α} {n : ℕ}
    (h : IsFactor u (iterMorph f n [a₀])) :
    IsFactorInf u (fixedPoint f a₀ hne hprol) := by
  apply isFactorInf_of_prefix (n := (iterMorph f n [a₀]).length)
  rwa [fixedPoint_prefix_eq]

theorem lt_applyMorph_prefix_length (τ : α → List β) (hτ : ∀ a, τ a ≠ []) (W : ℕ → α) (i : ℕ) :
    i < (applyMorph τ (prefixOf W (i + 1))).length := by
  have hge := applyMorph_length_ge τ hτ (prefixOf W (i + 1))
  simp only [prefixOf_length] at hge
  omega

/-- Apply a non-erasing morphism `τ : α → List β` to an infinite word `W : ℕ → α`. -/
def applyMorphInf (τ : α → List β) (hτ : ∀ a, τ a ≠ []) (W : ℕ → α) (i : ℕ) : β :=
  (applyMorph τ (prefixOf W (i + 1)))[i]'(lt_applyMorph_prefix_length τ hτ W i)

theorem applyMorphInf_eq_getElem (τ : α → List β) (hτ : ∀ a, τ a ≠ []) (W : ℕ → α)
    (n i : ℕ) (hi : i < (applyMorph τ (prefixOf W n)).length) :
    applyMorphInf τ hτ W i = (applyMorph τ (prefixOf W n))[i] := by
  unfold applyMorphInf
  by_cases h : i + 1 ≤ n
  · exact getElem_eq_of_prefix
      (applyMorph_prefix_of_prefix τ (prefixOf_prefix_of_le W h))
      (lt_applyMorph_prefix_length τ hτ W i) hi
  · exact (getElem_eq_of_prefix
      (applyMorph_prefix_of_prefix τ (prefixOf_prefix_of_le W (Nat.le_of_not_le h)))
      hi (lt_applyMorph_prefix_length τ hτ W i)).symm

theorem applyMorphInf_prefix_eq (τ : α → List β) (hτ : ∀ a, τ a ≠ []) (W : ℕ → α) (n : ℕ) :
    prefixOf (applyMorphInf τ hτ W) (applyMorph τ (prefixOf W n)).length =
      applyMorph τ (prefixOf W n) := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [prefixOf_getElem]
    exact applyMorphInf_eq_getElem τ hτ W n i hi2

/-- Fixed-point invariance under any iterate `g_k(a) := iterMorph f k [a]` (`k : ℕ`). -/
theorem fixedPoint_applyMorph_prefix_isPrefix
    (f : α → List α) (a₀ : α) (hne : ∀ a, f a ≠ [])
    (hprol : ∃ t, f a₀ = a₀ :: t ∧ t ≠ []) (k p : ℕ) :
    applyMorph (fun a => iterMorph f k [a]) (prefixOf (fixedPoint f a₀ hne hprol) p) =
      prefixOf (fixedPoint f a₀ hne hprol)
        (applyMorph (fun a => iterMorph f k [a]) (prefixOf (fixedPoint f a₀ hne hprol) p)).length := by
  let W := fixedPoint f a₀ hne hprol
  let gk : α → List α := fun a => iterMorph f k [a]
  have hgk_eq : ∀ u : List α, applyMorph gk u = iterMorph f k u := by
    intro u
    induction u with
    | nil =>
      have : ∀ m, iterMorph f m ([] : List α) = [] := fun m => by
        induction m with
        | zero => rfl
        | succ m ihm => simp [iterMorph_succ, ihm]
      exact (this k).symm
    | cons a t ih =>
      calc
        applyMorph gk (a :: t) = iterMorph f k [a] ++ applyMorph gk t := rfl
        _ = iterMorph f k [a] ++ iterMorph f k t := by rw [ih]
        _ = iterMorph f k ([a] ++ t) := (iterMorph_append f k [a] t).symm
        _ = iterMorph f k (a :: t) := rfl
  have hlen : p ≤ (iterMorph f p [a₀]).length := Nat.le_of_lt (lt_iterMorph_length f a₀ hne hprol p)
  have hpref : prefixOf W p <+: iterMorph f p [a₀] := by
    rw [← fixedPoint_prefix_eq f a₀ hne hprol p]
    exact prefixOf_prefix_of_le W hlen
  rcases hpref with ⟨rest, hrest⟩
  have himg : applyMorph gk (prefixOf W p) <+: prefixOf W (iterMorph f (k + p) [a₀]).length := by
    rw [fixedPoint_prefix_eq f a₀ hne hprol (k + p), iterMorph_add, ← hrest,
      iterMorph_append, ← hgk_eq]
    exact ⟨iterMorph f k rest, rfl⟩
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [prefixOf_getElem]
    have hi_big : i < (prefixOf W (iterMorph f (k + p) [a₀]).length).length := by
      rcases himg with ⟨t, ht⟩
      have hlen_eq := congrArg List.length ht
      dsimp only [W, gk] at hi1 hlen_eq ⊢
      simp only [List.length_append, prefixOf_length] at hi1 hlen_eq ⊢
      omega
    have hg := getElem_eq_of_prefix himg hi1 hi_big
    simpa [prefixOf_getElem] using hg

end WordsAndMorphisms

/-- Badkobeh & Ochem's 5-letter morphism `fB5 : Fin 5 → List (Fin 5)`:
`0 ↦ [0, 1]`, `1 ↦ [2, 3]`, `2 ↦ [4]`, `3 ↦ [2, 1]`, `4 ↦ [0]`. -/
def fB5 : Fin 5 → List (Fin 5)
  | 0 => [0, 1]
  | 1 => [2, 3]
  | 2 => [4]
  | 3 => [2, 1]
  | 4 => [0]

theorem fB5_nonempty : ∀ a : Fin 5, fB5 a ≠ [] := by
  intro a; fin_cases a <;> decide

theorem fB5_prolongable : ∃ t : List (Fin 5), fB5 0 = 0 :: t ∧ t ≠ [] :=
  ⟨[1], rfl, by decide⟩

theorem fB5_length_bounds (a : Fin 5) : 1 ≤ (fB5 a).length ∧ (fB5 a).length ≤ 2 := by
  fin_cases a <;> decide

/-- Badkobeh & Ochem's infinite 5-letter word `b5 = fB5^ω(0) : ℕ → Fin 5`. -/
def b5 : ℕ → Fin 5 :=
  fixedPoint fB5 0 fB5_nonempty fB5_prolongable

@[simp] theorem b5_zero : b5 0 = 0 := rfl

theorem b5_prefix_17 :
    prefixOf b5 17 = [0, 1, 2, 3, 4, 2, 1, 0, 4, 2, 3, 0, 1, 0, 4, 2, 1] := by
  have h := fixedPoint_prefix_eq fB5 0 fB5_nonempty fB5_prolongable 5
  have hlen : (iterMorph fB5 5 [0]).length = 17 := by decide
  rw [hlen] at h
  exact h.trans (by decide)

/-- Block-boundary position `s_p = |fB5(b5[0..p))|` in `b5 = fB5(b5)`. -/
def blockStart (p : ℕ) : ℕ :=
  (applyMorph fB5 (prefixOf b5 p)).length

@[simp] theorem blockStart_zero : blockStart 0 = 0 := rfl

theorem blockStart_succ (p : ℕ) :
    blockStart (p + 1) = blockStart p + (fB5 (b5 p)).length := by
  simp [blockStart, prefixOf_succ, applyMorph_append]

theorem blockStart_strictMono : StrictMono blockStart := by
  refine strictMono_nat_of_lt_succ fun p => ?_
  rw [blockStart_succ]
  have h1 := (fB5_length_bounds (b5 p)).1
  omega

theorem blockStart_ge_succ_of_pos {p : ℕ} (hp : 1 ≤ p) : p + 1 ≤ blockStart p := by
  induction p with
  | zero => omega
  | succ p ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simp [blockStart_succ, b5_zero, fB5]
    · have hp1 : 1 ≤ p := by omega
      have h1 := ih hp1
      have h2 := (fB5_length_bounds (b5 p)).1
      rw [blockStart_succ]
      omega

theorem b5_prefix_blockStart (p : ℕ) :
    prefixOf b5 (blockStart p) = applyMorph fB5 (prefixOf b5 p) := by
  have h := fixedPoint_applyMorph_prefix_isPrefix fB5 0 fB5_nonempty fB5_prolongable 1 p
  have heq : (fun a => iterMorph fB5 1 [a]) = fB5 := by
    funext a; simp [iterMorph]
  rw [heq] at h
  exact h.symm

/-- Exact unique block decomposition of every position `q : ℕ` in `b5 = fB5(b5)`. -/
theorem exists_block_decomp (q : ℕ) :
    ∃ p o : ℕ, ∃ ho : o < (fB5 (b5 p)).length,
      q = blockStart p + o ∧
      b5 q = (fB5 (b5 p))[o]'ho ∧
      prefixOf b5 q = applyMorph fB5 (prefixOf b5 p) ++ (fB5 (b5 p)).take o ∧
      (1 ≤ q → p < q) := by
  have hex : ∃ p : ℕ, blockStart p ≤ q ∧ q < blockStart (p + 1) := by
    induction q with
    | zero =>
      refine ⟨0, by simp, ?_⟩
      simp [blockStart_succ, b5_zero, fB5]
    | succ q ih =>
      rcases ih with ⟨p, hle, hlt⟩
      by_cases hnext : q + 1 < blockStart (p + 1)
      · exact ⟨p, by omega, hnext⟩
      · have heq : q + 1 = blockStart (p + 1) := by omega
        refine ⟨p + 1, by omega, ?_⟩
        rw [heq]
        rw [blockStart_succ (p + 1)]
        have hpos := (fB5_length_bounds (b5 (p + 1))).1
        omega
  rcases hex with ⟨p, hle, hlt⟩
  let o := q - blockStart p
  have ho : o < (fB5 (b5 p)).length := by
    have hs := blockStart_succ p
    omega
  have hq_eq : q = blockStart p + o := by omega
  have hbig : prefixOf b5 (blockStart (p + 1)) =
      applyMorph fB5 (prefixOf b5 p) ++ fB5 (b5 p) := by
    rw [b5_prefix_blockStart (p + 1), prefixOf_succ, applyMorph_append, applyMorph_singleton]
  have hb5_q : b5 q = (fB5 (b5 p))[o]'ho := by
    have hget : (prefixOf b5 (blockStart (p + 1)))[q]'(by simp [hlt]) = b5 q :=
      prefixOf_getElem b5 (blockStart (p + 1)) q (by simp [hlt])
    rw [← hget]
    simp only [hbig]
    rw [List.getElem_append_right (by change blockStart p ≤ q; omega)]
    congr 1
  have hpref_q : prefixOf b5 q = applyMorph fB5 (prefixOf b5 p) ++ (fB5 (b5 p)).take o := by
    have h1 : prefixOf b5 q = (prefixOf b5 (blockStart (p + 1))).take q := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 hi2
        simp
    rw [h1, hbig, hq_eq]
    change List.take ((applyMorph fB5 (prefixOf b5 p)).length + o)
      (applyMorph fB5 (prefixOf b5 p) ++ fB5 (b5 p)) = _
    rw [List.take_append]
    simp
  have hp_lt_q : 1 ≤ q → p < q := by
    intro hq1
    by_cases hp0 : p = 0
    · subst hp0; omega
    · have hge := blockStart_ge_succ_of_pos (by omega : 1 ≤ p)
      omega
  exact ⟨p, o, ho, hq_eq, hb5_q, hpref_q, hp_lt_q⟩

/-! ## Section 3: Conjugate Lengths `l'`, `lambda'`, and Theorem `R18-2-1` Part (1) -/

/-- Exact `QSqrt5` conjugate letter lengths:
`lQ(0) = 1`, `lQ(1) = lQ(3) = lQ(4) = -φ`, `lQ(2) = 1 + φ`. -/
def lQ : Fin 5 → QSqrt5
  | 0 => ⟨1, 0⟩
  | 1 => ⟨0, -1⟩
  | 2 => ⟨1, 1⟩
  | 3 => ⟨0, -1⟩
  | 4 => ⟨0, -1⟩

/-- Real conjugate letter lengths `l' : Fin 5 → ℝ`:
`l'(0) = 1`, `l'(1) = l'(3) = l'(4) = -φ`, `l'(2) = 1 + φ`. -/
noncomputable def l' : Fin 5 → ℝ
  | 0 => 1
  | 1 => -φ
  | 2 => 1 + φ
  | 3 => -φ
  | 4 => -φ

theorem lQ_toReal (a : Fin 5) : (lQ a).toReal = l' a := by
  fin_cases a <;> simp [lQ, l', QSqrt5.toReal]

/-- Conjugate length sum `lambdaQ w` in `QSqrt5`. -/
def lambdaQ (w : List (Fin 5)) : QSqrt5 :=
  (w.map lQ).foldr (· + ·) 0

/-- Conjugate length sum `lambda' w : ℝ := (w.map l').sum`. -/
noncomputable def lambda' (w : List (Fin 5)) : ℝ :=
  (w.map l').sum

@[simp] theorem lambdaQ_nil : lambdaQ [] = 0 := rfl
@[simp] theorem lambdaPrime_nil : lambda' [] = 0 := rfl

@[simp] theorem lambdaQ_cons (a : Fin 5) (w : List (Fin 5)) :
    lambdaQ (a :: w) = lQ a + lambdaQ w := rfl

@[simp] theorem lambdaPrime_cons (a : Fin 5) (w : List (Fin 5)) :
    lambda' (a :: w) = l' a + lambda' w := by
  simp [lambda']

theorem lambdaQ_append (u v : List (Fin 5)) :
    lambdaQ (u ++ v) = lambdaQ u + lambdaQ v := by
  induction u with
  | nil =>
    ext <;> simp [lambdaQ]
  | cons c t ih =>
    simp only [List.cons_append, lambdaQ_cons, ih]
    ext <;> simp <;> ring

theorem lambdaPrime_append (u v : List (Fin 5)) :
    lambda' (u ++ v) = lambda' u + lambda' v := by
  simp [lambda', List.map_append, List.sum_append]

theorem lambdaQ_toReal (w : List (Fin 5)) : (lambdaQ w).toReal = lambda' w := by
  induction w with
  | nil => simp
  | cons a t ih => simp [lambdaQ_cons, lambdaPrime_cons, lQ_toReal, ih]

/-- Explicit `QSqrt5` coordinates of `lambdaQ w` in terms of letter counts:
`a = count(0) + count(2)` and `b = count(2) - count(1) - count(3) - count(4)`. -/
theorem lambdaQ_coords (w : List (Fin 5)) :
    (lambdaQ w).a = (w.count 0 + w.count 2 : ℚ) ∧
    (lambdaQ w).b = (w.count 2 : ℚ) - (w.count 1 : ℚ) - (w.count 3 : ℚ) - (w.count 4 : ℚ) := by
  induction w with
  | nil => simp [lambdaQ]
  | cons c t ih =>
    rcases ih with ⟨ha, hb⟩
    rw [lambdaQ_cons]
    simp only [QSqrt5.add_a, QSqrt5.add_b, ha, hb]
    rcases c with ⟨val, hval⟩
    interval_cases val <;>
      · simp only [lQ, List.count_cons, beq_iff_eq, Fin.ext_iff]
        norm_num
        try constructor
        all_goals ring

/-- Every non-empty word over `Fin 5` (not only factors of `b5`!) has strictly non-zero
conjugate step `lambda' w ≠ 0`. -/
theorem lambdaPrime_ne_zero_of_ne_nil {w : List (Fin 5)} (hw : w ≠ []) : lambda' w ≠ 0 := by
  rw [← lambdaQ_toReal]
  intro h0
  have hz : lambdaQ w = 0 := QSqrt5.toReal_eq_zero_iff.mp h0
  rcases lambdaQ_coords w with ⟨ha, hb⟩
  rw [hz] at ha hb
  simp only [QSqrt5.zero_a, QSqrt5.zero_b] at ha hb
  have hc02 : w.count 0 + w.count 2 = 0 := by exact_mod_cast ha.symm
  have hc0 : w.count 0 = 0 := by omega
  have hc2 : w.count 2 = 0 := by omega
  have hc134 : w.count 1 + w.count 3 + w.count 4 = 0 := by
    have hb' : (0 : ℚ) = -((w.count 1 + w.count 3 + w.count 4 : ℕ) : ℚ) := by
      rw [hc2] at hb; push_cast at hb ⊢; linarith
    have hb'' : ((w.count 1 + w.count 3 + w.count 4 : ℕ) : ℚ) = 0 := by linarith
    exact_mod_cast hb''
  cases w with
  | nil => exact hw rfl
  | cons c t =>
    have hpos : 0 < (c :: t).count c := List.count_pos_iff.mpr List.mem_cons_self
    have hc_cases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
      fin_cases c <;> simp
    rcases hc_cases with rfl | rfl | rfl | rfl | rfl <;> omega

/-- Exact eigenvector identity on letters: `lambda' (fB5 a) = (-1 / φ) * l' a`. -/
theorem lambdaPrime_fB5_letter (a : Fin 5) :
    lambda' (fB5 a) = (-1 / φ) * l' a := by
  rw [neg_inv_phi]
  fin_cases a <;> simp [fB5, lambda', l'] <;> nlinarith [phi_sq]

/-- Exact eigenvector scaling law for every finite word `w`:
`lambda' (applyMorph fB5 w) = (-1 / φ) * lambda' w`. -/
theorem lambdaPrime_applyMorph_fB5 (w : List (Fin 5)) :
    lambda' (applyMorph fB5 w) = (-1 / φ) * lambda' w := by
  induction w with
  | nil => simp
  | cons a t ih =>
    rw [applyMorph_cons, lambdaPrime_append, lambdaPrime_cons, lambdaPrime_fB5_letter, ih]
    ring

/-- Lower endpoint of the open letter interval `P_a` in `ℝ`. -/
noncomputable def intervalLo (a : Fin 5) : ℝ :=
  match a with
  | 2 => -φ ^ 2 / 2
  | 0 => -1 / 2
  | 4 => (φ - 1) / 2
  | 1 => φ / 2
  | 3 => φ

/-- Upper endpoint of the open letter interval `P_a` in `ℝ`. -/
noncomputable def intervalHi (a : Fin 5) : ℝ :=
  match a with
  | 2 => -1 / 2
  | 0 => (φ - 1) / 2
  | 4 => φ / 2
  | 1 => φ
  | 3 => φ ^ 3 / 2

/-- Real open interval predicate `InLetterInterval a x` matching `R18-2-1` Part (1). -/
def InLetterInterval (a : Fin 5) (x : ℝ) : Prop :=
  intervalLo a < x ∧ x < intervalHi a

/-- The six ordered endpoints `-φ^2/2 < -1/2 < (φ-1)/2 < φ/2 < φ < φ^3/2`. -/
theorem cut_chain :
    -φ ^ 2 / 2 < -1 / 2 ∧
    (-1 / 2 : ℝ) < (φ - 1) / 2 ∧
    (φ - 1) / 2 < φ / 2 ∧
    φ / 2 < φ ∧
    φ < φ ^ 3 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [one_lt_phi, phi_lt_two, phi_sq, phi_cube]

/-- Pairwise disjointness of the five open coding intervals `P_0, P_1, P_2, P_3, P_4`. -/
theorem inLetterInterval_unique {a b : Fin 5} {x : ℝ}
    (ha : InLetterInterval a x) (hb : InLetterInterval b x) : a = b := by
  rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
  rcases a with ⟨va, hva⟩
  rcases b with ⟨vb, hvb⟩
  interval_cases va <;> interval_cases vb <;>
    first
    | rfl
    | (exfalso; simp only [InLetterInterval, intervalLo, intervalHi] at ha hb; linarith)

/-- All eight affine sub-interval inclusions of the induction step of `R18-2-1` Part (1):
if `x ∈ P_a`, then `(-1 / φ) * x + lambda' ((fB5 a).take o) ∈ P_{(fB5 a)[o]}`. -/
theorem coding_step_inclusion (a : Fin 5) (o : ℕ) (ho : o < (fB5 a).length)
    {x : ℝ} (hx : InLetterInterval a x) :
    InLetterInterval ((fB5 a)[o]) ((-1 / φ) * x + lambda' ((fB5 a).take o)) := by
  rw [neg_inv_phi]
  have h1 : 1 < φ := one_lt_phi
  have h2 : φ < 2 := phi_lt_two
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  rcases a with ⟨va, hva⟩
  interval_cases va
  · -- a = 0: fB5 0 = [0, 1]
    have ho2 : o = 0 ∨ o = 1 := by change o < ([0, 1] : List (Fin 5)).length at ho; simp at ho; omega
    rcases ho2 with rfl | rfl
    · simp only [InLetterInterval, intervalLo, intervalHi, fB5, List.take, lambda', List.map,
        List.sum_nil, add_zero, List.getElem_cons_zero] at hx ⊢
      exact ⟨by nlinarith, by nlinarith⟩
    · simp only [InLetterInterval, intervalLo, intervalHi, fB5, List.take, lambda', List.map,
        List.sum_cons, List.sum_nil, l', List.getElem_cons_succ, List.getElem_cons_zero] at hx ⊢
      exact ⟨by nlinarith, by nlinarith⟩
  · -- a = 1: fB5 1 = [2, 3]
    have ho2 : o = 0 ∨ o = 1 := by change o < ([2, 3] : List (Fin 5)).length at ho; simp at ho; omega
    rcases ho2 with rfl | rfl
    · simp only [InLetterInterval, intervalLo, intervalHi, fB5, List.take, lambda', List.map,
        List.sum_nil, add_zero, List.getElem_cons_zero] at hx ⊢
      exact ⟨by nlinarith, by nlinarith⟩
    · simp only [InLetterInterval, intervalLo, intervalHi, fB5, List.take, lambda', List.map,
        List.sum_cons, List.sum_nil, l', List.getElem_cons_succ, List.getElem_cons_zero] at hx ⊢
      exact ⟨by nlinarith, by nlinarith⟩
  · -- a = 2: fB5 2 = [4]
    have ho1 : o = 0 := by change o < ([4] : List (Fin 5)).length at ho; simp at ho; omega
    subst ho1
    simp only [InLetterInterval, intervalLo, intervalHi, fB5, List.take, lambda', List.map,
      List.sum_nil, add_zero, List.getElem_cons_zero] at hx ⊢
    exact ⟨by nlinarith, by nlinarith⟩
  · -- a = 3: fB5 3 = [2, 1]
    have ho2 : o = 0 ∨ o = 1 := by change o < ([2, 1] : List (Fin 5)).length at ho; simp at ho; omega
    rcases ho2 with rfl | rfl
    · simp only [InLetterInterval, intervalLo, intervalHi, fB5, List.take, lambda', List.map,
        List.sum_nil, add_zero, List.getElem_cons_zero] at hx ⊢
      exact ⟨by nlinarith, by nlinarith⟩
    · simp only [InLetterInterval, intervalLo, intervalHi, fB5, List.take, lambda', List.map,
        List.sum_cons, List.sum_nil, l', List.getElem_cons_succ, List.getElem_cons_zero] at hx ⊢
      exact ⟨by nlinarith, by nlinarith⟩
  · -- a = 4: fB5 4 = [0]
    have ho1 : o = 0 := by change o < ([0] : List (Fin 5)).length at ho; simp at ho; omega
    subst ho1
    simp only [InLetterInterval, intervalLo, intervalHi, fB5, List.take, lambda', List.map,
      List.sum_nil, add_zero, List.getElem_cons_zero] at hx ⊢
    exact ⟨by nlinarith, by nlinarith⟩

/-- Core strong-induction theorem: for EVERY `p : ℕ`, `lambda' (prefixOf b5 p)` lies in the
open interval `InLetterInterval (b5 p)`. -/
theorem b5_prefix_in_letter_interval (p : ℕ) :
    InLetterInterval (b5 p) (lambda' (prefixOf b5 p)) := by
  induction p using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0
      simp only [b5_zero, prefixOf_zero, lambdaPrime_nil, InLetterInterval, intervalLo, intervalHi]
      exact ⟨by norm_num, by linarith [one_lt_phi]⟩
    · rcases exists_block_decomp q with ⟨p, o, ho, _, hb5_q, hpref_q, hp_lt_q⟩
      have hpq : p < q := hp_lt_q (by omega)
      have ihp := ih p hpq
      rw [hb5_q, hpref_q, lambdaPrime_append, lambdaPrime_applyMorph_fB5]
      exact coding_step_inclusion (b5 p) o ho ihp

/-- **Theorem `R18-2-1` Part (1) (`b5_codes_interval_translation`)**:
Unconditional 5-interval coding of `b_5`: for every position `p : ℕ`, with
`x_p := lambda' (prefixOf b5 p)`, `x_p` lies strictly in `(-φ^2 / 2, φ^3 / 2)` (never hitting
any endpoint or cut point) and `b5 p` is uniquely characterized by the five open intervals
`P_2, P_0, P_4, P_1, P_3`. -/
theorem b5_codes_interval_translation (p : ℕ) :
    let x_p := lambda' (prefixOf b5 p)
    (-φ ^ 2 / 2 < x_p ∧ x_p < φ ^ 3 / 2) ∧
    (b5 p = 2 ↔ -φ ^ 2 / 2 < x_p ∧ x_p < -1 / 2) ∧
    (b5 p = 0 ↔ -1 / 2 < x_p ∧ x_p < (φ - 1) / 2) ∧
    (b5 p = 4 ↔ (φ - 1) / 2 < x_p ∧ x_p < φ / 2) ∧
    (b5 p = 1 ↔ φ / 2 < x_p ∧ x_p < φ) ∧
    (b5 p = 3 ↔ φ < x_p ∧ x_p < φ ^ 3 / 2) := by
  dsimp only
  have hin := b5_prefix_in_letter_interval p
  have hiff : ∀ c : Fin 5, b5 p = c ↔ InLetterInterval c (lambda' (prefixOf b5 p)) := by
    intro c
    constructor
    · rintro rfl; exact hin
    · intro hc; exact inLetterInterval_unique hin hc
  rcases cut_chain with ⟨c1, c2, c3, c4, c5⟩
  have hwin : -φ ^ 2 / 2 < lambda' (prefixOf b5 p) ∧ lambda' (prefixOf b5 p) < φ ^ 3 / 2 := by
    rcases hp : b5 p with ⟨v, hv⟩
    rw [hp] at hin
    interval_cases v <;>
      (simp only [InLetterInterval, intervalLo, intervalHi] at hin; exact ⟨by linarith, by linarith⟩)
  exact ⟨hwin, hiff 2, hiff 0, hiff 4, hiff 1, hiff 3⟩

/-! ## Section 4: Prefix-Step Additivity & General Interval-Coding Convexity Sign Law -/

/-- If `b5` matches `u` starting at `p`, then `prefixOf b5 (p + k) = prefixOf b5 p ++ u.take k`
for every `k ≤ u.length`. -/
theorem prefixOf_b5_add_take {u : List (Fin 5)} {p k : ℕ} (hk : k ≤ u.length)
    (hmatch : ∀ j (hj : j < u.length), b5 (p + j) = u[j]) :
    prefixOf b5 (p + k) = prefixOf b5 p ++ u.take k := by
  rw [prefixOf_add]
  congr 1
  apply List.ext_getElem
  · simp [hk]
  · intro j hj1 hj2
    simp only [List.getElem_ofFn, List.getElem_take]
    exact hmatch j (by simp at hj1; omega)

theorem lambdaPrime_prefixOf_occ {u : List (Fin 5)} {p : ℕ}
    (hmatch : ∀ j (hj : j < u.length), b5 (p + j) = u[j]) :
    lambda' (prefixOf b5 (p + u.length)) = lambda' (prefixOf b5 p) + lambda' u := by
  have h := prefixOf_b5_add_take (le_refl u.length) hmatch
  rw [List.take_of_length_le (le_refl _)] at h
  rw [h, lambdaPrime_append]

/-- Convexity of word cylinders along the `b5` orbit: if `u` occurs at `p₁` and `p₂`, and
another position `q : ℕ` has `x_q` lying in the closed segment between `x_{p₁}` and `x_{p₂}`,
then `u` also occurs at `q` in `b5`. -/
theorem occ_b5_of_between {u : List (Fin 5)} {p₁ p₂ q : ℕ}
    (h1 : ∀ j (hj : j < u.length), b5 (p₁ + j) = u[j])
    (h2 : ∀ j (hj : j < u.length), b5 (p₂ + j) = u[j])
    (hbet : min (lambda' (prefixOf b5 p₁)) (lambda' (prefixOf b5 p₂)) ≤ lambda' (prefixOf b5 q) ∧
            lambda' (prefixOf b5 q) ≤ max (lambda' (prefixOf b5 p₁)) (lambda' (prefixOf b5 p₂))) :
    ∀ j (hj : j < u.length), b5 (q + j) = u[j] := by
  intro j
  induction j using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hq_pref : prefixOf b5 (q + k) = prefixOf b5 q ++ u.take k := by
      rw [prefixOf_add]
      congr 1
      apply List.ext_getElem
      · simp [le_of_lt hk]
      · intro i hi1 hi2
        simp only [List.getElem_ofFn, List.getElem_take]
        exact ih i (by simp at hi1; omega) (by simp at hi1; omega)
    have hp1_pref := prefixOf_b5_add_take (le_of_lt hk) h1
    have hp2_pref := prefixOf_b5_add_take (le_of_lt hk) h2
    have hx1 : InLetterInterval u[k] (lambda' (prefixOf b5 p₁) + lambda' (u.take k)) := by
      rw [← lambdaPrime_append, ← hp1_pref, ← h1 k hk]
      exact b5_prefix_in_letter_interval (p₁ + k)
    have hx2 : InLetterInterval u[k] (lambda' (prefixOf b5 p₂) + lambda' (u.take k)) := by
      rw [← lambdaPrime_append, ← hp2_pref, ← h2 k hk]
      exact b5_prefix_in_letter_interval (p₂ + k)
    unfold InLetterInterval at hx1 hx2
    have hxq : InLetterInterval u[k] (lambda' (prefixOf b5 (q + k))) := by
      rw [hq_pref, lambdaPrime_append]
      unfold InLetterInterval
      rcases le_total (lambda' (prefixOf b5 p₁)) (lambda' (prefixOf b5 p₂)) with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at hbet
        exact ⟨by linarith [hx1.1, hbet.1], by linarith [hx2.2, hbet.2]⟩
      · rw [min_eq_right hle, max_eq_left hle] at hbet
        exact ⟨by linarith [hx2.1, hbet.1], by linarith [hx1.2, hbet.2]⟩
    exact inLetterInterval_unique (b5_prefix_in_letter_interval (q + k)) hxq

/-- **General Interval-Coding Convexity Sign Law (`R18-2-1` general form)**:
For ANY non-empty words `u, v` where `u ++ u` is NOT a factor of `b5` and `u ++ v ++ u` IS a
factor of `b5`, `lambda' u` and `lambda' v` are non-zero with strictly opposite signs, and
`|lambda' (u ++ v)| < |lambda' u|`. -/
theorem b5_uvu_opposite_signs_of_not_square {u v : List (Fin 5)}
    (hu : u ≠ []) (hv : v ≠ [])
    (hnosq : ¬ IsFactorInf (u ++ u) b5)
    (hfac : IsFactorInf (u ++ v ++ u) b5) :
    lambda' u ≠ 0 ∧ lambda' v ≠ 0 ∧
    lambda' u * lambda' v < 0 ∧
    |lambda' (u ++ v)| < |lambda' u| := by
  have hlu : lambda' u ≠ 0 := lambdaPrime_ne_zero_of_ne_nil hu
  have hlv : lambda' v ≠ 0 := lambdaPrime_ne_zero_of_ne_nil hv
  rcases hfac with ⟨p₁, hp₁⟩
  let p₂ := p₁ + u.length + v.length
  have hu1 : ∀ j (hj : j < u.length), b5 (p₁ + j) = u[j] := by
    intro j hj
    have hlt : j < (u ++ v ++ u).length := by simp; omega
    have h := hp₁ j hlt
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hj] at h
    exact h
  have huv1 : ∀ j (hj : j < (u ++ v).length), b5 (p₁ + j) = (u ++ v)[j] := by
    intro j hj
    have hlt : j < (u ++ v ++ u).length := by simp at hj ⊢; omega
    have h := hp₁ j hlt
    rw [List.getElem_append_left hj] at h
    exact h
  have hu2 : ∀ j (hj : j < u.length), b5 (p₂ + j) = u[j] := by
    intro j hj
    have hlt : (u ++ v).length + j < (u ++ v ++ u).length := by simp; omega
    have h := hp₁ ((u ++ v).length + j) hlt
    rw [List.getElem_append_right (by omega)] at h
    have hidx : p₁ + ((u ++ v).length + j) = p₂ + j := by
      simp only [List.length_append, p₂]; omega
    rw [hidx] at h
    simpa [Nat.add_sub_cancel_left] using h
  set x₁ := lambda' (prefixOf b5 p₁)
  set x₂ := lambda' (prefixOf b5 p₂)
  set D := lambda' u
  set Δ := lambda' (u ++ v)
  have hx₂ : x₂ = x₁ + Δ := by
    have h := lambdaPrime_prefixOf_occ huv1
    have hp2_eq : p₁ + (u ++ v).length = p₂ := by
      simp only [List.length_append, p₂]; omega
    rw [hp2_eq] at h
    exact h
  have hq1_val : lambda' (prefixOf b5 (p₁ + u.length)) = x₁ + D :=
    lambdaPrime_prefixOf_occ hu1
  have hq2_val : lambda' (prefixOf b5 (p₂ + u.length)) = x₂ + D :=
    lambdaPrime_prefixOf_occ hu2
  have mk_sq : ∀ p : ℕ,
      (∀ j (hj : j < u.length), b5 (p + j) = u[j]) →
      (∀ j (hj : j < u.length), b5 (p + u.length + j) = u[j]) →
      IsFactorInf (u ++ u) b5 := by
    intro p ha hb
    refine ⟨p, fun j hj => ?_⟩
    by_cases hju : j < u.length
    · rw [List.getElem_append_left hju]
      exact ha j hju
    · rw [List.getElem_append_right (by omega)]
      have hidx : p + j = p + u.length + (j - u.length) := by omega
      rw [hidx]
      exact hb (j - u.length) (by simp at hj; omega)
  have habs : |Δ| < |D| := by
    by_contra hnot
    have hge : |D| ≤ |Δ| := le_of_not_gt hnot
    rcases lt_or_gt_of_ne hlu with hDneg | hDpos
    · rw [abs_of_neg hDneg] at hge
      rcases le_abs.mp hge with hcase | hcase
      · have hbet : min x₁ x₂ ≤ lambda' (prefixOf b5 (p₂ + u.length)) ∧
            lambda' (prefixOf b5 (p₂ + u.length)) ≤ max x₁ x₂ := by
          have hle : x₁ ≤ x₂ := by linarith
          rw [min_eq_left hle, max_eq_right hle, hq2_val]
          exact ⟨by linarith, by linarith⟩
        exact hnosq (mk_sq p₂ hu2 (occ_b5_of_between hu1 hu2 hbet))
      · have hbet : min x₁ x₂ ≤ lambda' (prefixOf b5 (p₁ + u.length)) ∧
            lambda' (prefixOf b5 (p₁ + u.length)) ≤ max x₁ x₂ := by
          have hle : x₂ ≤ x₁ := by linarith
          rw [min_eq_right hle, max_eq_left hle, hq1_val]
          exact ⟨by linarith, by linarith⟩
        exact hnosq (mk_sq p₁ hu1 (occ_b5_of_between hu1 hu2 hbet))
    · rw [abs_of_pos hDpos] at hge
      rcases le_abs.mp hge with hcase | hcase
      · have hbet : min x₁ x₂ ≤ lambda' (prefixOf b5 (p₁ + u.length)) ∧
            lambda' (prefixOf b5 (p₁ + u.length)) ≤ max x₁ x₂ := by
          have hle : x₁ ≤ x₂ := by linarith
          rw [min_eq_left hle, max_eq_right hle, hq1_val]
          exact ⟨by linarith, by linarith⟩
        exact hnosq (mk_sq p₁ hu1 (occ_b5_of_between hu1 hu2 hbet))
      · have hbet : min x₁ x₂ ≤ lambda' (prefixOf b5 (p₂ + u.length)) ∧
            lambda' (prefixOf b5 (p₂ + u.length)) ≤ max x₁ x₂ := by
          have hle : x₂ ≤ x₁ := by linarith
          rw [min_eq_right hle, max_eq_left hle, hq2_val]
          exact ⟨by linarith, by linarith⟩
        exact hnosq (mk_sq p₂ hu2 (occ_b5_of_between hu1 hu2 hbet))
  have hsum : Δ = D + lambda' v := lambdaPrime_append u v
  have hopp : D * lambda' v < 0 := by
    rcases lt_or_gt_of_ne hlu with hDneg | hDpos
    · rw [abs_of_neg hDneg] at habs
      have h1 : D < Δ := by linarith [(abs_lt.mp habs).1]
      have h2 : 0 < lambda' v := by linarith
      nlinarith
    · rw [abs_of_pos hDpos] at habs
      have h1 : Δ < D := (abs_lt.mp habs).2
      have h2 : lambda' v < 0 := by linarith
      nlinarith
  exact ⟨hlu, hlv, hopp, habs⟩

/-! ## Section 5: XYX Digraph Formulas, Relation Graph `RelB5`, and Odd Cycles -/

/-- A loopless directed graph on vertex type `V`, where each arc `u → v` represents the
XYX-formula fragment `V_u V_v V_u`. -/
structure LooplessDigraph (V : Type*) where
  adj : V → V → Prop
  loopless : ∀ v : V, ¬ adj v v

/-- Exact Ochem–Rosenfeld XYX-formula occurrence in an infinite word `W : ℕ → α`. -/
def OccursDigraphInf {V α : Type*} (G : LooplessDigraph V) (W : ℕ → α) : Prop :=
  ∃ h : V → List α, (∀ v, h v ≠ []) ∧ ∀ u v, G.adj u v → IsFactorInf (h u ++ h v ++ h u) W

/-- An infinite word `W` avoids the XYX-formula of `G`. -/
def AvoidsDigraphInf {V α : Type*} (G : LooplessDigraph V) (W : ℕ → α) : Prop :=
  ¬ OccursDigraphInf G W

/-- Symmetric underlying undirected adjacency of a digraph `G`. -/
def UndirAdj {V : Type*} (G : LooplessDigraph V) (u v : V) : Prop :=
  G.adj u v ∨ G.adj v u

/-- The underlying undirected graph of `G` contains an odd closed walk / odd cycle of length
`2 * k + 1` (`k : ℕ`). -/
def HasOddCycle {V : Type*} (G : LooplessDigraph V) : Prop :=
  ∃ k : ℕ, ∃ cyc : Fin (2 * k + 1) → V,
    ∀ i : Fin (2 * k + 1),
      UndirAdj G (cyc i) (cyc ⟨(i.val + 1) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩)

/-- The symmetric XYX relation graph on non-empty factors of `b5`:
`RelB5 u v` holds iff `u ≠ []`, `v ≠ []`, and `u ++ v ++ u` or `v ++ u ++ v` is a factor of `b5`. -/
def RelB5 (u v : List (Fin 5)) : Prop :=
  u ≠ [] ∧ v ≠ [] ∧ (IsFactorInf (u ++ v ++ u) b5 ∨ IsFactorInf (v ++ u ++ v) b5)

/-- The cyclic 3-tournament `C3` on `Fin 3` (`0 → 1 → 2 → 0`). -/
def C3 : LooplessDigraph (Fin 3) where
  adj i j := (i.val + 1) % 3 = j.val
  loopless v := by fin_cases v <;> decide

/-- The transitive tournament `TT k` on `Fin k` (`i → j ↔ i < j`). -/
def TT (k : ℕ) : LooplessDigraph (Fin k) where
  adj i j := i.val < j.val
  loopless v := Nat.lt_irrefl v.val

/-- The complete bidirected loopless digraph `Kn n` on `Fin n` (`i → j ↔ i ≠ j`). -/
def Kn (n : ℕ) : LooplessDigraph (Fin n) where
  adj i j := i ≠ j
  loopless _ h := h rfl

end BadkobehOchemB5
