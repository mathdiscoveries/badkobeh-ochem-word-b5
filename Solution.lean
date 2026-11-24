module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import BadkobehOchemB5

/-!
# Palomar Solution: Badkobeh–Ochem's 5-Letter Word `b₅`

Discharges every theorem in `Challenge.lean` (`BadkobehOchemB5Challenge`)
unconditionally from `BadkobehOchemB5`, with zero `sorry`, zero `native_decide`,
and standard axioms only (`propext`, `Quot.sound`, `Classical.choice`).
-/

@[expose] public section

namespace BadkobehOchemB5Challenge

noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

def prefixOf {α : Type*} (W : ℕ → α) (n : ℕ) : List α :=
  List.ofFn fun i : Fin n => W i.val

def IsFactorInf {α : Type*} (u : List α) (W : ℕ → α) : Prop :=
  ∃ i : ℕ, ∀ j (hj : j < u.length), W (i + j) = u[j]

def applyMorph {α β : Type*} (f : α → List β) (w : List α) : List β :=
  w.flatMap f

def iterMorph {α : Type*} (f : α → List α) : ℕ → List α → List α
  | 0, w => w
  | n + 1, w => applyMorph f (iterMorph f n w)

def fB5 : Fin 5 → List (Fin 5)
  | 0 => [0, 1]
  | 1 => [2, 3]
  | 2 => [4]
  | 3 => [2, 1]
  | 4 => [0]

def b5 (i : ℕ) : Fin 5 :=
  (iterMorph fB5 i [0]).getD i 0

noncomputable def l' : Fin 5 → ℝ
  | 0 => 1
  | 1 => -φ
  | 2 => 1 + φ
  | 3 => -φ
  | 4 => -φ

noncomputable def lambda' (w : List (Fin 5)) : ℝ :=
  (w.map l').sum

def FactorsOfLen {α : Type*} (W : ℕ → α) (n : ℕ) : Set (List α) :=
  { w : List α | w.length = n ∧ IsFactorInf w W }

noncomputable def factorComplexity {α : Type*} (W : ℕ → α) (n : ℕ) : ℕ :=
  (FactorsOfLen W n).ncard

def fibMorph : Bool → List Bool
  | false => [false, true]
  | true => [false]

def fibWord (i : ℕ) : Bool :=
  (iterMorph fibMorph i [false]).getD i false

def gFib : Fin 5 → List Bool
  | 0 => [false, true]
  | 1 => [false]
  | 2 => [true]
  | 3 => [false]
  | 4 => [false]

def gFibB5 (i : ℕ) : Bool :=
  (applyMorph gFib (prefixOf b5 (i + 1))).getD i false

def gRf : Fin 5 → List Bool
  | ⟨0, _⟩ => [false, true]
  | ⟨1, _⟩ => [true, false]
  | ⟨2, _⟩ => []
  | ⟨3, _⟩ => [true, true]
  | ⟨4, _⟩ => [false, false]

def gRfB5 (k : ℕ) : Bool :=
  (applyMorph gRf (prefixOf b5 (2 * (k + 1)))).getD k false

def roteFib : ℕ → Bool
  | 0 => false
  | k + 1 => xor (roteFib k) (!(fibWord (k + 1)))

def IsPeriod {α : Type*} (w : List α) (p : ℕ) : Prop :=
  ∀ i : ℕ, ∀ hi : i + p < w.length, w[i]'(by omega) = w[i + p]'hi

def ExponentSet {α : Type*} (W : ℕ → α) : Set ℝ :=
  { e : ℝ | ∃ w p, IsFactorInf w W ∧ 1 ≤ p ∧ IsPeriod w p ∧ e = (w.length : ℝ) / (p : ℝ) }

noncomputable def critExp {α : Type*} (W : ℕ → α) : ℝ :=
  sSup (ExponentSet W)

def DeficitSet (W : ℕ → Fin 5) : Set ℝ :=
  { d : ℝ | ∃ w : List (Fin 5), ∃ p : ℕ,
      IsFactorInf w W ∧ 1 ≤ p ∧ IsPeriod w p ∧
      d = φ * (p : ℝ) - 2 * ((w.length : ℝ) - (p : ℝ)) }

def AsympExponentSet (W : ℕ → Fin 5) (L : ℕ) : Set ℝ :=
  { r : ℝ | ∃ w : List (Fin 5), ∃ p : ℕ,
      IsFactorInf w W ∧ L ≤ p ∧ 1 ≤ p ∧ IsPeriod w p ∧ r = (w.length : ℝ) / (p : ℝ) }

def swap34 : Fin 5 → Fin 5
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 3

def revSwap34 (w : List (Fin 5)) : List (Fin 5) :=
  w.reverse.map swap34

def pi3 : Fin 5 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 0

def pi3B5 (p : ℕ) : Fin 3 :=
  pi3 (b5 p)

/-! ### Definitional bridges to `BadkobehOchemB5` -/

private lemma iterMorph_eq {α : Type*} (f : α → List α) (n : ℕ) (w : List α) :
    iterMorph f n w = BadkobehOchemB5.iterMorph f n w := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterMorph, BadkobehOchemB5.iterMorph, applyMorph, BadkobehOchemB5.applyMorph, ih]

private lemma fB5_eq : fB5 = BadkobehOchemB5.fB5 := by
  funext a; fin_cases a <;> rfl

private lemma getD_eq_getElem_of_lt {α : Type*} (l : List α) (i : ℕ) (d : α) (h : i < l.length) :
    l.getD i d = l[i]'h := by
  simp [List.getD, List.getElem?_eq_getElem h]

private lemma b5_eq : b5 = BadkobehOchemB5.b5 := by
  funext i
  unfold b5 BadkobehOchemB5.b5 BadkobehOchemB5.fixedPoint
  rw [fB5_eq, iterMorph_eq]
  exact getD_eq_getElem_of_lt _ _ _
    (BadkobehOchemB5.lt_iterMorph_length _ _ BadkobehOchemB5.fB5_nonempty BadkobehOchemB5.fB5_prolongable i)

private lemma fibMorph_eq : fibMorph = BadkobehOchemB5.fibMorph := by
  funext b; cases b <;> rfl

private lemma fibWord_eq : fibWord = BadkobehOchemB5.fibWord := by
  funext i
  unfold fibWord BadkobehOchemB5.fibWord BadkobehOchemB5.fixedPoint
  rw [fibMorph_eq, iterMorph_eq]
  exact getD_eq_getElem_of_lt _ _ _
    (BadkobehOchemB5.lt_iterMorph_length _ _ BadkobehOchemB5.fibMorph_nonempty BadkobehOchemB5.fibMorph_prolongable i)

private lemma gFib_eq : gFib = BadkobehOchemB5.gFib := by
  funext a; fin_cases a <;> rfl

private lemma gFibB5_eq : gFibB5 = BadkobehOchemB5.gFibB5 := by
  funext i
  unfold gFibB5 BadkobehOchemB5.gFibB5 BadkobehOchemB5.applyMorphInf
  change (BadkobehOchemB5.applyMorph gFib (BadkobehOchemB5.prefixOf b5 (i + 1))).getD i false = _
  rw [gFib_eq, b5_eq]
  exact getD_eq_getElem_of_lt _ _ _
    (BadkobehOchemB5.lt_applyMorph_prefix_length _ BadkobehOchemB5.gFib_nonempty _ i)

private lemma gRf_eq : gRf = BadkobehOchemB5.gRf := by
  funext a; fin_cases a <;> rfl

private lemma gRfB5_eq : gRfB5 = BadkobehOchemB5.gRfB5 := by
  funext k
  unfold gRfB5 BadkobehOchemB5.gRfB5
  change (BadkobehOchemB5.applyMorph gRf (BadkobehOchemB5.prefixOf b5 (2 * (k + 1)))).getD k false = _
  rw [gRf_eq, b5_eq]
  have h := BadkobehOchemB5.gRfStart_two_mul_ge (k + 1)
  unfold BadkobehOchemB5.gRfStart at h
  exact getD_eq_getElem_of_lt _ _ _ (by omega)

private lemma roteFib_eq : roteFib = BadkobehOchemB5.roteFib := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [roteFib, BadkobehOchemB5.roteFib, ih, fibWord_eq]

private lemma l'_eq : l' = BadkobehOchemB5.l' := by
  funext a; fin_cases a <;> rfl

private lemma lambda'_eq (w : List (Fin 5)) : lambda' w = BadkobehOchemB5.lambda' w := by
  simp only [lambda', BadkobehOchemB5.lambda', l'_eq]

private lemma swap34_eq : swap34 = BadkobehOchemB5.swap34 := by
  funext a; fin_cases a <;> rfl

private lemma revSwap34_eq (w : List (Fin 5)) : revSwap34 w = BadkobehOchemB5.revSwap34 w := by
  simp only [revSwap34, BadkobehOchemB5.revSwap34, swap34_eq]

private lemma pi3_eq : pi3 = BadkobehOchemB5.pi3 := by
  funext a; fin_cases a <;> rfl

private lemma pi3B5_eq : pi3B5 = BadkobehOchemB5.pi3B5 := by
  funext p
  simp only [pi3B5, BadkobehOchemB5.pi3B5, pi3_eq, b5_eq]

/-! ### Principal theorems matching `Challenge.lean` -/

theorem b5_codes_interval_translation (p : ℕ) :
    let x_p := lambda' (prefixOf b5 p)
    (-φ ^ 2 / 2 < x_p ∧ x_p < φ ^ 3 / 2) ∧
    (b5 p = 2 ↔ -φ ^ 2 / 2 < x_p ∧ x_p < -1 / 2) ∧
    (b5 p = 0 ↔ -1 / 2 < x_p ∧ x_p < (φ - 1) / 2) ∧
    (b5 p = 4 ↔ (φ - 1) / 2 < x_p ∧ x_p < φ / 2) ∧
    (b5 p = 1 ↔ φ / 2 < x_p ∧ x_p < φ) ∧
    (b5 p = 3 ↔ φ < x_p ∧ x_p < φ ^ 3 / 2) := by
  dsimp only
  rw [lambda'_eq, b5_eq]
  exact BadkobehOchemB5.b5_codes_interval_translation p

theorem b5_factor_complexity (n : ℕ) :
    factorComplexity b5 n = 4 * n + 1 := by
  rw [b5_eq]
  exact BadkobehOchemB5.b5_factor_complexity n

theorem b5_sturmian_projection (n : ℕ) :
    FactorsOfLen gFibB5 n = FactorsOfLen fibWord n ∧
    factorComplexity gFibB5 n = n + 1 := by
  rw [gFibB5_eq, fibWord_eq]
  have h := BadkobehOchemB5.b5_sturmian_projection n
  exact ⟨h.1, h.2.2⟩

theorem b5_rote_fibonacci_projection (n : ℕ) :
    FactorsOfLen gRfB5 n = FactorsOfLen roteFib n ∧
    (1 ≤ n → factorComplexity gRfB5 n = 2 * n) := by
  rw [gRfB5_eq, roteFib_eq]
  exact ⟨BadkobehOchemB5.b5_rote_fibonacci_projection n,
         fun hn => BadkobehOchemB5.gRfB5_factor_complexity n hn⟩

theorem b5_critical_exponent :
    critExp b5 = (5 + Real.sqrt 5) / 4 ∧
    ¬ ∃ w p, IsFactorInf w b5 ∧ 1 ≤ p ∧ IsPeriod w p ∧
      (w.length : ℝ) / (p : ℝ) = (5 + Real.sqrt 5) / 4 := by
  rw [b5_eq]
  exact ⟨BadkobehOchemB5.b5_critical_exponent_eq,
         BadkobehOchemB5.b5_critical_exponent_not_attained⟩

theorem b5_sharp_second_order_and_deficit :
    sInf (DeficitSet b5) = (7 - Real.sqrt 5) / 4 ∧
    (∀ w p, IsFactorInf w b5 → 1 ≤ p → IsPeriod w p →
      (w.length : ℝ) / (p : ℝ) < (5 + Real.sqrt 5) / 4 - (7 - Real.sqrt 5) / (8 * (p : ℝ))) ∧
    ¬ ∃ w p, IsFactorInf w b5 ∧ 1 ≤ p ∧ IsPeriod w p ∧
      φ * (p : ℝ) - 2 * ((w.length : ℝ) - (p : ℝ)) = (7 - Real.sqrt 5) / 4 := by
  rw [b5_eq]
  exact ⟨BadkobehOchemB5.b5_sharp_deficit_inf_eq,
         BadkobehOchemB5.b5_exponent_lt_sharp_second_order,
         BadkobehOchemB5.b5_sharp_deficit_not_attained⟩

theorem b5_asymp_critExp_and_irrational :
    (∀ L : ℕ, sSup (AsympExponentSet b5 L) = (5 + Real.sqrt 5) / 4) ∧
    Irrational (critExp b5) := by
  rw [b5_eq]
  exact ⟨BadkobehOchemB5.b5_asymp_critExp_eq,
         BadkobehOchemB5.b5_critExp_irrational⟩

theorem b5_language_rev_swap34_invariant (w : List (Fin 5)) :
    IsFactorInf w b5 ↔ IsFactorInf (revSwap34 w) b5 := by
  rw [b5_eq, revSwap34_eq]
  exact BadkobehOchemB5.b5_language_rev_swap34_invariant w

theorem pi3B5_factor_complexity (n : ℕ) :
    factorComplexity pi3B5 n = 2 * n + 1 := by
  rw [pi3B5_eq]
  exact BadkobehOchemB5.pi3B5_factor_complexity n

theorem b5_not_C_balanced (C : ℕ) :
    ∃ n : ℕ, ∃ u v : List (Fin 5), ∃ a : Fin 5,
      u.length = n ∧ v.length = n ∧ IsFactorInf u b5 ∧ IsFactorInf v b5 ∧
      (C : ℤ) < |(u.count a : ℤ) - (v.count a : ℤ)| := by
  rw [b5_eq]
  exact BadkobehOchemB5.b5_not_C_balanced C

theorem fB5_iter_length_rec (w : List (Fin 5)) (k : ℕ) :
    (iterMorph fB5 (k + 5) w).length + (iterMorph fB5 (k + 2) w).length =
    (iterMorph fB5 (k + 4) w).length + (iterMorph fB5 (k + 3) w).length +
    (iterMorph fB5 (k + 1) w).length + (iterMorph fB5 k w).length := by
  simp only [fB5_eq, iterMorph_eq]
  exact BadkobehOchemB5.fB5_iter_length_rec w k

end BadkobehOchemB5Challenge
