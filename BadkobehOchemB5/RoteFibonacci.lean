/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BadkobehOchemB5.Defs
public import BadkobehOchemB5.ComplexityAndSturmian
import Mathlib.Tactic

/-!
# Complete Resolution of Badkobeh–Ochem (2015) Observation (O2): The Rote–Fibonacci Projection

This module resolves unconditionally the remaining open observation **(O2)** of Badkobeh and Ochem
(*Theoret. Comput. Sci.* 588, 2015, Section 5): under the erasing binary morphism
`g_rf : 0 ↦ 01, 1 ↦ 10, 2 ↦ ε, 3 ↦ 11, 4 ↦ 00`, the morphic image `g_rf(b_5)` not only has the
exact same set of factors as the Rote–Fibonacci word `r` (Du, Mousavi, Schaeffer and Shallit,
`arXiv:1406.0670` (2014), Theorem 35; Du, Mousavi, Rowland, Schaeffer and Shallit,
*Theoret. Comput. Sci.* 657 (2017), Theorem 1), but satisfies the exact
pointwise identity `g_rf(b_5) = 0 · complement(r)`.

Main theorems proved unconditionally (zero `sorry`, zero `native_decide`, standard 3 axioms only):
1. **`b5_eq_decTau_tauWord`**: Non-erasing 5-block factorization `b_5 = decTau(tauB5^ω(0))` under
   which `g_rf ∘ decTau` is 2-uniform (`01, 10, 11, 00, 10`).
2. **`gRfB5_complDiff_eq_fibWord`**: Exact complemented first-difference law
   `∀ k : ℕ, (gRfB5 k == gRfB5 (k + 1)) = fibWord k`.
3. **`roteFibTransducer_eq_roteFib`**: Exact pointwise equivalence between Du–Mousavi–Schaeffer–
   Shallit's 2-state transducer definition (`T_0(fibWord)`) and the complemented first-difference
   definition `roteFib`.
4. **`gRfB5_zero`** and **`gRfB5_succ_eq_not_roteFib`**: Exact pointwise identity
   `gRfB5 0 = false` and `∀ k : ℕ, gRfB5 (k + 1) = !(roteFib k)` (i.e. `g_rf(b_5) = 0 · r̄`).
5. **`b5_rote_fibonacci_projection`**: Exact factor-set equality
   `∀ n : ℕ, FactorsOfLen gRfB5 n = FactorsOfLen roteFib n`.
6. **`roteFib_factors_compl_invariant`** and **`gRfB5_factors_compl_invariant`**: Complement
   invariance of both factor languages.
7. **`roteFib_factor_complexity`** and **`gRfB5_factor_complexity`**: Exact Rote factor complexity
   `factorComplexity gRfB5 n = factorComplexity roteFib n = 2 * n` for every `n ≥ 1` (and `1` at `0`).
-/

@[expose] public section

namespace BadkobehOchemB5

/-! ## Section 1: Badkobeh–Ochem's Erasing Morphism `g_rf` and Infinite Image `gRfB5` -/

/-- Badkobeh–Ochem (2015, Section 5) erasing binary morphism
`g_rf(0) = 01, g_rf(1) = 10, g_rf(2) = ε, g_rf(3) = 11, g_rf(4) = 00`
(`false = 0`, `true = 1`). -/
def gRf : Fin 5 → List Bool
  | ⟨0, _⟩ => [false, true]
  | ⟨1, _⟩ => [true, false]
  | ⟨2, _⟩ => []
  | ⟨3, _⟩ => [true, true]
  | ⟨4, _⟩ => [false, false]

/-- Cumulative length of `g_rf(b_5[0..p))`. -/
def gRfStart (p : ℕ) : ℕ :=
  (applyMorph gRf (prefixOf b5 p)).length

theorem gRfStart_zero : gRfStart 0 = 0 := rfl

theorem gRfStart_succ (p : ℕ) :
    gRfStart (p + 1) = gRfStart p + (gRf (b5 p)).length := by
  unfold gRfStart
  rw [prefixOf_succ, applyMorph_append, List.length_append]
  simp [applyMorph]

theorem gRfStart_mono : Monotone gRfStart := by
  intro a b hab
  induction hab with
  | refl => exact le_refl _
  | @step m _ ih =>
    rw [gRfStart_succ]
    omega

/-- In `b_5`, the letter `2` is never followed immediately by `2`. -/
theorem b5_no_two_two (p : ℕ) (hp : b5 p = 2) : b5 (p + 1) ≠ 2 := by
  intro hp1
  have hx := b5_prefix_in_letter_interval p
  have hx1 := b5_prefix_in_letter_interval (p + 1)
  rw [hp] at hx
  rw [hp1] at hx1
  unfold InLetterInterval intervalLo intervalHi at hx hx1
  have hstep : lambda' (prefixOf b5 (p + 1)) = lambda' (prefixOf b5 p) + (1 + φ) := by
    rw [prefixOf_succ, lambdaPrime_append]
    simp [lambda', hp, l']
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have h1 : 1 < φ := one_lt_phi
  linarith

theorem gRf_length_pair_ge_two (p : ℕ) :
    2 ≤ (gRf (b5 p)).length + (gRf (b5 (p + 1))).length := by
  by_cases h2 : b5 p = 2
  · have hne : b5 (p + 1) ≠ 2 := b5_no_two_two p h2
    have hlen : (gRf (b5 (p + 1))).length = 2 := by
      rcases fin5_cases (b5 (p + 1)) with h | h | h | h | h
      · simp [h, gRf]
      · simp [h, gRf]
      · exact absurd h hne
      · simp [h, gRf]
      · simp [h, gRf]
    omega
  · have hlen : (gRf (b5 p)).length = 2 := by
      rcases fin5_cases (b5 p) with h | h | h | h | h
      · simp [h, gRf]
      · simp [h, gRf]
      · exact absurd h h2
      · simp [h, gRf]
      · simp [h, gRf]
    omega

theorem gRfStart_two_mul_ge (k : ℕ) : 2 * k ≤ gRfStart (2 * k) := by
  induction k with
  | zero => simp [gRfStart_zero]
  | succ k ih =>
    have h1 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h1, gRfStart_succ, gRfStart_succ]
    have hp := gRf_length_pair_ge_two (2 * k)
    omega

/-- The infinite binary word `g_rf(b_5)`, defined directly from `applyMorph gRf` on prefixes of `b_5`. -/
def gRfB5 (k : ℕ) : Bool :=
  (applyMorph gRf (prefixOf b5 (2 * (k + 1))))[k]'(by
    have h := gRfStart_two_mul_ge (k + 1)
    unfold gRfStart at h
    omega)

theorem gRfB5_eq_getElem {k n : ℕ} (hk : k < gRfStart n) :
    gRfB5 k = (applyMorph gRf (prefixOf b5 n))[k]'hk := by
  unfold gRfB5
  have hk2 : k < (applyMorph gRf (prefixOf b5 (2 * (k + 1)))).length := by
    have h := gRfStart_two_mul_ge (k + 1)
    unfold gRfStart at h
    omega
  by_cases hle : n ≤ 2 * (k + 1)
  · have hp : applyMorph gRf (prefixOf b5 n) <+: applyMorph gRf (prefixOf b5 (2 * (k + 1))) :=
      applyMorph_prefix_of_prefix gRf (prefixOf_prefix_of_le b5 hle)
    exact (getElem_eq_of_prefix hp hk hk2).symm
  · have hle' : 2 * (k + 1) ≤ n := by omega
    have hp : applyMorph gRf (prefixOf b5 (2 * (k + 1))) <+: applyMorph gRf (prefixOf b5 n) :=
      applyMorph_prefix_of_prefix gRf (prefixOf_prefix_of_le b5 hle')
    exact getElem_eq_of_prefix hp hk2 hk

theorem gRfB5_prefix_eq (n : ℕ) :
    prefixOf gRfB5 (gRfStart n) = applyMorph gRf (prefixOf b5 n) := by
  apply List.ext_getElem
  · rw [prefixOf_length]; rfl
  · intro i hi1 hi2
    rw [prefixOf_getElem]
    exact gRfB5_eq_getElem hi2

/-! ## Section 2: 5-Block Non-Erasing Factorization `tauB5` and `decTau` -/

/-- Non-erasing 5-letter morphism `tauB5` (`0↦01, 1↦2, 2↦34, 3↦0, 4↦32`) factoring `f_5`. -/
def tauB5 : Fin 5 → List (Fin 5)
  | ⟨0, _⟩ => [0, 1]
  | ⟨1, _⟩ => [2]
  | ⟨2, _⟩ => [3, 4]
  | ⟨3, _⟩ => [0]
  | ⟨4, _⟩ => [3, 2]

/-- Block decoding `decTau` (`0↦0, 1↦1, 2↦23, 3↦4, 4↦21`) satisfying `decTau ∘ tauB5 = f_5 ∘ decTau`. -/
def decTau : Fin 5 → List (Fin 5)
  | ⟨0, _⟩ => [0]
  | ⟨1, _⟩ => [1]
  | ⟨2, _⟩ => [2, 3]
  | ⟨3, _⟩ => [4]
  | ⟨4, _⟩ => [2, 1]

theorem tauB5_nonempty : ∀ x : Fin 5, tauB5 x ≠ [] := by
  intro x
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> decide

theorem tauB5_prolongable : ∃ t : List (Fin 5), tauB5 0 = 0 :: t ∧ t ≠ [] :=
  ⟨[1], rfl, by decide⟩

theorem decTau_nonempty : ∀ x : Fin 5, decTau x ≠ [] := by
  intro x
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The fixed point `tauWord = tauB5^ω(0)`. -/
def tauWord : ℕ → Fin 5 :=
  fixedPoint tauB5 0 tauB5_nonempty tauB5_prolongable

theorem decTau_tauB5_letter (x : Fin 5) :
    applyMorph decTau (tauB5 x) = applyMorph fB5 (decTau x) := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem decTau_tauB5_word (w : List (Fin 5)) :
    applyMorph decTau (applyMorph tauB5 w) = applyMorph fB5 (applyMorph decTau w) := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    change applyMorph decTau (tauB5 a ++ applyMorph tauB5 rest) =
      applyMorph fB5 (decTau a ++ applyMorph decTau rest)
    rw [applyMorph_append, applyMorph_append, decTau_tauB5_letter, ih]

theorem decTau_iter_tauB5 (n : ℕ) :
    applyMorph decTau (iterMorph tauB5 n [0]) = iterMorph fB5 n [0] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterMorph]
    rw [decTau_tauB5_word, ih]

/-- **5-Block Factorization Theorem (`b5_eq_decTau_tauWord`)**:
`b_5` is the exact `decTau`-image of `tauWord = tauB5^ω(0)`. -/
theorem b5_eq_decTau_tauWord (i : ℕ) :
    b5 i = applyMorphInf decTau decTau_nonempty tauWord i := by
  let N := i + 1
  have hpre_t : prefixOf tauWord (iterMorph tauB5 N [0]).length = iterMorph tauB5 N [0] :=
    fixedPoint_prefix_eq tauB5 0 tauB5_nonempty tauB5_prolongable N
  have hdec_eq : applyMorph decTau (prefixOf tauWord (iterMorph tauB5 N [0]).length) =
      iterMorph fB5 N [0] := by
    rw [hpre_t, decTau_iter_tauB5]
  have hi_f : i < (iterMorph fB5 N [0]).length := by
    have hlt := lt_iterMorph_length fB5 0 fB5_nonempty fB5_prolongable N
    omega
  have hi_d : i < (applyMorph decTau (prefixOf tauWord (iterMorph tauB5 N [0]).length)).length := by
    rw [hdec_eq]; exact hi_f
  have hb5 : b5 i = (iterMorph fB5 N [0])[i]'hi_f :=
    fixedPoint_eq_iterMorph_getElem fB5 0 fB5_nonempty fB5_prolongable N i hi_f
  have hinf : applyMorphInf decTau decTau_nonempty tauWord i =
      (applyMorph decTau (prefixOf tauWord (iterMorph tauB5 N [0]).length))[i]'hi_d :=
    applyMorphInf_eq_getElem decTau decTau_nonempty tauWord (iterMorph tauB5 N [0]).length i hi_d
  rw [hb5, hinf]
  have hget := congrArg (fun l => l[i]?) hdec_eq
  rw [List.getElem?_eq_getElem hi_d, List.getElem?_eq_getElem hi_f] at hget
  exact (Option.some.inj hget).symm

/-- The composed 2-uniform binary morphism `gRfDec := g_rf ∘ decTau`. -/
def gRfDec : Fin 5 → List Bool
  | ⟨0, _⟩ => [false, true]
  | ⟨1, _⟩ => [true, false]
  | ⟨2, _⟩ => [true, true]
  | ⟨3, _⟩ => [false, false]
  | ⟨4, _⟩ => [true, false]

theorem gRf_decTau_letter (x : Fin 5) :
    applyMorph gRf (decTau x) = gRfDec x := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem gRf_decTau_word (w : List (Fin 5)) :
    applyMorph gRf (applyMorph decTau w) = applyMorph gRfDec w := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    change applyMorph gRf (decTau a ++ applyMorph decTau rest) =
      gRfDec a ++ applyMorph gRfDec rest
    rw [applyMorph_append, gRf_decTau_letter, ih]

theorem gRfDec_length (x : Fin 5) : (gRfDec x).length = 2 := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem applyMorph_gRfDec_length (w : List (Fin 5)) :
    (applyMorph gRfDec w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    simp only [applyMorph, List.flatMap_cons, List.length_append, List.length_cons]
    rw [gRfDec_length]
    change 2 + (applyMorph gRfDec rest).length = 2 * (rest.length + 1)
    rw [ih]; omega

theorem prefixOf_b5_decTau (m : ℕ) :
    prefixOf b5 (applyMorph decTau (prefixOf tauWord m)).length =
    applyMorph decTau (prefixOf tauWord m) := by
  have h1 : prefixOf (applyMorphInf decTau decTau_nonempty tauWord)
      (applyMorph decTau (prefixOf tauWord m)).length =
      applyMorph decTau (prefixOf tauWord m) :=
    applyMorphInf_prefix_eq decTau decTau_nonempty tauWord m
  have h2 : prefixOf b5 (applyMorph decTau (prefixOf tauWord m)).length =
      prefixOf (applyMorphInf decTau decTau_nonempty tauWord)
      (applyMorph decTau (prefixOf tauWord m)).length := by
    apply List.ext_getElem
    · simp [prefixOf_length]
    · intro i hi1 hi2
      rw [prefixOf_getElem, prefixOf_getElem]
      exact b5_eq_decTau_tauWord i
  rw [h2, h1]

theorem gRfB5_prefix_two_mul (m : ℕ) :
    prefixOf gRfB5 (2 * m) = applyMorph gRfDec (prefixOf tauWord m) := by
  let L := (applyMorph decTau (prefixOf tauWord m)).length
  have hlen : gRfStart L = 2 * m := by
    unfold gRfStart
    rw [prefixOf_b5_decTau m, gRf_decTau_word, applyMorph_gRfDec_length, prefixOf_length]
  have hpre := gRfB5_prefix_eq L
  rw [hlen, prefixOf_b5_decTau m, gRf_decTau_word] at hpre
  exact hpre

def gRfDec0 (x : Fin 5) : Bool := (gRfDec x)[0]'(by rw [gRfDec_length]; omega)
def gRfDec1 (x : Fin 5) : Bool := (gRfDec x)[1]'(by rw [gRfDec_length]; omega)

theorem gRfDec_eq_pair (x : Fin 5) : gRfDec x = [gRfDec0 x, gRfDec1 x] := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem gRfB5_two_mul (i : ℕ) : gRfB5 (2 * i) = gRfDec0 (tauWord i) := by
  have hpre := gRfB5_prefix_two_mul (i + 1)
  have hidx : 2 * i < (prefixOf gRfB5 (2 * (i + 1))).length := by
    rw [prefixOf_length]; omega
  have h1 := congrArg (fun l => l[2 * i]?) hpre
  rw [List.getElem?_eq_getElem hidx, prefixOf_getElem] at h1
  rw [prefixOf_succ, applyMorph_append] at h1
  have hlen : (applyMorph gRfDec (prefixOf tauWord i)).length = 2 * i := by
    rw [applyMorph_gRfDec_length, prefixOf_length]
  rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self] at h1
  simp only [applyMorph, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    gRfDec_eq_pair, List.getElem?_cons_zero] at h1
  exact Option.some.inj h1

theorem gRfB5_two_mul_add_one (i : ℕ) : gRfB5 (2 * i + 1) = gRfDec1 (tauWord i) := by
  have hpre := gRfB5_prefix_two_mul (i + 1)
  have hidx : 2 * i + 1 < (prefixOf gRfB5 (2 * (i + 1))).length := by
    rw [prefixOf_length]; omega
  have h1 := congrArg (fun l => l[2 * i + 1]?) hpre
  rw [List.getElem?_eq_getElem hidx, prefixOf_getElem] at h1
  rw [prefixOf_succ, applyMorph_append] at h1
  have hlen : (applyMorph gRfDec (prefixOf tauWord i)).length = 2 * i := by
    rw [applyMorph_gRfDec_length, prefixOf_length]
  rw [List.getElem?_append_right (by omega), hlen] at h1
  have hsub : 2 * i + 1 - 2 * i = 1 := by omega
  rw [hsub] at h1
  simp only [applyMorph, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    gRfDec_eq_pair, List.getElem?_cons_succ, List.getElem?_cons_zero] at h1
  exact Option.some.inj h1

/-! ## Section 3: 9-Pair Closure and Telescoping Conjugacy to the Fibonacci Word -/

/-- The exact 9 allowed adjacent pairs in `tauWord`. -/
def validTauPair (x y : Fin 5) : Bool :=
  match x.val, y.val with
  | 0, 1 => true
  | 0, 3 => true
  | 1, 0 => true
  | 1, 2 => true
  | 2, 0 => true
  | 2, 3 => true
  | 3, 2 => true
  | 3, 4 => true
  | 4, 0 => true
  | _, _ => false

def tauFirst (x : Fin 5) : Fin 5 :=
  (tauB5 x)[0]'(List.length_pos_of_ne_nil (tauB5_nonempty x))

def tauLast (x : Fin 5) : Fin 5 :=
  (tauB5 x)[(tauB5 x).length - 1]'(by
    have h := List.length_pos_of_ne_nil (tauB5_nonempty x); omega)

theorem validTauPair_internal (x : Fin 5) (i : ℕ) (hi : i + 1 < (tauB5 x).length) :
    validTauPair ((tauB5 x)[i]'(by omega)) ((tauB5 x)[i + 1]'hi) = true := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl
  · have hi0 : i = 0 := by simp [tauB5] at hi; omega
    subst hi0; rfl
  · simp [tauB5] at hi
  · have hi0 : i = 0 := by simp [tauB5] at hi; omega
    subst hi0; rfl
  · simp [tauB5] at hi
  · have hi0 : i = 0 := by simp [tauB5] at hi; omega
    subst hi0; rfl

theorem validTauPair_boundary (x y : Fin 5) (h : validTauPair x y = true) :
    validTauPair (tauLast x) (tauFirst y) = true := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
  rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl <;>
  first | rfl | contradiction

/-- All adjacent pairs in a list satisfy `validTauPair`. -/
def ValidTauList : List (Fin 5) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => validTauPair x y = true ∧ ValidTauList (y :: rest)

theorem validTauList_append {u v : List (Fin 5)} (hu : ValidTauList u) (hv : ValidTauList v)
    (hcross : ∀ (hu' : u ≠ []) (hv' : v ≠ []),
      validTauPair (u.getLast hu') (v.head hv') = true) :
    ValidTauList (u ++ v) := by
  induction u with
  | nil => simpa using hv
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases v with
      | nil => trivial
      | cons b v' =>
        simp only [List.cons_append, List.nil_append, ValidTauList]
        exact ⟨hcross (by simp) (by simp), hv⟩
    | cons b rest' =>
      simp only [List.cons_append, ValidTauList] at hu ⊢
      refine ⟨hu.1, ih hu.2 ?_⟩
      intro _ hv'
      have hlast : (a :: b :: rest').getLast (by simp) = (b :: rest').getLast (by simp) := rfl
      rw [← hlast]
      exact hcross (by simp) hv'

theorem tauB5_getLast_eq (x : Fin 5) :
    (tauB5 x).getLast (tauB5_nonempty x) = tauLast x := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem tauB5_head_eq (x : Fin 5) :
    (tauB5 x).head (tauB5_nonempty x) = tauFirst x := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem applyMorph_tauB5_head {x : Fin 5} {rest : List (Fin 5)} :
    (applyMorph tauB5 (x :: rest)).head
      (applyMorph_ne_nil tauB5 tauB5_nonempty (by simp)) = tauFirst x := by
  have hne : tauB5 x ≠ [] := tauB5_nonempty x
  cases htx : tauB5 x with
  | nil => exact absurd htx hne
  | cons h t =>
    simp only [applyMorph, List.flatMap_cons, htx, List.cons_append, List.head_cons]
    unfold tauFirst
    simp [htx]

theorem validTauList_applyMorph_tauB5 {w : List (Fin 5)} (hw : ValidTauList w) :
    ValidTauList (applyMorph tauB5 w) := by
  induction w with
  | nil => trivial
  | cons x rest ih =>
    cases rest with
    | nil =>
      simp only [applyMorph, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
        simp [tauB5, ValidTauList, validTauPair]
    | cons y rest' =>
      simp only [ValidTauList] at hw
      simp only [applyMorph, List.flatMap_cons]
      have hx_valid : ValidTauList (tauB5 x) := by
        rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
          simp [tauB5, ValidTauList, validTauPair]
      have hrest_valid : ValidTauList (applyMorph tauB5 (y :: rest')) := ih hw.2
      apply validTauList_append hx_valid hrest_valid
      intro _ _
      rw [tauB5_getLast_eq, applyMorph_tauB5_head]
      exact validTauPair_boundary x y hw.1

theorem validTauList_iter_tauB5 (n : ℕ) : ValidTauList (iterMorph tauB5 n [0]) := by
  induction n with
  | zero => trivial
  | succ n ih => exact validTauList_applyMorph_tauB5 ih

theorem validTauList_getElem {w : List (Fin 5)} (hw : ValidTauList w)
    {i : ℕ} (hi : i + 1 < w.length) :
    validTauPair (w[i]'(by omega)) (w[i + 1]'hi) = true := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases rest with
    | nil => simp at hi
    | cons b rest' =>
      cases i with
      | zero => exact hw.1
      | succ i' =>
        simp only [List.length_cons] at hi
        exact ih hw.2 (by simp only [List.length_cons]; omega)

theorem tauWord_validPair (i : ℕ) :
    validTauPair (tauWord i) (tauWord (i + 1)) = true := by
  let N := i + 2
  have hlen : N < (iterMorph tauB5 N [0]).length :=
    lt_iterMorph_length tauB5 0 tauB5_nonempty tauB5_prolongable N
  have hi1 : i + 1 < (iterMorph tauB5 N [0]).length := by omega
  have h1 := fixedPoint_eq_iterMorph_getElem tauB5 0 tauB5_nonempty tauB5_prolongable N i (by omega)
  have h2 := fixedPoint_eq_iterMorph_getElem tauB5 0 tauB5_nonempty tauB5_prolongable N (i + 1) hi1
  unfold tauWord
  rw [h1, h2]
  exact validTauList_getElem (validTauList_iter_tauB5 N) hi1

/-- The 2-bit complemented first-difference block contributed by adjacent `tauWord` letters `x, y`. -/
def phiPair (x y : Fin 5) : List Bool :=
  [gRfDec0 x == gRfDec1 x, gRfDec1 x == gRfDec0 y]

/-- Chain concatenation of `phiPair` along adjacent pairs of a list. -/
def phiChain : List (Fin 5) → List Bool
  | [] => []
  | [_] => []
  | x :: y :: rest => phiPair x y ++ phiChain (y :: rest)

theorem phiChain_append_cons (u : List (Fin 5)) (y : Fin 5) (v : List (Fin 5)) :
    phiChain (u ++ y :: v) = phiChain (u ++ [y]) ++ phiChain (y :: v) := by
  induction u with
  | nil => simp [phiChain]
  | cons a rest ih =>
    cases rest with
    | nil => simp [phiChain]
    | cons b rest' =>
      simp only [List.cons_append, phiChain, List.append_assoc]
      exact congrArg (phiPair a b ++ ·) ih

/-- Left/right 1-bit conjugacy overhangs between `tauB5` and `fibMorph`. -/
def ovL : Fin 5 → List Bool
  | ⟨1, _⟩ => [false]
  | _ => []

def ovR : Fin 5 → List Bool
  | ⟨2, _⟩ => [true]
  | ⟨4, _⟩ => [true]
  | _ => []

theorem ovL_or_ovR_nil (x : Fin 5) : ovL x = [] ∨ ovR x = [] := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> simp [ovL, ovR]

theorem ovL_len_le_one (x : Fin 5) : (ovL x).length ≤ 1 := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> decide

theorem ovR_len_le_one (x : Fin 5) : (ovR x).length ≤ 1 := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Exact 9-pair one-step conjugacy identity between `tauB5` and `fibMorph`. -/
theorem phiPair_conjugacy_step (x y : Fin 5) (h : validTauPair x y = true) :
    ovL x ++ phiChain (tauB5 x ++ [tauFirst y]) ++ ovR y =
    ovR x ++ applyMorph fibMorph (phiPair x y) ++ ovL y := by
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
  rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl <;>
  first | rfl | contradiction

/-- Telescoping conjugacy identity along any valid chain `x :: mid ++ [z]`. -/
theorem phiChain_telescoping (mid : List (Fin 5)) (x z : Fin 5)
    (hvalid : ValidTauList (x :: mid ++ [z])) :
    ovL x ++ phiChain (applyMorph tauB5 (x :: mid) ++ [tauFirst z]) ++ ovR z =
    ovR x ++ applyMorph fibMorph (phiChain (x :: mid ++ [z])) ++ ovL z := by
  induction mid generalizing x with
  | nil =>
    simp only [applyMorph, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact phiPair_conjugacy_step x z hvalid.1
  | cons y rest ih =>
    simp only [List.cons_append, ValidTauList] at hvalid
    have hstep := phiPair_conjugacy_step x y hvalid.1
    have hih := ih y hvalid.2
    -- Split LHS: applyMorph tauB5 (x :: y :: rest) ++ [tauFirst z]
    -- = tauB5 x ++ (tauFirst y :: tail_of_rest)
    have hhead : ∃ t : List (Fin 5),
        applyMorph tauB5 (y :: rest) ++ [tauFirst z] = tauFirst y :: t := by
      have hne : tauB5 y ≠ [] := tauB5_nonempty y
      cases hty : tauB5 y with
      | nil => exact absurd hty hne
      | cons hd tl =>
        refine ⟨tl ++ applyMorph tauB5 rest ++ [tauFirst z], ?_⟩
        have hhd : hd = tauFirst y := by unfold tauFirst; simp [hty]
        simp [applyMorph, hty, hhd, List.append_assoc]
    rcases hhead with ⟨t, ht⟩
    have hlhs : phiChain (applyMorph tauB5 (x :: y :: rest) ++ [tauFirst z]) =
        phiChain (tauB5 x ++ [tauFirst y]) ++
        phiChain (applyMorph tauB5 (y :: rest) ++ [tauFirst z]) := by
      have happ : applyMorph tauB5 (x :: y :: rest) ++ [tauFirst z] =
          tauB5 x ++ (applyMorph tauB5 (y :: rest) ++ [tauFirst z]) := by
        simp [applyMorph, List.append_assoc]
      rw [happ, ht, phiChain_append_cons]
    have hrhs : applyMorph fibMorph (phiChain (x :: y :: rest ++ [z])) =
        applyMorph fibMorph (phiPair x y) ++
        applyMorph fibMorph (phiChain (y :: rest ++ [z])) := by
      simp only [List.cons_append, phiChain, applyMorph_append]
    rw [hlhs, hrhs]
    rcases ovL_or_ovR_nil y with hLy | hRy
    · -- ovL y = []
      rw [hLy, List.append_nil] at hstep
      rw [hLy, List.nil_append] at hih
      calc
        ovL x ++ (phiChain (tauB5 x ++ [tauFirst y]) ++
            phiChain (applyMorph tauB5 (y :: rest) ++ [tauFirst z])) ++ ovR z
          = (ovL x ++ phiChain (tauB5 x ++ [tauFirst y])) ++
            (phiChain (applyMorph tauB5 (y :: rest) ++ [tauFirst z]) ++ ovR z) := by
            simp [List.append_assoc]
        _ = (ovL x ++ phiChain (tauB5 x ++ [tauFirst y])) ++
            (ovR y ++ applyMorph fibMorph (phiChain (y :: rest ++ [z])) ++ ovL z) := by
            rw [hih]
        _ = (ovL x ++ phiChain (tauB5 x ++ [tauFirst y]) ++ ovR y) ++
            applyMorph fibMorph (phiChain (y :: rest ++ [z])) ++ ovL z := by
            simp [List.append_assoc]
        _ = (ovR x ++ applyMorph fibMorph (phiPair x y)) ++
            applyMorph fibMorph (phiChain (y :: rest ++ [z])) ++ ovL z := by
            rw [hstep]
        _ = ovR x ++ (applyMorph fibMorph (phiPair x y) ++
            applyMorph fibMorph (phiChain (y :: rest ++ [z]))) ++ ovL z := by
            simp [List.append_assoc]
    · -- ovR y = []
      rw [hRy, List.append_nil] at hstep
      rw [hRy, List.nil_append] at hih
      calc
        ovL x ++ (phiChain (tauB5 x ++ [tauFirst y]) ++
            phiChain (applyMorph tauB5 (y :: rest) ++ [tauFirst z])) ++ ovR z
          = (ovL x ++ phiChain (tauB5 x ++ [tauFirst y])) ++
            (phiChain (applyMorph tauB5 (y :: rest) ++ [tauFirst z]) ++ ovR z) := by
            simp [List.append_assoc]
        _ = (ovR x ++ applyMorph fibMorph (phiPair x y) ++ ovL y) ++
            (phiChain (applyMorph tauB5 (y :: rest) ++ [tauFirst z]) ++ ovR z) := by
            rw [hstep]
        _ = ovR x ++ applyMorph fibMorph (phiPair x y) ++
            (ovL y ++ phiChain (applyMorph tauB5 (y :: rest) ++ [tauFirst z]) ++ ovR z) := by
            simp [List.append_assoc]
        _ = ovR x ++ applyMorph fibMorph (phiPair x y) ++
            (applyMorph fibMorph (phiChain (y :: rest ++ [z])) ++ ovL z) := by
            rw [hih]
        _ = ovR x ++ (applyMorph fibMorph (phiPair x y) ++
            applyMorph fibMorph (phiChain (y :: rest ++ [z]))) ++ ovL z := by
            simp [List.append_assoc]

/-- Complemented first-difference sequence of `g_rf(b_5)`: `true` (`1`) iff adjacent bits agree. -/
def diffGRfB5 (k : ℕ) : Bool :=
  gRfB5 k == gRfB5 (k + 1)

theorem phiChain_prefixOf_tauWord (m : ℕ) :
    phiChain (prefixOf tauWord (m + 1)) = prefixOf diffGRfB5 (2 * m) := by
  induction m with
  | zero =>
    simp [prefixOf, phiChain]
  | succ m ih =>
    have hpre : prefixOf tauWord (m + 2) =
        prefixOf tauWord (m + 1) ++ [tauWord (m + 1)] := prefixOf_succ tauWord (m + 1)
    have hsplit : prefixOf tauWord (m + 1) = prefixOf tauWord m ++ [tauWord m] :=
      prefixOf_succ tauWord m
    rw [hpre, hsplit, List.append_assoc, List.singleton_append,
        phiChain_append_cons, ← hsplit, ih]
    have hdiff : prefixOf diffGRfB5 (2 * (m + 1)) =
        prefixOf diffGRfB5 (2 * m) ++ [diffGRfB5 (2 * m), diffGRfB5 (2 * m + 1)] := by
      have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [h1, prefixOf_succ, prefixOf_succ, List.append_assoc]
      rfl
    rw [hdiff]
    congr 1
    simp only [phiChain, List.append_nil, phiPair, diffGRfB5]
    have h0 := gRfB5_two_mul m
    have h1 := gRfB5_two_mul_add_one m
    have h2 := gRfB5_two_mul (m + 1)
    have h2' : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    rw [h0, h1, h2', h2]

theorem validTauList_prefixOf_tauWord (n : ℕ) : ValidTauList (prefixOf tauWord n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    cases n with
    | zero =>
      simp [prefixOf, ValidTauList]
    | succ m =>
      rw [prefixOf_succ]
      apply validTauList_append ih (by trivial)
      intro hu' _
      have hlast : (prefixOf tauWord (m + 1)).getLast hu' = tauWord m := by
        rw [List.getLast_eq_getElem]
        simp [prefixOf_length, prefixOf_getElem]
      rw [hlast]
      exact tauWord_validPair m

/-- Block start in `tauWord` under `tauB5`. -/
def tauStart (m : ℕ) : ℕ :=
  (applyMorph tauB5 (prefixOf tauWord m)).length

theorem tauStart_succ (m : ℕ) :
    tauStart (m + 1) = tauStart m + (tauB5 (tauWord m)).length := by
  unfold tauStart
  rw [prefixOf_succ, applyMorph_append, List.length_append]
  simp [applyMorph]

theorem tauStart_strictMono : StrictMono tauStart := by
  refine strictMono_nat_of_lt_succ fun m => ?_
  rw [tauStart_succ]
  have h := List.length_pos_of_ne_nil (tauB5_nonempty (tauWord m))
  omega

theorem tauWord_prefix_tauStart (m : ℕ) :
    prefixOf tauWord (tauStart m) = applyMorph tauB5 (prefixOf tauWord m) := by
  have hp := fixedPoint_applyMorph_prefix_isPrefix tauB5 0 tauB5_nonempty tauB5_prolongable 1 m
  have heq : (fun a => iterMorph tauB5 1 [a]) = tauB5 := by
    funext a; simp [iterMorph, applyMorph]
  rw [heq] at hp
  exact hp.symm

theorem tauWord_at_tauStart (m : ℕ) : tauWord (tauStart m) = tauFirst (tauWord m) := by
  have hpre := tauWord_prefix_tauStart (m + 1)
  have hlt : tauStart m < (prefixOf tauWord (tauStart (m + 1))).length := by
    rw [prefixOf_length]
    exact tauStart_strictMono (Nat.lt_succ_self m)
  have h1 := congrArg (fun l => l[tauStart m]?) hpre
  rw [List.getElem?_eq_getElem hlt, prefixOf_getElem, prefixOf_succ, applyMorph_append] at h1
  have hlen : (applyMorph tauB5 (prefixOf tauWord m)).length = tauStart m := rfl
  rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self] at h1
  have hne : tauB5 (tauWord m) ≠ [] := tauB5_nonempty (tauWord m)
  cases htx : tauB5 (tauWord m) with
  | nil => exact absurd htx hne
  | cons hd tl =>
    simp only [applyMorph, List.flatMap_cons, List.flatMap_nil, List.append_nil, htx,
      List.getElem?_cons_zero] at h1
    have hhd : hd = tauFirst (tauWord m) := by unfold tauFirst; simp [htx]
    rw [hhd] at h1
    exact Option.some.inj h1

theorem tauWord_zero : tauWord 0 = 0 := by
  have h := fixedPoint_eq_iterMorph_getElem tauB5 0 tauB5_nonempty tauB5_prolongable 1 0 (by decide)
  exact h

/-- Exact prefix conjugacy for `diffGRfB5`: for every `m ≥ 1`,
`prefixOf diffGRfB5 (2 * tauStart m) ++ ovR (tauWord m) =
 applyMorph fibMorph (prefixOf diffGRfB5 (2 * m)) ++ ovL (tauWord m)`. -/
theorem diffGRfB5_conjugacy (m : ℕ) :
    prefixOf diffGRfB5 (2 * tauStart m) ++ ovR (tauWord m) =
    applyMorph fibMorph (prefixOf diffGRfB5 (2 * m)) ++ ovL (tauWord m) := by
  cases m with
  | zero =>
    simp [tauStart, tauWord_zero, ovL, ovR, prefixOf, applyMorph]
  | succ m =>
    -- Express prefixOf tauWord (m + 2) as 0 :: mid ++ [tauWord (m + 1)]
    have hpre_eq : prefixOf tauWord (m + 2) =
        0 :: (prefixOf tauWord (m + 1)).tail ++ [tauWord (m + 1)] := by
      have h0 : prefixOf tauWord (m + 1) = 0 :: (prefixOf tauWord (m + 1)).tail := by
        cases h : prefixOf tauWord (m + 1) with
        | nil =>
          have hlen := prefixOf_length tauWord (m + 1)
          rw [h] at hlen; simp at hlen
        | cons a t =>
          have ha : a = 0 := by
            have hget := congrArg (fun l => l[0]?) h
            rw [List.getElem?_eq_getElem (by rw [prefixOf_length]; omega),
                prefixOf_getElem] at hget
            simp only [List.getElem?_cons_zero] at hget
            rw [tauWord_zero] at hget
            exact (Option.some.inj hget).symm
          rw [ha]; rfl
      rw [prefixOf_succ, h0]; rfl
    have hvalid : ValidTauList (0 :: (prefixOf tauWord (m + 1)).tail ++ [tauWord (m + 1)]) := by
      rw [← hpre_eq]
      exact validTauList_prefixOf_tauWord (m + 2)
    have htel := phiChain_telescoping (prefixOf tauWord (m + 1)).tail 0 (tauWord (m + 1)) hvalid
    simp only [ovL, ovR, List.nil_append] at htel
    have h0' : 0 :: (prefixOf tauWord (m + 1)).tail = prefixOf tauWord (m + 1) := by
      cases h : prefixOf tauWord (m + 1) with
      | nil =>
        have hlen := prefixOf_length tauWord (m + 1)
        rw [h] at hlen; simp at hlen
      | cons a t =>
        have ha : a = 0 := by
          have hget := congrArg (fun l => l[0]?) h
          rw [List.getElem?_eq_getElem (by rw [prefixOf_length]; omega),
              prefixOf_getElem] at hget
          simp only [List.getElem?_cons_zero] at hget
          rw [tauWord_zero] at hget
          exact (Option.some.inj hget).symm
        rw [ha]; rfl
    rw [← hpre_eq, h0', phiChain_prefixOf_tauWord (m + 1),
        ← tauWord_prefix_tauStart (m + 1), ← tauWord_at_tauStart (m + 1),
        ← prefixOf_succ, phiChain_prefixOf_tauWord (tauStart (m + 1))] at htel
    exact htel

theorem applyMorph_fibMorph_prefix_diffGRfB5 (m : ℕ) :
    applyMorph fibMorph (prefixOf diffGRfB5 (2 * m)) <+:
    prefixOf diffGRfB5 (2 * tauStart (m + 1)) := by
  have h1 := diffGRfB5_conjugacy m
  have h2 := diffGRfB5_conjugacy (m + 1)
  have hlen1 : (applyMorph fibMorph (prefixOf diffGRfB5 (2 * m))).length ≤ 2 * tauStart m + 1 := by
    have hl := congrArg List.length h1
    simp only [List.length_append, prefixOf_length] at hl
    have hr := ovR_len_le_one (tauWord m)
    omega
  have hst : tauStart m + 1 ≤ tauStart (m + 1) := tauStart_strictMono (Nat.lt_succ_self m)
  have hlen_le : (applyMorph fibMorph (prefixOf diffGRfB5 (2 * m))).length ≤
      (prefixOf diffGRfB5 (2 * tauStart (m + 1))).length := by
    rw [prefixOf_length]; omega
  have hp_sub : applyMorph fibMorph (prefixOf diffGRfB5 (2 * m)) <+:
      applyMorph fibMorph (prefixOf diffGRfB5 (2 * (m + 1))) ++ ovL (tauWord (m + 1)) := by
    have hpre : prefixOf diffGRfB5 (2 * m) <+: prefixOf diffGRfB5 (2 * (m + 1)) :=
      prefixOf_prefix_of_le diffGRfB5 (by omega)
    exact (applyMorph_prefix_of_prefix fibMorph hpre).trans (List.prefix_append _ _)
  rw [← h2] at hp_sub
  -- Both u := applyMorph fibMorph (prefixOf diffGRfB5 (2 * m)) and v := prefixOf diffGRfB5 (2 * tauStart (m + 1))
  -- are prefixes of v ++ ovR (tauWord (m + 1)), with |u| ≤ |v|, hence u <+: v!
  rcases hp_sub with ⟨rest, hrest⟩
  have htake := congrArg (List.take (applyMorph fibMorph (prefixOf diffGRfB5 (2 * m))).length) hrest
  rw [List.take_left, List.take_append_of_le_length hlen_le] at htake
  rw [htake]
  exact List.take_prefix _ _

theorem iterMorph_fibMorph_prefix_diffGRfB5 (r : ℕ) :
    ∃ L : ℕ, iterMorph fibMorph r [false] = prefixOf diffGRfB5 L := by
  induction r with
  | zero =>
    refine ⟨1, ?_⟩
    simp only [iterMorph, prefixOf, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, diffGRfB5]
    have h0 : gRfB5 0 = false := by
      have := gRfB5_two_mul 0; simp only [Nat.mul_zero, tauWord_zero] at this; exact this
    have h1 : gRfB5 1 = true := by
      have := gRfB5_two_mul_add_one 0; simp only [Nat.mul_zero, zero_add, tauWord_zero] at this; exact this
    rw [h0, h1]; rfl
  | succ r ih =>
    rcases ih with ⟨L, hL⟩
    have hpre : prefixOf diffGRfB5 L <+: prefixOf diffGRfB5 (2 * L) :=
      prefixOf_prefix_of_le diffGRfB5 (by omega)
    have hstep : applyMorph fibMorph (prefixOf diffGRfB5 L) <+:
        prefixOf diffGRfB5 (2 * tauStart (L + 1)) :=
      (applyMorph_prefix_of_prefix fibMorph hpre).trans
        (applyMorph_fibMorph_prefix_diffGRfB5 L)
    refine ⟨(applyMorph fibMorph (prefixOf diffGRfB5 L)).length, ?_⟩
    simp only [iterMorph, hL]
    apply List.ext_getElem
    · simp [prefixOf_length]
    · intro i hi1 hi2
      rw [prefixOf_getElem]
      have hget := getElem_eq_of_prefix hstep hi1 (lt_of_lt_of_le hi1 (List.IsPrefix.length_le hstep))
      rw [prefixOf_getElem] at hget
      exact hget

/-- **Exact Complemented First-Difference Theorem (`gRfB5_complDiff_eq_fibWord`)**:
For every `k : ℕ`, adjacent bits of `g_rf(b_5)` agree iff `fibWord k = true` (`1`). -/
theorem gRfB5_complDiff_eq_fibWord (k : ℕ) :
    (gRfB5 k == gRfB5 (k + 1)) = fibWord k := by
  let N := k + 1
  have hlt : k < (iterMorph fibMorph N [false]).length := by
    have h := lt_iterMorph_length fibMorph false fibMorph_nonempty fibMorph_prolongable N
    omega
  rcases iterMorph_fibMorph_prefix_diffGRfB5 N with ⟨L, hL⟩
  have hfib := fixedPoint_eq_iterMorph_getElem fibMorph false fibMorph_nonempty fibMorph_prolongable N k hlt
  have hget := congrArg (fun l => l[k]?) hL
  have hkL : k < L := by
    have hl := congrArg List.length hL
    rw [prefixOf_length] at hl
    omega
  rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem (by rw [prefixOf_length]; exact hkL),
      prefixOf_getElem] at hget
  unfold fibWord
  rw [hfib]
  exact (Option.some.inj hget).symm

/-! ## Section 4: Du–Mousavi–Schaeffer–Shallit's Rote–Fibonacci Word & Pointwise Identity -/

/-- The Rote–Fibonacci word `r = 001001101101100100...`: `r[0] = 0` and
`r[k+1] = r[k] ⊕ (1 - fibWord[k+1])`, the first-difference characterization of
Du–Mousavi–Schaeffer–Shallit (`arXiv:1406.0670` (2014), Corollary 36) and
Du–Mousavi–Rowland–Schaeffer–Shallit (*TCS* 657 (2017), Corollary 2). -/
def roteFib : ℕ → Bool
  | 0 => false
  | k + 1 => xor (roteFib k) (!(fibWord (k + 1)))

theorem roteFib_zero : roteFib 0 = false := rfl

theorem roteFib_complDiff (k : ℕ) :
    (roteFib k == roteFib (k + 1)) = fibWord (k + 1) := by
  simp only [roteFib]
  cases roteFib k <;> cases fibWord (k + 1) <;> rfl

/-- Exact 2-state transducer `T` of Du–Mousavi–Schaeffer–Shallit (`arXiv:1406.0670`, Fig. 18 &
Theorem 35(0)): from state `false` (`q_0`), `0 ↦ 00`, `1 ↦ 0` and flips to `true` (`q_1`);
from state `true` (`q_1`), `0 ↦ 11`, `1 ↦ 1` and flips to `false` (`q_0`). -/
def roteTransStep (st : Bool) (c : Bool) : List Bool × Bool :=
  match st, c with
  | false, false => ([false, false], true)
  | false, true  => ([false], true)
  | true,  false => ([true, true], false)
  | true,  true  => ([true], false)

def roteTransAux : Bool → List Bool → List Bool
  | _, [] => []
  | st, c :: rest =>
    let p := roteTransStep st c
    p.1 ++ roteTransAux p.2 rest

theorem roteTransAux_length_ge (st : Bool) (w : List Bool) :
    w.length ≤ (roteTransAux st w).length := by
  induction w generalizing st with
  | nil => simp [roteTransAux]
  | cons c rest ih =>
    simp only [roteTransAux, List.length_append, List.length_cons]
    have h1 : 1 ≤ (roteTransStep st c).1.length := by
      cases st <;> cases c <;> decide
    have h2 := ih (roteTransStep st c).2
    omega

theorem roteTransAux_prefix_of_prefix (st : Bool) {u v : List Bool} (hp : u <+: v) :
    roteTransAux st u <+: roteTransAux st v := by
  induction u generalizing st v with
  | nil => exact List.nil_prefix
  | cons a u' ih =>
    cases v with
    | nil => simp at hp
    | cons b v' =>
      rcases List.cons_prefix_cons.mp hp with ⟨rfl, hp'⟩
      simp only [roteTransAux]
      exact List.prefix_append_right_inj _ |>.mpr (ih (roteTransStep st a).2 hp')

/-- Output of the Du–Mousavi–Schaeffer–Shallit transducer `T_0` on `fibWord`. -/
def roteFibTransducer (k : ℕ) : Bool :=
  (roteTransAux false (prefixOf fibWord (k + 1)))[k]'(by
    have h := roteTransAux_length_ge false (prefixOf fibWord (k + 1))
    rw [prefixOf_length] at h; omega)

/-- Conjugate Fibonacci morphism `0 ↦ 10, 1 ↦ 0`. -/
def fibMorphConj : Bool → List Bool
  | false => [true, false]
  | true  => [false]

theorem false_cons_fibMorphConj (w : List Bool) :
    false :: applyMorph fibMorphConj w = applyMorph fibMorph w ++ [false] := by
  induction w with
  | nil => rfl
  | cons c rest ih =>
    cases c
    · simp only [applyMorph, List.flatMap_cons, fibMorphConj, fibMorph, List.cons_append]
      change false :: true :: (false :: applyMorph fibMorphConj rest) =
        false :: true :: (applyMorph fibMorph rest ++ [false])
      rw [ih]
    · simp only [applyMorph, List.flatMap_cons, fibMorphConj, fibMorph, List.cons_append]
      change false :: (false :: applyMorph fibMorphConj rest) =
        false :: (applyMorph fibMorph rest ++ [false])
      rw [ih]

/-- Complemented first-difference list of a binary word. -/
def complDiff : List Bool → List Bool
  | [] => []
  | [_] => []
  | a :: b :: rest => (a == b) :: complDiff (b :: rest)

theorem complDiff_length (w : List Bool) :
    (complDiff w).length = w.length - 1 := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      simp only [complDiff, List.length_cons] at ih ⊢
      omega

theorem complDiff_transAux_snoc (st : Bool) (w : List Bool) :
    complDiff (roteTransAux st w ++ [xor st (w.length % 2 == 1)]) =
    applyMorph fibMorphConj w := by
  induction w generalizing st with
  | nil =>
    simp [roteTransAux, complDiff, applyMorph]
  | cons c rest ih =>
    have hparity : xor (roteTransStep st c).2 (rest.length % 2 == 1) =
        xor st ((c :: rest).length % 2 == 1) := by
      have hst : (roteTransStep st c).2 = !st := by cases st <;> cases c <;> rfl
      rw [hst, List.length_cons]
      have hmod : ((rest.length + 1) % 2 == 1) = !(rest.length % 2 == 1) := by
        cases h : rest.length % 2 with
        | zero => simp [Nat.add_mod, h]
        | succ m =>
          have hm : m = 0 := by omega
          subst hm; simp [Nat.add_mod, h]
      rw [hmod]
      cases st <;> cases (rest.length % 2 == 1) <;> rfl
    have hhead : ∃ tl : List Bool,
        roteTransAux (roteTransStep st c).2 rest ++ [xor st ((c :: rest).length % 2 == 1)] =
        (!st) :: tl := by
      rw [← hparity]
      have hst : (roteTransStep st c).2 = !st := by cases st <;> cases c <;> rfl
      rw [hst]
      cases rest with
      | nil => exact ⟨[], by simp [roteTransAux]⟩
      | cons d rest' =>
        cases st <;> cases d <;> simp [roteTransAux, roteTransStep]
    rcases hhead with ⟨tl, htl⟩
    simp only [roteTransAux, List.append_assoc, htl]
    have hih := ih (roteTransStep st c).2
    rw [hparity, htl] at hih
    cases st <;> cases c <;>
    · simp only [Bool.not_false, Bool.not_true] at hih
      simp only [roteTransStep, complDiff, List.cons_append, List.nil_append]
      change _ = fibMorphConj _ ++ applyMorph fibMorphConj rest
      rw [← hih]
      rfl

theorem roteTransAux_head_false (w : List Bool) (hw : w ≠ []) :
    (roteTransAux false w)[0]'(by
      have h := roteTransAux_length_ge false w
      have hpos := List.length_pos_of_ne_nil hw; omega) = false := by
  cases w with
  | nil => exact absurd rfl hw
  | cons c rest =>
    cases c <;> simp [roteTransAux, roteTransStep]

theorem complDiff_getElem (w : List Bool) {i : ℕ} (hi : i + 1 < w.length) :
    (complDiff w)[i]'(by rw [complDiff_length]; omega) =
    (w[i]'(by omega) == w[i + 1]'hi) := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases rest with
    | nil => simp at hi
    | cons b rest' =>
      cases i with
      | zero => rfl
      | succ i' =>
        simp only [List.length_cons] at hi
        exact ih (by simp only [List.length_cons]; omega)

/-- **Exact Transducer Equivalence (`roteFibTransducer_eq_roteFib`)**:
The 2-state transducer `T_0` on `fibWord` (Du–Mousavi–Schaeffer–Shallit (2014), Figure 18 and
Theorem 35(0); Du–Mousavi–Rowland–Schaeffer–Shallit (2017), Figure 1 and Theorem 1(a))
equals `roteFib` letter for letter at every index `k : ℕ`. -/
theorem roteFibTransducer_eq_roteFib (k : ℕ) :
    roteFibTransducer k = roteFib k := by
  induction k with
  | zero =>
    unfold roteFibTransducer
    have hne : prefixOf fibWord 1 ≠ [] := by simp [prefixOf]
    exact roteTransAux_head_false (prefixOf fibWord 1) hne
  | succ k ih =>
    -- Compare roteFibTransducer k and roteFibTransducer (k + 1) via complDiff_transAux_snoc!
    let M := k + 2
    let w := prefixOf fibWord M
    have hlen : k + 1 < (roteTransAux false w).length := by
      have h := roteTransAux_length_ge false w
      rw [prefixOf_length] at h; omega
    have htk : roteFibTransducer k = (roteTransAux false w)[k]'(by omega) := by
      unfold roteFibTransducer
      have hp := roteTransAux_prefix_of_prefix false (prefixOf_prefix_of_le fibWord (m := k + 1) (n := M) (by omega))
      have hlt : k < (roteTransAux false (prefixOf fibWord (k + 1))).length := by
        have h := roteTransAux_length_ge false (prefixOf fibWord (k + 1))
        rw [prefixOf_length] at h; omega
      exact getElem_eq_of_prefix hp hlt (by dsimp only [w] at hlen; omega)
    have htk1 : roteFibTransducer (k + 1) = (roteTransAux false w)[k + 1]'hlen := rfl
    -- Pull k-th element of complDiff (roteTransAux false w ++ [bit]) = applyMorph fibMorphConj w
    have hcd := complDiff_transAux_snoc false w
    have hlen_cd : k < (applyMorph fibMorphConj w).length := by
      have hcl := congrArg List.length hcd
      rw [complDiff_length, List.length_append, List.length_singleton] at hcl
      omega
    have hcd_k := congrArg (fun l => l[k]?) hcd
    rw [List.getElem?_eq_getElem (by rw [complDiff_length, List.length_append, List.length_singleton]; omega),
        complDiff_getElem _ (by rw [List.length_append, List.length_singleton]; omega),
        List.getElem?_eq_getElem hlen_cd] at hcd_k
    have hcd_eq : ((roteTransAux false w ++ [xor false (w.length % 2 == 1)])[k]'(by
        rw [List.length_append, List.length_singleton]; omega) ==
      (roteTransAux false w ++ [xor false (w.length % 2 == 1)])[k + 1]'(by
        rw [List.length_append, List.length_singleton]; omega)) =
      (applyMorph fibMorphConj w)[k]'hlen_cd := Option.some.inj hcd_k
    rw [List.getElem_append_left (by omega), List.getElem_append_left hlen] at hcd_eq
    -- Connect (applyMorph fibMorphConj w)[k] to fibWord (k + 1) via false_cons_fibMorphConj!
    have hconj := false_cons_fibMorphConj w
    have hpre_fib : applyMorph fibMorph w = prefixOf fibWord (applyMorph fibMorph w).length := by
      have hp := fixedPoint_applyMorph_prefix_isPrefix fibMorph false fibMorph_nonempty fibMorph_prolongable 1 M
      have heq : (fun a => iterMorph fibMorph 1 [a]) = fibMorph := by
        funext a; cases a <;> rfl
      rw [heq] at hp
      exact hp
    have hfib_len : k + 1 < (applyMorph fibMorph w).length := by
      have hge := applyMorph_length_ge fibMorph fibMorph_nonempty w
      rw [prefixOf_length] at hge; omega
    have hfib_k1 : (applyMorph fibMorphConj w)[k]'hlen_cd = fibWord (k + 1) := by
      have hget := congrArg (fun l => l[k + 1]?) hconj
      simp only [List.getElem?_cons_succ] at hget
      rw [List.getElem?_eq_getElem hlen_cd, List.getElem?_append_left hfib_len,
          List.getElem?_eq_getElem hfib_len] at hget
      have h1 : (applyMorph fibMorphConj w)[k]'hlen_cd = (applyMorph fibMorph w)[k + 1]'hfib_len :=
        Option.some.inj hget
      have hget2 := congrArg (fun l => l[k + 1]?) hpre_fib
      rw [List.getElem?_eq_getElem hfib_len,
          List.getElem?_eq_getElem (by rw [prefixOf_length]; exact hfib_len),
          prefixOf_getElem] at hget2
      rw [h1, Option.some.inj hget2]
    rw [hfib_k1, ← htk, ← htk1, ih] at hcd_eq
    simp only [roteFib]
    cases h1 : roteFib k <;> cases h2 : roteFibTransducer (k + 1) <;>
      cases h3 : fibWord (k + 1) <;>
    · rw [h1, h2, h3] at hcd_eq
      first | rfl | exact Bool.noConfusion hcd_eq

/-- First bit of `g_rf(b_5)` is `0` (`false`). -/
theorem gRfB5_zero : gRfB5 0 = false := by
  have h := gRfB5_two_mul 0
  simp only [Nat.mul_zero, tauWord_zero] at h
  exact h

/-- **Exact Pointwise Identity (`gRfB5_succ_eq_not_roteFib`)**:
For every `k : ℕ`, `g_rf(b_5)[k + 1] = !(roteFib k)`. Together with `gRfB5 0 = false`, this proves
`g_rf(b_5) = 0 · complement(r)` identically letter for letter. -/
theorem gRfB5_succ_eq_not_roteFib (k : ℕ) :
    gRfB5 (k + 1) = !(roteFib k) := by
  induction k with
  | zero =>
    have h1 := gRfB5_two_mul_add_one 0
    simp only [Nat.mul_zero, zero_add, tauWord_zero] at h1
    rw [h1]; rfl
  | succ k ih =>
    have hdiff := gRfB5_complDiff_eq_fibWord (k + 1)
    rw [ih] at hdiff
    simp only [roteFib]
    cases h1 : roteFib k <;> cases h2 : gRfB5 (k + 2) <;> cases h3 : fibWord (k + 1) <;>
      simp_all

/-! ## Section 5: Factor-Set Equivalence, Complement Invariance, and Exact Complexity `2n` -/

/-- Count of `false` (`0`) bits in a binary word. -/
def countFalse (w : List Bool) : ℕ :=
  w.count false

theorem countFalse_append (u v : List Bool) :
    countFalse (u ++ v) = countFalse u + countFalse v := by
  simp [countFalse, List.count_append]

/-- Recurrence of Fibonacci iterate words `X_{n+2} = X_{n+1} ++ X_n`. -/
theorem fibIter_add_two (n : ℕ) :
    iterMorph fibMorph (n + 2) [false] =
    iterMorph fibMorph (n + 1) [false] ++ iterMorph fibMorph n [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change applyMorph fibMorph (iterMorph fibMorph (n + 2) [false]) =
      applyMorph fibMorph (iterMorph fibMorph (n + 1) [false]) ++
      applyMorph fibMorph (iterMorph fibMorph n [false])
    rw [ih, applyMorph_append]

theorem fibIter_countFalse_add_two (n : ℕ) :
    countFalse (iterMorph fibMorph (n + 2) [false]) =
    countFalse (iterMorph fibMorph (n + 1) [false]) +
    countFalse (iterMorph fibMorph n [false]) := by
  rw [fibIter_add_two, countFalse_append]

/-- Consecutive Fibonacci iterate `0`-counts are never both even. -/
theorem fibIter_countFalse_not_both_even (n : ℕ) :
    countFalse (iterMorph fibMorph n [false]) % 2 = 1 ∨
    countFalse (iterMorph fibMorph (n + 1) [false]) % 2 = 1 := by
  induction n with
  | zero => left; decide
  | succ n ih =>
    rcases ih with h0 | h1
    · by_cases h1 : countFalse (iterMorph fibMorph (n + 1) [false]) % 2 = 1
      · left; exact h1
      · right
        rw [fibIter_countFalse_add_two]
        omega
    · left; exact h1

/-- Among three consecutive Fibonacci iterate `0`-counts `c(n), c(n+1), c(n+2)`, both parities occur. -/
theorem fibIter_countFalse_both_parities (n : ℕ) (p : Bool) :
    ∃ r ∈ ([0, 1, 2] : List ℕ),
      (countFalse (iterMorph fibMorph (n + r) [false]) % 2 == 1) = p := by
  have h12 := fibIter_countFalse_not_both_even n
  have hrec := fibIter_countFalse_add_two n
  set a := countFalse (iterMorph fibMorph n [false])
  set b := countFalse (iterMorph fibMorph (n + 1) [false])
  set c := countFalse (iterMorph fibMorph (n + 2) [false])
  have ha : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
  have hb : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  cases p
  · rcases ha with ha0 | ha1
    · refine ⟨0, by simp, ?_⟩
      change (a % 2 == 1) = false
      simp [ha0]
    · rcases hb with hb0 | hb1
      · refine ⟨1, by simp, ?_⟩
        change (b % 2 == 1) = false
        simp [hb0]
      · refine ⟨2, by simp, ?_⟩
        change (c % 2 == 1) = false
        have hc0 : c % 2 = 0 := by omega
        simp [hc0]
  · rcases h12 with ha1 | hb1
    · refine ⟨0, by simp, ?_⟩
      change (a % 2 == 1) = true
      simp [ha1]
    · refine ⟨1, by simp, ?_⟩
      change (b % 2 == 1) = true
      simp [hb1]

/-- Parity formula for `roteFib`: `roteFib k` is the parity of `countFalse` on `fibWord[1..k+1)`. -/
theorem roteFib_eq_parity_countFalse (k : ℕ) :
    roteFib k = ((countFalse (prefixOf fibWord (k + 1)) - 1) % 2 == 1) := by
  induction k with
  | zero =>
    have h0 : fibWord 0 = false :=
      fixedPoint_eq_iterMorph_getElem fibMorph false fibMorph_nonempty fibMorph_prolongable 1 0 (by decide)
    simp [roteFib, prefixOf, countFalse, h0]
  | succ k ih =>
    have hpos : 1 ≤ countFalse (prefixOf fibWord (k + 1)) := by
      have h0 : fibWord 0 = false :=
        fixedPoint_eq_iterMorph_getElem fibMorph false fibMorph_nonempty fibMorph_prolongable 1 0 (by decide)
      have hpre : prefixOf fibWord (k + 1) = false :: (prefixOf fibWord (k + 1)).tail := by
        cases h : prefixOf fibWord (k + 1) with
        | nil =>
          have hl := prefixOf_length fibWord (k + 1); rw [h] at hl; simp at hl
        | cons a t =>
          have ha : a = false := by
            have hg := congrArg (fun l => l[0]?) h
            rw [List.getElem?_eq_getElem (by rw [prefixOf_length]; omega),
                prefixOf_getElem, h0] at hg
            simp only [List.getElem?_cons_zero] at hg
            exact (Option.some.inj hg).symm
          rw [ha]; rfl
      rw [hpre]; simp [countFalse]
    change xor (roteFib k) (!(fibWord (k + 1))) =
      ((countFalse (prefixOf fibWord (k + 2)) - 1) % 2 == 1)
    rw [ih, prefixOf_succ fibWord (k + 1), countFalse_append]
    set c := countFalse (prefixOf fibWord (k + 1))
    cases h : fibWord (k + 1)
    · have hc : countFalse [false] = 1 := rfl
      rw [hc]
      have hsub : c + 1 - 1 = (c - 1) + 1 := by omega
      rw [hsub]
      cases hm : (c - 1) % 2 with
      | zero => simp [Nat.add_mod, hm]
      | succ m =>
        have hm0 : m = 0 := by omega
        subst hm0; simp [Nat.add_mod, hm]
    · have hc : countFalse [true] = 0 := rfl
      rw [hc, Nat.add_zero]
      cases ((c - 1) % 2 == 1) <;> rfl

/-- Occurrence of `X_N = iterMorph fibMorph N [false]` inside `fibWord` at position `|X_{N+1+r}| ≥ 1`
for every `r ∈ {0, 1, 2}`. -/
theorem fibIter_occurs_at_shift (N r : ℕ) :
    let pos := (iterMorph fibMorph (N + 1 + r) [false]).length
    1 ≤ pos ∧
    ∀ j (hj : j < (iterMorph fibMorph N [false]).length),
      fibWord (pos + j) = (iterMorph fibMorph N [false])[j]'hj := by
  intro pos
  have hpos1 : 1 ≤ pos := by
    have h := lt_iterMorph_length fibMorph false fibMorph_nonempty fibMorph_prolongable (N + 1 + r)
    omega
  refine ⟨hpos1, fun j hj => ?_⟩
  have hpre_sub : iterMorph fibMorph N [false] <+: iterMorph fibMorph (N + r) [false] :=
    iterMorph_prefix_le fibMorph false fibMorph_prolongable (by omega)
  have hcat : iterMorph fibMorph (N + 1 + r) [false] ++ iterMorph fibMorph N [false] <+:
      iterMorph fibMorph (N + 2 + r) [false] := by
    have h2 : N + 2 + r = (N + r) + 2 := by omega
    have h1 : N + 1 + r = (N + r) + 1 := by omega
    rw [h2, fibIter_add_two, ← h1]
    exact List.prefix_append_right_inj _ |>.mpr hpre_sub
  have hj_cat : pos + j < (iterMorph fibMorph (N + 1 + r) [false] ++
      iterMorph fibMorph N [false]).length := by
    rw [List.length_append]; omega
  have hj_big : pos + j < (iterMorph fibMorph (N + 2 + r) [false]).length :=
    lt_of_lt_of_le hj_cat (List.IsPrefix.length_le hcat)
  have hfib := fixedPoint_eq_iterMorph_getElem fibMorph false fibMorph_nonempty fibMorph_prolongable
    (N + 2 + r) (pos + j) hj_big
  have hget := getElem_eq_of_prefix hcat hj_cat hj_big
  unfold fibWord
  rw [hfib, ← hget, List.getElem_append_right (by omega)]
  have hsub : pos + j - pos = j := by omega
  congr 1

/-- Every factor `d` of `fibWord` occurs at a position `q ≥ 1` where `roteFib (q - 1)` takes ANY
prescribed target bit `b : Bool`. -/
theorem fibWord_factor_both_roteFib_starts {d : List Bool} (hd : IsFactorInf d fibWord)
    (b : Bool) :
    ∃ q : ℕ, 1 ≤ q ∧ roteFib (q - 1) = b ∧
      ∀ j (hj : j < d.length), fibWord (q + j) = d[j]'hj := by
  rcases hd with ⟨p, hp⟩
  -- Pick N so that p + d.length < |X_N|
  let N := p + d.length + 1
  have hlenN : p + d.length < (iterMorph fibMorph N [false]).length := by
    have h := lt_iterMorph_length fibMorph false fibMorph_nonempty fibMorph_prolongable N
    omega
  -- Inside X_N, d occurs at offset p!
  have hd_in_XN : ∀ j (hj : j < d.length),
      (iterMorph fibMorph N [false])[p + j]'(by omega) = d[j]'hj := by
    intro j hj
    have hfib := fixedPoint_eq_iterMorph_getElem fibMorph false fibMorph_nonempty fibMorph_prolongable
      N (p + j) (by omega)
    rw [← hfib]
    exact hp j hj
  -- Compute parity of countFalse on fibWord[0..p)
  let cP := countFalse (prefixOf fibWord p)
  -- We want ((countFalse (prefixOf fibWord (pos + p)) - 1) % 2 == 1) = b
  -- Note prefixOf fibWord (pos + p) = X_{N+1+r} ++ prefixOf fibWord p (since X_N starts with prefixOf fibWord p!)
  -- So countFalse (prefixOf fibWord (pos + p)) = countFalse X_{N+1+r} + cP!
  let target : Bool := xor b (cP % 2 == 0)
  rcases fibIter_countFalse_both_parities (N + 1) target with ⟨r, hr_mem, hr_par⟩
  have hshift := fibIter_occurs_at_shift N r
  let pos := (iterMorph fibMorph (N + 1 + r) [false]).length
  have hpos1 : 1 ≤ pos := hshift.1
  have hpos_p_ge : 1 ≤ pos + p := by omega
  refine ⟨pos + p, hpos_p_ge, ?_, ?_⟩
  · -- Show roteFib (pos + p - 1) = b
    rw [roteFib_eq_parity_countFalse]
    have hidx_eq : pos + p - 1 + 1 = pos + p := by omega
    rw [hidx_eq]
    have hpre_split : prefixOf fibWord (pos + p) =
        iterMorph fibMorph (N + 1 + r) [false] ++ prefixOf fibWord p := by
      apply List.ext_getElem
      · rw [prefixOf_length, List.length_append, prefixOf_length]
      · intro i hi1 hi2
        rw [prefixOf_getElem]
        by_cases hlt : i < pos
        · rw [List.getElem_append_left hlt]
          exact fixedPoint_eq_iterMorph_getElem fibMorph false fibMorph_nonempty fibMorph_prolongable
            (N + 1 + r) i hlt
        · rw [List.getElem_append_right (by omega), prefixOf_getElem]
          have hsub : i - pos < p := by
            rw [prefixOf_length] at hi1; omega
          have hi_eq : i = pos + (i - pos) := by omega
          conv_lhs => rw [hi_eq]
          rw [hshift.2 (i - pos) (by omega)]
          have hfib := fixedPoint_eq_iterMorph_getElem fibMorph false fibMorph_nonempty fibMorph_prolongable
            N (i - pos) (by omega)
          exact hfib.symm
    rw [hpre_split, countFalse_append]
    have hc_pos : 1 ≤ countFalse (iterMorph fibMorph (N + 1 + r) [false]) := by
      have hpre0 : [false] <+: iterMorph fibMorph (N + 1 + r) [false] :=
        iterMorph_prefix_le fibMorph false fibMorph_prolongable (Nat.zero_le _)
      rcases hpre0 with ⟨t, ht⟩
      rw [← ht]; simp [countFalse]
    have hsub1 : countFalse (iterMorph fibMorph (N + 1 + r) [false]) + cP - 1 =
        (countFalse (iterMorph fibMorph (N + 1 + r) [false]) - 1) + cP := by omega
    -- Relate (c + cP - 1) % 2 to c % 2 and cP % 2
    set cX := countFalse (iterMorph fibMorph (N + 1 + r) [false])
    have hcX_eq : (cX % 2 == 1) = target := hr_par
    have hcase : ∀ (x y : ℕ), 1 ≤ x →
        ((x + y - 1) % 2 == 1) = xor (x % 2 == 1) (y % 2 == 0) := by
      intro x y hx
      have hx2 : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
      have hy2 : y % 2 = 0 ∨ y % 2 = 1 := Nat.mod_two_eq_zero_or_one y
      rcases hx2 with h0 | h1 <;> rcases hy2 with g0 | g1
      · have : (x + y - 1) % 2 = 1 := by omega
        simp [this, h0, g0]
      · have : (x + y - 1) % 2 = 0 := by omega
        simp [this, h0, g1]
      · have : (x + y - 1) % 2 = 0 := by omega
        simp [this, h1, g0]
      · have : (x + y - 1) % 2 = 1 := by omega
        simp [this, h1, g1]
    rw [hcase cX cP hc_pos, hcX_eq]
    dsimp [target]
    cases b <;> cases (cP % 2 == 0) <;> rfl
  · -- Show d occurs at pos + p in fibWord
    intro j hj
    have h1 : pos + p + j = pos + (p + j) := by omega
    rw [h1, hshift.2 (p + j) (by omega), hd_in_XN j hj]

/-- Reconstruct a binary word of length `d.length + 1` from its starting bit `b` and
complemented first-difference list `d`. -/
def fromComplDiff (b : Bool) : List Bool → List Bool
  | [] => [b]
  | c :: rest => b :: fromComplDiff (xor b (!c)) rest

theorem fromComplDiff_length (b : Bool) (d : List Bool) :
    (fromComplDiff b d).length = d.length + 1 := by
  induction d generalizing b with
  | nil => rfl
  | cons c rest ih =>
    simp only [fromComplDiff, List.length_cons, ih]

theorem complDiff_fromComplDiff (b : Bool) (d : List Bool) :
    complDiff (fromComplDiff b d) = d := by
  induction d generalizing b with
  | nil => rfl
  | cons c rest ih =>
    cases rest with
    | nil =>
      simp only [fromComplDiff, complDiff]
      cases b <;> cases c <;> rfl
    | cons c' rest' =>
      have hih := ih (xor b (!c))
      simp only [fromComplDiff, complDiff] at hih ⊢
      have h1 : (b == xor b (!c)) = c := by cases b <;> cases c <;> rfl
      rw [h1, hih]

theorem fromComplDiff_head (b : Bool) (d : List Bool) :
    (fromComplDiff b d)[0]'(by rw [fromComplDiff_length]; omega) = b := by
  cases d <;> rfl

theorem eq_fromComplDiff_of_complDiff (w : List Bool) (hw : 1 ≤ w.length) :
    w = fromComplDiff (w[0]'(by omega)) (complDiff w) := by
  induction w with
  | nil => simp at hw
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      simp only [List.getElem_cons_zero, complDiff, fromComplDiff]
      congr 1
      have hstep : xor a (!(a == b)) = b := by cases a <;> cases b <;> rfl
      rw [hstep]
      exact ih (by simp)

/-- **Exact Factor-Set Characterization of `roteFib` (`factorsOfLen_roteFib_eq`)**:
For every `n ≥ 1`, a binary word `w` of length `n` is a factor of `roteFib` iff its complemented
first-difference word `complDiff w` is a factor of `fibWord` of length `n - 1`. -/
theorem factorsOfLen_roteFib_eq {n : ℕ} (hn : 1 ≤ n) :
    FactorsOfLen roteFib n =
    { w : List Bool | w.length = n ∧ complDiff w ∈ FactorsOfLen fibWord (n - 1) } := by
  ext w
  simp only [FactorsOfLen, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hlen, ⟨p, hp⟩⟩
    refine ⟨hlen, by rw [complDiff_length, hlen], ⟨p + 1, fun j hj => ?_⟩⟩
    have hj' : j + 1 < w.length := by rw [complDiff_length] at hj; omega
    rw [complDiff_getElem w hj', ← hp j (by omega), ← hp (j + 1) hj']
    have hidx : p + 1 + j = p + j + 1 := by omega
    rw [hidx]
    exact (roteFib_complDiff (p + j)).symm
  · rintro ⟨hlen, _, hd_fac⟩
    rcases fibWord_factor_both_roteFib_starts hd_fac (w[0]'(by omega)) with ⟨q, hq1, hstart, hocc⟩
    refine ⟨hlen, ⟨q - 1, ?_⟩⟩
    -- Prove roteFib (q - 1 + j) = w[j] by induction on j < w.length!
    intro j hj
    induction j with
    | zero =>
      simp only [Nat.add_zero]
      exact hstart
    | succ j ih =>
      have hj_prev : j < w.length := by omega
      have hcd_j : j < (complDiff w).length := by rw [complDiff_length]; omega
      have h1 := roteFib_complDiff (q - 1 + j)
      have h2 := hocc j hcd_j
      have hidx1 : q - 1 + j + 1 = q + j := by omega
      rw [hidx1] at h1
      rw [h2, complDiff_getElem w hj, ih hj_prev] at h1
      have hidx2 : q - 1 + (j + 1) = q + j := by omega
      rw [hidx2]
      cases hA : w[j]'hj_prev <;> cases hB : roteFib (q + j) <;> cases hC : w[j + 1]'hj <;>
        simp_all

/-- **Exact Factor-Set Characterization of `gRfB5` (`factorsOfLen_gRfB5_eq`)**:
For every `n ≥ 1`, `g_rf(b_5)` has the exact same factor characterization as `roteFib`. -/
theorem factorsOfLen_gRfB5_eq {n : ℕ} (hn : 1 ≤ n) :
    FactorsOfLen gRfB5 n =
    { w : List Bool | w.length = n ∧ complDiff w ∈ FactorsOfLen fibWord (n - 1) } := by
  ext w
  simp only [FactorsOfLen, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hlen, ⟨p, hp⟩⟩
    refine ⟨hlen, by rw [complDiff_length, hlen], ⟨p, fun j hj => ?_⟩⟩
    have hj' : j + 1 < w.length := by rw [complDiff_length] at hj; omega
    rw [complDiff_getElem w hj', ← hp j (by omega), ← hp (j + 1) hj']
    have hidx : p + (j + 1) = p + j + 1 := by omega
    rw [hidx]
    exact (gRfB5_complDiff_eq_fibWord (p + j)).symm
  · rintro ⟨hlen, _, hd_fac⟩
    -- Since gRfB5 (k + 1) = !(roteFib k), pick q ≥ 1 with roteFib (q - 1) = !(w[0])!
    rcases fibWord_factor_both_roteFib_starts hd_fac (!(w[0]'(by omega))) with ⟨q, hq1, hstart, hocc⟩
    refine ⟨hlen, ⟨q, ?_⟩⟩
    intro j hj
    induction j with
    | zero =>
      simp only [Nat.add_zero]
      have hq_eq : q = (q - 1) + 1 := by omega
      rw [hq_eq, gRfB5_succ_eq_not_roteFib, hstart, Bool.not_not]
    | succ j ih =>
      have hj_prev : j < w.length := by omega
      have hcd_j : j < (complDiff w).length := by rw [complDiff_length]; omega
      have h1 := gRfB5_complDiff_eq_fibWord (q + j)
      have h2 := hocc j hcd_j
      rw [h2, complDiff_getElem w hj, ih hj_prev] at h1
      have hidx : q + (j + 1) = q + j + 1 := by omega
      rw [hidx]
      cases hA : w[j]'hj_prev <;> cases hB : gRfB5 (q + j + 1) <;> cases hC : w[j + 1]'hj <;>
        simp_all

/-- **Complete Resolution of Badkobeh–Ochem (2015, Sec. 5) Observation (O2)
(`b5_rote_fibonacci_projection`)**:
For EVERY `n : ℕ`, `g_rf(b_5)` and the Rote–Fibonacci word `roteFib` have the exact same set of
length-`n` factors. -/
theorem b5_rote_fibonacci_projection (n : ℕ) :
    FactorsOfLen gRfB5 n = FactorsOfLen roteFib n := by
  cases n with
  | zero =>
    rw [factorsOfLen_zero, factorsOfLen_zero]
  | succ m =>
    rw [factorsOfLen_gRfB5_eq (Nat.succ_pos m), factorsOfLen_roteFib_eq (Nat.succ_pos m)]

theorem complDiff_map_not (w : List Bool) :
    complDiff (w.map (!·)) = complDiff w := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      simp only [List.map_cons, complDiff] at ih ⊢
      have h : ((!a) == (!b)) = (a == b) := by cases a <;> cases b <;> rfl
      rw [h, ih]

/-- Complement invariance of the Rote–Fibonacci factor language. -/
theorem roteFib_factors_compl_invariant (w : List Bool) :
    IsFactorInf w roteFib ↔ IsFactorInf (w.map (!·)) roteFib := by
  cases w with
  | nil => simp [isFactorInf_nil]
  | cons a rest =>
    let n := (a :: rest).length
    have hn : 1 ≤ n := by simp [n]
    have hmem : ∀ u : List Bool, u.length = n →
        (IsFactorInf u roteFib ↔ u ∈ FactorsOfLen roteFib n) := by
      intro u hu; simp [FactorsOfLen, hu]
    rw [hmem (a :: rest) rfl, hmem ((a :: rest).map (!·)) (by simp [n]),
        factorsOfLen_roteFib_eq hn]
    simp only [Set.mem_ofPred_eq, List.length_map, complDiff_map_not, n, true_and]

/-- Complement invariance of the `g_rf(b_5)` factor language. -/
theorem gRfB5_factors_compl_invariant (w : List Bool) :
    IsFactorInf w gRfB5 ↔ IsFactorInf (w.map (!·)) gRfB5 := by
  have h1 : IsFactorInf w gRfB5 ↔ w ∈ FactorsOfLen gRfB5 w.length := by
    simp [FactorsOfLen]
  have h2 : IsFactorInf (w.map (!·)) gRfB5 ↔ w.map (!·) ∈ FactorsOfLen gRfB5 w.length := by
    simp [FactorsOfLen]
  rw [h1, h2, b5_rote_fibonacci_projection w.length]
  simp only [FactorsOfLen, Set.mem_ofPred_eq, List.length_map, true_and]
  exact roteFib_factors_compl_invariant w

/-- **Exact Rote Factor Complexity of `roteFib` (`roteFib_factor_complexity`)**:
For every `n ≥ 1`, `factorComplexity roteFib n = 2 * n`. -/
theorem roteFib_factor_complexity (n : ℕ) (hn : 1 ≤ n) :
    factorComplexity roteFib n = 2 * n := by
  unfold factorComplexity
  rw [factorsOfLen_roteFib_eq hn]
  let S := { w : List Bool | w.length = n ∧ complDiff w ∈ FactorsOfLen fibWord (n - 1) }
  let T : Set (Bool × List Bool) := Set.univ ×ˢ FactorsOfLen fibWord (n - 1)
  have hbij : Set.BijOn (fun p : Bool × List Bool => fromComplDiff p.1 p.2) T S := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨b, d⟩ ⟨_, hd⟩
      refine ⟨?_, ?_⟩
      · rw [fromComplDiff_length, hd.1]; omega
      · rw [complDiff_fromComplDiff]; exact hd
    · rintro ⟨b1, d1⟩ _ ⟨b2, d2⟩ _ heq
      have hb : b1 = b2 := by
        have h0 := congrArg (fun l => l[0]?) heq
        rw [List.getElem?_eq_getElem (by rw [fromComplDiff_length]; omega),
            List.getElem?_eq_getElem (by rw [fromComplDiff_length]; omega),
            fromComplDiff_head, fromComplDiff_head] at h0
        exact Option.some.inj h0
      have hd : d1 = d2 := by
        have hcd := congrArg complDiff heq
        rw [complDiff_fromComplDiff, complDiff_fromComplDiff] at hcd
        exact hcd
      exact Prod.ext hb hd
    · intro w hw
      refine ⟨(w[0]'(by rw [hw.1]; omega), complDiff w), ⟨Set.mem_univ _, hw.2⟩, ?_⟩
      exact (eq_fromComplDiff_of_complDiff w (by rw [hw.1]; omega)).symm
  have hcard_eq : S.ncard = T.ncard := (Set.ncard_congr (fun p _ => fromComplDiff p.1 p.2)
    (fun p hp => hbij.mapsTo hp)
    (fun p1 p2 hp1 hp2 heq => hbij.injOn hp1 hp2 heq)
    (fun w hw => by
      rcases hbij.surjOn hw with ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩)).symm
  rw [hcard_eq]
  change (Set.univ ×ˢ FactorsOfLen fibWord (n - 1)).ncard = 2 * n
  rw [Set.ncard_prod]
  have huniv : (Set.univ : Set Bool).ncard = 2 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool]
  have hfib : (FactorsOfLen fibWord (n - 1)).ncard = n := by
    have h := fibWord_factor_complexity (n - 1)
    unfold factorComplexity at h
    omega
  rw [huniv, hfib]

/-- **Exact Rote Factor Complexity of `g_rf(b_5)` (`gRfB5_factor_complexity`)**:
For every `n ≥ 1`, `factorComplexity gRfB5 n = 2 * n`. -/
theorem gRfB5_factor_complexity (n : ℕ) (hn : 1 ≤ n) :
    factorComplexity gRfB5 n = 2 * n := by
  unfold factorComplexity
  rw [b5_rote_fibonacci_projection n]
  exact roteFib_factor_complexity n hn

theorem gRfB5_factor_complexity_zero :
    factorComplexity gRfB5 0 = 1 := by
  unfold factorComplexity
  rw [factorsOfLen_zero]
  simp

end BadkobehOchemB5
