/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BadkobehOchemB5.Defs
public import BadkobehOchemB5.SeedsCert
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Exact Critical Exponent `E(b_5) = (5 + √5) / 4` (Not Attained, `R18-2-ce-1`)

Resolves Badkobeh & Ochem's (*Theoret. Comput. Sci.* 588, 2015, Section 5) open problem on the
exact critical exponent of `b_5 = f_5^ω(0)` **100% unconditionally**:

1. **Strict Upper Bound (`b5_exponent_lt_crit`)**: For every factor `w` of `b_5` and every period
   `p ≥ 1` of `w`, `(w.length : ℝ) / (p : ℝ) < (5 + Real.sqrt 5) / 4 = 1 + φ / 2`.
2. **Unconditional Square-Freeness (`b5_squarefree`)**: Since `(5 + √5) / 4 < 2`, no non-empty
   square `u ++ u` occurs in `b_5`.
3. **Asymptotic Attainment (`b5_sup_exponent_ge_crit`)**: Along the explicit `Phi`-orbit of the
   extremal seed `123010421` (`p_0 = 2, m_0 = 1`), `D_{2 + 6j} = φ p_{2 + 6j} - 2 m_{2 + 6j} ≤ 4`
   while `p_{2 + 6j} → ∞`, producing factors `(w_j, p_j)` with `|w_j| / p_j → (5 + √5) / 4`.
4. **Exact Supremum & Non-Attainment (`b5_critical_exponent_eq`, `b5_critical_exponent_not_attained`)**:
   `critExp b5 = (5 + Real.sqrt 5) / 4`, and no factor of `b_5` attains `(5 + Real.sqrt 5) / 4`.
-/

@[expose] public section

namespace BadkobehOchemB5

/-! ## Section 1: Period, Repetition Exponent, and Critical Exponent Definitions -/

/-- `IsPeriod w p` means `p` is a period of the finite word `w`:
`∀ i, i + p < w.length → w[i] = w[i + p]`. -/
def IsPeriod {α : Type*} (w : List α) (p : ℕ) : Prop :=
  ∀ i : ℕ, ∀ hi : i + p < w.length, w[i]'(by omega) = w[i + p]'hi

/-- Fractional repetition exponent `|w| / p` of a factor `w` with period `p`. -/
noncomputable def exponent {α : Type*} (w : List α) (p : ℕ) : ℝ :=
  (w.length : ℝ) / (p : ℝ)

/-- Set of all repetition exponents `|w| / p` over factors `w` of `W` and periods `p ≥ 1`. -/
def ExponentSet {α : Type*} (W : ℕ → α) : Set ℝ :=
  { e : ℝ | ∃ w p, IsFactorInf w W ∧ 1 ≤ p ∧ IsPeriod w p ∧ e = (w.length : ℝ) / (p : ℝ) }

/-- Set of repetition exponents over non-empty factors `w ≠ []` of `W` and periods `p ≥ 1`. -/
def NonemptyExponentSet {α : Type*} (W : ℕ → α) : Set ℝ :=
  { e : ℝ | ∃ w p, w ≠ [] ∧ IsFactorInf w W ∧ 1 ≤ p ∧ IsPeriod w p ∧ e = exponent w p }

/-- Critical exponent `E(W) = sup { |w| / p }` of an infinite word `W : ℕ → α`. -/
noncomputable def critExp {α : Type*} (W : ℕ → α) : ℝ :=
  sSup (ExponentSet W)

theorem critVal_eq_one_add_half_phi :
    (5 + Real.sqrt 5) / 4 = 1 + φ / 2 := by
  unfold φ; ring

theorem critVal_lt_two : (5 + Real.sqrt 5) / 4 < 2 := by
  linarith [sqrt5_lt_three]

theorem one_lt_critVal : 1 < (5 + Real.sqrt 5) / 4 := by
  linarith [two_lt_sqrt5]

/-! ## Section 2: `Sym5` Representation `b5Sym`, Block Decomposition, and `L1` -/

/-- `Sym5` representation of `b_5`, linked 1-to-1 to `b5 : ℕ → Fin 5`. -/
def b5Sym (n : ℕ) : Sym5 :=
  Sym5.ofFin (b5 n)

@[simp] theorem b5Sym_toFin (n : ℕ) : (b5Sym n).toFin = b5 n :=
  Sym5.toFin_ofFin (b5 n)

@[simp] theorem b5Sym_zero : b5Sym 0 = .s0 := rfl

@[simp] theorem sym5_beq_self (x : Sym5) : Sym5.beq x x = true := by
  cases x <;> rfl

theorem b5Sym_eq_iff (m n : ℕ) : b5Sym m = b5Sym n ↔ b5 m = b5 n := by
  constructor
  · intro h; rw [← b5Sym_toFin m, ← b5Sym_toFin n, h]
  · intro h; simp [b5Sym, h]

/-- Contiguous slice `b5Sym[q .. q + len)` of length `len`. -/
def symSlice (q len : ℕ) : List Sym5 :=
  List.ofFn fun k : Fin len => b5Sym (q + k.val)

@[simp] theorem symSlice_length (q len : ℕ) : (symSlice q len).length = len := by
  simp [symSlice]

@[simp] theorem symSlice_getElem (q len k : ℕ) (hk : k < (symSlice q len).length) :
    (symSlice q len)[k] = b5Sym (q + k) := by
  simp [symSlice]

theorem symSlice_zero (q : ℕ) : symSlice q 0 = [] := rfl

theorem symSlice_add (q m n : ℕ) :
    symSlice q (m + n) = symSlice q m ++ symSlice (q + m) n := by
  apply List.ext_getElem
  · simp
  · intro k hk1 hk2
    by_cases h : k < m
    · rw [List.getElem_append_left (by simp [h])]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [symSlice_length, symSlice_getElem]
      congr 1; omega

theorem symSlice_map_toFin (q len : ℕ) :
    (symSlice q len).map Sym5.toFin = List.ofFn (fun k : Fin len => b5 (q + k.val)) := by
  apply List.ext_getElem
  · simp
  · intro k hk1 hk2
    simp

theorem fSym5_length_eq (a : Fin 5) : (fSym5 (Sym5.ofFin a)).length = (fB5 a).length := by
  fin_cases a <;> rfl

theorem fSym5_length_bounds (x : Sym5) : 1 ≤ (fSym5 x).length ∧ (fSym5 x).length ≤ 2 := by
  cases x <;> decide

theorem blockStart_succ_sym (p : ℕ) :
    blockStart (p + 1) = blockStart p + (fSym5 (b5Sym p)).length := by
  rw [blockStart_succ, b5Sym, fSym5_length_eq]

theorem blockStart_le_two_mul (p : ℕ) : blockStart p ≤ 2 * p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [blockStart_succ_sym]
    have hb := (fSym5_length_bounds (b5Sym p)).2
    omega

theorem sym_block_decomp_unique {p₁ o₁ p₂ o₂ : ℕ}
    (ho₁ : o₁ < (fSym5 (b5Sym p₁)).length)
    (ho₂ : o₂ < (fSym5 (b5Sym p₂)).length)
    (heq : blockStart p₁ + o₁ = blockStart p₂ + o₂) :
    p₁ = p₂ ∧ o₁ = o₂ := by
  have h12 : ¬ (p₁ < p₂) := by
    intro hlt
    have hle : blockStart (p₁ + 1) ≤ blockStart p₂ :=
      blockStart_strictMono.monotone (Nat.succ_le_of_lt hlt)
    rw [blockStart_succ_sym] at hle
    omega
  have h21 : ¬ (p₂ < p₁) := by
    intro hlt
    have hle : blockStart (p₂ + 1) ≤ blockStart p₁ :=
      blockStart_strictMono.monotone (Nat.succ_le_of_lt hlt)
    rw [blockStart_succ_sym] at hle
    omega
  have hp : p₁ = p₂ := by omega
  subst hp
  exact ⟨rfl, by omega⟩

theorem exists_sym_block_decomp (q : ℕ) :
    ∃ p o : ℕ, ∃ ho : o < (fSym5 (b5Sym p)).length,
      q = blockStart p + o ∧
      b5Sym q = (fSym5 (b5Sym p))[o]'ho ∧
      (1 ≤ q → p < q) := by
  rcases exists_block_decomp q with ⟨p, o, ho_fin, hq_eq, hb5_q, _, hp_lt⟩
  have hlen : (fSym5 (b5Sym p)).length = (fB5 (b5 p)).length := fSym5_length_eq (b5 p)
  have ho : o < (fSym5 (b5Sym p)).length := by omega
  refine ⟨p, o, ho, hq_eq, ?_, hp_lt⟩
  have hmap := fSym5_map_toFin (b5Sym p)
  rw [b5Sym_toFin] at hmap
  have hget : ((fSym5 (b5Sym p))[o]'ho).toFin = (fB5 (b5 p))[o]'ho_fin := by
    have := congrArg (fun l : List (Fin 5) => l[o]?) hmap
    rw [List.getElem?_eq_getElem (by simp [ho]), List.getElem?_eq_getElem ho_fin,
        Option.some.injEq, List.getElem_map] at this
    exact this
  rw [← Sym5.ofFin_toFin ((fSym5 (b5Sym p))[o]'ho), hget, ← hb5_q]
  rfl

theorem b5Sym_blockStart_add (p o : ℕ) (ho : o < (fSym5 (b5Sym p)).length) :
    b5Sym (blockStart p + o) = (fSym5 (b5Sym p))[o]'ho := by
  rcases exists_sym_block_decomp (blockStart p + o) with ⟨p', o', ho', heq, hb, _⟩
  rcases sym_block_decomp_unique ho ho' heq with ⟨rfl, rfl⟩
  exact hb

theorem symSlice_blockStart_single (p : ℕ) :
    symSlice (blockStart p) (fSym5 (b5Sym p)).length = fSym5 (b5Sym p) := by
  apply List.ext_getElem
  · simp
  · intro o ho1 ho2
    rw [symSlice_getElem]
    exact b5Sym_blockStart_add p o ho2

theorem symSlice_blockStart (a b : ℕ) (hab : a ≤ b) :
    symSlice (blockStart a) (blockStart b - blockStart a) =
      morphSym5 (symSlice a (b - a)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero =>
    simp [symSlice_zero, morphSym5]
  | succ d ih =>
    have hle : blockStart a ≤ blockStart (a + d) :=
      blockStart_strictMono.monotone (by omega)
    have hsplit : blockStart (a + (d + 1)) - blockStart a =
        (blockStart (a + d) - blockStart a) + (fSym5 (b5Sym (a + d))).length := by
      have hs := blockStart_succ_sym (a + d)
      have ha : a + (d + 1) = a + d + 1 := by omega
      rw [ha, hs]
      omega
    rw [hsplit, symSlice_add, Nat.add_sub_of_le hle, ih, symSlice_blockStart_single]
    have hslice1 : symSlice a (d + 1) = symSlice a d ++ [b5Sym (a + d)] := by
      rw [symSlice_add]; rfl
    rw [hslice1, morphSym5_append]
    simp [morphSym5]

def firstFSym5 (x : Sym5) : Sym5 :=
  (fSym5 x).headD .s0

def secondFSym5 (x : Sym5) : Sym5 :=
  ((fSym5 x).drop 1).headD .s0

def lastFSym5 (x : Sym5) : Sym5 :=
  (fSym5 x).getLastD .s0

theorem fSym5_getElem_zero (x : Sym5) (h : 0 < (fSym5 x).length) :
    (fSym5 x)[0]'h = firstFSym5 x := by
  cases x <;> rfl

theorem fSym5_getElem_one (x : Sym5) (h : 1 < (fSym5 x).length) :
    (fSym5 x)[1]'h = secondFSym5 x := by
  cases x <;> first | rfl | (simp [fSym5] at h)

theorem fSym5_getElem_last (x : Sym5) (h : (fSym5 x).length - 1 < (fSym5 x).length) :
    (fSym5 x)[(fSym5 x).length - 1]'h = lastFSym5 x := by
  cases x <;> rfl

/-- **Lemma `L1` (`b5Sym_valid2`)**: Every adjacent pair in `b5Sym` is one of the 9 valid 2-factors. -/
theorem b5Sym_valid2 (i : ℕ) : valid2Sym (b5Sym i) (b5Sym (i + 1)) = true := by
  induction i using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0
      have hb1 : b5 1 = 1 := by
        have h := congrArg (fun l : List (Fin 5) => l[1]?) b5_prefix_17
        simp [prefixOf] at h
        exact h
      have hs1 : b5Sym 1 = .s1 := by simp [b5Sym, hb1, Sym5.ofFin]
      rw [b5Sym_zero, hs1]
      rfl
    · rcases exists_sym_block_decomp q with ⟨p, o, ho, hq_eq, hbq, hp_lt⟩
      have hpq : p < q := hp_lt (by omega)
      have hvp : valid2Sym (b5Sym p) (b5Sym (p + 1)) = true := ih p hpq
      by_cases ho_next : o + 1 < (fSym5 (b5Sym p)).length
      · have hlen2 : (fSym5 (b5Sym p)).length = 2 := by
          have := (fSym5_length_bounds (b5Sym p)).2; omega
        have ho0 : o = 0 := by omega
        subst ho0
        have ho1 : 1 < (fSym5 (b5Sym p)).length := by omega
        have hq1 : q + 1 = blockStart p + 1 := by omega
        rw [hq1, hq_eq, b5Sym_blockStart_add p 0 ho, b5Sym_blockStart_add p 1 ho1,
            fSym5_getElem_zero, fSym5_getElem_one]
        cases hsp : b5Sym p <;> rw [hsp] at hlen2 <;>
          first | rfl | (simp [fSym5] at hlen2)
      · have ho_end : o + 1 = (fSym5 (b5Sym p)).length := by omega
        have ho_val : o = (fSym5 (b5Sym p)).length - 1 := by omega
        subst ho_val
        have hq1 : q + 1 = blockStart (p + 1) + 0 := by
          rw [blockStart_succ_sym, ← ho_end]; omega
        have ho0' : 0 < (fSym5 (b5Sym (p + 1))).length :=
          (fSym5_length_bounds (b5Sym (p + 1))).1
        rw [hq1, hq_eq, b5Sym_blockStart_add p _ ho, b5Sym_blockStart_add (p + 1) 0 ho0',
            fSym5_getElem_last, fSym5_getElem_zero]
        revert hvp
        generalize b5Sym p = a, b5Sym (p + 1) = b
        intro hvp
        cases a <;> cases b <;> first | rfl | exact Bool.noConfusion hvp

theorem b5Sym_ne_succ (i : ℕ) : b5Sym i ≠ b5Sym (i + 1) := by
  intro heq
  have hv := b5Sym_valid2 i
  rw [heq, valid2Sym_no_self] at hv
  exact Bool.noConfusion hv

theorem symWord3At_isValid (q : ℕ) :
    (⟨b5Sym q, b5Sym (q + 1), b5Sym (q + 2)⟩ : Word3).isValid = true := by
  simp only [Word3.isValid, Bool.and_eq_true]
  exact ⟨b5Sym_valid2 q, b5Sym_valid2 (q + 1)⟩

/-! ## Section 3: Level-`k` Block Decomposition, Primitivity (`exists_sym_occ_ge`), and `g10Val` Coverage -/

/-- Start index of the `p`-th `fB5^k`-block in `b5`. -/
def blockStartK (k p : ℕ) : ℕ :=
  (applyMorph (fun a => iterMorph fB5 k [a]) (prefixOf b5 p)).length

@[simp] theorem blockStartK_zero (k : ℕ) : blockStartK k 0 = 0 := rfl

theorem blockStartK_succ (k p : ℕ) :
    blockStartK k (p + 1) = blockStartK k p + (iterMorph fB5 k [b5 p]).length := by
  simp [blockStartK, prefixOf_succ, applyMorph_append]

theorem iterMorph_fB5_pos (k : ℕ) (a : Fin 5) : 1 ≤ (iterMorph fB5 k [a]).length :=
  List.length_pos_of_ne_nil (iterMorph_ne_nil fB5 fB5_nonempty k (List.cons_ne_nil a []))

theorem blockStartK_ge (k p : ℕ) : p ≤ blockStartK k p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [blockStartK_succ]
    have h1 := iterMorph_fB5_pos k (b5 p)
    omega

theorem symSlice_blockStartK_single (k p : ℕ) :
    symSlice (blockStartK k p) (iterSym5 k [b5Sym p]).length = iterSym5 k [b5Sym p] := by
  have hlen : (iterSym5 k [b5Sym p]).length = (iterMorph fB5 k [b5 p]).length := by
    have h := congrArg List.length (iterSym5_map_toFin k [b5Sym p])
    simpa using h
  have hpref := fixedPoint_applyMorph_prefix_isPrefix fB5 0 fB5_nonempty fB5_prolongable k (p + 1)
  change applyMorph (fun a => iterMorph fB5 k [a]) (prefixOf b5 (p + 1)) =
    prefixOf b5 (blockStartK k (p + 1)) at hpref
  rw [prefixOf_succ, applyMorph_append, applyMorph_singleton] at hpref
  apply List.ext_getElem
  · simp
  · intro o ho1 ho2
    rw [symSlice_getElem]
    have hidx_lt : blockStartK k p + o < (prefixOf b5 (blockStartK k (p + 1))).length := by
      simp [blockStartK_succ]; omega
    have hget := congrArg (fun l : List (Fin 5) => l[blockStartK k p + o]?) hpref
    rw [List.getElem?_eq_getElem hidx_lt, prefixOf_getElem] at hget
    rw [List.getElem?_append_right (by change blockStartK k p ≤ blockStartK k p + o; omega)] at hget
    change (iterMorph fB5 k [b5 p])[blockStartK k p + o - blockStartK k p]? =
      some (b5 (blockStartK k p + o)) at hget
    have ho_fin : blockStartK k p + o - blockStartK k p < (iterMorph fB5 k [b5 p]).length := by
      omega
    rw [List.getElem?_eq_getElem ho_fin, Option.some.injEq] at hget
    have ho_fin' : o < (iterMorph fB5 k [b5 p]).length := by omega
    have hsub_get : (iterMorph fB5 k [b5 p])[blockStartK k p + o - blockStartK k p]'ho_fin =
        (iterMorph fB5 k [b5 p])[o]'ho_fin' := by
      congr 1; omega
    rw [hsub_get] at hget
    have hmap := iterSym5_map_toFin k [b5Sym p]
    simp only [List.map_cons, List.map_nil, b5Sym_toFin] at hmap
    have hm_eq := congrArg (fun l : List (Fin 5) => l[o]?) hmap
    rw [List.getElem?_eq_getElem (by simp [ho2]), List.getElem?_eq_getElem ho_fin',
        Option.some.injEq, List.getElem_map] at hm_eq
    rw [← hm_eq] at hget
    rw [← Sym5.ofFin_toFin ((iterSym5 k [b5Sym p])[o]), hget]
    rfl

theorem isFactor_iterSym5 (n : ℕ) {u w : List Sym5} (h : IsFactor u w) :
    IsFactor (iterSym5 n u) (iterSym5 n w) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rcases ih with ⟨p, s, hps⟩
    exact ⟨morphSym5 p, morphSym5 s, by rw [iterSym5, hps, morphSym5_append, morphSym5_append]; rfl⟩

/-- **Arbitrary-Index Recurrence (`exists_sym_occ_ge`)**:
Every factor occurring at `i₀` in `b5Sym` re-occurs at some index `q ≥ B` for EVERY `B : ℕ`. -/
theorem exists_sym_occ_ge (i₀ len B : ℕ) :
    ∃ q : ℕ, B ≤ q ∧ symSlice q len = symSlice i₀ len := by
  let N := i₀ + len
  have hN_def : N = i₀ + len := rfl
  let k := N + 5
  have hk_def : k = N + 5 := rfl
  have hmem0 : Sym5.s0 ∈ g5Val (b5Sym B) := fSym5_prim5 (b5Sym B) .s0
  rw [g5Val_eq_iterSym5] at hmem0
  rcases List.append_of_mem hmem0 with ⟨pre5, suf5, h5eq⟩
  have hfac5 : IsFactor [.s0] (iterSym5 5 [b5Sym B]) :=
    ⟨pre5, suf5, by simpa [List.append_assoc] using h5eq⟩
  have hfack : IsFactor (iterSym5 N [.s0]) (iterSym5 k [b5Sym B]) := by
    have hk_add : iterSym5 k [b5Sym B] = iterSym5 N (iterSym5 5 [b5Sym B]) :=
      iterSym5_add N 5 [b5Sym B]
    rw [hk_add]
    exact isFactor_iterSym5 N hfac5
  rcases isFactor_iff_exists_idx.mp hfack with ⟨off, hoff_le, hoff_get⟩
  let q := blockStartK k B + off + i₀
  have hq_def : q = blockStartK k B + off + i₀ := rfl
  have hB_le : B ≤ q := by
    have := blockStartK_ge k B
    omega
  refine ⟨q, hB_le, ?_⟩
  have hN_len : N < (iterSym5 N [.s0]).length := by
    have hmap := congrArg List.length (iterSym5_map_toFin N [.s0])
    simp only [List.length_map, List.map_cons, List.map_nil, Sym5.toFin] at hmap
    rw [hmap]
    exact lt_iterMorph_length fB5 0 fB5_nonempty fB5_prolongable N
  have hiterN_get : ∀ m (hm : m < (iterSym5 N [.s0]).length), (iterSym5 N [.s0])[m]'hm = b5Sym m := by
    intro m hm
    have hmap := iterSym5_map_toFin N [.s0]
    simp only [List.map_cons, List.map_nil, Sym5.toFin] at hmap
    have hm_fin : m < (iterMorph fB5 N [0]).length := by
      have hc := congrArg List.length hmap; simp at hc; omega
    have hfp := fixedPoint_eq_iterMorph_getElem fB5 0 fB5_nonempty fB5_prolongable N m hm_fin
    change b5 m = (iterMorph fB5 N [0])[m] at hfp
    have hm_eq := congrArg (fun l : List (Fin 5) => l[m]?) hmap
    rw [List.getElem?_eq_getElem (by simp [hm]), List.getElem?_eq_getElem hm_fin,
        Option.some.injEq, List.getElem_map] at hm_eq
    have hg : ((iterSym5 N [.s0])[m]'hm).toFin = b5 m := by rw [hm_eq, ← hfp]
    rw [← Sym5.ofFin_toFin ((iterSym5 N [.s0])[m]'hm), hg]
    rfl
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    simp only [symSlice_length] at hj1
    rw [symSlice_getElem, symSlice_getElem]
    have hj_in_N : i₀ + j < (iterSym5 N [.s0]).length := by omega
    have h1 := (hiterN_get (i₀ + j) hj_in_N).symm
    have h2 := (hoff_get (i₀ + j) hj_in_N).symm
    have hblk := symSlice_blockStartK_single k B
    have hoff_in_k : off + (i₀ + j) < (iterSym5 k [b5Sym B]).length := by omega
    have h3 : (iterSym5 k [b5Sym B])[off + (i₀ + j)] = b5Sym (blockStartK k B + (off + (i₀ + j))) := by
      have := congrArg (fun l : List Sym5 => l[off + (i₀ + j)]?) hblk
      rw [List.getElem?_eq_getElem (by simp [hoff_in_k]),
          List.getElem?_eq_getElem hoff_in_k, Option.some.injEq, symSlice_getElem] at this
      exact this.symm
    have hq_idx : q + j = blockStartK k B + (off + (i₀ + j)) := by omega
    rw [hq_idx, ← h3, ← h2, ← h1]

/-- **Completeness of `g10Val` Pairs for Length `≤ 48` (`symSlice_in_g10_pair`)**:
Every slice `symSlice q L` of length `L ≤ 48` in `b5Sym` occurs at some offset `o` inside
`g10Val a ++ g10Val b` for a valid 2-factor `(a, b) ∈ twoFactorSymList`. -/
theorem symSlice_in_g10_pair (q L : ℕ) (hL : L ≤ 48) :
    ∃ a b : Sym5, ∃ o : ℕ,
      (a, b) ∈ twoFactorSymList ∧
      o < 256 ∧
      o + L ≤ (g10Val a ++ g10Val b).length ∧
      symSlice q L = ((g10Val a ++ g10Val b).drop o).take L := by
  have hex : ∃ r : ℕ, blockStartK 10 r ≤ q ∧ q < blockStartK 10 (r + 1) := by
    induction q with
    | zero =>
      refine ⟨0, by simp, ?_⟩
      rw [blockStartK_succ, blockStartK_zero]
      have := iterMorph_fB5_pos 10 (b5 0)
      omega
    | succ q ih =>
      rcases ih with ⟨r, hle, hlt⟩
      by_cases hnext : q + 1 < blockStartK 10 (r + 1)
      · exact ⟨r, by omega, hnext⟩
      · refine ⟨r + 1, by omega, ?_⟩
        rw [blockStartK_succ 10 (r + 1)]
        have := iterMorph_fB5_pos 10 (b5 (r + 1))
        omega
  rcases hex with ⟨r, hle, hlt⟩
  let a := b5Sym r
  let b := b5Sym (r + 1)
  let o := q - blockStartK 10 r
  have ho_def : o = q - blockStartK 10 r := rfl
  have ha_len_eq : (g10Val a).length = (iterMorph fB5 10 [b5 r]).length := by
    rw [g10Val_eq_iterSym5]
    have h := congrArg List.length (iterSym5_map_toFin 10 [a])
    simpa [a] using h
  have hb_len_eq : (g10Val b).length = (iterMorph fB5 10 [b5 (r + 1)]).length := by
    rw [g10Val_eq_iterSym5]
    have h := congrArg List.length (iterSym5_map_toFin 10 [b])
    simpa [b] using h
  have ho_lt : o < (g10Val a).length := by
    rw [blockStartK_succ] at hlt; omega
  have ha_lt256 : (g10Val a).length < 256 := by
    by_contra hge
    have ht : hasLenAtLeast 256 (g10Val a) = true :=
      (hasLenAtLeast_iff 256 (g10Val a)).mpr (by omega)
    rw [g10Val_len_lt_256_bool] at ht
    exact Bool.noConfusion ht
  have hb_ge72 : 72 ≤ (g10Val b).length :=
    (hasLenAtLeast_iff 72 (g10Val b)).mp (g10Val_len_ge_72 b)
  have hmem : (a, b) ∈ twoFactorSymList :=
    (valid2Sym_iff_mem a b).mp (b5Sym_valid2 r)
  have hfit : o + L ≤ (g10Val a ++ g10Val b).length := by
    rw [List.length_append]; omega
  refine ⟨a, b, o, hmem, by omega, hfit, ?_⟩
  have hblk0 : symSlice (blockStartK 10 r) (g10Val a).length = g10Val a := by
    rw [g10Val_eq_iterSym5]; exact symSlice_blockStartK_single 10 r
  have hblk1 : symSlice (blockStartK 10 (r + 1)) (g10Val b).length = g10Val b := by
    rw [g10Val_eq_iterSym5]; exact symSlice_blockStartK_single 10 (r + 1)
  have hblk01 : symSlice (blockStartK 10 r) ((g10Val a).length + (g10Val b).length) =
      g10Val a ++ g10Val b := by
    rw [symSlice_add]
    have hs1 : blockStartK 10 r + (g10Val a).length = blockStartK 10 (r + 1) := by
      rw [blockStartK_succ, ha_len_eq]
    rw [hs1, hblk0, hblk1]
  apply List.ext_getElem
  · simp; omega
  · intro j hj1 hj2
    simp only [symSlice_length] at hj1
    rw [symSlice_getElem, List.getElem_take, List.getElem_drop]
    simp only [List.length_append] at hfit
    have h1 := congrArg (fun l : List Sym5 => l[o + j]?) hblk01
    rw [List.getElem?_eq_getElem (by simp; omega),
        List.getElem?_eq_getElem (by rw [List.length_append]; omega),
        Option.some.injEq, symSlice_getElem] at h1
    rw [← h1]
    congr 1; omega

/-- No length-5 slice in `b5Sym` has period `2` (`L4` / `C1`). -/
theorem no_sym_period2_len5 (q : ℕ) :
    ¬ (b5Sym q = b5Sym (q + 2) ∧ b5Sym (q + 1) = b5Sym (q + 3) ∧ b5Sym (q + 2) = b5Sym (q + 4)) := by
  rintro ⟨h02, h13, h24⟩
  rcases symSlice_in_g10_pair q 5 (by omega) with ⟨a, b, o, hmem, ho256, hfit, hslice⟩
  let full := g10Val a ++ g10Val b
  let s := full.drop o
  have hall := no_period2_len5
  rw [allTR_eq_all] at hall
  have hp := List.all_eq_true.mp hall (a, b) hmem
  have hs_ok := (scanDrops256_iff _ full).mp hp o ho256
  change (!(hasLenAtLeast 5 s && symOptEq s[0]? s[2]? && symOptEq s[1]? s[3]? && symOptEq s[2]? s[4]?)) = true at hs_ok
  have hlen5 : hasLenAtLeast 5 s = true :=
    (hasLenAtLeast_iff 5 s).mpr (by dsimp [s, full]; rw [List.length_drop]; omega)
  have hs_get : ∀ k (hk : k < 5), s[k]? = some (b5Sym (q + k)) := by
    intro k hk
    have h1 := congrArg (fun l : List Sym5 => l[k]?) hslice
    rw [List.getElem?_eq_getElem (by simp [hk]), symSlice_getElem,
        List.getElem?_take_of_lt hk] at h1
    exact h1.symm
  rw [hs_get 0 (by omega), hs_get 1 (by omega), hs_get 2 (by omega),
      hs_get 3 (by omega), hs_get 4 (by omega)] at hs_ok
  simp only [Nat.add_zero] at hs_ok
  rw [h02, h24, h13] at hs_ok
  simp only [symOptEq, sym5_beq_self, hlen5, Bool.and_self] at hs_ok
  exact Bool.noConfusion hs_ok

/-! ## Section 4: Cut Rule (`L2`), Norm Lower Bound, and Bounded Overlap (`L8`) -/

/-- **Lemma `L2` (`isCutPairSym_iff_exists_blockStart`)**:
For every `t ≥ 1`, `(b5Sym (t - 1), b5Sym t)` is a cut pair iff `t` is a block boundary `blockStart a`. -/
theorem isCutPairSym_iff_exists_blockStart {t : ℕ} (ht : 1 ≤ t) :
    isCutPairSym (b5Sym (t - 1)) (b5Sym t) = true ↔ ∃ a : ℕ, blockStart a = t := by
  constructor
  · intro hcut
    rcases exists_sym_block_decomp t with ⟨p, o, ho, ht_eq, hbt, _⟩
    by_cases ho0 : o = 0
    · exact ⟨p, by omega⟩
    · exfalso
      have hlen2 : (fSym5 (b5Sym p)).length ≤ 2 := (fSym5_length_bounds (b5Sym p)).2
      have ho1 : o = 1 := by omega
      subst ho1
      have ht_prev : t - 1 = blockStart p + 0 := by omega
      have ho_zero : 0 < (fSym5 (b5Sym p)).length := by omega
      rw [ht_prev, b5Sym_blockStart_add p 0 ho_zero, hbt,
          fSym5_getElem_zero, fSym5_getElem_one] at hcut
      cases hsp : b5Sym p <;> rw [hsp] at ho hcut <;>
        first | exact Bool.noConfusion hcut | (simp [fSym5] at ho)
  · rintro ⟨a, rfl⟩
    have ha1 : 1 ≤ a := by
      by_contra ha0
      have : a = 0 := by omega
      subst this; simp at ht
    let p := a - 1
    have hap : a = p + 1 := by omega
    rw [hap]
    have hlen_p : 1 ≤ (fSym5 (b5Sym p)).length := (fSym5_length_bounds (b5Sym p)).1
    have hprev : blockStart (p + 1) - 1 = blockStart p + ((fSym5 (b5Sym p)).length - 1) := by
      rw [blockStart_succ_sym]; omega
    have ho_last : (fSym5 (b5Sym p)).length - 1 < (fSym5 (b5Sym p)).length := by omega
    have ho_first : 0 < (fSym5 (b5Sym (p + 1))).length := (fSym5_length_bounds (b5Sym (p + 1))).1
    have hcurr : blockStart (p + 1) = blockStart (p + 1) + 0 := by omega
    rw [hprev, b5Sym_blockStart_add p _ ho_last, fSym5_getElem_last]
    conv_lhs => arg 2; rw [hcurr, b5Sym_blockStart_add (p + 1) 0 ho_first, fSym5_getElem_zero]
    cases b5Sym p <;> cases b5Sym (p + 1) <;> rfl

theorem exists_cut_in_two {i : ℕ} (hi : 1 ≤ i) :
    (∃ a, blockStart a = i + 1) ∨ (∃ a, blockStart a = i + 2) := by
  rw [← isCutPairSym_iff_exists_blockStart (by omega : 1 ≤ i + 1),
      ← isCutPairSym_iff_exists_blockStart (by omega : 1 ≤ i + 2)]
  have h1 : i + 1 - 1 = i := by omega
  have h2 : i + 2 - 1 = i + 1 := by omega
  rw [h1, h2]
  have hor : ∀ x y z : Sym5, isCutPairSym x y = true ∨ isCutPairSym y z = true := by
    intro x y z; cases x <;> cases y <;> cases z <;> simp [isCutPairSym]
  exact hor (b5Sym i) (b5Sym (i + 1)) (b5Sym (i + 2))

/-- Liouville / norm lower bound on `lambda' u` for any non-empty word `u : List (Fin 5)` of
length `p ≥ 1`: `1 ≤ |lambda' u| * (2 * p)`. -/
theorem lambdaPrime_abs_mul_ge_one {u : List (Fin 5)} (hu : u ≠ []) :
    1 ≤ |lambda' u| * (2 * (u.length : ℝ)) := by
  have hp_pos : 1 ≤ u.length := List.length_pos_of_ne_nil hu
  -- Decompose lambdaQ u into integer coordinates a, b with |a| ≤ |u|, |b| ≤ |u|
  have hint_coords : ∀ w : List (Fin 5),
      ∃ a b : ℤ, |a| ≤ (w.length : ℤ) ∧ |b| ≤ (w.length : ℤ) ∧
        lambda' w = (a : ℝ) + (b : ℝ) * φ := by
    intro w
    induction w with
    | nil => exact ⟨0, 0, by simp, by simp, by simp⟩
    | cons c rest ih =>
      rcases ih with ⟨a, b, ha, hb, hval⟩
      rw [lambdaPrime_cons, hval]
      fin_cases c
      · refine ⟨a + 1, b, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; rw [abs_le] at ha ⊢; omega
        · simp only [List.length_cons]; rw [abs_le] at hb ⊢; omega
        · simp [l']; ring
      · refine ⟨a, b - 1, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; rw [abs_le] at ha ⊢; omega
        · simp only [List.length_cons]; rw [abs_le] at hb ⊢; omega
        · simp [l']; ring
      · refine ⟨a + 1, b + 1, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; rw [abs_le] at ha ⊢; omega
        · simp only [List.length_cons]; rw [abs_le] at hb ⊢; omega
        · simp [l']; ring
      · refine ⟨a, b - 1, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; rw [abs_le] at ha ⊢; omega
        · simp only [List.length_cons]; rw [abs_le] at hb ⊢; omega
        · simp [l']; ring
      · refine ⟨a, b - 1, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; rw [abs_le] at ha ⊢; omega
        · simp only [List.length_cons]; rw [abs_le] at hb ⊢; omega
        · simp [l']; ring
  rcases hint_coords u with ⟨a, b, ha_le, hb_le, hlu_eq⟩
  have hlu_ne : lambda' u ≠ 0 := lambdaPrime_ne_zero_of_ne_nil hu
  let N : ℤ := a ^ 2 + a * b - b ^ 2
  have hN_ne : N ≠ 0 := by
    intro h0
    have h4 : (2 * a + b) ^ 2 = 5 * b ^ 2 := by dsimp [N] at h0; linarith
    rcases int_sq_eq_five_mul_sq h4 with ⟨h1, hb0⟩
    have ha0 : a = 0 := by omega
    rw [ha0, hb0] at hlu_eq
    simp at hlu_eq
    exact hlu_ne hlu_eq
  have hN_ge1 : (1 : ℝ) ≤ |(N : ℝ)| := by
    have hZ : (1 : ℤ) ≤ |N| := Int.one_le_abs hN_ne
    exact_mod_cast hZ
  let conj : ℝ := (a : ℝ) + (b : ℝ) * (1 - φ)
  have hprod : lambda' u * conj = (N : ℝ) := by
    dsimp [conj, N]
    rw [hlu_eq]
    push_cast
    linear_combination -(b : ℝ) ^ 2 * phi_sq
  have hconj_le : |conj| ≤ 2 * (u.length : ℝ) := by
    have haR : |(a : ℝ)| ≤ (u.length : ℝ) := by exact_mod_cast ha_le
    have hbR : |(b : ℝ)| ≤ (u.length : ℝ) := by exact_mod_cast hb_le
    have hphi_sub : |1 - φ| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [one_lt_phi, phi_lt_two]
    calc
      |conj| = |(a : ℝ) + (b : ℝ) * (1 - φ)| := rfl
      _ ≤ |(a : ℝ)| + |(b : ℝ) * (1 - φ)| := abs_add_le _ _
      _ = |(a : ℝ)| + |(b : ℝ)| * |1 - φ| := by rw [abs_mul]
      _ ≤ (u.length : ℝ) + (u.length : ℝ) * 1 := by nlinarith [abs_nonneg (b : ℝ)]
      _ = 2 * (u.length : ℝ) := by ring
  calc
    (1 : ℝ) ≤ |(N : ℝ)| := hN_ge1
    _ = |lambda' u * conj| := by rw [← hprod]
    _ = |lambda' u| * |conj| := abs_mul _ _
    _ ≤ |lambda' u| * (2 * (u.length : ℝ)) :=
      mul_le_mul_of_nonneg_left hconj_le (abs_nonneg _)

/-- Universal overlap bound `maxOverlap p := 10 * p^3` (`L8`). -/
def maxOverlap (p : ℕ) : ℕ :=
  10 * p * p * p

/-- **Lemma `L8` (`overlap_le_maxOverlap`)**:
Every `p`-periodic stretch `[q, q + p + m)` (`p ≥ 1`) in `b5Sym` satisfies `m ≤ maxOverlap p`. -/
theorem overlap_le_maxOverlap {q p m : ℕ} (hp : 1 ≤ p)
    (hper : ∀ j < m, b5Sym (q + j) = b5Sym (q + j + p)) :
    m ≤ maxOverlap p := by
  by_contra hgt
  have hm_ge : (10 * p * p) * p ≤ m := by
    unfold maxOverlap at hgt; omega
  let K := 10 * p * p
  have hK_eq : K = 10 * p * p := rfl
  let u : List (Fin 5) := List.ofFn fun r : Fin p => b5 (q + r.val)
  have hu_len : u.length = p := by simp [u]
  have hu_ne : u ≠ [] := by intro h; rw [h] at hu_len; simp at hu_len; omega
  have hrep : ∀ c ≤ K, ∀ r (hr : r < u.length), b5 (q + c * p + r) = u[r] := by
    intro c
    induction c with
    | zero =>
      intro _ r hr
      simp [u]
    | succ c ih =>
      intro hc r hr
      have hc' : c ≤ K := by omega
      have hj_lt : c * p + r < m := by
        have h1 : (c + 1) * p ≤ K * p := Nat.mul_le_mul_right p hc
        rw [Nat.add_mul, one_mul, hK_eq] at h1
        omega
      have heq_sym := hper (c * p + r) hj_lt
      rw [b5Sym_eq_iff] at heq_sym
      have hidx : q + (c + 1) * p + r = q + (c * p + r) + p := by ring
      rw [hidx, ← heq_sym]
      have hidx2 : q + (c * p + r) = q + c * p + r := by omega
      rw [hidx2]
      exact ih hc' r hr
  have hsum_K : ∀ c ≤ K + 1,
      lambda' (prefixOf b5 (q + c * p)) = lambda' (prefixOf b5 q) + (c : ℝ) * lambda' u := by
    intro c
    induction c with
    | zero => simp
    | succ c ih =>
      intro hc
      have hstep := lambdaPrime_prefixOf_occ (p := q + c * p) (hrep c (by omega))
      rw [hu_len] at hstep
      have hidx : q + (c + 1) * p = q + c * p + p := by ring
      rw [hidx, hstep, ih (by omega)]
      push_cast; ring
  have hdiff := hsum_K (K + 1) (le_refl _)
  push_cast at hdiff
  have hw0 := (b5_codes_interval_translation q).1
  have hwK := (b5_codes_interval_translation (q + (K + 1) * p)).1
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hcu : φ ^ 3 = 2 * φ + 1 := phi_cube
  have hphi2 : φ < 2 := phi_lt_two
  have habs_lt : |(K + 1 : ℝ) * lambda' u| < 5 := by
    have hd : (K + 1 : ℝ) * lambda' u =
        lambda' (prefixOf b5 (q + (K + 1) * p)) - lambda' (prefixOf b5 q) := by linarith
    rw [hd, abs_lt]
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (K + 1 : ℝ))] at habs_lt
  have hnorm := lambdaPrime_abs_mul_ge_one hu_ne
  rw [hu_len] at hnorm
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hK_def : (K : ℝ) = 10 * (p : ℝ) * (p : ℝ) := by rw [hK_eq]; push_cast; ring
  have hprod_lt : (K + 1 : ℝ) * (|lambda' u| * (2 * (p : ℝ))) < 10 * (p : ℝ) := by
    have : (K + 1 : ℝ) * (|lambda' u| * (2 * (p : ℝ))) =
        ((K + 1 : ℝ) * |lambda' u|) * (2 * (p : ℝ)) := by ring
    rw [this]
    nlinarith
  have hprod_ge : (K + 1 : ℝ) * 1 ≤ (K + 1 : ℝ) * (|lambda' u| * (2 * (p : ℝ))) :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hp_sq : (p : ℝ) ≤ (p : ℝ) * (p : ℝ) := by nlinarith [hpR]
  nlinarith

/-! ## Section 5: Concrete Runs, Forward Map `Phi` (`L5–L6`), and Desubstitution (`L7`, `P9`) -/

/-- A maximal `p`-periodic run `[i, i + p + m)` in `b5Sym` starting at `i ≥ 10` (`p ≥ 1`). -/
def ConcreteRun (i p m : ℕ) : Prop :=
  10 ≤ i ∧ 1 ≤ p ∧
  (∀ j < m, b5Sym (i + j) = b5Sym (i + j + p)) ∧
  b5Sym (i - 1) ≠ b5Sym (i + p - 1) ∧
  b5Sym (i + p + m) ≠ b5Sym (i + m)

def symWord3At (q : ℕ) : Word3 :=
  ⟨b5Sym q, b5Sym (q + 1), b5Sym (q + 2)⟩

def runCtxState (i p m : ℕ) : CtxState :=
  { X := symWord3At (i - 3)
    Y := symWord3At (i + p - 3)
    S := symWord3At (i + p + m)
    T := symWord3At (i + m) }

def runSummary (i p m : ℕ) : SeedSummary :=
  { st := runCtxState i p m
    pu := parikhSym (symSlice i p)
    pz := parikhSym (symSlice (i + p) m) }

@[simp] theorem parikhSym_nil : parikhSym [] = Vec5Z.zero := rfl

theorem parikhSym_append (u v : List Sym5) :
    parikhSym (u ++ v) = Vec5Z.add (parikhSym u) (parikhSym v) := by
  induction u with
  | nil =>
    cases h : parikhSym v
    simp [h, parikhSym, Vec5Z.zero, Vec5Z.add]
  | cons a rest ih =>
    simp only [List.cons_append, parikhSym, ih]
    rcases Vec5Z.ofSym a with ⟨a0, a1, a2, a3, a4⟩
    rcases parikhSym rest with ⟨b0, b1, b2, b3, b4⟩
    rcases parikhSym v with ⟨c0, c1, c2, c3, c4⟩
    simp only [Vec5Z.add]
    congr 1 <;> ring

theorem parikhSym_morphSym5 (w : List Sym5) :
    parikhSym (morphSym5 w) = stepMZ (parikhSym w) := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    rw [morphSym5, parikhSym_append, ih, parikhSym]
    rcases parikhSym rest with ⟨r0, r1, r2, r3, r4⟩
    cases a <;>
      (simp only [fSym5, parikhSym, Vec5Z.ofSym, Vec5Z.zero, Vec5Z.add, stepMZ];
       congr 1 <;> ring)

theorem parikhSym_sum_eq_length (w : List Sym5) :
    (parikhSym w).sum = (w.length : ℤ) := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    simp only [parikhSym, List.length_cons]
    have hadd : ∀ x y : Vec5Z, (Vec5Z.add x y).sum = x.sum + y.sum := by
      rintro ⟨x0, x1, x2, x3, x4⟩ ⟨y0, y1, y2, y3, y4⟩
      simp only [Vec5Z.add, Vec5Z.sum]; ring
    rw [hadd, ih]
    have h1 : (Vec5Z.ofSym a).sum = 1 := by cases a <;> rfl
    rw [h1]; push_cast; ring

theorem runSummary_sums (i p m : ℕ) :
    (runSummary i p m).pu.sum = (p : ℤ) ∧ (runSummary i p m).pz.sum = (m : ℤ) := by
  simp [runSummary, parikhSym_sum_eq_length]

theorem parikhSym_shift_left {q p : ℕ} (hq : 1 ≤ q) (hp : 1 ≤ p)
    (heq : b5Sym (q - 1) = b5Sym (q - 1 + p)) :
    parikhSym (symSlice (q - 1) p) = parikhSym (symSlice q p) := by
  have h1 : symSlice (q - 1) p = [b5Sym (q - 1)] ++ symSlice q (p - 1) := by
    have hp_split : p = 1 + (p - 1) := by omega
    conv_lhs => rw [hp_split, symSlice_add]
    have hq1 : q - 1 + 1 = q := by omega
    rw [hq1]; rfl
  have h2 : symSlice q p = symSlice q (p - 1) ++ [b5Sym (q - 1 + p)] := by
    have hp_split : p = (p - 1) + 1 := by omega
    conv_lhs => rw [hp_split, symSlice_add]
    have hqp : q + (p - 1) = q - 1 + p := by omega
    rw [hqp]; rfl
  rw [h1, h2, parikhSym_append, parikhSym_append, heq]
  rcases parikhSym [b5Sym (q - 1 + p)] with ⟨a0, a1, a2, a3, a4⟩
  rcases parikhSym (symSlice q (p - 1)) with ⟨b0, b1, b2, b3, b4⟩
  simp only [Vec5Z.add]
  congr 1 <;> ring

theorem word3OfList_eq_of_ge3 {l : List Sym5} (hl : 3 ≤ l.length) :
    word3OfList l = ⟨l[0]'(by omega), l[1]'(by omega), l[2]'(by omega)⟩ := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at hl ⊢
  rfl

/-- Unpack the certified left-context step properties from `left_ctx_step_props` (`L4`). -/
theorem left_ctx_unpack {X Y : Word3}
    (hX : X.isValid = true) (hY : Y.isValid = true) (hne : X.c ≠ Y.c) :
    let eL := eLOf X.c Y.c
    let lam := eL.length
    let fX := morphSym5 X.toList
    let fY := morphSym5 Y.toList
    lam ≤ 1 ∧ 3 + lam ≤ fX.length ∧ 3 + lam ≤ fY.length ∧
    fX.drop (fX.length - lam) = eL ∧ fY.drop (fY.length - lam) = eL ∧
    fX[fX.length - lam - 1]? ≠ fY[fY.length - lam - 1]? := by
  dsimp only
  have hXm := (word3_isValid_iff_mem X).mp hX
  have hYm := (word3_isValid_iff_mem Y).mp hY
  have hall1 := left_ctx_step_props
  rw [allTR_eq_all] at hall1
  have hall2 := List.all_eq_true.mp hall1 X hXm
  rw [allTR_eq_all] at hall2
  have hpair := List.all_eq_true.mp hall2 Y hYm
  have hbeq_f : (!Sym5.beq X.c Y.c) = true := by
    cases h : Sym5.beq X.c Y.c
    · rfl
    · exact absurd ((Sym5.beq_iff_eq _ _).mp h) hne
  simp only [hbeq_f, ↓reduceIte, Bool.and_eq_true, Nat.ble_eq, hasLenAtLeast_iff,
    decide_eq_true_eq] at hpair
  rcases hpair with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, _⟩, _⟩, _⟩
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro heq_opt
  rw [heq_opt] at h6
  have hltX : (morphSym5 X.toList).length - (eLOf X.c Y.c).length - 1 <
      (morphSym5 X.toList).length := by omega
  have hltY : (morphSym5 Y.toList).length - (eLOf X.c Y.c).length - 1 <
      (morphSym5 Y.toList).length := by omega
  rw [List.getElem?_eq_getElem hltY] at h6
  simp only [symOptNe, sym5_beq_self, Bool.not_true] at h6
  exact Bool.noConfusion h6

/-- Unpack the certified right-context step properties from `right_ctx_step_props` (`L4`). -/
theorem right_ctx_unpack {S T : Word3}
    (hS : S.isValid = true) (hT : T.isValid = true) (hne : S.a ≠ T.a) :
    let eR := eROf S.a T.a
    let rho := eR.length
    let fS := morphSym5 S.toList
    let fT := morphSym5 T.toList
    rho ≤ 1 ∧ 3 + rho ≤ fS.length ∧ 3 + rho ≤ fT.length ∧
    fS.take rho = eR ∧ fT.take rho = eR ∧
    fS[rho]? ≠ fT[rho]? := by
  dsimp only
  have hSm := (word3_isValid_iff_mem S).mp hS
  have hTm := (word3_isValid_iff_mem T).mp hT
  have hall1 := right_ctx_step_props
  rw [allTR_eq_all] at hall1
  have hall2 := List.all_eq_true.mp hall1 S hSm
  rw [allTR_eq_all] at hall2
  have hpair := List.all_eq_true.mp hall2 T hTm
  have hbeq_f : (!Sym5.beq S.a T.a) = true := by
    cases h : Sym5.beq S.a T.a
    · rfl
    · exact absurd ((Sym5.beq_iff_eq _ _).mp h) hne
  simp only [hbeq_f, ↓reduceIte, Bool.and_eq_true, Nat.ble_eq, hasLenAtLeast_iff,
    decide_eq_true_eq] at hpair
  rcases hpair with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, _⟩, _⟩, _⟩
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro heq_opt
  rw [heq_opt] at h6
  have hltT : (eROf S.a T.a).length < (morphSym5 T.toList).length := by omega
  rw [List.getElem?_eq_getElem hltT] at h6
  simp only [symOptNe, sym5_beq_self, Bool.not_true] at h6
  exact Bool.noConfusion h6

theorem last3_take_sub_eq {L : List Sym5} {lam q : ℕ}
    (hlen : 3 + lam ≤ L.length)
    (hat : ∀ k (hk : k < L.length), L[k] = b5Sym (q + k)) :
    last3 (L.take (L.length - lam)) = symWord3At (q + L.length - lam - 3) := by
  unfold last3
  have htl : (L.take (L.length - lam)).length = L.length - lam := by
    rw [List.length_take]; omega
  have hdl : 3 ≤ ((L.take (L.length - lam)).drop ((L.take (L.length - lam)).length - 3)).length := by
    rw [List.length_drop, htl]; omega
  rw [word3OfList_eq_of_ge3 hdl]
  simp only [List.getElem_drop, List.getElem_take, htl, symWord3At]
  rw [hat _ (by omega), hat _ (by omega), hat _ (by omega)]
  congr 1 <;> (congr 1; omega)

theorem first3_drop_eq {L : List Sym5} {rho q : ℕ}
    (hlen : 3 + rho ≤ L.length)
    (hat : ∀ k (hk : k < L.length), L[k] = b5Sym (q + k)) :
    first3 (L.drop rho) = symWord3At (q + rho) := by
  unfold first3
  have hdl : 3 ≤ (L.drop rho).length := by rw [List.length_drop]; omega
  rw [word3OfList_eq_of_ge3 hdl]
  simp only [List.getElem_drop, symWord3At]
  rw [hat _ (by omega), hat _ (by omega), hat _ (by omega)]
  rfl

theorem vec5Z_add_add_comm (x y z : Vec5Z) :
    Vec5Z.add (Vec5Z.add x y) z = Vec5Z.add y (Vec5Z.add x z) := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  rcases y with ⟨y0, y1, y2, y3, y4⟩
  rcases z with ⟨z0, z1, z2, z3, z4⟩
  simp only [Vec5Z.add]
  congr 1 <;> ring

/-- **Lemmas `L5` & `L6` (`concreteRun_phi_step`)**:
Forward action of `Phi` on any `ConcreteRun i p m` (`m ≥ 0`), producing `ConcreteRun i' p' m'`
covering `[blockStart i, blockStart (i + p + m))` and matching `stepSummary (runSummary i p m)`. -/
theorem concreteRun_phi_step {i p m : ℕ} (hrun : ConcreteRun i p m) :
    let st := runCtxState i p m
    let eL := eLOf st.X.c st.Y.c
    let eR := eROf st.S.a st.T.a
    let lam := eL.length
    let rho := eR.length
    let i' := blockStart i - lam
    let p' := blockStart (i + p) - blockStart i
    let m' := lam + (blockStart (i + p + m) - blockStart (i + p)) + rho
    ConcreteRun i' p' m' ∧
    i' ≤ blockStart i ∧
    blockStart (i + p + m) ≤ i' + p' + m' ∧
    runSummary i' p' m' = stepSummary (runSummary i p m) := by
  rcases hrun with ⟨hi10, hp1, hper, hmisL, hmisR⟩
  intro st eL eR lam rho i' p' m'
  have hstX : st.X = symWord3At (i - 3) := rfl
  have hstY : st.Y = symWord3At (i + p - 3) := rfl
  have hstS : st.S = symWord3At (i + p + m) := rfl
  have hstT : st.T = symWord3At (i + m) := rfl
  have heL_def : eL = eLOf st.X.c st.Y.c := rfl
  have heR_def : eR = eROf st.S.a st.T.a := rfl
  have hlam_def : lam = eL.length := rfl
  have hrho_def : rho = eR.length := rfl
  have hi'_def : i' = blockStart i - lam := rfl
  have hp'_def : p' = blockStart (i + p) - blockStart i := rfl
  let m_mid := blockStart (i + p + m) - blockStart (i + p)
  have hm_mid_def : m_mid = blockStart (i + p + m) - blockStart (i + p) := rfl
  have hm'_def : m' = lam + m_mid + rho := rfl
  have hX_val : st.X.isValid = true := symWord3At_isValid (i - 3)
  have hY_val : st.Y.isValid = true := symWord3At_isValid (i + p - 3)
  have hS_val : st.S.isValid = true := symWord3At_isValid (i + p + m)
  have hT_val : st.T.isValid = true := symWord3At_isValid (i + m)
  have hXc_eq : st.X.c = b5Sym (i - 1) := by
    rw [hstX]; dsimp [symWord3At]; congr 1; omega
  have hYc_eq : st.Y.c = b5Sym (i + p - 1) := by
    rw [hstY]; dsimp [symWord3At]; congr 1; omega
  have hSa_eq : st.S.a = b5Sym (i + p + m) := rfl
  have hTa_eq : st.T.a = b5Sym (i + m) := rfl
  have hl_upk := left_ctx_unpack hX_val hY_val (by rw [hXc_eq, hYc_eq]; exact hmisL)
  dsimp only at hl_upk
  rw [← heL_def, ← hlam_def] at hl_upk
  rcases hl_upk with ⟨hlam1, hfX_len, hfY_len, hfX_drop, hfY_drop, hfXY_mis⟩
  have hr_upk := right_ctx_unpack hS_val hT_val (by rw [hSa_eq, hTa_eq]; exact hmisR)
  dsimp only at hr_upk
  rw [← heR_def, ← hrho_def] at hr_upk
  rcases hr_upk with ⟨hrho1, hfS_len, hfT_len, hfS_take, hfT_take, hfST_mis⟩
  -- Relate morphSym5 of X, Y, S, T to symSlice in b5Sym
  have hword3_slice : ∀ q : ℕ, (symWord3At q).toList = symSlice q 3 := fun _ => rfl
  have hfX_slice : morphSym5 st.X.toList =
      symSlice (blockStart (i - 3)) (blockStart i - blockStart (i - 3)) := by
    have h := symSlice_blockStart (i - 3) i (by omega)
    have hsub : i - (i - 3) = 3 := by omega
    rw [hsub, ← hword3_slice, ← hstX] at h
    exact h.symm
  have hfY_slice : morphSym5 st.Y.toList =
      symSlice (blockStart (i + p - 3)) (blockStart (i + p) - blockStart (i + p - 3)) := by
    have h := symSlice_blockStart (i + p - 3) (i + p) (by omega)
    have hsub : i + p - (i + p - 3) = 3 := by omega
    rw [hsub, ← hword3_slice, ← hstY] at h
    exact h.symm
  have hfS_slice : morphSym5 st.S.toList =
      symSlice (blockStart (i + p + m)) (blockStart (i + p + m + 3) - blockStart (i + p + m)) := by
    have h := symSlice_blockStart (i + p + m) (i + p + m + 3) (by omega)
    have hsub : i + p + m + 3 - (i + p + m) = 3 := by omega
    rw [hsub, ← hword3_slice, ← hstS] at h
    exact h.symm
  have hfT_slice : morphSym5 st.T.toList =
      symSlice (blockStart (i + m)) (blockStart (i + m + 3) - blockStart (i + m)) := by
    have h := symSlice_blockStart (i + m) (i + m + 3) (by omega)
    have hsub : i + m + 3 - (i + m) = 3 := by omega
    rw [hsub, ← hword3_slice, ← hstT] at h
    exact h.symm
  -- Inner overlap equality from symSlice i m = symSlice (i + p) m
  have hz_eq : symSlice i m = symSlice (i + p) m := by
    apply List.ext_getElem
    · simp
    · intro j hj1 hj2
      simp only [symSlice_length] at hj1
      rw [symSlice_getElem, symSlice_getElem]
      have hidx : i + p + j = i + j + p := by omega
      rw [hidx]
      exact hper j hj1
  have hfz_eq : symSlice (blockStart i) (blockStart (i + m) - blockStart i) =
      symSlice (blockStart (i + p)) m_mid := by
    have h1 := symSlice_blockStart i (i + m) (by omega)
    have h2 := symSlice_blockStart (i + p) (i + p + m) (by omega)
    simp only [Nat.add_sub_cancel_left] at h1 h2
    rw [h1, ← hm_mid_def] at *
    rw [h2, hz_eq]
  have hfz_len : blockStart (i + m) - blockStart i = m_mid := by
    have := congrArg List.length hfz_eq
    simpa using this
  have hbs_le_i : i + 1 ≤ blockStart i := blockStart_ge_succ_of_pos (by omega)
  have hbs_mono_ip : blockStart i < blockStart (i + p) :=
    blockStart_strictMono (by omega)
  have hbs_mono_im : blockStart i ≤ blockStart (i + m) :=
    blockStart_strictMono.monotone (by omega)
  have hbs_mono_ipm : blockStart (i + p) ≤ blockStart (i + p + m) :=
    blockStart_strictMono.monotone (by omega)
  have hbs_X : blockStart (i - 3) ≤ blockStart i :=
    blockStart_strictMono.monotone (by omega)
  have hbs_Y : blockStart (i + p - 3) ≤ blockStart (i + p) :=
    blockStart_strictMono.monotone (by omega)
  have hfX_len_eq : (morphSym5 st.X.toList).length = blockStart i - blockStart (i - 3) := by
    rw [hfX_slice, symSlice_length]
  have hfY_len_eq : (morphSym5 st.Y.toList).length = blockStart (i + p) - blockStart (i + p - 3) := by
    rw [hfY_slice, symSlice_length]
  have hfS_len_eq : (morphSym5 st.S.toList).length =
      blockStart (i + p + m + 3) - blockStart (i + p + m) := by
    rw [hfS_slice, symSlice_length]
  have hfT_len_eq : (morphSym5 st.T.toList).length =
      blockStart (i + m + 3) - blockStart (i + m) := by
    rw [hfT_slice, symSlice_length]
  -- Helper indexing into fX, fY, fS, fT
  have hfX_at : ∀ k (hk : k < (morphSym5 st.X.toList).length),
      (morphSym5 st.X.toList)[k] = b5Sym (blockStart (i - 3) + k) := by
    intro k hk
    have h := congrArg (fun l : List Sym5 => l[k]?) hfX_slice
    rw [List.getElem?_eq_getElem hk,
        List.getElem?_eq_getElem (by simp; omega), Option.some.injEq, symSlice_getElem] at h
    exact h
  have hfY_at : ∀ k (hk : k < (morphSym5 st.Y.toList).length),
      (morphSym5 st.Y.toList)[k] = b5Sym (blockStart (i + p - 3) + k) := by
    intro k hk
    have h := congrArg (fun l : List Sym5 => l[k]?) hfY_slice
    rw [List.getElem?_eq_getElem hk,
        List.getElem?_eq_getElem (by simp; omega), Option.some.injEq, symSlice_getElem] at h
    exact h
  have hfS_at : ∀ k (hk : k < (morphSym5 st.S.toList).length),
      (morphSym5 st.S.toList)[k] = b5Sym (blockStart (i + p + m) + k) := by
    intro k hk
    have h := congrArg (fun l : List Sym5 => l[k]?) hfS_slice
    rw [List.getElem?_eq_getElem hk,
        List.getElem?_eq_getElem (by simp; omega), Option.some.injEq, symSlice_getElem] at h
    exact h
  have hfT_at : ∀ k (hk : k < (morphSym5 st.T.toList).length),
      (morphSym5 st.T.toList)[k] = b5Sym (blockStart (i + m) + k) := by
    intro k hk
    have h := congrArg (fun l : List Sym5 => l[k]?) hfT_slice
    rw [List.getElem?_eq_getElem hk,
        List.getElem?_eq_getElem (by simp; omega), Option.some.injEq, symSlice_getElem] at h
    exact h
  -- Left & right single-letter extensions match eL and eR
  have heL_slice : symSlice (blockStart i - lam) lam = eL ∧
      symSlice (blockStart (i + p) - lam) lam = eL := by
    constructor
    · rw [← hfX_drop]
      apply List.ext_getElem
      · simp; omega
      · intro k hk1 hk2
        rw [symSlice_length] at hk1
        rw [symSlice_getElem, List.getElem_drop, hfX_at _ (by omega)]
        congr 1; omega
    · rw [← hfY_drop]
      apply List.ext_getElem
      · simp; omega
      · intro k hk1 hk2
        rw [symSlice_length] at hk1
        rw [symSlice_getElem, List.getElem_drop, hfY_at _ (by omega)]
        congr 1; omega
  have heR_slice : symSlice (blockStart (i + p + m)) rho = eR ∧
      symSlice (blockStart (i + m)) rho = eR := by
    constructor
    · rw [← hfS_take]
      apply List.ext_getElem
      · simp; omega
      · intro k hk1 hk2
        rw [symSlice_length] at hk1
        rw [symSlice_getElem, List.getElem_take, hfS_at _ (by omega)]
    · rw [← hfT_take]
      apply List.ext_getElem
      · simp; omega
      · intro k hk1 hk2
        rw [symSlice_length] at hk1
        rw [symSlice_getElem, List.getElem_take, hfT_at _ (by omega)]
  -- Full m'-slice equality between i' and i' + p'
  have hi'_p' : i' + p' = blockStart (i + p) - lam := by omega
  have hm'_slice1 : symSlice i' m' =
      eL ++ symSlice (blockStart i) m_mid ++ eR := by
    rw [hm'_def, symSlice_add, symSlice_add]
    have h1 : i' + lam = blockStart i := by omega
    have h2 : i' + (lam + m_mid) = blockStart (i + m) := by omega
    rw [h2, h1, hi'_def, heL_slice.1, heR_slice.2]
  have hm'_slice2 : symSlice (i' + p') m' =
      eL ++ symSlice (blockStart (i + p)) m_mid ++ eR := by
    rw [hi'_p', hm'_def, symSlice_add, symSlice_add]
    have h1 : blockStart (i + p) - lam + lam = blockStart (i + p) := by omega
    have h2 : blockStart (i + p) - lam + (lam + m_mid) = blockStart (i + p + m) := by omega
    rw [h2, h1, heL_slice.2, heR_slice.1]
  have hfz_eq' : symSlice (blockStart i) m_mid = symSlice (blockStart (i + p)) m_mid := by
    conv_lhs => rw [← hfz_len]
    exact hfz_eq
  have hm'_slices_eq : symSlice i' m' = symSlice (i' + p') m' := by
    rw [hm'_slice1, hm'_slice2, hfz_eq']
  -- Prove ConcreteRun i' p' m'
  have hrun' : ConcreteRun i' p' m' := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro j hj
      have h := congrArg (fun l : List Sym5 => l[j]?) hm'_slices_eq
      rw [List.getElem?_eq_getElem (by simp [hj]),
          List.getElem?_eq_getElem (by simp [hj]),
          Option.some.injEq, symSlice_getElem, symSlice_getElem] at h
      have hidx : i' + p' + j = i' + j + p' := by omega
      rwa [hidx] at h
    · intro heqL
      apply hfXY_mis
      have hkX : (morphSym5 st.X.toList).length - lam - 1 < (morphSym5 st.X.toList).length := by
        omega
      have hkY : (morphSym5 st.Y.toList).length - lam - 1 < (morphSym5 st.Y.toList).length := by
        omega
      rw [List.getElem?_eq_getElem hkX, List.getElem?_eq_getElem hkY, Option.some.injEq,
          hfX_at _ hkX, hfY_at _ hkY]
      have hx_idx : blockStart (i - 3) + ((morphSym5 st.X.toList).length - lam - 1) = i' - 1 := by
        omega
      have hy_idx : blockStart (i + p - 3) + ((morphSym5 st.Y.toList).length - lam - 1) =
          i' + p' - 1 := by omega
      rw [hx_idx, hy_idx]
      exact heqL
    · intro heqR
      apply hfST_mis
      have hkS : rho < (morphSym5 st.S.toList).length := by omega
      have hkT : rho < (morphSym5 st.T.toList).length := by omega
      rw [List.getElem?_eq_getElem hkS, List.getElem?_eq_getElem hkT, Option.some.injEq,
          hfS_at _ hkS, hfT_at _ hkT]
      have hs_idx : blockStart (i + p + m) + rho = i' + p' + m' := by omega
      have ht_idx : blockStart (i + m) + rho = i' + m' := by omega
      rw [hs_idx, ht_idx]
      exact heqR
  refine ⟨hrun', by omega, by omega, ?_⟩
  -- Prove runSummary i' p' m' = stepSummary (runSummary i p m)
  have hX'_eq : symWord3At (i' - 3) = nextLeftCtx st.X lam := by
    unfold nextLeftCtx; dsimp only
    rw [last3_take_sub_eq hfX_len hfX_at, hfX_len_eq]
    exact congrArg symWord3At (by omega)
  have hY'_eq : symWord3At (i' + p' - 3) = nextLeftCtx st.Y lam := by
    unfold nextLeftCtx; dsimp only
    rw [last3_take_sub_eq hfY_len hfY_at, hfY_len_eq]
    exact congrArg symWord3At (by omega)
  have hS'_eq : symWord3At (i' + p' + m') = nextRightCtx st.S rho := by
    unfold nextRightCtx; dsimp only
    rw [first3_drop_eq hfS_len hfS_at]
    exact congrArg symWord3At (by omega)
  have hT'_eq : symWord3At (i' + m') = nextRightCtx st.T rho := by
    unfold nextRightCtx; dsimp only
    rw [first3_drop_eq hfT_len hfT_at]
    exact congrArg symWord3At (by omega)
  have hpu'_eq : parikhSym (symSlice i' p') = stepMZ (parikhSym (symSlice i p)) := by
    have hfu : symSlice (blockStart i) p' = morphSym5 (symSlice i p) := by
      have h := symSlice_blockStart i (i + p) (by omega)
      rw [Nat.add_sub_cancel_left, ← hp'_def] at h
      exact h
    have h01 : lam = 0 ∨ lam = 1 := by omega
    rcases h01 with h0 | h1
    · have hi'_eq : i' = blockStart i := by omega
      rw [hi'_eq, hfu, parikhSym_morphSym5]
    · have hi'_eq : i' = blockStart i - 1 := by omega
      have hmatch_end : b5Sym (blockStart i - 1) = b5Sym (blockStart i - 1 + p') := by
        have hm0 : 0 < m' := by omega
        have hp0 := hrun'.2.2.1 0 hm0
        simpa [hi'_eq] using hp0
      rw [hi'_eq, parikhSym_shift_left (by omega) (by omega) hmatch_end, hfu, parikhSym_morphSym5]
  have hpz'_eq : parikhSym (symSlice (i' + p') m') =
      Vec5Z.add (stepMZ (parikhSym (symSlice (i + p) m))) (parikhSym (eL ++ eR)) := by
    rw [hm'_slice2, parikhSym_append, parikhSym_append, parikhSym_append]
    have hfz_m : symSlice (blockStart (i + p)) m_mid = morphSym5 (symSlice (i + p) m) := by
      have h := symSlice_blockStart (i + p) (i + p + m) (by omega)
      rw [Nat.add_sub_cancel_left, ← hm_mid_def] at h
      exact h
    rw [hfz_m, parikhSym_morphSym5]
    exact vec5Z_add_add_comm _ _ _
  unfold runSummary stepSummary phiStepCtx runCtxState
  dsimp only
  rw [← hstX, ← hstY, ← hstS, ← hstT, ← heL_def, ← heR_def, ← hlam_def, ← hrho_def]
  rw [hX'_eq, hY'_eq, hS'_eq, hT'_eq, hpu'_eq, hpz'_eq]

/-- **Union Lemma (`concreteRun_unique_of_overlap_p`)**:
Two maximal `p`-periodic runs sharing a common interval `[t, t + p)` of length `p` are identical. -/
theorem concreteRun_unique_of_overlap_p {i₁ m₁ i₂ m₂ p t : ℕ}
    (hr1 : ConcreteRun i₁ p m₁) (hr2 : ConcreteRun i₂ p m₂)
    (ht1 : i₁ ≤ t ∧ t + p ≤ i₁ + p + m₁)
    (ht2 : i₂ ≤ t ∧ t + p ≤ i₂ + p + m₂) :
    i₁ = i₂ ∧ m₁ = m₂ := by
  rcases hr1 with ⟨hi1, hp1, hper1, hmisL1, hmisR1⟩
  rcases hr2 with ⟨hi2, _, hper2, hmisL2, hmisR2⟩
  have hn12 : ¬ (i₂ < i₁) := by
    intro hlt
    have hj : i₁ - 1 - i₂ < m₂ := by omega
    have hp := hper2 (i₁ - 1 - i₂) hj
    have hidx1 : i₂ + (i₁ - 1 - i₂) = i₁ - 1 := by omega
    have hidx2 : i₂ + (i₁ - 1 - i₂) + p = i₁ + p - 1 := by omega
    rw [hidx2, hidx1] at hp
    exact hmisL1 hp
  have hn21 : ¬ (i₁ < i₂) := by
    intro hlt
    have hj : i₂ - 1 - i₁ < m₁ := by omega
    have hp := hper1 (i₂ - 1 - i₁) hj
    have hidx1 : i₁ + (i₂ - 1 - i₁) = i₂ - 1 := by omega
    have hidx2 : i₁ + (i₂ - 1 - i₁) + p = i₂ + p - 1 := by omega
    rw [hidx2, hidx1] at hp
    exact hmisL2 hp
  have hi_eq : i₁ = i₂ := by omega
  subst hi_eq
  have hm12 : ¬ (m₁ < m₂) := by
    intro hlt
    have h := (hper2 m₁ hlt).symm
    have hidx : i₁ + m₁ + p = i₁ + p + m₁ := by omega
    rw [hidx] at h
    exact hmisR1 h
  have hm21 : ¬ (m₂ < m₁) := by
    intro hlt
    have h := (hper1 m₂ hlt).symm
    have hidx : i₁ + m₂ + p = i₁ + p + m₂ := by omega
    rw [hidx] at h
    exact hmisR2 h
  exact ⟨rfl, by omega⟩

/-- Helper: extend any `p`-periodic stretch `[a, a + p)` (`a ≥ maxOverlap p + 20`) to a maximal
`ConcreteRun alpha p r` containing `[a, a + p)`. -/
theorem extend_to_concreteRun {a p : ℕ} (hp : 1 ≤ p) (ha : maxOverlap p + 20 ≤ a) :
    ∃ alpha r : ℕ,
      ConcreteRun alpha p r ∧
      alpha ≤ a ∧ a + p ≤ alpha + p + r := by
  -- Left extension: minimal alpha ≤ a such that ∀ j < a - alpha, b5Sym (alpha + j) = b5Sym (alpha + j + p)
  have hex_left : ∃ alpha : ℕ, alpha ≤ a ∧
      ∀ j < a - alpha, b5Sym (alpha + j) = b5Sym (alpha + j + p) :=
    ⟨a, le_refl a, fun _ hj => by omega⟩
  classical
  let alpha := Nat.find hex_left
  rcases Nat.find_spec hex_left with ⟨halpha_le, hleft_per⟩
  have hleft_len : a - alpha ≤ maxOverlap p :=
    overlap_le_maxOverlap hp hleft_per
  have halpha_ge10 : 10 ≤ alpha := by omega
  have hmisL : b5Sym (alpha - 1) ≠ b5Sym (alpha + p - 1) := by
    intro heq
    have hmin := Nat.find_min hex_left (by omega : alpha - 1 < alpha)
    apply hmin
    refine ⟨by omega, fun j hj => ?_⟩
    by_cases hj0 : j = 0
    · subst hj0
      have hidx : alpha - 1 + 0 + p = alpha + p - 1 := by omega
      rw [hidx, Nat.add_zero]
      exact heq
    · have hprev := hleft_per (j - 1) (by omega)
      have h1 : alpha - 1 + j = alpha + (j - 1) := by omega
      have h2 : alpha - 1 + j + p = alpha + (j - 1) + p := by omega
      rwa [h2, h1]
  -- Right extension: first mismatch offset r ≥ a - alpha (bounded above by maxOverlap p + 1)
  have hex_misR : ∃ r : ℕ, b5Sym (alpha + r) ≠ b5Sym (alpha + r + p) := by
    by_contra hno
    have hall : ∀ j < maxOverlap p + 1, b5Sym (alpha + j) = b5Sym (alpha + j + p) := by
      intro j _
      by_contra hne
      exact hno ⟨j, hne⟩
    have hle := overlap_le_maxOverlap hp hall
    omega
  let r := Nat.find hex_misR
  have hr_mis : b5Sym (alpha + r) ≠ b5Sym (alpha + r + p) := Nat.find_spec hex_misR
  have hr_per : ∀ j < r, b5Sym (alpha + j) = b5Sym (alpha + j + p) := by
    intro j hj
    by_contra hne
    exact Nat.find_min hex_misR hj hne
  have ha_sub_le_r : a - alpha ≤ r := by
    by_contra hgt
    exact hr_mis (hleft_per r (by omega))
  have hr_mis' : b5Sym (alpha + p + r) ≠ b5Sym (alpha + r) := by
    have hidx : alpha + p + r = alpha + r + p := by omega
    rw [hidx]
    exact hr_mis.symm
  exact ⟨alpha, r, ⟨halpha_ge10, hp, hr_per, hmisL, hr_mis'⟩, halpha_le, by omega⟩

/-- **Lemma `L7` (`concreteRun_desubst`)**:
Every `ConcreteRun i p m` with `m ≥ 3` comes via `stepSummary` from a `ConcreteRun alpha p_Y r`
with strictly smaller period `p_Y < p` and `r ≥ 1`. -/
theorem concreteRun_desubst {i p m : ℕ} (hrun : ConcreteRun i p m) (hm3 : 3 ≤ m) :
    ∃ alpha p_Y r : ℕ,
      ConcreteRun alpha p_Y r ∧
      p_Y < p ∧
      1 ≤ r ∧
      stepSummary (runSummary alpha p_Y r) = runSummary i p m := by
  rcases hrun with ⟨hi10, hp1, hper, hmisL, hmisR⟩
  -- Step 1: p ≥ 3 (p ≠ 1 by b5Sym_ne_succ, p ≠ 2 by no_sym_period2_len5)
  have hp_ge3 : 3 ≤ p := by
    by_contra hlt3
    have hp12 : p = 1 ∨ p = 2 := by omega
    rcases hp12 with rfl | rfl
    · have h0 := hper 0 (by omega)
      simp at h0
      exact b5Sym_ne_succ i h0
    · exact no_sym_period2_len5 i ⟨hper 0 (by omega), hper 1 (by omega), hper 2 (by omega)⟩
  -- Step 2: Move the context+run window [i - 3, i + p + m + 3) to a large position q₀
  let B := 2 * (maxOverlap p + 30)
  have hB_def : B = 2 * (maxOverlap p + 30) := rfl
  rcases exists_sym_occ_ge (i - 3) (p + m + 6) B with ⟨q₀, hB_le, hslice_eq⟩
  let i₁ := q₀ + 3
  have hi1_def : i₁ = q₀ + 3 := rfl
  have hget_shift : ∀ k (hk : k < p + m + 6), b5Sym (q₀ + k) = b5Sym (i - 3 + k) := by
    intro k hk
    have h := congrArg (fun l : List Sym5 => l[k]?) hslice_eq
    rw [List.getElem?_eq_getElem (by simp [hk]),
        List.getElem?_eq_getElem (by simp [hk]),
        Option.some.injEq, symSlice_getElem, symSlice_getElem] at h
    exact h
  have hrun1 : ConcreteRun i₁ p m := by
    refine ⟨by omega, hp1, ?_, ?_, ?_⟩
    · intro j hj
      have h1 := hget_shift (3 + j) (by omega)
      have h2 := hget_shift (3 + j + p) (by omega)
      have hi1_j : i₁ + j = q₀ + (3 + j) := by omega
      have hi1_jp : i₁ + j + p = q₀ + (3 + j + p) := by omega
      have hi_j : i - 3 + (3 + j) = i + j := by omega
      have hi_jp : i - 3 + (3 + j + p) = i + j + p := by omega
      rw [hi1_jp, hi1_j, h1, h2, hi_j, hi_jp]
      exact hper j hj
    · have h1 := hget_shift 2 (by omega)
      have h2 := hget_shift (2 + p) (by omega)
      have hi1_1 : i₁ - 1 = q₀ + 2 := by omega
      have hi1_p1 : i₁ + p - 1 = q₀ + (2 + p) := by omega
      have hi_1 : i - 3 + 2 = i - 1 := by omega
      have hi_p1 : i - 3 + (2 + p) = i + p - 1 := by omega
      rw [hi1_p1, hi1_1, h1, h2, hi_1, hi_p1]
      exact hmisL
    · have h1 := hget_shift (3 + p + m) (by omega)
      have h2 := hget_shift (3 + m) (by omega)
      have hi1_pm : i₁ + p + m = q₀ + (3 + p + m) := by omega
      have hi1_m : i₁ + m = q₀ + (3 + m) := by omega
      have hi_pm : i - 3 + (3 + p + m) = i + p + m := by omega
      have hi_m : i - 3 + (3 + m) = i + m := by omega
      rw [hi1_pm, hi1_m, h1, h2, hi_pm, hi_m]
      exact hmisR
  have hsum1 : runSummary i₁ p m = runSummary i p m := by
    have hw3 : ∀ off (hoff : off + 3 ≤ p + m + 6),
        symWord3At (q₀ + off) = symWord3At (i - 3 + off) := by
      intro off hoff
      simp only [symWord3At]
      have h0 : b5Sym (q₀ + off) = b5Sym (i - 3 + off) := hget_shift off (by omega)
      have h1 : b5Sym (q₀ + off + 1) = b5Sym (i - 3 + off + 1) := by
        simpa [Nat.add_assoc] using hget_shift (off + 1) (by omega)
      have h2 : b5Sym (q₀ + off + 2) = b5Sym (i - 3 + off + 2) := by
        simpa [Nat.add_assoc] using hget_shift (off + 2) (by omega)
      rw [h2, h1, h0]
    have hu_eq : symSlice i₁ p = symSlice i p := by
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        simp only [symSlice_length] at hk1
        rw [symSlice_getElem, symSlice_getElem]
        have h := hget_shift (3 + k) (by omega)
        have h1 : i₁ + k = q₀ + (3 + k) := by omega
        have h2 : i - 3 + (3 + k) = i + k := by omega
        rw [h1, h, h2]
    have hz_eq : symSlice (i₁ + p) m = symSlice (i + p) m := by
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        simp only [symSlice_length] at hk1
        rw [symSlice_getElem, symSlice_getElem]
        have h := hget_shift (3 + p + k) (by omega)
        have h1 : i₁ + p + k = q₀ + (3 + p + k) := by omega
        have h2 : i - 3 + (3 + p + k) = i + p + k := by omega
        rw [h1, h, h2]
    unfold runSummary runCtxState
    have hx : symWord3At (i₁ - 3) = symWord3At (i - 3) := by
      simpa [i₁] using hw3 0 (by omega)
    have hy : symWord3At (i₁ + p - 3) = symWord3At (i + p - 3) := by
      have h := hw3 p (by omega)
      have h1 : q₀ + p = i₁ + p - 3 := by omega
      have h2 : i - 3 + p = i + p - 3 := by omega
      rwa [h1, h2] at h
    have hs : symWord3At (i₁ + p + m) = symWord3At (i + p + m) := by
      have h := hw3 (3 + p + m) (by omega)
      have h1 : q₀ + (3 + p + m) = i₁ + p + m := by omega
      have h2 : i - 3 + (3 + p + m) = i + p + m := by omega
      rwa [h1, h2] at h
    have ht : symWord3At (i₁ + m) = symWord3At (i + m) := by
      have h := hw3 (3 + m) (by omega)
      have h1 : q₀ + (3 + m) = i₁ + m := by omega
      have h2 : i - 3 + (3 + m) = i + m := by omega
      rwa [h1, h2] at h
    rw [hx, hy, hs, ht, hu_eq, hz_eq]
  -- Step 3: Find a block boundary t₁ ∈ {i₁ + 1, i₁ + 2} and transfer by +p to t₁ + p = blockStart a'
  have hex_t1 : ∃ t₁ a : ℕ, (t₁ = i₁ + 1 ∨ t₁ = i₁ + 2) ∧ blockStart a = t₁ := by
    rcases exists_cut_in_two (by omega : 1 ≤ i₁) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨i₁ + 1, a, Or.inl rfl, ha⟩
    · exact ⟨i₁ + 2, a, Or.inr rfl, ha⟩
  rcases hex_t1 with ⟨t₁, a, ht1_cases, ha_eq⟩
  have ht1_cut : isCutPairSym (b5Sym (t₁ - 1)) (b5Sym t₁) = true :=
    (isCutPairSym_iff_exists_blockStart (by omega)).mpr ⟨a, ha_eq⟩
  have ht1_p_cut : isCutPairSym (b5Sym (t₁ + p - 1)) (b5Sym (t₁ + p)) = true := by
    have hp_prev : b5Sym (t₁ - 1) = b5Sym (t₁ + p - 1) := by
      have h := hrun1.2.2.1 (t₁ - 1 - i₁) (by omega)
      have h1 : i₁ + (t₁ - 1 - i₁) = t₁ - 1 := by omega
      have h2 : i₁ + (t₁ - 1 - i₁) + p = t₁ + p - 1 := by omega
      rwa [h2, h1] at h
    have hp_curr : b5Sym t₁ = b5Sym (t₁ + p) := by
      have h := hrun1.2.2.1 (t₁ - i₁) (by omega)
      have h1 : i₁ + (t₁ - i₁) = t₁ := by omega
      have h2 : i₁ + (t₁ - i₁) + p = t₁ + p := by omega
      rwa [h2, h1] at h
    rwa [← hp_prev, ← hp_curr]
  rcases (isCutPairSym_iff_exists_blockStart (by omega)).mp ht1_p_cut with ⟨a', ha'_eq⟩
  have ha_lt_a' : a < a' := by
    apply blockStart_strictMono.lt_iff_lt.mp
    rw [ha_eq, ha'_eq]; omega
  let p_Y := a' - a
  have hpY_def : p_Y = a' - a := rfl
  have hpY_pos : 1 ≤ p_Y := by omega
  have ha'_add : a' = a + p_Y := by omega
  -- Prove p_Y < p (using no_len3_in_24_sym)
  have hge_bs : ∀ d : ℕ, d ≤ blockStart (a + d) - blockStart a := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have hle1 : blockStart a ≤ blockStart (a + d) := blockStart_strictMono.monotone (by omega)
      have hs := blockStart_succ_sym (a + d)
      have hlen1 := (fSym5_length_bounds (b5Sym (a + d))).1
      have ha1 : a + (d + 1) = a + d + 1 := by omega
      rw [ha1, hs]; omega
  have hpY_le_p : p_Y ≤ p := by
    have hdiff : blockStart (a + p_Y) - blockStart a = p := by
      rw [← ha'_add, ha'_eq, ha_eq]; omega
    exact hdiff ▸ hge_bs p_Y
  have hpY_lt_p : p_Y < p := by
    by_contra hge
    have hpY_eq : p_Y = p := by omega
    have hdiff : blockStart (a + p) - blockStart a = p := by
      rw [← hpY_eq, ← ha'_add, ha'_eq, ha_eq]; omega
    -- Every block in [a, a + p) must have length 1
    have hall_len1 : ∀ k < p, (fSym5 (b5Sym (a + k))).length = 1 := by
      intro k hk
      by_contra hne1
      have hlen2 : (fSym5 (b5Sym (a + k))).length = 2 := by
        have hb := fSym5_length_bounds (b5Sym (a + k)); omega
      have hsum_gt : ∀ d : ℕ, k < d → d + 1 ≤ blockStart (a + d) - blockStart a := by
        intro d hd
        induction d with
        | zero => omega
        | succ d ih =>
          have hle1 : blockStart a ≤ blockStart (a + d) := blockStart_strictMono.monotone (by omega)
          have hs := blockStart_succ_sym (a + d)
          have ha1 : a + (d + 1) = a + d + 1 := by omega
          rw [ha1, hs]
          by_cases hkd : k < d
          · have hprev := ih hkd
            have hb1 := (fSym5_length_bounds (b5Sym (a + d))).1
            omega
          · have hkeq : d = k := by omega
            subst hkeq
            have hge_d := hge_bs d
            omega
      have := hsum_gt p hk
      omega
    have hin24 : ∀ k < 3, (Sym5.beq (b5Sym (a + k)) .s2 || Sym5.beq (b5Sym (a + k)) .s4) = true := by
      intro k hk
      have hl1 := hall_len1 k (by omega)
      cases h : b5Sym (a + k) <;> rw [h] at hl1 <;> first | rfl | (simp [fSym5] at hl1)
    have hno24 := no_len3_in_24_sym (b5Sym a) (b5Sym (a + 1)) (b5Sym (a + 2))
      (b5Sym_valid2 a) (b5Sym_valid2 (a + 1))
    have h0 := hin24 0 (by omega); rw [Nat.add_zero] at h0
    have h1 := hin24 1 (by omega)
    have h2 := hin24 2 (by omega)
    rw [h0, h1, h2] at hno24
    exact Bool.noConfusion hno24
  -- Step 4: Extend [a, a + p_Y) to a maximal ConcreteRun alpha p_Y r and apply L5 + Union Lemma
  have ha_large : maxOverlap p_Y + 20 ≤ a := by
    have h2a : blockStart a ≤ 2 * a := blockStart_le_two_mul a
    have hmax_mono : maxOverlap p_Y ≤ maxOverlap p := by
      unfold maxOverlap
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 10 hpY_le_p) hpY_le_p) hpY_le_p
    omega
  rcases extend_to_concreteRun hpY_pos ha_large with ⟨alpha, r, hrunY, halpha_le, ha_end_le⟩
  rcases concreteRun_phi_step hrunY with ⟨hrun_phi, hphi_lo, hphi_hi, hphi_sum⟩
  -- Show p' = p: blockStart (alpha + p_Y) - blockStart alpha = blockStart (a + p_Y) - blockStart a = p
  have hp'_eq_p : blockStart (alpha + p_Y) - blockStart alpha = p := by
    have hshift : ∀ d : ℕ, d ≤ a - alpha →
        blockStart (alpha + d + p_Y) - blockStart (alpha + d) =
          blockStart (alpha + p_Y) - blockStart alpha := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        intro hd
        have hprev := ih (by omega)
        have hper_d := hrunY.2.2.1 d (by omega)
        have hs1 := blockStart_succ_sym (alpha + d)
        have hs2 := blockStart_succ_sym (alpha + d + p_Y)
        have hlen_eq : (fSym5 (b5Sym (alpha + d))).length =
            (fSym5 (b5Sym (alpha + d + p_Y))).length := by rw [hper_d]
        have hle1 : blockStart (alpha + d) ≤ blockStart (alpha + d + p_Y) :=
          blockStart_strictMono.monotone (by omega)
        have ha1 : alpha + (d + 1) = alpha + d + 1 := by omega
        have ha2 : alpha + (d + 1) + p_Y = alpha + d + p_Y + 1 := by omega
        rw [ha2, ha1, hs1, hs2]
        omega
    have h_at_a := hshift (a - alpha) (le_refl _)
    have ha_add : alpha + (a - alpha) = a := by omega
    rw [ha_add] at h_at_a
    have hp_val : blockStart (a + p_Y) - blockStart a = p := by
      rw [← ha'_add, ha'_eq, ha_eq]; omega
    omega
  -- Both hrun_phi and hrun1 share [t₁, t₁ + p)
  have ht1_in_phi : blockStart alpha - (eLOf (runCtxState alpha p_Y r).X.c (runCtxState alpha p_Y r).Y.c).length ≤ t₁ ∧
      t₁ + p ≤ (blockStart alpha - (eLOf (runCtxState alpha p_Y r).X.c (runCtxState alpha p_Y r).Y.c).length) +
        (blockStart (alpha + p_Y) - blockStart alpha) +
        ((eLOf (runCtxState alpha p_Y r).X.c (runCtxState alpha p_Y r).Y.c).length +
          (blockStart (alpha + p_Y + r) - blockStart (alpha + p_Y)) +
          (eROf (runCtxState alpha p_Y r).S.a (runCtxState alpha p_Y r).T.a).length) := by
    have hbs_alpha_a : blockStart alpha ≤ blockStart a := blockStart_strictMono.monotone halpha_le
    have hbs_a'_end : blockStart (a + p_Y) ≤ blockStart (alpha + p_Y + r) :=
      blockStart_strictMono.monotone ha_end_le
    have htp : t₁ + p = blockStart (a + p_Y) := by rw [← ha'_add, ha'_eq]
    constructor
    · omega
    · omega
  have ht1_in_1 : i₁ ≤ t₁ ∧ t₁ + p ≤ i₁ + p + m := by omega
  rw [hp'_eq_p] at hrun_phi ht1_in_phi hphi_sum
  rcases concreteRun_unique_of_overlap_p hrun_phi hrun1 ht1_in_phi ht1_in_1 with ⟨hi_phi_eq, hm_phi_eq⟩
  rw [hi_phi_eq, hm_phi_eq] at hphi_sum
  -- Prove 1 ≤ r (if r = 0, m = lam + 0 + rho ≤ 2, contradicting m ≥ 3!)
  have hr_pos : 1 ≤ r := by
    by_contra hr0
    have hr_zero : r = 0 := by omega
    subst hr_zero
    have hmis_c : (symWord3At (alpha - 3)).c ≠ (symWord3At (alpha + p_Y - 3)).c := by
      dsimp only [symWord3At]
      have h1 : alpha - 3 + 2 = alpha - 1 := by omega
      have h2 : alpha + p_Y - 3 + 2 = alpha + p_Y - 1 := by omega
      rw [h1, h2]
      exact hrunY.2.2.2.1
    have hlam_upk := left_ctx_unpack (symWord3At_isValid (alpha - 3))
      (symWord3At_isValid (alpha + p_Y - 3)) hmis_c
    have hlam_le1 : (eLOf (symWord3At (alpha - 3)).c (symWord3At (alpha + p_Y - 3)).c).length ≤ 1 :=
      hlam_upk.1
    have hrho_upk := right_ctx_unpack (symWord3At_isValid (alpha + p_Y + 0))
      (symWord3At_isValid (alpha + 0)) hrunY.2.2.2.2
    have hrho_le1 : (eROf (symWord3At (alpha + p_Y + 0)).a (symWord3At (alpha + 0)).a).length ≤ 1 :=
      hrho_upk.1
    have hm_val : (eLOf (symWord3At (alpha - 3)).c (symWord3At (alpha + p_Y - 3)).c).length +
        (blockStart (alpha + p_Y + 0) - blockStart (alpha + p_Y)) +
        (eROf (symWord3At (alpha + p_Y + 0)).a (symWord3At (alpha + 0)).a).length = m :=
      hm_phi_eq
    dsimp only [symWord3At] at hm_val hlam_le1 hrho_le1
    simp only [Nat.add_zero, Nat.sub_self] at hm_val hlam_le1 hrho_le1
    omega
  exact ⟨alpha, p_Y, r, hrunY, hpY_lt_p, hr_pos, hphi_sum.symm.trans hsum1⟩

/-- **Proposition `P9` (`concreteRun_from_seed`)**:
Every `ConcreteRun i p m` with `m ≥ 1` has `runSummary i p m = (stepSummary^[k]) (runSummary i₀ p₀ m₀)`
for some `k : ℕ` and some seed `ConcreteRun i₀ p₀ m₀` with `m₀ ∈ {1, 2}`. -/
theorem concreteRun_from_seed :
    ∀ p i m : ℕ, ConcreteRun i p m → 1 ≤ m →
      ∃ k i₀ p₀ m₀ : ℕ,
        ConcreteRun i₀ p₀ m₀ ∧
        (m₀ = 1 ∨ m₀ = 2) ∧
        (stepSummary^[k]) (runSummary i₀ p₀ m₀) = runSummary i p m := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro i m hrun hm1
    by_cases hm2 : m ≤ 2
    · exact ⟨0, i, p, m, hrun, by omega, rfl⟩
    · rcases concreteRun_desubst hrun (by omega) with ⟨alpha, p_Y, r, hrunY, hpY_lt, hr1, hstep⟩
      rcases ih p_Y hpY_lt alpha r hrunY hr1 with ⟨k, i₀, p₀, m₀, hseed, hm0, hiter⟩
      refine ⟨k + 1, i₀, p₀, m₀, hseed, hm0, ?_⟩
      rw [Function.iterate_succ_apply', hiter, hstep]

/-! ## Section 6: Large-Period Bound (`L10–L11`, `p₀ ≥ 41`) and Small-Period `ZPhi` Soundness (`P12`, `p₀ ≤ 40`) -/

/-- Exact Perron–Frobenius weight `nu` on `Vec5Z` (`L10`). -/
noncomputable def nuVec (v : Vec5Z) : ℝ :=
  (v.v0 : ℝ) + ((v.v1 + v.v3 + v.v4 : ℤ) : ℝ) * (1 / φ) + (v.v2 : ℝ) * (1 / φ ^ 2)

theorem nuVec_add (x y : Vec5Z) : nuVec (Vec5Z.add x y) = nuVec x + nuVec y := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  rcases y with ⟨y0, y1, y2, y3, y4⟩
  simp only [Vec5Z.add, nuVec]
  push_cast; ring

theorem nuVec_stepMZ (v : Vec5Z) : nuVec (stepMZ v) = φ * nuVec v := by
  rcases v with ⟨v0, v1, v2, v3, v4⟩
  simp only [stepMZ, nuVec]
  have hne : φ ≠ 0 := ne_of_gt phi_pos
  have hne2 : φ ^ 2 ≠ 0 := pow_ne_zero 2 hne
  push_cast
  field_simp [hne, hne2]
  ring_nf
  rw [phi_cube, phi_sq]
  ring

def Vec5Z.Nonneg (v : Vec5Z) : Prop :=
  0 ≤ v.v0 ∧ 0 ≤ v.v1 ∧ 0 ≤ v.v2 ∧ 0 ≤ v.v3 ∧ 0 ≤ v.v4

theorem parikhSym_nonneg (w : List Sym5) : (parikhSym w).Nonneg := by
  induction w with
  | nil => exact ⟨le_refl 0, le_refl 0, le_refl 0, le_refl 0, le_refl 0⟩
  | cons a rest ih =>
    rcases ih with ⟨h0, h1, h2, h3, h4⟩
    cases a <;> (simp only [parikhSym, Vec5Z.ofSym, Vec5Z.add, Vec5Z.Nonneg]; omega)

theorem stepMZ_nonneg {v : Vec5Z} (hv : v.Nonneg) : (stepMZ v).Nonneg := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  simp only [stepMZ, Vec5Z.Nonneg]; omega

theorem vec5Z_add_nonneg {x y : Vec5Z} (hx : x.Nonneg) (hy : y.Nonneg) :
    (Vec5Z.add x y).Nonneg := by
  rcases hx with ⟨x0, x1, x2, x3, x4⟩
  rcases hy with ⟨y0, y1, y2, y3, y4⟩
  simp only [Vec5Z.add, Vec5Z.Nonneg]; omega

theorem nuVec_bounds_of_nonneg {v : Vec5Z} (hv : v.Nonneg) :
    (v.sum : ℝ) ≤ φ ^ 2 * nuVec v ∧ nuVec v ≤ (v.sum : ℝ) := by
  rcases v with ⟨v0, v1, v2, v3, v4⟩
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hv0 : (0 : ℝ) ≤ (v0 : ℝ) := by exact_mod_cast h0
  have hv1 : (0 : ℝ) ≤ (v1 : ℝ) := by exact_mod_cast h1
  have hv2 : (0 : ℝ) ≤ (v2 : ℝ) := by exact_mod_cast h2
  have hv3 : (0 : ℝ) ≤ (v3 : ℝ) := by exact_mod_cast h3
  have hv4 : (0 : ℝ) ≤ (v4 : ℝ) := by exact_mod_cast h4
  simp only [nuVec, Vec5Z.sum]
  push_cast
  have h1_phi : 1 / φ = φ - 1 := inv_phi
  have hphi_pos : 0 < φ := phi_pos
  have hsq_pos : 0 < φ ^ 2 := by positivity
  have hmul_inv : φ ^ 2 * (1 / φ) = φ := by
    field_simp [ne_of_gt hphi_pos]
  have hmul_inv2 : φ ^ 2 * (1 / φ ^ 2) = 1 := mul_one_div_cancel (ne_of_gt hsq_pos)
  have hinv2_le1 : 1 / φ ^ 2 ≤ 1 := by
    rw [div_le_one hsq_pos]; nlinarith [one_lt_phi]
  constructor
  · have hexp : φ ^ 2 * ((v0 : ℝ) + ((v1 : ℝ) + (v3 : ℝ) + (v4 : ℝ)) * (1 / φ) +
        (v2 : ℝ) * (1 / φ ^ 2)) =
        φ ^ 2 * (v0 : ℝ) + ((v1 : ℝ) + (v3 : ℝ) + (v4 : ℝ)) * φ + (v2 : ℝ) := by
      linear_combination ((v1 : ℝ) + (v3 : ℝ) + (v4 : ℝ)) * hmul_inv + (v2 : ℝ) * hmul_inv2
    rw [hexp]
    nlinarith [one_lt_phi, phi_sq]
  · rw [h1_phi]
    nlinarith [one_lt_phi, phi_lt_two]

theorem nuVec_extra_le_phi (st : CtxState) :
    nuVec (parikhSym (phiStepCtx st).2) ≤ φ := by
  dsimp only [phiStepCtx]
  rw [parikhSym_append, nuVec_add]
  have hinv_pos : 0 < 1 / φ := one_div_pos.mpr phi_pos
  have hinv2_pos : 0 < 1 / φ ^ 2 := by positivity [phi_pos]
  have heL : nuVec (parikhSym (eLOf st.X.c st.Y.c)) ≤ 1 / φ := by
    cases st.X.c <;> cases st.Y.c <;>
      simp only [eLOf, parikhSym, Vec5Z.ofSym, Vec5Z.zero, Vec5Z.add, nuVec] <;>
      push_cast <;> linarith [hinv_pos]
  have heR : nuVec (parikhSym (eROf st.S.a st.T.a)) ≤ 1 := by
    have hsq_ge1 : (1 : ℝ) ≤ φ ^ 2 := by nlinarith [one_lt_phi]
    have hinv2_le1 : 1 / φ ^ 2 ≤ 1 := (div_le_one (by positivity [phi_pos])).mpr hsq_ge1
    cases st.S.a <;> cases st.T.a <;>
      simp only [eROf, parikhSym, Vec5Z.ofSym, Vec5Z.zero, Vec5Z.add, nuVec] <;>
      push_cast <;> linarith [hinv2_pos]
  linarith [inv_phi, phi_sq]

/-- **Lemma `L11` (`seed_pos_of_p_ge_41`)**:
For ANY seed `ConcreteRun i₀ p₀ m₀` with `41 ≤ p₀` and `m₀ ≤ 2`, every forward iterate `k : ℕ`
satisfies `0 < (summaryD ((stepSummary^[k]) (runSummary i₀ p₀ m₀))).toReal`. -/
theorem seed_pos_of_p_ge_41 {i₀ p₀ m₀ : ℕ}
    (hp41 : 41 ≤ p₀) (hm2 : m₀ ≤ 2) (k : ℕ) :
    0 < (summaryD ((stepSummary^[k]) (runSummary i₀ p₀ m₀))).toReal := by
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
      rw [hsn]
      dsimp only [stepSummary]
      refine ⟨stepMZ_nonneg hpu_nn,
        vec5Z_add_nonneg (stepMZ_nonneg hpz_nn) (parikhSym_nonneg _), ?_, ?_⟩
      · rw [nuVec_stepMZ, hpu_eq]; ring
      · rw [nuVec_add, nuVec_stepMZ]
        have hextra := nuVec_extra_le_phi (s n).st
        have hstep : φ * nuVec (s n).pz + nuVec (parikhSym (phiStepCtx (s n).st).2) + φ ^ 2 ≤
            φ * (nuVec (s n).pz + φ ^ 2) := by
          nlinarith [phi_sq, phi_pos]
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
  have hsq : φ ^ 2 = φ + 1 := phi_sq
  have hphi_pos : 0 < φ := phi_pos
  have hpow_pos : 0 < φ ^ k := pow_pos hphi_pos k
  have hsq_pos : 0 < φ ^ 2 := by positivity
  -- Lower bound on φ * p_k: φ ^ 2 * p_k ≥ φ ^ 2 * nuVec(pu_k) = φ ^ k * (φ ^ 2 * nuVec(pu_0)) ≥ φ ^ k * p₀
  have hpk_lb : φ ^ k * (p₀ : ℝ) ≤ φ ^ 2 * ((s k).pu.sum : ℝ) := by
    have h1 : φ ^ k * ((p₀ : ℤ) : ℝ) ≤ φ ^ k * (φ ^ 2 * nuVec (s 0).pu) :=
      mul_le_mul_of_nonneg_left hp0_le_nu0 (le_of_lt hpow_pos)
    have h2 : φ ^ k * (φ ^ 2 * nuVec (s 0).pu) = φ ^ 2 * nuVec (s k).pu := by
      rw [hpu_eq]; ring
    have h3 : φ ^ 2 * nuVec (s k).pu ≤ φ ^ 2 * ((s k).pu.sum : ℝ) :=
      mul_le_mul_of_nonneg_left hnu_le_pk (le_of_lt hsq_pos)
    push_cast at h1
    linarith
  -- Strict upper bound on m_k: m_k < φ ^ k * φ ^ 2 * (2 + φ ^ 2)
  have hmk_ub : ((s k).pz.sum : ℝ) < φ ^ k * (φ ^ 2 * (2 + φ ^ 2)) := by
    have hnu_lt : nuVec (s k).pz < φ ^ k * (2 + φ ^ 2) := by linarith [hsq_pos]
    have hmul : φ ^ 2 * nuVec (s k).pz < φ ^ 2 * (φ ^ k * (2 + φ ^ 2)) :=
      mul_lt_mul_of_pos_left hnu_lt hsq_pos
    linarith
  -- Key numerical inequality: 2 * φ ^ 3 * (2 + φ ^ 2) = 18 φ + 10 < 41 ≤ p₀
  have h18_lt_41 : 2 * φ ^ 3 * (2 + φ ^ 2) < (p₀ : ℝ) := by
    have hsimp : 2 * φ ^ 3 * (2 + φ ^ 2) = 18 * φ + 10 := by
      calc
        2 * φ ^ 3 * (2 + φ ^ 2)
          = 2 * (2 * φ + 1) * (2 + (φ + 1)) := by rw [phi_cube, phi_sq]
        _ = 4 * φ ^ 2 + 14 * φ + 6 := by ring
        _ = 4 * (φ + 1) + 14 * φ + 6 := by rw [phi_sq]
        _ = 18 * φ + 10 := by ring
    rw [hsimp]
    have hp0R : (41 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp41
    have h9sqrt5 : 9 * Real.sqrt 5 < 22 := by
      have hsq5 : (9 * Real.sqrt 5) ^ 2 < 22 ^ 2 := by
        rw [mul_pow, sqrt5_sq]; norm_num
      nlinarith [sqrt5_pos]
    have h18phi : 18 * φ + 10 < 41 := by unfold φ; linarith
    linarith
  -- Combine: φ ^ 2 * (2 * m_k) < φ ^ 2 * (φ * p_k), divide by φ ^ 2 > 0
  have h2mk_lt : φ ^ 2 * (2 * ((s k).pz.sum : ℝ)) < φ ^ 2 * (φ * ((s k).pu.sum : ℝ)) := by
    calc
      φ ^ 2 * (2 * ((s k).pz.sum : ℝ))
        < φ ^ 2 * (2 * (φ ^ k * (φ ^ 2 * (2 + φ ^ 2)))) := by nlinarith
      _ = φ * (φ ^ k * (2 * φ ^ 3 * (2 + φ ^ 2))) := by ring
      _ < φ * (φ ^ k * (p₀ : ℝ)) :=
          mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left h18_lt_41 hpow_pos) hphi_pos
      _ ≤ φ * (φ ^ 2 * ((s k).pu.sum : ℝ)) :=
          mul_le_mul_of_nonneg_left hpk_lb (le_of_lt hphi_pos)
      _ = φ ^ 2 * (φ * ((s k).pu.sum : ℝ)) := by ring
  unfold summaryD ZPhi.toReal
  dsimp only
  push_cast
  nlinarith

/-- Explicit 5×5 matrix form of `stepM6Z` (`M^6`), avoiding `2^24` AST blowup on 4-step compositions. -/
def stepM6ZFast (v : Vec5Z) : Vec5Z :=
  ⟨7 * v.v0 + 4 * v.v1 + 2 * v.v2 + 4 * v.v3 + 4 * v.v4,
   6 * v.v0 + 5 * v.v1 + 2 * v.v2 + 4 * v.v3 + 4 * v.v4,
   6 * v.v0 + 4 * v.v1 + 3 * v.v2 + 4 * v.v3 + 4 * v.v4,
   4 * v.v0 + 2 * v.v1 + 2 * v.v2 + 3 * v.v3 + 2 * v.v4,
   4 * v.v0 + 2 * v.v1 + 2 * v.v2 + 2 * v.v3 + 3 * v.v4⟩

theorem stepM6Z_eq_fast (v : Vec5Z) : stepM6Z v = stepM6ZFast v := by
  rcases v with ⟨v0, v1, v2, v3, v4⟩
  simp only [stepM6Z, stepMZ, stepM6ZFast]
  congr 1 <;> ring

theorem step6_affine_eq (v c0 c1 c2 c3 c4 c5 : Vec5Z) :
    let step (c x : Vec5Z) := Vec5Z.add (stepMZ x) c
    step c5 (step c4 (step c3 (step c2 (step c1 (step c0 v))))) =
      Vec5Z.add (stepM6Z v)
        (step c5 (step c4 (step c3 (step c2 (step c1 (step c0 Vec5Z.zero)))))) := by
  dsimp only
  simp only [stepM6Z, stepMZ, Vec5Z.add, Vec5Z.zero]
  congr 1 <;> ring

/-- **Cayley–Hamilton Theorem on `Vec5Z` (`stepM6Z_cayley_hamilton`)**:
`B := stepM6Z` satisfies `(B^2 - 18 B + I)(B - I) = B^3 - 19 B^2 + 19 B - I = 0`. -/
theorem stepM6Z_cayley_hamilton (v : Vec5Z) :
    Vec5Z.sub
      (Vec5Z.add
        (Vec5Z.sub (stepM6Z (stepM6Z (stepM6Z v))) (Vec5Z.smul 19 (stepM6Z (stepM6Z v))))
        (Vec5Z.smul 19 (stepM6Z v)))
      v = Vec5Z.zero := by
  rcases v with ⟨v0, v1, v2, v3, v4⟩
  simp only [stepM6Z_eq_fast, stepM6ZFast, Vec5Z.add, Vec5Z.sub, Vec5Z.smul, Vec5Z.zero]
  congr 1 <;> ring

/-- Every affine iterate `v (j + 1) = stepM6Z (v j) + C` satisfies the 4th-order linear recurrence
`v (j + 4) - 20 v (j + 3) + 38 v (j + 2) - 20 v (j + 1) + v j = 0` (`sum`-projected to `ℤ`). -/
theorem affine_stepM6Z_sum_rec {v : ℕ → Vec5Z} {C : Vec5Z}
    (hstep : ∀ j : ℕ, v (j + 1) = Vec5Z.add (stepM6Z (v j)) C) (j : ℕ) :
    (v (j + 4)).sum - 20 * (v (j + 3)).sum + 38 * (v (j + 2)).sum -
      20 * (v (j + 1)).sum + (v j).sum = 0 := by
  have h1 : v (j + 1) = Vec5Z.add (stepM6Z (v j)) C := hstep j
  have h2 : v (j + 2) = Vec5Z.add (stepM6Z (v (j + 1))) C := hstep (j + 1)
  have h3 : v (j + 3) = Vec5Z.add (stepM6Z (v (j + 2))) C := hstep (j + 2)
  have h4 : v (j + 4) = Vec5Z.add (stepM6Z (v (j + 3))) C := hstep (j + 3)
  rw [h4, h3, h2, h1]
  rcases v j with ⟨v0, v1, v2, v3, v4⟩
  rcases C with ⟨c0, c1, c2, c3, c4⟩
  simp only [stepM6Z_eq_fast, stepM6ZFast, Vec5Z.add, Vec5Z.sum]
  ring

theorem collectSummaries_getElem? (N : ℕ) (s₀ : SeedSummary) (k : ℕ) (hk : k < N) :
    (collectSummaries N s₀)[k]? = some ((stepSummary^[k]) s₀) := by
  induction N generalizing s₀ k with
  | zero => omega
  | succ N ih =>
    cases k with
    | zero => simp [collectSummaries]
    | succ k =>
      simp only [collectSummaries, List.getElem?_cons_succ]
      rw [ih (stepSummary s₀) k (by omega), Function.iterate_succ_apply]

/-- Soundness of Branch 1 (`checkResidueInc`) on a `ZPhi` sequence satisfying the 4th-order recurrence. -/
theorem residueInc_sound {D : ℕ → ZPhi}
    (hrec : ∀ j : ℕ, D (j + 4) - ⟨20, 0⟩ * D (j + 3) + ⟨38, 0⟩ * D (j + 2) -
      ⟨20, 0⟩ * D (j + 1) + D j = 0)
    (hcert : checkResidueInc (D 0) (D 1) (D 2) (D 3) = true) :
    ∀ j : ℕ, 0 < (D j).toReal := by
  unfold checkResidueInc at hcert
  simp only [Bool.and_eq_true, zphiPosFast_eq_isPos, ZPhi.isPos_iff_toReal_pos] at hcert
  rcases hcert with ⟨⟨⟨hd0, hd10⟩, hA0⟩, hA10⟩
  let A (j : ℕ) : ZPhi := (D (j + 2) - ⟨2, 0⟩ * D (j + 1)) + D j
  have hA_rec : ∀ j : ℕ, (A (j + 2)).toReal = 18 * (A (j + 1)).toReal - (A j).toReal := by
    intro j
    have hz : A (j + 2) - ⟨18, 0⟩ * A (j + 1) + A j = 0 := by
      have hr := hrec j
      dsimp only [A]
      ext
      · have ha := congrArg ZPhi.a hr
        simp only [ZPhi.add_a, ZPhi.sub_a, ZPhi.mul_a, ZPhi.zero_a] at ha ⊢
        linarith
      · have hb := congrArg ZPhi.b hr
        simp only [ZPhi.add_b, ZPhi.sub_b, ZPhi.mul_b, ZPhi.zero_b] at hb ⊢
        linarith
    have hR := congrArg ZPhi.toReal hz
    simp only [ZPhi.toReal_add, ZPhi.toReal_sub, ZPhi.toReal_mul, ZPhi.toReal_zero] at hR
    have h18 : (⟨18, 0⟩ : ZPhi).toReal = 18 := by simp [ZPhi.toReal]
    rw [h18] at hR
    linarith
  have hA_pos : ∀ j : ℕ, 0 < (A j).toReal ∧ (A j).toReal < (A (j + 1)).toReal := by
    intro j
    induction j with
    | zero =>
      refine ⟨hA0, ?_⟩
      rw [ZPhi.toReal_sub, sub_pos] at hA10
      exact hA10
    | succ j ih =>
      rcases ih with ⟨hj_pos, hj_inc⟩
      refine ⟨by linarith, ?_⟩
      rw [hA_rec j]
      linarith
  have hD_step : ∀ j : ℕ,
      (D (j + 2)).toReal - (D (j + 1)).toReal =
        ((D (j + 1)).toReal - (D j).toReal) + (A j).toReal := by
    intro j
    dsimp only [A]
    simp only [ZPhi.toReal_add, ZPhi.toReal_sub, ZPhi.toReal_mul]
    have h2 : (⟨2, 0⟩ : ZPhi).toReal = 2 := by simp [ZPhi.toReal]
    rw [h2]; ring
  have hD_pos : ∀ j : ℕ, 0 < (D j).toReal ∧ (D j).toReal < (D (j + 1)).toReal := by
    intro j
    induction j with
    | zero =>
      rw [ZPhi.toReal_sub, sub_pos] at hd10
      exact ⟨hd0, hd10⟩
    | succ j ih =>
      rcases ih with ⟨hj_pos, hj_inc⟩
      have hAj := (hD_step j)
      have hAp := (hA_pos j).1
      exact ⟨by linarith, by linarith⟩
  exact fun j => (hD_pos j).1

/-- Soundness of Branch 2 (`checkResidueBdd`) on a `ZPhi` sequence satisfying the 4th-order recurrence. -/
theorem residueBdd_inv {D : ℕ → ZPhi}
    (hrec : ∀ j : ℕ, D (j + 4) - ⟨20, 0⟩ * D (j + 3) + ⟨38, 0⟩ * D (j + 2) -
      ⟨20, 0⟩ * D (j + 1) + D j = 0)
    (hR0 : lamZPhi * (D 2 - D 1) - (D 1 - D 0) = 0)
    (hR1 : lamZPhi * (D 3 - D 2) - (D 2 - D 1) = 0) :
    ∀ j : ℕ, lamZPhi * D (j + 1) - D j = lamZPhi * D 1 - D 0 := by
  let R (j : ℕ) : ZPhi := lamZPhi * (D (j + 2) - D (j + 1)) - (D (j + 1) - D j)
  have hR_step : ∀ j : ℕ,
      R (j + 2) = (lamZPhi + 1) * R (j + 1) - lamZPhi * R j := by
    intro j
    have hr := hrec j
    dsimp only [R, lamZPhi]
    have idx11 : j + 1 + 1 = j + 2 := by omega
    have idx12 : j + 1 + 2 = j + 3 := by omega
    have idx21 : j + 2 + 1 = j + 3 := by omega
    have idx22 : j + 2 + 2 = j + 4 := by omega
    rw [idx11, idx12, idx21, idx22]
    have ha := congrArg ZPhi.a hr
    have hb := congrArg ZPhi.b hr
    simp only [ZPhi.add_a, ZPhi.add_b, ZPhi.sub_a, ZPhi.sub_b, ZPhi.mul_a, ZPhi.mul_b,
      ZPhi.zero_a, ZPhi.zero_b] at ha hb
    ext
    · simp only [ZPhi.add_a, ZPhi.add_b, ZPhi.sub_a, ZPhi.sub_b, ZPhi.mul_a, ZPhi.mul_b,
        ZPhi.one_a, ZPhi.one_b]
      linarith
    · simp only [ZPhi.add_a, ZPhi.add_b, ZPhi.sub_a, ZPhi.sub_b, ZPhi.mul_a, ZPhi.mul_b,
        ZPhi.one_a, ZPhi.one_b]
      linarith
  have hR_zero : ∀ j : ℕ, R j = 0 ∧ R (j + 1) = 0 := by
    intro j
    induction j with
    | zero => exact ⟨hR0, hR1⟩
    | succ j ih =>
      rcases ih with ⟨hz0, hz1⟩
      refine ⟨hz1, ?_⟩
      rw [hR_step j, hz0, hz1]
      ext <;> simp
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have hz := (hR_zero j).1
    dsimp only [R] at hz
    rw [← ih]
    ext
    · have ha := congrArg ZPhi.a hz
      simp only [ZPhi.sub_a, ZPhi.sub_b, ZPhi.mul_a, ZPhi.zero_a] at ha ⊢; linarith
    · have hb := congrArg ZPhi.b hz
      simp only [ZPhi.sub_a, ZPhi.sub_b, ZPhi.mul_b, ZPhi.zero_b] at hb ⊢; linarith

theorem residueBdd_sound {D : ℕ → ZPhi}
    (hrec : ∀ j : ℕ, D (j + 4) - ⟨20, 0⟩ * D (j + 3) + ⟨38, 0⟩ * D (j + 2) -
      ⟨20, 0⟩ * D (j + 1) + D j = 0)
    (hcert : checkResidueBdd (D 0) (D 1) (D 2) (D 3) = true) :
    ∀ j : ℕ, 0 < (D j).toReal := by
  unfold checkResidueBdd at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq, zphiPosFast_eq_isPos,
    ZPhi.isPos_iff_toReal_pos] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨h0a, h0b⟩, h1a⟩, h1b⟩, hd0⟩, hK⟩
  have hR0 : lamZPhi * (D 2 - D 1) - (D 1 - D 0) = 0 := by ext <;> assumption
  have hR1 : lamZPhi * (D 3 - D 2) - (D 2 - D 1) = 0 := by ext <;> assumption
  have hinv := residueBdd_inv hrec hR0 hR1
  have hlam_pos : 0 < lamZPhi.toReal := by
    simp only [lamZPhi, ZPhi.toReal]; push_cast; linarith [phi_pos]
  intro j
  induction j with
  | zero => exact hd0
  | succ j ih =>
    have hstep := congrArg ZPhi.toReal (hinv j)
    rw [ZPhi.toReal_sub, ZPhi.toReal_mul] at hstep
    have hpos_prod : 0 < lamZPhi.toReal * (D (j + 1)).toReal := by linarith
    exact (mul_pos_iff_of_pos_left hlam_pos).mp hpos_prod

/-- **Soundness of `checkSummaryZPhi` (`checkSummaryZPhi_sound`)**:
If `checkSummaryZPhi s₀ = true`, then `0 < (summaryD ((stepSummary^[k]) s₀)).toReal` for ALL `k : ℕ`. -/
theorem checkSummaryZPhi_sound {s₀ : SeedSummary} (h : checkSummaryZPhi s₀ = true) :
    ∀ k : ℕ, 0 < (summaryD ((stepSummary^[k]) s₀)).toReal := by
  unfold checkSummaryZPhi at h
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
  rcases h with ⟨hst8, ⟨⟨hd0_pos, hd1_pos⟩, hall_r⟩⟩
  let s (n : ℕ) := (stepSummary^[n]) s₀
  have hds_at : ∀ n (hn : n < 26),
      (orb.map summaryD).getD n ⟨0, 0⟩ = summaryD (s n) := by
    intro n hn
    rw [← horb, List.getD_eq_getElem?_getD, List.getElem?_map,
        collectSummaries_getElem? 26 s₀ n hn]
    rfl
  -- State periodicity for n ≥ 2: (s (n + 6)).st = (s n).st
  have hst_per : ∀ m : ℕ, (s (2 + m + 6)).st = (s (2 + m)).st := by
    intro m
    induction m with
    | zero => exact hst8
    | succ m ih =>
      have h1 : s (2 + (m + 1) + 6) = stepSummary (s (2 + m + 6)) := by
        have hidx : 2 + (m + 1) + 6 = (2 + m + 6) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      have h2 : s (2 + (m + 1)) = stepSummary (s (2 + m)) := by
        have hidx : 2 + (m + 1) = (2 + m) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      rw [h1, h2]
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
  -- 6-step affine step on pu and pz along each residue class r
  have h6_affine : ∀ r : ℕ, ∃ C_r : Vec5Z, ∀ j : ℕ,
      (s (2 + r + 6 * (j + 1))).pu = stepM6Z ((s (2 + r + 6 * j)).pu) ∧
      (s (2 + r + 6 * (j + 1))).pz = Vec5Z.add (stepM6Z ((s (2 + r + 6 * j)).pz)) C_r := by
    intro r
    -- Define 6-step context-driven step from fixed context sequence st_0 .. st_5
    let st_at (t : ℕ) := (s (2 + r + t)).st
    have hst_shift : ∀ j t : ℕ, (s (2 + r + 6 * j + t)).st = st_at t := by
      intro j t
      have hidx : 2 + r + 6 * j + t = 2 + (r + t) + 6 * j := by omega
      rw [hidx, hst_per_j (r + t) j]
      dsimp [st_at]; congr 2; omega
    -- Compute C_r by applying 6 steps starting from Vec5Z.zero
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
      rw [hstep1 t]
      dsimp only [stepSummary, stepPz]
      rw [hst_shift j t]
      exact ⟨rfl, rfl⟩
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
  -- Now prove positivity for every k : ℕ
  intro k
  by_cases hk0 : k = 0
  · subst hk0; rwa [hds_at 0 (by omega)] at hd0_pos
  · by_cases hk1 : k = 1
    · subst hk1; rwa [hds_at 1 (by omega)] at hd1_pos
    · let r := (k - 2) % 6
      let j := (k - 2) / 6
      have hr_lt : r < 6 := Nat.mod_lt _ (by omega)
      have hk_eq : k = 2 + r + 6 * j := by
        have := Nat.div_add_mod (k - 2) 6
        omega
      rw [hk_eq]
      rcases h6_affine r with ⟨C_r, haff_r⟩
      let D (n : ℕ) : ZPhi := summaryD (s (2 + r + 6 * n))
      have hpu_step : ∀ n : ℕ,
          (s (2 + r + 6 * (n + 1))).pu = Vec5Z.add (stepM6Z ((s (2 + r + 6 * n)).pu)) Vec5Z.zero := by
        intro n
        rw [(haff_r n).1]
        cases stepM6Z (s (2 + r + 6 * n)).pu
        simp [Vec5Z.add, Vec5Z.zero]
      have hpz_step : ∀ n : ℕ,
          (s (2 + r + 6 * (n + 1))).pz = Vec5Z.add (stepM6Z ((s (2 + r + 6 * n)).pz)) C_r :=
        fun n => (haff_r n).2
      have hD_rec : ∀ n : ℕ, D (n + 4) - ⟨20, 0⟩ * D (n + 3) + ⟨38, 0⟩ * D (n + 2) -
          ⟨20, 0⟩ * D (n + 1) + D n = 0 := by
        intro n
        have hpu_r := affine_stepM6Z_sum_rec
          (v := fun m => (s (2 + r + 6 * m)).pu) (C := Vec5Z.zero) hpu_step n
        have hpz_r := affine_stepM6Z_sum_rec
          (v := fun m => (s (2 + r + 6 * m)).pz) (C := C_r) hpz_step n
        dsimp only [D, summaryD]
        ext
        · simp only [ZPhi.add_a, ZPhi.sub_a, ZPhi.mul_a, ZPhi.zero_a]
          linarith
        · simp only [ZPhi.add_b, ZPhi.sub_b, ZPhi.mul_b, ZPhi.zero_b]
          linarith
      have hr_mem : r ∈ ([0, 1, 2, 3, 4, 5] : List ℕ) := by
        have hrc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
        rcases hrc with h | h | h | h | h | h <;> simp [h]
      have hr_cert := List.all_eq_true.mp hall_r r hr_mem
      rw [hds_at (2 + r) (by omega), hds_at (8 + r) (by omega),
          hds_at (14 + r) (by omega), hds_at (20 + r) (by omega)] at hr_cert
      have hd0_eq : s (2 + r) = s (2 + r + 6 * 0) := rfl
      have hd1_eq : s (8 + r) = s (2 + r + 6 * 1) := congrArg s (by omega)
      have hd2_eq : s (14 + r) = s (2 + r + 6 * 2) := congrArg s (by omega)
      have hd3_eq : s (20 + r) = s (2 + r + 6 * 3) := congrArg s (by omega)
      rw [hd0_eq, hd1_eq, hd2_eq, hd3_eq] at hr_cert
      rw [Bool.or_eq_true] at hr_cert
      rcases hr_cert with hinc | hbdd
      · exact residueInc_sound hD_rec hinc j
      · exact residueBdd_sound hD_rec hbdd j

/-- **Proposition `P12` (`seed_pos_of_p_le_40`)**:
Every seed `ConcreteRun i₀ p₀ m₀` with `1 ≤ p₀ ≤ 40` and `m₀ ∈ {1, 2}` lies in `seedBucket` and
therefore satisfies `0 < (summaryD ((stepSummary^[k]) (runSummary i₀ p₀ m₀))).toReal` for all `k : ℕ`. -/
theorem seed_pos_of_p_le_40 {i₀ p₀ m₀ : ℕ}
    (hrun : ConcreteRun i₀ p₀ m₀) (hp40 : p₀ ≤ 40) (hm0 : m₀ = 1 ∨ m₀ = 2) (k : ℕ) :
    0 < (summaryD ((stepSummary^[k]) (runSummary i₀ p₀ m₀))).toReal := by
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
  -- Show runSummary i₀ p₀ m₀ = summaryOfSuffix p₀ m₀ suf
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
      rw [g0, g1, g2]
      simp only [Nat.add_assoc]
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
        rw [g]
        congr 1; omega
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
  -- Extract checkSeedAtSuffix p₀ m₀ suf = true from all_twoFactor_seeds_in_buckets
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
  -- Evaluate the guards in checkSeedAtSuffix p₀ m₀ suf to deduce inSeedBuckets = true
  unfold checkSeedAtSuffix at hseed_chk
  have hg_3 : symOptEq suf[3]? suf[3 + p₀]? = true := by
    rw [hsuf_at 3 (by omega), hsuf_at (3 + p₀) (by omega)]
    have h0 := hper 0 (by omega)
    have idx1 : i₀ - 3 + 3 = i₀ := by omega
    have idx2 : i₀ - 3 + (3 + p₀) = i₀ + 0 + p₀ := by omega
    rw [idx1, idx2]
    exact (Sym5.beq_iff_eq _ _).mpr h0
  have hg_len : hasLenAtLeast (p₀ + m₀ + 6) suf = true :=
    (hasLenAtLeast_iff _ _).mpr hsuf_len
  have hg_m : (Nat.beq m₀ 1 || symOptEq suf[4]? suf[4 + p₀]?) = true := by
    rcases hm0 with rfl | rfl
    · rfl
    · simp only [Nat.beq, Bool.false_or]
      rw [hsuf_at 4 (by omega), hsuf_at (4 + p₀) (by omega)]
      have h1 := hper 1 (by omega)
      have idx1 : i₀ - 3 + 4 = i₀ + 1 := by omega
      have idx2 : i₀ - 3 + (4 + p₀) = i₀ + 1 + p₀ := by omega
      rw [idx1, idx2]
      exact (Sym5.beq_iff_eq _ _).mpr h1
  have hg_L : symOptNe suf[2]? suf[2 + p₀]? = true := by
    rw [hsuf_at 2 (by omega), hsuf_at (2 + p₀) (by omega)]
    have idx1 : i₀ - 3 + 2 = i₀ - 1 := by omega
    have idx2 : i₀ - 3 + (2 + p₀) = i₀ + p₀ - 1 := by omega
    rw [idx1, idx2]
    simp only [symOptNe, Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr (mt (Sym5.beq_iff_eq _ _).mp hmisL)
  have hg_R : symOptNe suf[3 + p₀ + m₀]? suf[3 + m₀]? = true := by
    rw [hsuf_at (3 + p₀ + m₀) (by omega), hsuf_at (3 + m₀) (by omega)]
    have idx1 : i₀ - 3 + (3 + p₀ + m₀) = i₀ + p₀ + m₀ := by omega
    have idx2 : i₀ - 3 + (3 + m₀) = i₀ + m₀ := by omega
    rw [idx1, idx2]
    simp only [symOptNe, Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr (mt (Sym5.beq_iff_eq _ _).mp hmisR)
  simp only [hg_3, hg_len, hg_m, hg_L, hg_R, Bool.and_self, ↓reduceIte] at hseed_chk
  rw [← hsum_eq] at hseed_chk
  unfold inSeedBuckets at hseed_chk
  have hmem_bkt := (memSummaryList_iff _ _).mp hseed_chk
  have hvalid_s0 := all_seedBuckets_valid _ _ _ hmem_bkt
  exact checkSummaryZPhi_sound hvalid_s0 k

/-! ## Section 7: Main Theorems — Strict Upper Bound, Square-Freeness, Supremum & Non-Attainment -/

/-- For EVERY `ConcreteRun i p m` (`m ≥ 0`), `2 * m < φ * p` (`0 < φ * p - 2 * m`). -/
theorem concreteRun_D_pos {i p m : ℕ} (hrun : ConcreteRun i p m) :
    (2 : ℝ) * (m : ℝ) < φ * (p : ℝ) := by
  by_cases hm0 : m = 0
  · subst hm0
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hrun.2.1
    simp only [Nat.cast_zero, mul_zero]
    exact mul_pos phi_pos hpR
  · rcases concreteRun_from_seed p i m hrun (by omega) with ⟨k, i₀, p₀, m₀, hseed, hm0_12, hiter⟩
    have hD_pos : 0 < (summaryD ((stepSummary^[k]) (runSummary i₀ p₀ m₀))).toReal := by
      by_cases hp40 : p₀ ≤ 40
      · exact seed_pos_of_p_le_40 hseed hp40 hm0_12 k
      · exact seed_pos_of_p_ge_41 (by omega) (by omega) k
    rw [hiter] at hD_pos
    rcases runSummary_sums i p m with ⟨hpu, hpz⟩
    unfold summaryD ZPhi.toReal at hD_pos
    dsimp only at hD_pos
    rw [hpu, hpz] at hD_pos
    push_cast at hD_pos
    linarith

/-- **Strict Critical-Exponent Upper Bound (`b5_exponent_lt_crit`, NOT ATTAINED)**:
For EVERY factor `w : List (Fin 5)` of `b_5` (both `w = []` and `w ≠ []`) and EVERY period
`p ≥ 1` of `w`, `(w.length : ℝ) / (p : ℝ) < (5 + Real.sqrt 5) / 4`. -/
theorem b5_exponent_lt_crit (w : List (Fin 5)) (p : ℕ)
    (hfac : IsFactorInf w b5) (hp : 1 ≤ p) (hper : IsPeriod w p) :
    (w.length : ℝ) / (p : ℝ) < (5 + Real.sqrt 5) / 4 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  by_cases hle : w.length ≤ p
  · have hw_le : (w.length : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
    have hdiv_le1 : (w.length : ℝ) / (p : ℝ) ≤ 1 := (div_le_one hpR).mpr hw_le
    linarith [one_lt_critVal]
  · -- w.length > p: move w to a large occurrence q ≥ maxOverlap p + 30 and extend to ConcreteRun
    have hgt : p < w.length := lt_of_not_ge hle
    let m₀ := w.length - p
    rcases hfac with ⟨i₀, hi₀⟩
    rcases exists_sym_occ_ge i₀ w.length (maxOverlap p + 30) with ⟨q, hq_ge, hslice⟩
    have hq_per : ∀ j < m₀, b5Sym (q + j) = b5Sym (q + j + p) := by
      intro j hj
      have h1 := congrArg (fun l : List Sym5 => l[j]?) hslice
      have h2 := congrArg (fun l : List Sym5 => l[j + p]?) hslice
      rw [List.getElem?_eq_getElem (by simp; omega),
          List.getElem?_eq_getElem (by simp; omega),
          Option.some.injEq, symSlice_getElem, symSlice_getElem] at h1 h2
      have hqp : q + j + p = q + (j + p) := by omega
      rw [hqp, h1, h2, b5Sym_eq_iff, hi₀ j (by omega), hi₀ (j + p) (by omega)]
      exact hper j (by omega)
    rcases extend_to_concreteRun hp (by omega : maxOverlap p + 20 ≤ q) with
      ⟨alpha, r, hrun, halpha_le, hq_end_le⟩
    -- Extend right bound: q + p + m₀ ≤ alpha + p + r
    have hlen_le_r : q + p + m₀ ≤ alpha + p + r := by
      by_contra hgt_r
      have hr_in : alpha + r - q < m₀ := by omega
      have hp_q := hq_per (alpha + r - q) hr_in
      have idx1 : q + (alpha + r - q) = alpha + r := by omega
      have idx2 : q + (alpha + r - q) + p = alpha + p + r := by omega
      rw [idx2, idx1] at hp_q
      exact hrun.2.2.2.2 hp_q.symm
    have hm0_le_r : m₀ ≤ r := by omega
    have hD := concreteRun_D_pos hrun
    have hm0R : (m₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hm0_le_r
    have hw_len_eq : (w.length : ℝ) = (p : ℝ) + (m₀ : ℝ) := by
      have : w.length = p + m₀ := by omega
      exact_mod_cast this
    rw [critVal_eq_one_add_half_phi, hw_len_eq, div_lt_iff₀ hpR]
    nlinarith

/-- **Unconditional Square-Freeness of `b_5` (`b5_squarefree`)**:
No non-empty word `u` has `u ++ u` occurring as a factor of `b_5`. -/
theorem b5_squarefree {u : List (Fin 5)} (hu : u ≠ []) :
    ¬ IsFactorInf (u ++ u) b5 := by
  intro hfac
  have hp : 1 ≤ u.length := List.length_pos_of_ne_nil hu
  have hper : IsPeriod (u ++ u) u.length := by
    intro i hi
    have hi_lt : i < u.length := by simp at hi; omega
    rw [List.getElem_append_left hi_lt, List.getElem_append_right (by omega)]
    simp
  have hlt := b5_exponent_lt_crit (u ++ u) u.length hfac hp hper
  have hpR : (u.length : ℝ) ≠ 0 := by positivity
  have hexp2 : ((u ++ u).length : ℝ) / (u.length : ℝ) = 2 := by
    simp only [List.length_append]
    push_cast
    field_simp [hpR]
    ring
  rw [hexp2] at hlt
  linarith [critVal_lt_two]

/-- Explicit occurrence of the extremal seed `123010421` (`p₀ = 2, m₀ = 1`) at index `i₀ = 38`
in `b5Sym`, matching `extremalSeedSummary`. -/
theorem extremalSeed_concreteRun :
    ConcreteRun 38 2 1 ∧ runSummary 38 2 1 = extremalSeedSummary := by
  have hslice8 : symSlice 0 (iterSym5 8 [.s0]).length = iterSym5 8 [.s0] := by
    simpa [blockStartK_zero] using symSlice_blockStartK_single 8 0
  have h8_eq : iterSym5 8 [.s0] = iterSym5 3 (g5Val .s0) := by
    rw [g5Val_eq_iterSym5, ← iterSym5_add]
  have h8_len : 44 ≤ (iterSym5 8 [.s0]).length := by
    rw [h8_eq]
    exact (hasLenAtLeast_iff 44 _).mp (by rfl)
  have hsub9 : symSlice 35 9 = extremalSeedWord := by
    rw [← extremalSeed_occurs_at_35, ← h8_eq, ← hslice8]
    apply List.ext_getElem
    · rw [symSlice_length, List.length_take, List.length_drop, symSlice_length]; omega
    · intro k hk1 hk2
      rw [symSlice_length] at hk1
      rw [symSlice_getElem, List.getElem_take, List.getElem_drop, symSlice_getElem]
      congr 1; omega
  have hat : ∀ k (hk : k < 9), b5Sym (35 + k) = extremalSeedWord[k]'(by simp [extremalSeedWord]; omega) := by
    intro k hk
    have h := congrArg (fun l : List Sym5 => l[k]?) hsub9
    rw [List.getElem?_eq_getElem (by simp [hk]),
        List.getElem?_eq_getElem (by simp [extremalSeedWord]; omega),
        Option.some.injEq, symSlice_getElem] at h
    exact h
  have b35 := hat 0 (by omega); simp [extremalSeedWord] at b35
  have b36 := hat 1 (by omega); simp [extremalSeedWord] at b36
  have b37 := hat 2 (by omega); simp [extremalSeedWord] at b37
  have b38 := hat 3 (by omega); simp [extremalSeedWord] at b38
  have b39 := hat 4 (by omega); simp [extremalSeedWord] at b39
  have b40 := hat 5 (by omega); simp [extremalSeedWord] at b40
  have b41 := hat 6 (by omega); simp [extremalSeedWord] at b41
  have b42 := hat 7 (by omega); simp [extremalSeedWord] at b42
  have b43 := hat 8 (by omega); simp [extremalSeedWord] at b43
  have hrun : ConcreteRun 38 2 1 := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := by omega
      subst hj0; simp [b38, b40]
    · simp [b37, b39]
    · simp [b41, b39]
  refine ⟨hrun, ?_⟩
  have hu : symSlice 38 2 = [.s0, .s1] := by
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      simp only [symSlice_length] at hk1
      have hkc : k = 0 ∨ k = 1 := by omega
      rcases hkc with rfl | rfl <;> simp [b38, b39]
  have hz : symSlice 40 1 = [.s0] := by
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      simp only [symSlice_length] at hk1
      have hk0 : k = 0 := by omega
      subst hk0; simp [b40]
  unfold runSummary extremalSeedSummary summaryOfSuffix runCtxState symWord3At extremalSeedWord
  simp only [Nat.reduceSub, Nat.reduceAdd, hu, hz, b35, b36, b37, b38, b39, b40, b41, b42, b43]
  rfl

/-- Iterated `concreteRun_phi_step` produces concrete runs of `b5Sym` matching `stepSummary^[k]`. -/
theorem exists_concreteRun_iter_summary (k : ℕ) {i₀ p₀ m₀ : ℕ} (hrun₀ : ConcreteRun i₀ p₀ m₀) :
    ∃ i_k p_k m_k : ℕ,
      ConcreteRun i_k p_k m_k ∧
      runSummary i_k p_k m_k = (stepSummary^[k]) (runSummary i₀ p₀ m₀) := by
  induction k with
  | zero => exact ⟨i₀, p₀, m₀, hrun₀, rfl⟩
  | succ k ih =>
    rcases ih with ⟨i_k, p_k, m_k, hrk, hsum_k⟩
    rcases concreteRun_phi_step hrk with ⟨hr_next, _, _, hsum_next⟩
    refine ⟨_, _, _, hr_next, ?_⟩
    rw [Function.iterate_succ_apply', ← hsum_k, hsum_next]

/-- **Asymptotic Attainment from Below (`b5_sup_exponent_ge_crit`)**:
For EVERY `ε > 0`, there exist a non-empty factor `w` of `b_5` and period `p ≥ 1` of `w` such that
`(5 + Real.sqrt 5) / 4 - ε < (w.length : ℝ) / (p : ℝ)`. -/
theorem b5_sup_exponent_ge_crit (ε : ℝ) (hε : 0 < ε) :
    ∃ w : List (Fin 5), ∃ p : ℕ,
      w ≠ [] ∧ IsFactorInf w b5 ∧ 1 ≤ p ∧ IsPeriod w p ∧
      (5 + Real.sqrt 5) / 4 - ε < (w.length : ℝ) / (p : ℝ) := by
  rcases extremalSeed_concreteRun with ⟨hrun0, hsum0⟩
  -- Unpack extremalSeed_cert: along k = 2 + 6*j, D_j satisfies Λ * D_{j+1} - D_j = ⟨14, 26⟩ and D_0 = ⟨-8, 7⟩
  have hcert := extremalSeed_cert
  unfold checkExtremalSeedCert at hcert
  generalize horb : collectSummaries 26 extremalSeedSummary = orb at hcert
  have h2 : orb[2]? = some ((stepSummary^[2]) extremalSeedSummary) := by
    rw [← horb]; exact collectSummaries_getElem? 26 extremalSeedSummary 2 (by omega)
  have h8 : orb[8]? = some ((stepSummary^[8]) extremalSeedSummary) := by
    rw [← horb]; exact collectSummaries_getElem? 26 extremalSeedSummary 8 (by omega)
  dsimp only at hcert
  rw [h2, h8] at hcert
  dsimp only at hcert
  simp only [Bool.and_eq_true, CtxState.beq_iff_eq, decide_eq_true_eq] at hcert
  rcases hcert with ⟨hst8, ⟨⟨⟨⟨⟨⟨⟨⟨⟨hd0a, hd0b⟩, hd1a⟩, hd1b⟩, hR0a⟩, hR0b⟩, hR1a⟩, hR1b⟩, hKa⟩, hKb⟩⟩
  let s (n : ℕ) := (stepSummary^[n]) extremalSeedSummary
  have hds_at : ∀ n (hn : n < 26),
      (orb.map summaryD).getD n ⟨0, 0⟩ = summaryD (s n) := by
    intro n hn
    rw [← horb, List.getD_eq_getElem?_getD, List.getElem?_map,
        collectSummaries_getElem? 26 extremalSeedSummary n hn]
    rfl
  rw [hds_at 2 (by omega)] at hd0a hd0b hR0a hR0b hKa hKb
  rw [hds_at 8 (by omega)] at hd1a hd1b hR0a hR0b hR1a hR1b hKa hKb
  rw [hds_at 14 (by omega)] at hR0a hR0b hR1a hR1b
  rw [hds_at 20 (by omega)] at hR1a hR1b
  -- Same 6-step periodicity for r = 0 (k = 2 + 6 * j)
  have hst_per : ∀ m : ℕ, (s (2 + m + 6)).st = (s (2 + m)).st := by
    intro m
    induction m with
    | zero => exact hst8
    | succ m ih =>
      have h1 : s (2 + (m + 1) + 6) = stepSummary (s (2 + m + 6)) := by
        have hidx : 2 + (m + 1) + 6 = (2 + m + 6) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      have h2 : s (2 + (m + 1)) = stepSummary (s (2 + m)) := by
        have hidx : 2 + (m + 1) = (2 + m) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      rw [h1, h2]; dsimp only [stepSummary]; rw [ih]
  have hst_per_j : ∀ t j : ℕ, (s (2 + t + 6 * j)).st = (s (2 + t)).st := by
    intro t j
    induction j with
    | zero => simp
    | succ j ih =>
      have hidx : 2 + t + 6 * (j + 1) = 2 + (t + 6 * j) + 6 := by omega
      rw [hidx, hst_per (t + 6 * j)]
      have hidx2 : 2 + (t + 6 * j) = 2 + t + 6 * j := by omega
      rw [hidx2, ih]
  -- Affine 6-step recurrence on pu, pz for r = 0
  let st_at (t : ℕ) := (s (2 + t)).st
  let stepPz (t : ℕ) (v : Vec5Z) : Vec5Z :=
    Vec5Z.add (stepMZ v) (parikhSym (phiStepCtx (st_at t)).2)
  let C0 : Vec5Z :=
    stepPz 5 (stepPz 4 (stepPz 3 (stepPz 2 (stepPz 1 (stepPz 0 Vec5Z.zero)))))
  have haff0 : ∀ j : ℕ,
      (s (2 + 6 * (j + 1))).pu = Vec5Z.add (stepM6Z ((s (2 + 6 * j)).pu)) Vec5Z.zero ∧
      (s (2 + 6 * (j + 1))).pz = Vec5Z.add (stepM6Z ((s (2 + 6 * j)).pz)) C0 := by
    intro j
    have hs_step : ∀ t : ℕ,
        (s (2 + 6 * j + (t + 1))).pu = stepMZ ((s (2 + 6 * j + t)).pu) ∧
        (s (2 + 6 * j + (t + 1))).pz = stepPz t ((s (2 + 6 * j + t)).pz) := by
      intro t
      have h1 : s (2 + 6 * j + (t + 1)) = stepSummary (s (2 + 6 * j + t)) := by
        have hidx : 2 + 6 * j + (t + 1) = (2 + 6 * j + t) + 1 := by omega
        rw [hidx]; exact Function.iterate_succ_apply' _ _ _
      rw [h1]; dsimp only [stepSummary, stepPz]
      have hsh : (s (2 + 6 * j + t)).st = st_at t := by
        have hidx : 2 + 6 * j + t = 2 + t + 6 * j := by omega
        rw [hidx, hst_per_j t j]
      rw [hsh]; exact ⟨rfl, rfl⟩
    have hidx6 : 2 + 6 * (j + 1) = 2 + 6 * j + 6 := by omega
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
      change stepM6Z (s (2 + 6 * j)).pu = Vec5Z.add (stepM6Z (s (2 + 6 * j)).pu) Vec5Z.zero
      cases stepM6Z (s (2 + 6 * j)).pu
      simp [Vec5Z.add, Vec5Z.zero]
    · rw [hz5, hz4, hz3, hz2, hz1, hz0]
      exact step6_affine_eq _ _ _ _ _ _ _
  let D (j : ℕ) : ZPhi := summaryD (s (2 + 6 * j))
  have hD_rec : ∀ j : ℕ, D (j + 4) - ⟨20, 0⟩ * D (j + 3) + ⟨38, 0⟩ * D (j + 2) -
      ⟨20, 0⟩ * D (j + 1) + D j = 0 := by
    intro j
    have hpu_r := affine_stepM6Z_sum_rec
      (v := fun n => (s (2 + 6 * n)).pu) (C := Vec5Z.zero) (fun n => (haff0 n).1) j
    have hpz_r := affine_stepM6Z_sum_rec
      (v := fun n => (s (2 + 6 * n)).pz) (C := C0) (fun n => (haff0 n).2) j
    dsimp only [D, summaryD]
    ext
    · simp only [ZPhi.add_a, ZPhi.sub_a, ZPhi.mul_a, ZPhi.zero_a]; linarith
    · simp only [ZPhi.add_b, ZPhi.sub_b, ZPhi.mul_b, ZPhi.zero_b]; linarith
  have hD0 : D 0 = summaryD (s 2) := congrArg (fun n => summaryD (s n)) (by omega)
  have hD1 : D 1 = summaryD (s 8) := congrArg (fun n => summaryD (s n)) (by omega)
  have hD2 : D 2 = summaryD (s 14) := congrArg (fun n => summaryD (s n)) (by omega)
  have hD3 : D 3 = summaryD (s 20) := congrArg (fun n => summaryD (s n)) (by omega)
  have hR0 : lamZPhi * (D 2 - D 1) - (D 1 - D 0) = 0 := by
    rw [hD2, hD1, hD0]; exact ZPhi.ext hR0a hR0b
  have hR1 : lamZPhi * (D 3 - D 2) - (D 2 - D 1) = 0 := by
    rw [hD3, hD2, hD1]; exact ZPhi.ext hR1a hR1b
  have hK_eq : lamZPhi * D 1 - D 0 = ⟨14, 26⟩ := by
    rw [hD1, hD0]; exact ZPhi.ext hKa hKb
  have hD0_eq : D 0 = ⟨-8, 7⟩ := by
    rw [hD0]; exact ZPhi.ext hd0a hd0b
  have hinv := residueBdd_inv hD_rec hR0 hR1
  -- 3-line upper bound: (D j).toReal ≤ 4 for ALL j : ℕ!
  have hD_le4 : ∀ j : ℕ, (D j).toReal ≤ 4 := by
    intro j
    induction j with
    | zero =>
      rw [hD0_eq]; simp only [ZPhi.toReal]; push_cast
      have h7s5 : 7 * Real.sqrt 5 < 17 := by
        have hsq : (7 * Real.sqrt 5) ^ 2 < 17 ^ 2 := by
          rw [mul_pow, sqrt5_sq]; norm_num
        nlinarith [sqrt5_pos]
      have h7 : 7 * φ ≤ 12 := by unfold φ; linarith
      linarith
    | succ j ih =>
      have hstep := congrArg ZPhi.toReal (hinv j)
      rw [hK_eq, ZPhi.toReal_sub, ZPhi.toReal_mul] at hstep
      have hlamR : lamZPhi.toReal = 5 + 8 * φ := by simp [lamZPhi, ZPhi.toReal]
      have hKR : (⟨14, 26⟩ : ZPhi).toReal = 14 + 26 * φ := by simp [ZPhi.toReal]
      rw [hlamR, hKR] at hstep
      have hlam_pos : 0 < 5 + 8 * φ := by linarith [phi_pos]
      have hprod_le : (5 + 8 * φ) * (D (j + 1)).toReal ≤ (5 + 8 * φ) * 4 := by
        linarith [one_lt_phi]
      exact le_of_mul_le_mul_left hprod_le hlam_pos
  -- Unbounded growth of pu.sum: nuVec ((s k).pu) = φ ^ k * nuVec (s 0).pu ≥ φ ^ k
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
  -- Choose j large enough so that 2 / φ ^ (2 + 6 * j) < ε
  -- Note φ ^ (6 * j) ≥ (3 / 2) ^ j ≥ 1 + j / 2, or even simpler: p_{2+6j} strictly grows by ≥ 1 each step!
  -- Wait: φ ^ 6 = 5 + 8 φ > 17 ≥ 2, so φ ^ (6 * j) ≥ 17 ^ j ≥ j + 1!
  have hphi6_ge2 : ∀ j : ℕ, (j + 1 : ℝ) ≤ φ ^ (2 + 6 * j) := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, Nat.cast_zero, zero_add]
      nlinarith [one_lt_phi]
    | succ j ih =>
      have hpow_split : φ ^ (2 + 6 * (j + 1)) = φ ^ (2 + 6 * j) * φ ^ 6 := by
        have : 2 + 6 * (j + 1) = (2 + 6 * j) + 6 := by omega
        rw [this, pow_add]
      have hphi6 : (2 : ℝ) ≤ φ ^ 6 := by
        have h1 : 1 < φ := one_lt_phi
        have h2 : 1 ≤ φ ^ 2 := by nlinarith
        have h3 : 1 ≤ φ ^ 4 := by nlinarith
        nlinarith [phi_sq]
      rw [hpow_split]
      push_cast
      have hge1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      nlinarith
  let j₀ : ℕ := ⌊2 / ε⌋₊ + 1
  have hj0_def : j₀ = ⌊2 / ε⌋₊ + 1 := rfl
  have hj0_gt : 2 / ε < (j₀ : ℝ) + 1 := by
    rw [hj0_def]
    have := Nat.lt_floor_add_one (2 / ε)
    push_cast; linarith
  let k₀ := 2 + 6 * j₀
  have hk0_def : k₀ = 2 + 6 * j₀ := rfl
  rcases exists_concreteRun_iter_summary k₀ hrun0 with ⟨i_k, p_k, m_k, hrk, hsum_k⟩
  rw [hsum0] at hsum_k
  change runSummary i_k p_k m_k = s k₀ at hsum_k
  rcases runSummary_sums i_k p_k m_k with ⟨hpu_sum, hpz_sum⟩
  rw [hsum_k] at hpu_sum hpz_sum
  -- Construct the finite factor w_k := List.ofFn (fun r : Fin (p_k + m_k) => b5 (i_k + r.val))
  let w_k : List (Fin 5) := List.ofFn fun r : Fin (p_k + m_k) => b5 (i_k + r.val)
  have hwk_len : w_k.length = p_k + m_k := by simp [w_k]
  have hpk_pos : 1 ≤ p_k := hrk.2.1
  have hwk_ne : w_k ≠ [] := by
    intro h; rw [h] at hwk_len; simp at hwk_len; omega
  have hwk_fac : IsFactorInf w_k b5 :=
    ⟨i_k, fun r hr => by simp [w_k]⟩
  have hwk_per : IsPeriod w_k p_k := by
    intro r hr
    rw [hwk_len] at hr
    simp only [w_k, List.getElem_ofFn]
    rw [← b5Sym_eq_iff]
    have hidx : i_k + (r + p_k) = i_k + r + p_k := by omega
    rw [hidx]
    exact hrk.2.2.1 r (by omega)
  refine ⟨w_k, p_k, hwk_ne, hwk_fac, hpk_pos, hwk_per, ?_⟩
  -- Bound (w_k.length : ℝ) / p_k = 1 + φ / 2 - (D j₀).toReal / (2 * p_k) > (5 + √5)/4 - ε
  have hDj0_le4 : (D j₀).toReal ≤ 4 := hD_le4 j₀
  have hDj0_val : (D j₀).toReal = -2 * (m_k : ℝ) + (p_k : ℝ) * φ := by
    change (summaryD (s (2 + 6 * j₀))).toReal = -2 * (m_k : ℝ) + (p_k : ℝ) * φ
    rw [← hk0_def]
    unfold summaryD ZPhi.toReal
    dsimp only
    rw [hpz_sum, hpu_sum]
    push_cast; ring
  have hpk_gt : 2 / ε < (p_k : ℝ) := by
    have h1 := hphi6_ge2 j₀
    have h2 := hpk_ge_pow k₀
    rw [hpu_sum] at h2
    push_cast at h2
    rw [hk0_def] at h2
    linarith
  have hpkR_pos : (0 : ℝ) < (p_k : ℝ) := by positivity
  have h2_div_lt : 2 / (p_k : ℝ) < ε := by
    rw [div_lt_iff₀ hpkR_pos]
    have := (div_lt_iff₀ hε).mp hpk_gt
    linarith
  rw [critVal_eq_one_add_half_phi, hwk_len]
  push_cast
  have hexp_id : ((p_k : ℝ) + (m_k : ℝ)) / (p_k : ℝ) =
      1 + φ / 2 - (D j₀).toReal / (2 * (p_k : ℝ)) := by
    rw [hDj0_val]
    field_simp [ne_of_gt hpkR_pos]
    ring
  rw [hexp_id]
  have hfrac_le : (D j₀).toReal / (2 * (p_k : ℝ)) ≤ 2 / (p_k : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hpkR_pos]
    nlinarith
  linarith

/-- **Main Theorem `R18-2-ce-1` (`b5_critical_exponent_eq`)**:
The exact critical exponent of `b_5` is `(5 + Real.sqrt 5) / 4`. -/
theorem b5_critical_exponent_eq :
    critExp b5 = (5 + Real.sqrt 5) / 4 := by
  unfold critExp
  have hnonempty : (ExponentSet b5).Nonempty := by
    refine ⟨0, [], 1, isFactorInf_nil b5, le_refl 1, ?_, by simp⟩
    intro _ hi; simp at hi
  apply le_antisymm
  · refine csSup_le hnonempty ?_
    rintro e ⟨w, p, hfac, hp, hper, rfl⟩
    exact le_of_lt (b5_exponent_lt_crit w p hfac hp hper)
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    rcases b5_sup_exponent_ge_crit (ε / 2) (by linarith) with ⟨w, p, _, hfac, hp, hper, hgt⟩
    have hmem : (w.length : ℝ) / (p : ℝ) ∈ ExponentSet b5 :=
      ⟨w, p, hfac, hp, hper, rfl⟩
    have hbdd : BddAbove (ExponentSet b5) := by
      refine ⟨(5 + Real.sqrt 5) / 4, ?_⟩
      rintro e ⟨w', p', hf', hp', hpr', rfl⟩
      exact le_of_lt (b5_exponent_lt_crit w' p' hf' hp' hpr')
    have hle_sup : (w.length : ℝ) / (p : ℝ) ≤ sSup (ExponentSet b5) :=
      le_csSup hbdd hmem
    linarith

/-- Equivalent `sSup` identity over `NonemptyExponentSet b5` (`w ≠ []`). -/
theorem b5_nonempty_critical_exponent_eq :
    sSup (NonemptyExponentSet b5) = (5 + Real.sqrt 5) / 4 := by
  rcases b5_sup_exponent_ge_crit 1 zero_lt_one with ⟨w₀, p₀, hw₀, hfac₀, hp₀, hper₀, _⟩
  have hnonempty : (NonemptyExponentSet b5).Nonempty :=
    ⟨exponent w₀ p₀, w₀, p₀, hw₀, hfac₀, hp₀, hper₀, rfl⟩
  apply le_antisymm
  · refine csSup_le hnonempty ?_
    rintro e ⟨w, p, _, hfac, hp, hper, rfl⟩
    exact le_of_lt (b5_exponent_lt_crit w p hfac hp hper)
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    rcases b5_sup_exponent_ge_crit (ε / 2) (by linarith) with ⟨w, p, hw, hfac, hp, hper, hgt⟩
    have hmem : exponent w p ∈ NonemptyExponentSet b5 :=
      ⟨w, p, hw, hfac, hp, hper, rfl⟩
    have hbdd : BddAbove (NonemptyExponentSet b5) := by
      refine ⟨(5 + Real.sqrt 5) / 4, ?_⟩
      rintro e ⟨w', p', _, hf', hp', hpr', rfl⟩
      exact le_of_lt (b5_exponent_lt_crit w' p' hf' hp' hpr')
    have hle_sup : exponent w p ≤ sSup (NonemptyExponentSet b5) :=
      le_csSup hbdd hmem
    unfold exponent at hle_sup
    linarith

/-- **Non-Attainment Theorem (`b5_critical_exponent_not_attained`)**:
No factor `w` of `b_5` and period `p ≥ 1` of `w` attains `(w.length : ℝ) / p = (5 + Real.sqrt 5) / 4`. -/
theorem b5_critical_exponent_not_attained :
    ¬ ∃ w p, IsFactorInf w b5 ∧ 1 ≤ p ∧ IsPeriod w p ∧
      (w.length : ℝ) / (p : ℝ) = (5 + Real.sqrt 5) / 4 := by
  rintro ⟨w, p, hfac, hp, hper, heq⟩
  exact ne_of_lt (b5_exponent_lt_crit w p hfac hp hper) heq

end BadkobehOchemB5
