module

public import BadkobehOchemB5.Defs
public import BadkobehOchemB5.CriticalExponent
import Mathlib.Tactic

/-!
# Theorem `R18-2-1` Part (2): Opposite-Sign Law, Bipartite XYX Graph, and Odd-Cycle Avoidance

Combining the 5-interval coding convexity theorem `b5_uvu_opposite_signs_of_not_square` from
`Defs.lean` with unconditional square-freeness `b5_squarefree` from `CriticalExponent.lean`
(`E(b_5) = (5 + √5) / 4 < 2`), this module proves **100% unconditionally**:

1. **`b5_uvu_opposite_signs`**: For EVERY pair of non-empty words `u, v : List (Fin 5)` such that
   `u ++ v ++ u` is a factor of `b5`, `lambda' u ≠ 0`, `lambda' v ≠ 0`,
   `lambda' u * lambda' v < 0`, and `|lambda' (u ++ v)| < |lambda' u|`.
2. **`b5_relation_bipartite`**: The symmetric XYX relation graph `RelB5` on non-empty factors of
   `b5` is strictly 2-colourable / bipartite under `b5SignCol u := decide (0 < lambda' u)`.
3. **`b5_avoids_odd_cycle_xyx`**: `b5` avoids the XYX-formula `F_G` of **every** loopless digraph
   `G` whose underlying undirected graph contains an odd cycle — in particular `C3`, every
   transitive tournament `TT n` (`n ≥ 3`), and every complete digraph `Kn n` (`n ≥ 3`).
-/

@[expose] public section

namespace BadkobehOchemB5

/-- **Theorem `R18-2-1` Part (2) (`b5_uvu_opposite_signs`)**:
Whenever `u ++ v ++ u` (`u ≠ []`, `v ≠ []`) is a factor of `b_5`:
1. `lambda' u ≠ 0` and `lambda' v ≠ 0`;
2. `lambda' u` and `lambda' v` have strictly opposite signs (`lambda' u * lambda' v < 0`);
3. `|lambda' (u ++ v)| < |lambda' u|`. -/
theorem b5_uvu_opposite_signs {u v : List (Fin 5)}
    (hu : u ≠ []) (hv : v ≠ [])
    (hfac : IsFactorInf (u ++ v ++ u) b5) :
    lambda' u ≠ 0 ∧ lambda' v ≠ 0 ∧
    lambda' u * lambda' v < 0 ∧
    |lambda' (u ++ v)| < |lambda' u| :=
  b5_uvu_opposite_signs_of_not_square hu hv (b5_squarefree hu) hfac

/-- Canonical 2-colouring of non-empty factors of `b_5` by the sign of `lambda' u`. -/
noncomputable def b5SignCol (u : List (Fin 5)) : Bool :=
  decide (0 < lambda' u)

theorem b5SignCol_ne_of_rel {u v : List (Fin 5)} (hrel : RelB5 u v) :
    b5SignCol u ≠ b5SignCol v := by
  rcases hrel with ⟨hu, hv, hfac | hfac⟩
  · rcases b5_uvu_opposite_signs hu hv hfac with ⟨hlu, hlv, hopp, _⟩
    intro heq
    unfold b5SignCol at heq
    by_cases hpu : 0 < lambda' u
    · have hpv : 0 < lambda' v := by
        have htrue : decide (0 < lambda' v) = true := heq ▸ decide_eq_true_eq.mpr hpu
        exact decide_eq_true_eq.mp htrue
      nlinarith [mul_pos hpu hpv]
    · have hnpv : ¬ (0 < lambda' v) := by
        have hfalse : decide (0 < lambda' v) = false := heq ▸ decide_eq_false_iff_not.mpr hpu
        exact decide_eq_false_iff_not.mp hfalse
      have hnu : lambda' u < 0 := lt_of_le_of_ne (le_of_not_gt hpu) hlu
      have hnv : lambda' v < 0 := lt_of_le_of_ne (le_of_not_gt hnpv) hlv
      nlinarith [mul_pos_of_neg_of_neg hnu hnv]
  · rcases b5_uvu_opposite_signs hv hu hfac with ⟨hlv, hlu, hopp, _⟩
    intro heq
    unfold b5SignCol at heq
    by_cases hpu : 0 < lambda' u
    · have hpv : 0 < lambda' v := by
        have htrue : decide (0 < lambda' v) = true := heq ▸ decide_eq_true_eq.mpr hpu
        exact decide_eq_true_eq.mp htrue
      nlinarith [mul_pos hpv hpu]
    · have hnpv : ¬ (0 < lambda' v) := by
        have hfalse : decide (0 < lambda' v) = false := heq ▸ decide_eq_false_iff_not.mpr hpu
        exact decide_eq_false_iff_not.mp hfalse
      have hnu : lambda' u < 0 := lt_of_le_of_ne (le_of_not_gt hpu) hlu
      have hnv : lambda' v < 0 := lt_of_le_of_ne (le_of_not_gt hnpv) hlv
      nlinarith [mul_pos_of_neg_of_neg hnv hnu]

/-- **Bipartiteness of the XYX Relation Graph of `b_5` (`b5_relation_bipartite`)**:
`b5SignCol` is a proper 2-colouring of `RelB5`, so `RelB5` is bipartite. -/
theorem b5_relation_bipartite :
    (∀ u v, RelB5 u v → b5SignCol u ≠ b5SignCol v) ∧
    ∃ col : List (Fin 5) → Bool, ∀ u v, RelB5 u v → col u ≠ col v :=
  ⟨fun _ _ h => b5SignCol_ne_of_rel h, b5SignCol, fun _ _ h => b5SignCol_ne_of_rel h⟩

/-- Parity alternation along a `Bool`-valued sequence where consecutive entries differ. -/
theorem bool_seq_parity {f : ℕ → Bool} {L : ℕ}
    (hstep : ∀ j < L, f (j + 1) ≠ f j) :
    ∀ j ≤ L, f j = (if j % 2 = 0 then f 0 else !(f 0)) := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hprev := ih (by omega)
    have hne := hstep j (by omega)
    have hflip : f (j + 1) = !(f j) := by
      cases h1 : f (j + 1) <;> cases h2 : f j <;> simp_all
    rw [hflip, hprev]
    by_cases heven : j % 2 = 0
    · have hodd : (j + 1) % 2 ≠ 0 := by omega
      simp [heven, hodd]
    · have heven' : (j + 1) % 2 = 0 := by omega
      simp [heven, heven']

/-- **Unconditional Odd-Cycle XYX Avoidance (`b5_avoids_odd_cycle_xyx`)**:
`b_5` avoids the XYX-formula `F_G` of EVERY loopless digraph `G` whose underlying undirected
graph contains an odd cycle. -/
theorem b5_avoids_odd_cycle_xyx {V : Type*} (G : LooplessDigraph V)
    (hodd : HasOddCycle G) : AvoidsDigraphInf G b5 := by
  rintro ⟨h, hne, hocc⟩
  rcases hodd with ⟨k, cyc, hcyc⟩
  let L := 2 * k + 1
  have hL_pos : 0 < L := by dsimp [L]; omega
  let seq (j : ℕ) : Bool := b5SignCol (h (cyc ⟨j % L, Nat.mod_lt j hL_pos⟩))
  have hstep : ∀ j < L, seq (j + 1) ≠ seq j := by
    intro j hj
    dsimp [seq]
    have hj_mod : j % L = j := Nat.mod_eq_of_lt hj
    have hadj := hcyc ⟨j, hj⟩
    have hrel : RelB5 (h (cyc ⟨j, hj⟩)) (h (cyc ⟨(j + 1) % L, Nat.mod_lt _ hL_pos⟩)) := by
      refine ⟨hne _, hne _, ?_⟩
      rcases hadj with h1 | h2
      · exact Or.inl (hocc _ _ h1)
      · exact Or.inr (hocc _ _ h2)
    have hcol_ne := b5SignCol_ne_of_rel hrel
    have hfin_eq : (⟨j % L, Nat.mod_lt j hL_pos⟩ : Fin L) = ⟨j, hj⟩ := by
      ext; exact hj_mod
    rw [hfin_eq]
    exact hcol_ne.symm
  have hL_val := bool_seq_parity hstep L (le_refl L)
  have hL_wrap : seq L = seq 0 := by
    dsimp [seq]
    congr 3
    ext
    simp [Nat.mod_self]
  have hL_odd : L % 2 ≠ 0 := by dsimp [L]; omega
  rw [hL_wrap] at hL_val
  simp only [hL_odd, ↓reduceIte] at hL_val
  cases seq 0 <;> simp at hL_val

/-- `C3` contains an odd cycle of length `3`. -/
theorem hasOddCycle_C3 : HasOddCycle C3 := by
  refine ⟨1, id, ?_⟩
  intro i
  left
  fin_cases i <;> rfl

/-- **Corollary (`b5_avoids_C3`)**: `b_5` avoids the cyclic triangle `C_3`. -/
theorem b5_avoids_C3 : AvoidsDigraphInf C3 b5 :=
  b5_avoids_odd_cycle_xyx C3 hasOddCycle_C3

/-- Every transitive tournament `TT n` with `n ≥ 3` contains an undirected triangle. -/
theorem hasOddCycle_TT {n : ℕ} (hn : 3 ≤ n) : HasOddCycle (TT n) := by
  let v : Fin 3 → Fin n
    | 0 => ⟨0, by omega⟩
    | 1 => ⟨1, by omega⟩
    | 2 => ⟨2, by omega⟩
  refine ⟨1, v, ?_⟩
  intro i
  fin_cases i
  · left; change (0 : ℕ) < 1; omega
  · left; change (1 : ℕ) < 2; omega
  · right; change (0 : ℕ) < 2; omega

/-- **Corollary (`b5_avoids_TT`)**: `b_5` avoids every transitive tournament `TT n` for `n ≥ 3`
(`TT 3`, `TT 4`, `TT 5`, ...). -/
theorem b5_avoids_TT (n : ℕ) (hn : 3 ≤ n) : AvoidsDigraphInf (TT n) b5 :=
  b5_avoids_odd_cycle_xyx (TT n) (hasOddCycle_TT hn)

/-- Every complete digraph `Kn n` with `n ≥ 3` contains a triangle. -/
theorem hasOddCycle_Kn {n : ℕ} (hn : 3 ≤ n) : HasOddCycle (Kn n) := by
  let v : Fin 3 → Fin n
    | 0 => ⟨0, by omega⟩
    | 1 => ⟨1, by omega⟩
    | 2 => ⟨2, by omega⟩
  refine ⟨1, v, ?_⟩
  intro i
  left
  fin_cases i <;>
    (intro heq; have hval := congrArg Fin.val heq; dsimp [v] at hval; omega)

/-- **Corollary (`b5_avoids_Kn`)**: `b_5` avoids `K_n` for all `n ≥ 3`. -/
theorem b5_avoids_Kn (n : ℕ) (hn : 3 ≤ n) : AvoidsDigraphInf (Kn n) b5 :=
  b5_avoids_odd_cycle_xyx (Kn n) (hasOddCycle_Kn hn)

end BadkobehOchemB5
