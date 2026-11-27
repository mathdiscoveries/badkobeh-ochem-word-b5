# Badkobeh and Ochem's Word `b5`: Lean 4 + Mathlib Formalization

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490746.svg)](https://doi.org/10.5281/zenodo.24490746)

Unconditional Lean 4 (`v4.35.0`) + Mathlib (`v4.35.0`) formalization (514 audited declarations, zero `sorry`, zero `native_decide`, standard axioms `propext`, `Quot.sound`, `Classical.choice` only) resolving all four questions and observations (Q1, Q2, O1, O2) from Badkobeh and Ochem (*Theoret. Comput. Sci.* 588, 2015) for the 5-letter fixed point `b5 = f5^ω(0)` (`0 ↦ 01, 1 ↦ 23, 2 ↦ 4, 3 ↦ 21, 4 ↦ 0`).

Coverage by this package's Palomar comparison: the four headline questions and observations are compared in Lean, 4 of 4 (100%). Of the companion paper's 10 theorem parts, 2 are compared in full (20%; parts 2(A) and 5(B)) and 6 in part (1(A), 2(B), 3(B), 4(A), 4(B) and 5(A); part 1(A) is compared through its coding statement, not its orbit equation $x_{p+1} = T(x_p)$); parts 1(B) and 3(A) are not compared. The supporting library has declarations for each uncompared part and piece; for Theorem 4(B) it proves the inverse-power formula $E_j = \varphi^{-(11 + 6j)}$, and the paper's expansion of $E_j$ in Fibonacci numbers is a further identity not stated in Lean.

Companion manuscript, interactive Proof Blueprint, and verification archive:
<https://mathdiscoveries.org/results/badkobeh-ochem-word-b5>

## Compared Theorems (`Challenge.lean` / `Solution.lean`)

1. `b5_codes_interval_translation` — 5-interval coding of `b5` via the golden-ratio 3-interval exchange on `(-φ²/2, φ³/2)`.
2. `b5_factor_complexity` — **(Q1)** exact factor complexity `4n + 1` for all `n ≥ 0`.
3. `b5_sturmian_projection` — **(O1)** exact factor-set equality `L_n(g_fib(b5)) = L_n(f)` with complexity `n + 1`.
4. `b5_rote_fibonacci_projection` — **(O2)** exact factor-set equality `L_n(g_rf(b5)) = L_n(r)` with complexity `2n` (`n ≥ 1`).
5. `b5_critical_exponent` — **(Q2)** exact unattained critical exponent `E(b5) = (5 + √5) / 4`.
6. `b5_sharp_second_order_and_deficit` — sharp second-order bound `|w|/p < (5 + √5)/4 - (7 - √5)/(8p)` and exact unattained deficit infimum `(7 - √5)/4`.
7. `b5_asymp_critExp_and_irrational` — asymptotic critical exponent `E*(b5) = (5 + √5)/4` and irrationality of `E(b5)`.
8. `b5_language_rev_swap34_invariant` — invariance of the factor language under reversal composed with `3 ↔ 4`.
9. `pi3B5_factor_complexity` — ternary 3-IET collapse `π₃(b5)` complexity `2n + 1`.
10. `b5_not_C_balanced` — unbounded balance defect (`b5` is not `C`-balanced for any `C`).
11. `fB5_iter_length_rec` — exact 5th-order `A005252` length recurrence.

## Verification

```sh
lake build BadkobehOchemB5 BadkobehOchemB5.Verify Challenge Solution
lake env lean BadkobehOchemB5/Verify.lean
```

## Disclosure & License

Generated and checked by AI research agents built and directed by **Tyler B. Hughes**. No human mathematician has yet refereed the proof. Licensed under Apache-2.0.
