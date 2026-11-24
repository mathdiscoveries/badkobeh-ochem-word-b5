module

public import BadkobehOchemB5.Defs
import Mathlib.Tactic

/-!
# Fast Pure-Kernel Certificates for `R18-2-ce-1` (`SeedsCert`)

Uses constructor-tag alphabet `Sym5` (isomorphic to `Fin 5` via `Sym5.toFin` / `Sym5.ofFin`),
two-stage pre-evaluated `g5Val` / `g10Val` (`= iterSym5 10 [x]`), and tail-recursive scanners
`allTR` / `scanDrops256` / `hasLenAtLeast` so every finite certificate checks in the Lean 4 kernel
via `rfl` / `decide` well within default `maxHeartbeats` and `maxRecDepth` (zero `native_decide`).
-/

@[expose] public section

namespace BadkobehOchemB5

/-- Five-letter constructor-tag alphabet isomorphic to `Fin 5`, giving 1-step kernel reduction. -/
inductive Sym5 where
  | s0 | s1 | s2 | s3 | s4
  deriving DecidableEq, Repr

def Sym5.toFin : Sym5 → Fin 5
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4

def Sym5.ofFin : Fin 5 → Sym5
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | 3 => .s3 | 4 => .s4

theorem Sym5.ofFin_toFin (x : Sym5) : Sym5.ofFin x.toFin = x := by
  cases x <;> rfl

theorem Sym5.toFin_ofFin (a : Fin 5) : (Sym5.ofFin a).toFin = a := by
  fin_cases a <;> rfl

def Sym5.beq (x y : Sym5) : Bool :=
  match x, y with
  | .s0, .s0 | .s1, .s1 | .s2, .s2 | .s3, .s3 | .s4, .s4 => true
  | _, _ => false

theorem Sym5.beq_iff_eq (x y : Sym5) : Sym5.beq x y = true ↔ x = y := by
  cases x <;> cases y <;> decide

/-- Tail-recursive `List.all` with `O(1)` stack depth in `whnf`. -/
def allTR {α : Type*} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => if p x then allTR p xs else false

theorem allTR_eq_all {α : Type*} (p : α → Bool) (l : List α) :
    allTR p l = l.all p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [allTR, List.all_cons, ih]
    cases p x <;> rfl

/-- Bounded-depth length check `k ≤ l.length` (`O(k)` frames instead of `O(l.length)`). -/
def hasLenAtLeast {α : Type*} : ℕ → List α → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | k + 1, _ :: xs => hasLenAtLeast k xs

theorem hasLenAtLeast_iff {α : Type*} (k : ℕ) (l : List α) :
    hasLenAtLeast k l = true ↔ k ≤ l.length := by
  induction k generalizing l with
  | zero => simp [hasLenAtLeast]
  | succ k ih =>
    cases l with
    | nil => simp [hasLenAtLeast]
    | cons _ xs =>
      simp only [hasLenAtLeast, ih, List.length_cons]
      omega

/-- Morphism `f_5` on `Sym5`: `0 ↦ 01, 1 ↦ 23, 2 ↦ 4, 3 ↦ 21, 4 ↦ 0`. -/
def fSym5 : Sym5 → List Sym5
  | .s0 => [.s0, .s1]
  | .s1 => [.s2, .s3]
  | .s2 => [.s4]
  | .s3 => [.s2, .s1]
  | .s4 => [.s0]

def morphSym5 : List Sym5 → List Sym5
  | [] => []
  | a :: rest => fSym5 a ++ morphSym5 rest

def iterSym5 : ℕ → List Sym5 → List Sym5
  | 0, w => w
  | n + 1, w => morphSym5 (iterSym5 n w)

theorem fSym5_map_toFin (x : Sym5) : (fSym5 x).map Sym5.toFin = fB5 x.toFin := by
  cases x <;> rfl

theorem morphSym5_map_toFin (w : List Sym5) :
    (morphSym5 w).map Sym5.toFin = applyMorph fB5 (w.map Sym5.toFin) := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    simp only [morphSym5, List.map_append, fSym5_map_toFin, ih, List.map_cons, applyMorph_cons]

theorem morphSym5_append (u v : List Sym5) :
    morphSym5 (u ++ v) = morphSym5 u ++ morphSym5 v := by
  induction u with
  | nil => rfl
  | cons a rest ih => simp only [List.cons_append, morphSym5, ih, List.append_assoc]

theorem iterSym5_append (n : ℕ) (u v : List Sym5) :
    iterSym5 n (u ++ v) = iterSym5 n u ++ iterSym5 n v := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterSym5, ih, morphSym5_append]

theorem iterSym5_add (m n : ℕ) (w : List Sym5) :
    iterSym5 (m + n) w = iterSym5 m (iterSym5 n w) := by
  induction m with
  | zero => simp [iterSym5]
  | succ m ih => simp only [Nat.succ_add, iterSym5, ih]

theorem iterSym5_map_toFin (n : ℕ) (w : List Sym5) :
    (iterSym5 n w).map Sym5.toFin = iterMorph fB5 n (w.map Sym5.toFin) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterSym5, morphSym5_map_toFin, ih, iterMorph_succ]

def sym5All : List Sym5 := [.s0, .s1, .s2, .s3, .s4]

theorem mem_sym5All (x : Sym5) : x ∈ sym5All := by
  cases x <;> decide

/-- Explicit level-5 and level-10 blocks `g5Val` and `g10Val`, kernel-verified equal to `iterSym5`. -/
def g5Val : Sym5 → List Sym5
  | .s0 => [.s0, .s1, .s2, .s3, .s4, .s2, .s1, .s0, .s4, .s2, .s3, .s0, .s1, .s0, .s4, .s2, .s1]
  | .s1 => [.s0, .s1, .s2, .s3, .s0, .s1, .s0, .s4, .s2, .s3]
  | .s2 => [.s0, .s1, .s2, .s3, .s4, .s2, .s1]
  | .s3 => [.s0, .s1, .s2, .s3, .s0, .s1, .s0, .s4, .s2, .s1]
  | .s4 => [.s0, .s1, .s2, .s3, .s4, .s2, .s1, .s0, .s4, .s2, .s3]

theorem g5Val_eq_iterSym5 (x : Sym5) : g5Val x = iterSym5 5 [x] := by
  cases x <;> rfl

def expandG5 : List Sym5 → List Sym5
  | [] => []
  | y :: ys => g5Val y ++ expandG5 ys

def g10Val (x : Sym5) : List Sym5 :=
  expandG5 (g5Val x)

theorem expandG5_eq_iterSym5 (w : List Sym5) : expandG5 w = iterSym5 5 w := by
  induction w with
  | nil => rfl
  | cons y ys ih =>
    change g5Val y ++ expandG5 ys = iterSym5 5 ([y] ++ ys)
    rw [g5Val_eq_iterSym5, ih, iterSym5_append]

theorem g10Val_eq_iterSym5 (x : Sym5) : g10Val x = iterSym5 10 [x] := by
  rw [g10Val, expandG5_eq_iterSym5, g5Val_eq_iterSym5, ← iterSym5_add]

theorem g10Val_len_lt_256_bool (x : Sym5) : hasLenAtLeast 256 (g10Val x) = false := by
  cases x <;> rfl

/-- The 9 valid 2-factors of `b_5`: `01, 04, 10, 12, 21, 23, 30, 34, 42`. -/
def valid2Sym : Sym5 → Sym5 → Bool
  | .s0, .s1 | .s0, .s4 | .s1, .s0 | .s1, .s2 | .s2, .s1
  | .s2, .s3 | .s3, .s0 | .s3, .s4 | .s4, .s2 => true
  | _, _ => false

def valid2 (a b : Fin 5) : Bool :=
  valid2Sym (Sym5.ofFin a) (Sym5.ofFin b)

def twoFactorSymList : List (Sym5 × Sym5) :=
  [(.s0, .s1), (.s0, .s4), (.s1, .s0), (.s1, .s2), (.s2, .s1),
   (.s2, .s3), (.s3, .s0), (.s3, .s4), (.s4, .s2)]

def allAdjValid2Sym : List Sym5 → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => valid2Sym a b && allAdjValid2Sym (b :: rest)

def isCutPairSym : Sym5 → Sym5 → Bool
  | .s0, .s1 | .s2, .s1 | .s2, .s3 => false
  | _, _ => true

def isCutPair (a b : Fin 5) : Bool :=
  isCutPairSym (Sym5.ofFin a) (Sym5.ofFin b)

structure Word3 where
  a : Sym5
  b : Sym5
  c : Sym5
  deriving DecidableEq, Repr

def Word3.beq (x y : Word3) : Bool :=
  Sym5.beq x.a y.a && Sym5.beq x.b y.b && Sym5.beq x.c y.c

theorem Word3.beq_iff_eq (x y : Word3) : Word3.beq x y = true ↔ x = y := by
  rcases x with ⟨a1, b1, c1⟩; rcases y with ⟨a2, b2, c2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;> decide

def Word3.toList (w : Word3) : List Sym5 := [w.a, w.b, w.c]

def Word3.isValid (w : Word3) : Bool :=
  valid2Sym w.a w.b && valid2Sym w.b w.c

def word3OfList : List Sym5 → Word3
  | a :: b :: c :: _ => ⟨a, b, c⟩
  | [a, b] => ⟨a, b, .s0⟩
  | [a] => ⟨a, .s0, .s0⟩
  | [] => ⟨.s0, .s0, .s0⟩

def last3 (l : List Sym5) : Word3 :=
  word3OfList (l.drop (l.length - 3))

def first3 (l : List Sym5) : Word3 :=
  word3OfList l

def validWord3List : List Word3 :=
  [⟨.s0, .s1, .s0⟩, ⟨.s0, .s1, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩,
   ⟨.s1, .s0, .s4⟩, ⟨.s1, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s2, .s1, .s0⟩,
   ⟨.s2, .s1, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s3, .s0, .s1⟩,
   ⟨.s3, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩]

def eLOf : Sym5 → Sym5 → List Sym5
  | .s0, .s3 | .s3, .s0 => [.s1]
  | _, _ => []

def eROf : Sym5 → Sym5 → List Sym5
  | .s0, .s4 | .s4, .s0 => [.s0]
  | .s1, .s3 | .s3, .s1 => [.s2]
  | _, _ => []

def nextLeftCtx (W : Word3) (lam : ℕ) : Word3 :=
  let fw := morphSym5 W.toList
  last3 (fw.take (fw.length - lam))

def nextRightCtx (W : Word3) (rho : ℕ) : Word3 :=
  let fw := morphSym5 W.toList
  first3 (fw.drop rho)

structure CtxState where
  X : Word3
  Y : Word3
  S : Word3
  T : Word3
  deriving DecidableEq, Repr

def CtxState.beq (s1 s2 : CtxState) : Bool :=
  Word3.beq s1.X s2.X && Word3.beq s1.Y s2.Y && Word3.beq s1.S s2.S && Word3.beq s1.T s2.T

theorem CtxState.beq_iff_eq (s1 s2 : CtxState) : CtxState.beq s1 s2 = true ↔ s1 = s2 := by
  simp only [CtxState.beq, Bool.and_eq_true, Word3.beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; cases s1; cases s2; simp_all
  · rintro rfl; simp

def CtxState.isValid (st : CtxState) : Bool :=
  st.X.isValid && st.Y.isValid && st.S.isValid && st.T.isValid &&
  !Sym5.beq st.X.c st.Y.c && !Sym5.beq st.S.a st.T.a

def phiStepCtx (st : CtxState) : CtxState × List Sym5 :=
  let eL := eLOf st.X.c st.Y.c
  let eR := eROf st.S.a st.T.a
  let lam := eL.length
  let rho := eR.length
  ({ X := nextLeftCtx st.X lam
     Y := nextLeftCtx st.Y lam
     S := nextRightCtx st.S rho
     T := nextRightCtx st.T rho }, eL ++ eR)

structure Vec5Z where
  v0 : ℤ
  v1 : ℤ
  v2 : ℤ
  v3 : ℤ
  v4 : ℤ
  deriving DecidableEq, Repr

def Vec5Z.beq (x y : Vec5Z) : Bool :=
  decide (x.v0 = y.v0) && decide (x.v1 = y.v1) && decide (x.v2 = y.v2) &&
  decide (x.v3 = y.v3) && decide (x.v4 = y.v4)

theorem Vec5Z.beq_iff_eq (x y : Vec5Z) : Vec5Z.beq x y = true ↔ x = y := by
  simp only [Vec5Z.beq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩; cases x; cases y; simp_all
  · rintro rfl; simp

def Vec5Z.zero : Vec5Z := ⟨0, 0, 0, 0, 0⟩

def Vec5Z.add (x y : Vec5Z) : Vec5Z :=
  ⟨x.v0 + y.v0, x.v1 + y.v1, x.v2 + y.v2, x.v3 + y.v3, x.v4 + y.v4⟩

def Vec5Z.sub (x y : Vec5Z) : Vec5Z :=
  ⟨x.v0 - y.v0, x.v1 - y.v1, x.v2 - y.v2, x.v3 - y.v3, x.v4 - y.v4⟩

def Vec5Z.smul (k : ℤ) (x : Vec5Z) : Vec5Z :=
  ⟨k * x.v0, k * x.v1, k * x.v2, k * x.v3, k * x.v4⟩

def Vec5Z.sum (x : Vec5Z) : ℤ :=
  x.v0 + x.v1 + x.v2 + x.v3 + x.v4

def Vec5Z.ofSym : Sym5 → Vec5Z
  | .s0 => ⟨1, 0, 0, 0, 0⟩
  | .s1 => ⟨0, 1, 0, 0, 0⟩
  | .s2 => ⟨0, 0, 1, 0, 0⟩
  | .s3 => ⟨0, 0, 0, 1, 0⟩
  | .s4 => ⟨0, 0, 0, 0, 1⟩

def parikhSym : List Sym5 → Vec5Z
  | [] => Vec5Z.zero
  | a :: rest => Vec5Z.add (Vec5Z.ofSym a) (parikhSym rest)

def stepMZ (v : Vec5Z) : Vec5Z :=
  ⟨v.v0 + v.v4, v.v0 + v.v3, v.v1 + v.v3, v.v1, v.v2⟩

def stepM6Z (v : Vec5Z) : Vec5Z :=
  stepMZ (stepMZ (stepMZ (stepMZ (stepMZ (stepMZ v)))))

def zphiPosFast (z : ZPhi) : Bool :=
  let p : ℤ := 2 * z.a + z.b
  let q : ℤ := z.b
  if decide (0 ≤ p) && decide (0 ≤ q) then decide (0 < p) || decide (0 < q)
  else if decide (p ≤ 0) && decide (q ≤ 0) then false
  else if decide (0 < p) then decide (5 * (q * q) < p * p)
  else decide (p * p < 5 * (q * q))

theorem zphiPosFast_eq_isPos (z : ZPhi) : zphiPosFast z = z.isPos := by
  unfold zphiPosFast ZPhi.isPos
  dsimp only
  by_cases hp0 : 0 ≤ 2 * z.a + z.b <;> by_cases hq0 : 0 ≤ z.b <;>
    by_cases hple : 2 * z.a + z.b ≤ 0 <;> by_cases hqle : z.b ≤ 0 <;>
    by_cases hplt : 0 < 2 * z.a + z.b <;> by_cases hqlt : 0 < z.b <;>
    simp [sq, hp0, hq0, hple, hqle, hplt, hqlt]

structure SeedSummary where
  st : CtxState
  pu : Vec5Z
  pz : Vec5Z
  deriving DecidableEq, Repr

def SeedSummary.beq (x y : SeedSummary) : Bool :=
  CtxState.beq x.st y.st && Vec5Z.beq x.pu y.pu && Vec5Z.beq x.pz y.pz

theorem SeedSummary.beq_iff_eq (x y : SeedSummary) : SeedSummary.beq x y = true ↔ x = y := by
  simp only [SeedSummary.beq, Bool.and_eq_true, CtxState.beq_iff_eq, Vec5Z.beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; cases x; cases y; simp_all
  · rintro rfl; simp

def stepSummary (s : SeedSummary) : SeedSummary :=
  let res := phiStepCtx s.st
  { st := res.1
    pu := stepMZ s.pu
    pz := Vec5Z.add (stepMZ s.pz) (parikhSym res.2) }

def summaryD (s : SeedSummary) : ZPhi :=
  ⟨-2 * s.pz.sum, s.pu.sum⟩

def collectSummaries : ℕ → SeedSummary → List SeedSummary
  | 0, _ => []
  | k + 1, s => s :: collectSummaries k (stepSummary s)

def lamZPhi : ZPhi := ⟨5, 8⟩

def checkResidueInc (d0 d1 d2 d3 : ZPhi) : Bool :=
  let two : ZPhi := ⟨2, 0⟩
  let A0 := (d2 - two * d1) + d0
  let A1 := (d3 - two * d2) + d1
  zphiPosFast d0 && zphiPosFast (d1 - d0) && zphiPosFast A0 && zphiPosFast (A1 - A0)

def checkResidueBdd (d0 d1 d2 d3 : ZPhi) : Bool :=
  let R0 := lamZPhi * (d2 - d1) - (d1 - d0)
  let R1 := lamZPhi * (d3 - d2) - (d2 - d1)
  let K := lamZPhi * d1 - d0
  decide (R0.a = 0) && decide (R0.b = 0) &&
  decide (R1.a = 0) && decide (R1.b = 0) &&
  zphiPosFast d0 && zphiPosFast K

def checkSummaryZPhi (s : SeedSummary) : Bool :=
  let orb := collectSummaries 26 s
  match orb[2]?, orb[8]? with
  | some s2, some s8 =>
    CtxState.beq s8.st s2.st &&
    let ds := orb.map summaryD
    zphiPosFast (ds.getD 0 ⟨0, 0⟩) &&
    zphiPosFast (ds.getD 1 ⟨0, 0⟩) &&
    allTR (fun r =>
      let d0 := ds.getD (2 + r) ⟨0, 0⟩
      let d1 := ds.getD (8 + r) ⟨0, 0⟩
      let d2 := ds.getD (14 + r) ⟨0, 0⟩
      let d3 := ds.getD (20 + r) ⟨0, 0⟩
      checkResidueInc d0 d1 d2 d3 || checkResidueBdd d0 d1 d2 d3)
      [0, 1, 2, 3, 4, 5]
  | _, _ => false

/-- 3-way `Sym5` lookup table of all 336 distinct `SeedSummary` records (3-step dispatch!). -/
def seedBucket : Sym5 → Sym5 → Sym5 → List SeedSummary
  | .s0, .s2, .s0 =>
    [⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨2, 2, 2, 1, 1⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨6, 5, 6, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨6, 6, 6, 3, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨6, 6, 6, 4, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨3, 3, 4, 2, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨5, 6, 7, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨3, 3, 4, 3, 2⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨5, 6, 7, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨2, 3, 5, 3, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨3, 3, 4, 3, 2⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨3, 4, 4, 2, 2⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨7, 8, 8, 5, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨0, 1, 2, 1, 1⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨6, 7, 9, 6, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨6, 8, 9, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨3, 3, 4, 2, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨3, 4, 4, 2, 2⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨7, 8, 8, 4, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨0, 1, 2, 1, 1⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨6, 7, 9, 5, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨6, 8, 9, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s1, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨0, 1, 2, 1, 1⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨4, 5, 6, 3, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨4, 5, 6, 4, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨4, 6, 6, 3, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨8, 9, 10, 6, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩]
  | .s0, .s2, .s1 =>
    [⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨1, 1, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨5, 5, 5, 2, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨7, 8, 8, 4, 5⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨8, 7, 7, 4, 5⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨8, 8, 7, 4, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨5, 4, 5, 3, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨5, 5, 5, 3, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨9, 9, 9, 5, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨4, 5, 6, 3, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨5, 5, 5, 3, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨9, 9, 9, 5, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨2, 2, 3, 2, 2⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨8, 8, 10, 6, 7⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨8, 9, 10, 6, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s0⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨9, 8, 9, 6, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩]
  | .s0, .s3, .s1 =>
    [⟨⟨⟨.s0, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨1, 1, 2, 2, 1⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s0, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨7, 7, 9, 6, 6⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s0, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨7, 8, 9, 6, 5⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s0, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨8, 7, 8, 6, 5⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s0, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨1, 1, 2, 2, 1⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s0, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨5, 5, 6, 4, 4⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s0, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨5, 6, 6, 4, 3⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨1, 1, 2, 2, 1⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨5, 5, 6, 4, 4⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨6, 5, 5, 4, 3⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨5, 5, 6, 5, 3⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨5, 6, 6, 4, 3⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨6, 5, 5, 4, 3⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s2, .s1, .s0⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨10, 10, 9, 6, 5⟩, ⟨0, 0, 1, 0, 1⟩⟩]
  | .s1, .s3, .s0 =>
    [⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨1, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨5, 5, 5, 4, 2⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨7, 8, 8, 5, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨8, 7, 7, 5, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨8, 8, 7, 4, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨4, 5, 6, 4, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨5, 5, 5, 3, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨9, 9, 9, 6, 5⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨5, 4, 5, 4, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨5, 5, 5, 3, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩⟩, ⟨9, 9, 9, 6, 5⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨2, 2, 3, 2, 2⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨8, 8, 10, 7, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨8, 9, 10, 6, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s4⟩⟩, ⟨9, 8, 9, 6, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩]
  | .s1, .s3, .s1 =>
    [⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨2, 2, 2, 1, 1⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨5, 6, 7, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨6, 6, 6, 3, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨6, 6, 6, 4, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨3, 3, 4, 3, 2⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨6, 5, 6, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨3, 3, 4, 2, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨6, 5, 6, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨3, 2, 4, 3, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨3, 3, 4, 2, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨4, 3, 3, 2, 2⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨8, 7, 7, 4, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨1, 0, 1, 1, 1⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨7, 6, 8, 5, 6⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨8, 6, 7, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨3, 3, 4, 3, 2⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨4, 3, 3, 2, 2⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨8, 7, 7, 5, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨1, 0, 1, 1, 1⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨7, 6, 8, 6, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨8, 6, 7, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨1, 0, 1, 1, 1⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨5, 4, 5, 3, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨5, 4, 5, 4, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨6, 4, 4, 3, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s3⟩⟩, ⟨9, 8, 9, 6, 6⟩, ⟨1, 0, 0, 0, 0⟩⟩]
  | .s1, .s4, .s0 =>
    [⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s0⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨1, 1, 2, 1, 2⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s0⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨7, 7, 9, 6, 6⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s0⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨7, 8, 9, 5, 6⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s0⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨8, 7, 8, 5, 6⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s2⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨1, 1, 2, 1, 2⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s2⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨5, 5, 6, 4, 4⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s2⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨6, 5, 5, 3, 4⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s0⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨1, 1, 2, 1, 2⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s0⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨5, 5, 6, 4, 4⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s0⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨5, 6, 6, 3, 4⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s2⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s2⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨5, 5, 6, 3, 5⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s2⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨5, 6, 6, 3, 4⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s2⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨6, 5, 5, 3, 4⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s2⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s0, .s1, .s2⟩, ⟨.s4, .s2, .s1⟩⟩, ⟨10, 10, 9, 5, 6⟩, ⟨0, 0, 1, 1, 0⟩⟩]
  | .s1, .s4, .s1 =>
    [⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨2, 1, 1, 1, 1⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨6, 4, 5, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨6, 5, 5, 3, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨6, 5, 5, 4, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨3, 2, 3, 2, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨5, 5, 6, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨10, 8, 9, 6, 7⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨3, 2, 3, 3, 2⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨5, 5, 6, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨10, 8, 9, 7, 6⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨2, 2, 4, 3, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨7, 6, 7, 5, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨3, 2, 3, 3, 2⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨7, 6, 7, 5, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨7, 7, 7, 5, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨6, 6, 8, 6, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨6, 7, 8, 5, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨7, 6, 7, 5, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨3, 2, 3, 2, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨7, 6, 7, 5, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨7, 7, 7, 4, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨6, 6, 8, 5, 6⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨6, 7, 8, 5, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨7, 6, 7, 5, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨4, 4, 5, 3, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨4, 4, 5, 4, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨4, 5, 5, 3, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s0, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s4⟩, ⟨.s3, .s4, .s2⟩⟩, ⟨8, 8, 9, 6, 6⟩, ⟨0, 0, 1, 0, 0⟩⟩]
  | .s2, .s0, .s2 =>
    [⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨4, 5, 5, 3, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨5, 5, 4, 2, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨5, 5, 4, 3, 2⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨9, 9, 8, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨7, 8, 7, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨8, 7, 6, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨8, 8, 6, 4, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨4, 3, 2, 2, 1⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨7, 7, 7, 5, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨8, 7, 6, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨10, 10, 9, 6, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨7, 8, 7, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨8, 7, 6, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨8, 8, 6, 3, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨4, 3, 2, 1, 2⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨7, 7, 7, 4, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨8, 7, 6, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨10, 10, 9, 5, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨4, 4, 2, 1, 1⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨8, 7, 6, 4, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨4, 3, 2, 1, 2⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨6, 6, 5, 3, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨10, 10, 9, 5, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨11, 9, 8, 5, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s1, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨11, 10, 8, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨4, 3, 2, 2, 1⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨6, 6, 5, 3, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨10, 10, 9, 6, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨11, 9, 8, 6, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨11, 10, 8, 5, 5⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨2, 1, 1, 1, 1⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨6, 5, 5, 3, 4⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨6, 5, 5, 4, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨7, 5, 4, 3, 3⟩, ⟨0, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨0, 1, 0, 0, 0⟩⟩]
  | .s2, .s0, .s4 =>
    [⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨5, 6, 6, 4, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨6, 5, 5, 4, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨6, 6, 5, 4, 2⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨10, 10, 9, 6, 5⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨2, 2, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨5, 6, 6, 4, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s0, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨6, 6, 5, 3, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨2, 2, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨6, 5, 5, 4, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨6, 6, 5, 3, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨2, 2, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨8, 9, 8, 5, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨9, 8, 7, 5, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s3, .s4, .s2⟩, ⟨.s2, .s3, .s0⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨9, 9, 7, 4, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩]
  | .s3, .s0, .s3 =>
    [⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s0, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨3, 3, 2, 1, 1⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s0, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨9, 10, 9, 5, 5⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s0, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨10, 9, 8, 5, 5⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s0, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨10, 10, 8, 4, 5⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s0, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨5, 5, 5, 3, 3⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s0, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨6, 5, 4, 2, 3⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s0, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨9, 9, 9, 5, 6⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s2, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨5, 5, 5, 3, 3⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s2, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨5, 6, 5, 2, 3⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s2, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨9, 9, 9, 5, 6⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s2, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s2, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨5, 5, 5, 2, 4⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s2, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s2, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨7, 8, 8, 4, 5⟩, ⟨0, 0, 1, 0, 1⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s2, .s1, .s0⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨8, 7, 7, 4, 5⟩, ⟨0, 0, 1, 0, 1⟩⟩]
  | .s3, .s1, .s2 =>
    [⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨5, 6, 6, 3, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨6, 5, 5, 3, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨6, 6, 5, 2, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨10, 9, 9, 6, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨10, 10, 9, 5, 6⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨2, 2, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨6, 5, 5, 3, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨6, 6, 5, 3, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨2, 2, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨5, 6, 6, 3, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s0⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨6, 6, 5, 3, 3⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨2, 2, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨8, 9, 8, 4, 5⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨9, 8, 7, 4, 5⟩, ⟨1, 1, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s2, .s3, .s4⟩, ⟨.s0, .s4, .s2⟩⟩, ⟨9, 9, 7, 4, 4⟩, ⟨1, 1, 0, 0, 0⟩⟩]
  | .s3, .s1, .s4 =>
    [⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨1, 1, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨5, 4, 4, 3, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨5, 5, 4, 2, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨5, 5, 4, 3, 2⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨9, 9, 8, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨1, 1, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨7, 8, 7, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨8, 7, 6, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨8, 8, 6, 3, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨3, 4, 3, 1, 2⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨7, 7, 7, 4, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨7, 8, 7, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨10, 10, 9, 5, 6⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨1, 1, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨7, 8, 7, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨8, 7, 6, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨8, 8, 6, 4, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨3, 3, 3, 2, 2⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨3, 4, 3, 2, 1⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨7, 7, 7, 5, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨7, 8, 7, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨10, 10, 9, 6, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨4, 4, 2, 1, 1⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨7, 8, 7, 4, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨3, 4, 3, 2, 1⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨6, 6, 5, 3, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨10, 10, 9, 6, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨10, 11, 9, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨3, 4, 3, 1, 2⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨6, 6, 5, 3, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨10, 10, 9, 5, 6⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨10, 11, 9, 5, 5⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨1, 2, 2, 1, 1⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨5, 6, 6, 3, 4⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨5, 6, 6, 4, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩,
     ⟨⟨⟨.s4, .s2, .s3⟩, ⟨.s4, .s2, .s1⟩, ⟨.s4, .s2, .s3⟩, ⟨.s1, .s2, .s3⟩⟩, ⟨5, 7, 6, 3, 3⟩, ⟨1, 0, 0, 0, 0⟩⟩]
  | .s4, .s1, .s3 =>
    [⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨1, 2, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨4, 6, 6, 3, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨5, 6, 5, 2, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨5, 6, 5, 3, 2⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨9, 10, 9, 5, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨1, 2, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨7, 9, 8, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨8, 8, 7, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨8, 9, 7, 4, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨3, 4, 4, 2, 2⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨4, 4, 3, 2, 1⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨7, 8, 8, 5, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨8, 8, 7, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨1, 2, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨7, 9, 8, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨8, 8, 7, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨8, 9, 7, 3, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨3, 4, 4, 2, 2⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨4, 4, 3, 1, 2⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨7, 8, 8, 4, 5⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s0, .s1⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨8, 8, 7, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨4, 5, 3, 1, 1⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨8, 8, 7, 4, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨4, 4, 3, 1, 2⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨6, 7, 6, 3, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨4, 4, 3, 2, 1⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s1⟩⟩, ⟨6, 7, 6, 3, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨2, 2, 2, 1, 1⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨6, 6, 6, 3, 4⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨6, 6, 6, 4, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩,
     ⟨⟨⟨.s2, .s3, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s3, .s4, .s2⟩, ⟨.s1, .s0, .s4⟩⟩, ⟨7, 6, 5, 3, 3⟩, ⟨0, 0, 1, 0, 0⟩⟩]
  | .s4, .s1, .s4 =>
    [⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s0⟩⟩, ⟨3, 3, 2, 1, 1⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s0⟩⟩, ⟨9, 10, 9, 5, 5⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s0⟩⟩, ⟨10, 9, 8, 5, 5⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s0⟩⟩, ⟨10, 10, 8, 5, 4⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨5, 5, 5, 3, 3⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨5, 6, 5, 3, 2⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s1, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨9, 9, 9, 6, 5⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s0⟩⟩, ⟨5, 5, 5, 3, 3⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s0⟩⟩, ⟨6, 5, 4, 3, 2⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s0⟩⟩, ⟨9, 9, 9, 6, 5⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨5, 5, 5, 4, 2⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨7, 7, 8, 5, 5⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨7, 8, 8, 5, 4⟩, ⟨0, 0, 1, 1, 0⟩⟩,
     ⟨⟨⟨.s1, .s0, .s4⟩, ⟨.s3, .s0, .s1⟩, ⟨.s4, .s2, .s1⟩, ⟨.s0, .s1, .s2⟩⟩, ⟨8, 7, 7, 5, 4⟩, ⟨0, 0, 1, 1, 0⟩⟩]
  | _, _, _ => []

def memSummaryList (s : SeedSummary) : List SeedSummary → Bool
  | [] => false
  | x :: xs => if SeedSummary.beq s x then true else memSummaryList s xs

theorem memSummaryList_iff (s : SeedSummary) (l : List SeedSummary) :
    memSummaryList s l = true ↔ s ∈ l := by
  induction l with
  | nil => simp [memSummaryList]
  | cons x xs ih =>
    unfold memSummaryList
    cases h : SeedSummary.beq s x
    · simp only [Bool.false_eq_true, ↓reduceIte, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (heq | hmem)
        · have ht := (SeedSummary.beq_iff_eq s x).mpr heq
          rw [h] at ht; exact Bool.noConfusion ht
        · exact hmem
    · simp only [↓reduceIte, List.mem_cons, true_iff]
      exact Or.inl ((SeedSummary.beq_iff_eq s x).mp h)

def inSeedBuckets (s : SeedSummary) : Bool :=
  memSummaryList s (seedBucket s.st.X.c s.st.Y.c s.st.S.a)

/-- Binary-tree divide-and-conquer range check over `[lo, lo + 2^d)`: stack depth `d`! -/
def allRangeBin (P : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, lo => P lo
  | d + 1, lo => allRangeBin P d lo && allRangeBin P d (lo + 2 ^ d)

theorem allRangeBin_iff (P : ℕ → Bool) (d lo : ℕ) :
    allRangeBin P d lo = true ↔ ∀ k < 2 ^ d, P (lo + k) = true := by
  induction d generalizing lo with
  | zero =>
    simp only [allRangeBin, Nat.pow_zero, Nat.lt_one_iff]
    constructor
    · intro h k hk; subst hk; simpa using h
    · intro h; simpa using h 0 rfl
  | succ d ih =>
    simp only [allRangeBin, Bool.and_eq_true, ih, Nat.pow_succ]
    constructor
    · rintro ⟨hL, hR⟩ k hk
      by_cases hlt : k < 2 ^ d
      · exact hL k hlt
      · have hk2 : k - 2 ^ d < 2 ^ d := by omega
        have heq : lo + 2 ^ d + (k - 2 ^ d) = lo + k := by omega
        rw [← heq]
        exact hR (k - 2 ^ d) hk2
    · intro hall
      refine ⟨fun k hk => hall k (by omega), fun k hk => ?_⟩
      have heq : lo + 2 ^ d + k = lo + (2 ^ d + k) := by omega
      rw [heq]
      exact hall (2 ^ d + k) (by omega)

/-- Check `P (l.drop o)` for all `o < 256` with logarithmic recursion depth! -/
def scanDrops256 (P : List Sym5 → Bool) (l : List Sym5) : Bool :=
  allRangeBin (fun o => P (l.drop o)) 8 0

theorem scanDrops256_iff (P : List Sym5 → Bool) (l : List Sym5) :
    scanDrops256 P l = true ↔ ∀ o < 256, P (l.drop o) = true := by
  simpa [scanDrops256] using allRangeBin_iff (fun o => P (l.drop o)) 8 0

def symOptEq : Option Sym5 → Option Sym5 → Bool
  | some x, some y => Sym5.beq x y
  | none, none => true
  | _, _ => false

def symOptNe : Option Sym5 → Option Sym5 → Bool
  | some x, some y => !Sym5.beq x y
  | _, _ => true

def summaryOfSuffix (p m : ℕ) (s : List Sym5) : SeedSummary :=
  { st :=
      { X := word3OfList s
        Y := word3OfList (s.drop p)
        S := word3OfList (s.drop (p + m + 3))
        T := word3OfList (s.drop (m + 3)) }
    pu := parikhSym ((s.drop 3).take p)
    pz := parikhSym ((s.drop (3 + p)).take m) }

def checkSeedAtSuffix (p m : ℕ) (s : List Sym5) : Bool :=
  if symOptEq s[3]? s[3 + p]? then
    if hasLenAtLeast (p + m + 6) s &&
       (Nat.beq m 1 || symOptEq s[4]? s[4 + p]?) &&
       symOptNe s[2]? s[2 + p]? &&
       symOptNe s[3 + p + m]? s[3 + m]? then
      inSeedBuckets (summaryOfSuffix p m s)
    else true
  else true

def periods1To40 : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
   21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]

def checkSuffixAllPM (s : List Sym5) : Bool :=
  allRangeBin (fun k =>
    if Nat.blt k 40 then checkSeedAtSuffix (k + 1) 1 s && checkSeedAtSuffix (k + 1) 2 s
    else true) 6 0

/-! ## Pure-Kernel Certificate Theorems (`rfl` / `decide`, zero `native_decide`) -/

theorem valid2Sym_iff_mem (x y : Sym5) :
    valid2Sym x y = true ↔ (x, y) ∈ twoFactorSymList := by
  cases x <;> cases y <;> decide

theorem valid2Sym_no_self (x : Sym5) : valid2Sym x x = false := by
  cases x <;> rfl

theorem fSym5_single_adj_valid2 (x : Sym5) : allAdjValid2Sym (fSym5 x) = true := by
  cases x <;> rfl

theorem fSym5_pair_adj_valid2 :
    allTR (fun p => allAdjValid2Sym (fSym5 p.1 ++ fSym5 p.2)) twoFactorSymList = true := rfl

theorem no_len3_in_24_sym (x y z : Sym5) :
    valid2Sym x y = true → valid2Sym y z = true →
    !((Sym5.beq x .s2 || Sym5.beq x .s4) &&
      (Sym5.beq y .s2 || Sym5.beq y .s4) &&
      (Sym5.beq z .s2 || Sym5.beq z .s4)) = true := by
  cases x <;> cases y <;> cases z <;> decide

theorem fSym5_prim5 (x c : Sym5) : c ∈ g5Val x := by
  cases x <;> cases c <;> decide

def isSublist2 (a b : Sym5) : List Sym5 → Bool
  | x :: y :: rest => if Sym5.beq a x && Sym5.beq b y then true else isSublist2 a b (y :: rest)
  | _ => false

theorem twoFactor_in_iter6 :
    allTR (fun p => isSublist2 p.1 p.2 (morphSym5 (g5Val .s0))) twoFactorSymList = true := rfl

theorem g10Val_len_ge_72 (x : Sym5) : hasLenAtLeast 72 (g10Val x) = true := by
  cases x <;> rfl

theorem no_period2_len5 :
    allTR (fun p =>
      scanDrops256 (fun s =>
        !(hasLenAtLeast 5 s &&
          symOptEq s[0]? s[2]? &&
          symOptEq s[1]? s[3]? &&
          symOptEq s[2]? s[4]?))
        (g10Val p.1 ++ g10Val p.2)) twoFactorSymList = true := rfl

theorem word3_isValid_iff_mem (w : Word3) :
    w.isValid = true ↔ w ∈ validWord3List := by
  rcases w with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

theorem left_ctx_step_props :
    allTR (fun X =>
      allTR (fun Y =>
        if !Sym5.beq X.c Y.c then
          let eL := eLOf X.c Y.c
          let lam := eL.length
          let fX := morphSym5 X.toList
          let fY := morphSym5 Y.toList
          let X2 := nextLeftCtx X lam
          let Y2 := nextLeftCtx Y lam
          Nat.ble lam 1 &&
          hasLenAtLeast (3 + lam) fX &&
          hasLenAtLeast (3 + lam) fY &&
          decide (fX.drop (fX.length - lam) = eL) &&
          decide (fY.drop (fY.length - lam) = eL) &&
          symOptNe fX[fX.length - lam - 1]? fY[fY.length - lam - 1]? &&
          X2.isValid && Y2.isValid && !Sym5.beq X2.c Y2.c
        else true) validWord3List) validWord3List = true := rfl

theorem right_ctx_step_props :
    allTR (fun S =>
      allTR (fun T =>
        if !Sym5.beq S.a T.a then
          let eR := eROf S.a T.a
          let rho := eR.length
          let fS := morphSym5 S.toList
          let fT := morphSym5 T.toList
          let S2 := nextRightCtx S rho
          let T2 := nextRightCtx T rho
          Nat.ble rho 1 &&
          hasLenAtLeast (3 + rho) fS &&
          hasLenAtLeast (3 + rho) fT &&
          decide (fS.take rho = eR) &&
          decide (fT.take rho = eR) &&
          symOptNe fS[rho]? fT[rho]? &&
          S2.isValid && T2.isValid && !Sym5.beq S2.a T2.a
        else true) validWord3List) validWord3List = true := rfl

theorem twoFactor_seeds_covered_0 :
    scanDrops256 checkSuffixAllPM (g10Val .s0 ++ g10Val .s1) = true := rfl

theorem twoFactor_seeds_covered_1 :
    scanDrops256 checkSuffixAllPM (g10Val .s0 ++ g10Val .s4) = true := rfl

theorem twoFactor_seeds_covered_2 :
    scanDrops256 checkSuffixAllPM (g10Val .s1 ++ g10Val .s0) = true := rfl

theorem twoFactor_seeds_covered_3 :
    scanDrops256 checkSuffixAllPM (g10Val .s1 ++ g10Val .s2) = true := rfl

theorem twoFactor_seeds_covered_4 :
    scanDrops256 checkSuffixAllPM (g10Val .s2 ++ g10Val .s1) = true := rfl

theorem twoFactor_seeds_covered_5 :
    scanDrops256 checkSuffixAllPM (g10Val .s2 ++ g10Val .s3) = true := rfl

theorem twoFactor_seeds_covered_6 :
    scanDrops256 checkSuffixAllPM (g10Val .s3 ++ g10Val .s0) = true := rfl

theorem twoFactor_seeds_covered_7 :
    scanDrops256 checkSuffixAllPM (g10Val .s3 ++ g10Val .s4) = true := rfl

theorem twoFactor_seeds_covered_8 :
    scanDrops256 checkSuffixAllPM (g10Val .s4 ++ g10Val .s2) = true := rfl

theorem all_twoFactor_seeds_in_buckets :
    twoFactorSymList.all (fun p => scanDrops256 checkSuffixAllPM (g10Val p.1 ++ g10Val p.2)) = true := by
  simp only [twoFactorSymList, List.all_cons, List.all_nil, Bool.and_true]
  rw [twoFactor_seeds_covered_0, twoFactor_seeds_covered_1, twoFactor_seeds_covered_2,
      twoFactor_seeds_covered_3, twoFactor_seeds_covered_4, twoFactor_seeds_covered_5,
      twoFactor_seeds_covered_6, twoFactor_seeds_covered_7, twoFactor_seeds_covered_8]
  rfl

def checkListBin64 (l : List SeedSummary) : Bool :=
  allRangeBin (fun i =>
    match l[i]? with
    | some s => checkSummaryZPhi s
    | none => true) 6 0

theorem seedBuckets_valid_s0 (y z : Sym5) : checkListBin64 (seedBucket .s0 y z) = true := by
  cases y <;> cases z <;> rfl

theorem seedBuckets_valid_s1 (y z : Sym5) : checkListBin64 (seedBucket .s1 y z) = true := by
  cases y <;> cases z <;> rfl

theorem seedBuckets_valid_s2 (y z : Sym5) : checkListBin64 (seedBucket .s2 y z) = true := by
  cases y <;> cases z <;> rfl

theorem seedBuckets_valid_s3 (y z : Sym5) : checkListBin64 (seedBucket .s3 y z) = true := by
  cases y <;> cases z <;> rfl

theorem seedBuckets_valid_s4 (y z : Sym5) : checkListBin64 (seedBucket .s4 y z) = true := by
  cases y <;> cases z <;> rfl

theorem seedBucket_len_lt_64 (x y z : Sym5) : Nat.blt (seedBucket x y z).length 64 = true := by
  cases x <;> cases y <;> cases z <;> rfl

theorem all_seedBuckets_valid (x y z : Sym5) {s : SeedSummary}
    (hs : s ∈ seedBucket x y z) : checkSummaryZPhi s = true := by
  have hbin : checkListBin64 (seedBucket x y z) = true := by
    cases x
    · exact seedBuckets_valid_s0 y z
    · exact seedBuckets_valid_s1 y z
    · exact seedBuckets_valid_s2 y z
    · exact seedBuckets_valid_s3 y z
    · exact seedBuckets_valid_s4 y z
  have hlt64 : (seedBucket x y z).length < 64 :=
    Nat.blt_eq.mp (seedBucket_len_lt_64 x y z)
  rcases List.mem_iff_getElem.mp hs with ⟨i, hi, rfl⟩
  have hall := (allRangeBin_iff _ 6 0).mp hbin i (by omega)
  simp only [Nat.zero_add, List.getElem?_eq_getElem hi] at hall
  exact hall

/-- Extremal seed `123010421` (`p₀ = 2, m₀ = 1`) at index `35` of `iterSym5 8 [.s0]`. -/
def extremalSeedWord : List Sym5 :=
  [.s1, .s2, .s3, .s0, .s1, .s0, .s4, .s2, .s1]

def extremalSeedSummary : SeedSummary :=
  summaryOfSuffix 2 1 extremalSeedWord

theorem extremalSeed_occurs_at_35 :
    ((iterSym5 3 (g5Val .s0)).drop 35).take 9 = extremalSeedWord := rfl

def checkExtremalSeedCert : Bool :=
  let orb := collectSummaries 26 extremalSeedSummary
  match orb[2]?, orb[8]? with
  | some s2, some s8 =>
    CtxState.beq s8.st s2.st &&
    let ds := orb.map summaryD
    let d0 := ds.getD 2 ⟨0, 0⟩
    let d1 := ds.getD 8 ⟨0, 0⟩
    let d2 := ds.getD 14 ⟨0, 0⟩
    let d3 := ds.getD 20 ⟨0, 0⟩
    decide (d0.a = -8) && decide (d0.b = 7) &&
    decide (d1.a = -186) && decide (d1.b = 117) &&
    decide ((lamZPhi * (d2 - d1) - (d1 - d0)).a = 0) &&
    decide ((lamZPhi * (d2 - d1) - (d1 - d0)).b = 0) &&
    decide ((lamZPhi * (d3 - d2) - (d2 - d1)).a = 0) &&
    decide ((lamZPhi * (d3 - d2) - (d2 - d1)).b = 0) &&
    decide ((lamZPhi * d1 - d0).a = 14) &&
    decide ((lamZPhi * d1 - d0).b = 26)
  | _, _ => false

theorem extremalSeed_cert : checkExtremalSeedCert = true := rfl

end BadkobehOchemB5
