import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.ReadK

-- Count the two single-side traces separately from the doubly reread traces.
-- The single-side bounds correspond to L-meta-2970 and L-meta-2972.
theorem PEqualNP.Outside.R_meta_4453_1
    (hOnce : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      131 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      IsAO2 (N + N) C →
      (∀ x : Fin (N + N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false) →
      let E := (Finset.univ : Finset (Fin N × Fin N)).filter fun e =>
        I e.1 e.2 ∧ circuitFun (N + N) C
          (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true
      let readOnce := fun (e : Fin N × Fin N) =>
        lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) ||
        lineSingle C (N + N) (fun k => decide (k < N)) e.1.val (N + e.2.val)
      (E.filter fun e => readOnce e = true).card ≤ 20 * C.size)
    (hTwice : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      131 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      IsAO2 (N + N) C →
      (∀ x : Fin (N + N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false) →
      let E := (Finset.univ : Finset (Fin N × Fin N)).filter fun e =>
        I e.1 e.2 ∧ circuitFun (N + N) C
          (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true
      let readOnce := fun (e : Fin N × Fin N) =>
        lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) ||
        lineSingle C (N + N) (fun k => decide (k < N)) e.1.val (N + e.2.val)
      (∀ v : Fin (N + N), let d := (E.filter fun e =>
        v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2).card
        d = 0 ∨ 44 < d) →
      (E.filter fun e => readOnce e = false).card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (131 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : Finset (Fin x2 × Fin x2) := {x12 : Fin x2 × Fin x2 | x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true};               (∀ (x13 : Fin (x2 + x2)),                   have x14 : ℕ := {x14 ∈ x12 | x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2}.card;                   x14 = (0 : ℕ) ∨ (44 : ℕ) < x14) →                 x12.card ≤ (44 : ℕ) * x5.size := by
  intro q N I inst C hq order lines unique lawful sound E dense
  let readOnce := fun (e : Fin N × Fin N) =>
    lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) ||
    lineSingle C (N + N) (fun k => decide (k < N)) e.1.val (N + e.2.val)
  change E.card ≤ 44 * C.size
  have hs : (E.filter fun e => readOnce e = true).card ≤ 20 * C.size :=
    hOnce q N I C hq order lines unique lawful sound
  have ht : (E.filter fun e => readOnce e = false).card ≤ 24 * C.size :=
    hTwice q N I C hq order lines unique lawful sound dense
  have count := Finset.card_filter_add_card_filter_not (s := E) (fun e => readOnce e = true)
  have eqFilter : E.filter (fun e => ¬ readOnce e = true) =
      E.filter (fun e => readOnce e = false) := by
    ext e
    cases readOnce e <;> simp
  rw [eqFilter] at count
  omega
