import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- Two disjoint incident pairs rule out primary inputs as final AND operands.
-- Keep only the gates through the later operand and order the two operands by index.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_4241_1
    (prune : ∀ (n : ℕ) (C : Circuit) (a b : ℕ), Monotone2 C →
      a < b → n ≤ b → b < n + C.size →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ (b + 1 = n + D.size) ∧
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD a false = (C.wires (List.ofFn x)).getD a false ∧
          (D.wires (List.ofFn x)).getD b false = (C.wires (List.ofFn x)).getD b false)
    (lastOperand :
      let offsets : Finset (Fin 13) := {0,1,3,9}
      let inc := fun (p l : Fin 13) => ∃ a ∈ offsets, p = l + a
      let free := fun (S : Finset (Fin 13)) (l : Fin 13) => ∀ p ∈ S, ¬ inc p l
      let row := fun (S : Finset (Fin 13)) (i : Fin 26) =>
        decide ((∃ p ∈ S, i = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ free S l)
      let read := fun (C : Circuit) (a : ℕ) (x : Fin 26 → Bool) =>
        (C.wires (List.ofFn x)).getD a false
      ∀ C : Circuit, Monotone2 C → ∀ a : ℕ, 26 ≤ a → a < 26 + C.size - 1 →
      (∀ p l : Fin 13, inc p l →
        let x := pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)
        (read C a x && read C (26 + C.size - 1) x) = true) →
      (∀ S : Finset (Fin 13), (∀ p ∉ S, ∃ l, free S l ∧ inc p l) →
        (S.card ≤ 2 ∨ Nat.card {l : Fin 13 // free S l} ≤ 2 ∨
          S.card = 3 ∧ ∃ l : Fin 13, ∀ p ∈ S, inc p l) →
        (read C a (row S) && read C (26 + C.size - 1) (row S)) = false) →
      63 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4;
      have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4;
      have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5);
      have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10);
      have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false;
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → ∀ (x9 x10 : Fin ((26 : ℕ) + x7.size)), x9 ≠ x10 → (∀ (x12 x13 : Fin (13 : ℕ)), x2 x12 x13 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x9) (x4 x12 x13), x6 x7 (↑x10) (x4 x12 x13)] = Bool.true) → (∀ (x13 : Finset (Fin (13 : ℕ))), (∀ x14 ∉ x13, ∃ (x16 : Fin (13 : ℕ)), x3 x13 x16 ∧ x2 x14 x16) → (x13.card ≤ (2 : ℕ) ∨ Nat.card { x15 : Fin (13 : ℕ) // x3 x13 x15 } ≤ (2 : ℕ) ∨ x13.card = (3 : ℕ) ∧ ∃ (x15 : Fin (13 : ℕ)), ∀ x16 ∈ x13, x2 x16 x15) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x9) (x5 x13), x6 x7 (↑x10) (x5 x13)] = Bool.false) → (63 : ℕ) ≤ x7.size := by
  dsimp only
  intro C mono a b distinct accepts rejects
  let offsets : Finset (Fin 13) := {0,1,3,9}
  let inc := fun (p l : Fin 13) => ∃ a ∈ offsets, p = l + a
  let free := fun (S : Finset (Fin 13)) (l : Fin 13) => ∀ p ∈ S, ¬ inc p l
  let row := fun (S : Finset (Fin 13)) (i : Fin 26) =>
    decide ((∃ p ∈ S, i = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ free S l)
  let read := fun (C : Circuit) (a : ℕ) (x : Fin 26 → Bool) =>
    (C.wires (List.ofFn x)).getD a false
  let pointPair (p l : Fin 13) := pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have atInput (x : Fin 26 → Bool) (i : Fin 26) : read C i.val x = x i := by
    change (C.gates.foldl step (List.ofFn x)).getD i.val false = _
    rw [keep _ _ _ (by simpa using i.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  have disjoint : ∀ i : Fin 26, pointPair 0 0 i = false ∨ pointPair 1 1 i = false := by
    decide
  have lo (i : ℕ) (both : read C i (pointPair 0 0) = true ∧ read C i (pointPair 1 1) = true) :
      26 ≤ i := by
    by_contra! out
    let q : Fin 26 := ⟨i, out⟩
    rcases disjoint q with first | second
    · exact Bool.false_ne_true (first.symm.trans ((atInput (pointPair 0 0) q).symm.trans both.1))
    · exact Bool.false_ne_true (second.symm.trans ((atInput (pointPair 1 1) q).symm.trans both.2))
  have positive (p l : Fin 13) (hit : inc p l) :
      (read C a.val (pointPair p l) && read C b.val (pointPair p l)) = true := by
    have h : GateOp.and.eval [read C a.val (pointPair p l), read C b.val (pointPair p l)] = true :=
      accepts p l hit
    change (read C a.val (pointPair p l) && (read C b.val (pointPair p l) && true)) = true at h
    simpa only [Bool.and_true] using h
  have neg (S : Finset (Fin 13)) (maximal : ∀ p ∉ S, ∃ l, free S l ∧ inc p l)
      (degenerate : S.card ≤ 2 ∨ Nat.card {l : Fin 13 // free S l} ≤ 2 ∨
        S.card = 3 ∧ ∃ l : Fin 13, ∀ p ∈ S, inc p l) :
      (read C a.val (row S) && read C b.val (row S)) = false := by
    have h : GateOp.and.eval [read C a.val (row S), read C b.val (row S)] = false :=
      rejects S maximal degenerate
    change (read C a.val (row S) && (read C b.val (row S) && true)) = false at h
    simpa only [Bool.and_true] using h
  have p0 := Bool.and_eq_true_iff.mp (positive 0 0 (by decide))
  have p1 := Bool.and_eq_true_iff.mp (positive 1 1 (by decide))
  have la : 26 ≤ a.val := lo a.val ⟨p0.1, p1.1⟩
  have lb : 26 ≤ b.val := lo b.val ⟨p0.2, p1.2⟩
  have ordered (i j : ℕ) (lower : 26 ≤ i) (ij : i < j) (top : j < 26 + C.size)
      (pos : ∀ p l : Fin 13, inc p l →
        (read C i (pointPair p l) && read C j (pointPair p l)) = true)
      (neg : ∀ S : Finset (Fin 13), (∀ p ∉ S, ∃ l, free S l ∧ inc p l) →
        (S.card ≤ 2 ∨ Nat.card {l : Fin 13 // free S l} ≤ 2 ∨
          S.card = 3 ∧ ∃ l : Fin 13, ∀ p ∈ S, inc p l) →
        (read C i (row S) && read C j (row S)) = false) :
      63 ≤ C.size := by
    obtain ⟨D, dm, size, last, same⟩ := prune 26 C i j mono ij (by omega) top
    have tail : 26 + D.size - 1 = j := by omega
    have equal (x : Fin 26 → Bool) : read D i x = read C i x ∧ read D j x = read C j x := same x
    have early : i < 26 + D.size - 1 := by rw [tail]; exact ij
    have posD (p l : Fin 13) (edge : inc p l) :
        (read D i (pointPair p l) && read D (26 + D.size - 1) (pointPair p l)) = true := by
      rw [tail, (equal (pointPair p l)).1, (equal (pointPair p l)).2]
      exact pos p l edge
    have negD (S : Finset (Fin 13)) (maximal : ∀ p ∉ S, ∃ l, free S l ∧ inc p l)
        (degenerate : S.card ≤ 2 ∨ Nat.card {l : Fin 13 // free S l} ≤ 2 ∨
          S.card = 3 ∧ ∃ l : Fin 13, ∀ p ∈ S, inc p l) :
        (read D i (row S) && read D (26 + D.size - 1) (row S)) = false := by
      rw [tail, (equal (row S)).1, (equal (row S)).2]
      exact neg S maximal degenerate
    exact (lastOperand D dm i lower early posD negD).trans size
  have ne : a.val ≠ b.val := fun eq => distinct (Fin.ext eq)
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact ordered a.val b.val la lt b.isLt positive neg
  · exact ordered b.val a.val lb gt a.isLt
      (fun p l e => by simpa only [Bool.and_comm] using positive p l e)
      (fun S m d => by simpa only [Bool.and_comm] using neg S m d)
