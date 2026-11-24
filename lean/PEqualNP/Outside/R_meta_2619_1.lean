import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- Exclude point 2 from the core. Its four lines are 1, 2, 6 and 12.
-- Distribute the core value over the point and its line disjunction.
theorem PEqualNP.Outside.R_meta_2619_1
    (hCore : ∃ C : Circuit, C.size ≤ 58 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      C.output < 26 + C.size ∧ C.output ≠ 2 ∧
      ∀ p l : Fin 13 → Bool, C.eval (List.ofFn ((fun i : Fin (13 + 13) => Fin.addCases p l i))) = true ↔
        ∃ j : Fin 13, l j = true ∧ ∃ a : Fin 13,
          a ≠ 2 ∧ p a = true ∧ (a = j ∨ a = j + 1 ∨ a = j + 3 ∨ a = j + 9))
    (hAppend : ∀ C : Circuit, IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      C.output < 26 + C.size → C.output ≠ 2 →
      ∃ D : Circuit, D.size = C.size + 6 ∧ IsAO2 26 D ∧
        (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        ∃ k a b : ℕ, D.output = 26 + k ∧ D.gates[k]? = some ⟨.and, [a, b]⟩ ∧
          ∀ x : Fin 26 → Bool,
            let y := C.eval (List.ofFn x)
            let s := x 14 || x 15 || x 19 || x 25
            let ws := D.wires (List.ofFn x)
            D.eval (List.ofFn x) = ((y || x 2) && (y || s)) ∧
              ws.getD a false = (y || x 2) ∧ ws.getD b false = (y || s)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧       (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧         (∀ (x2 x3 : Fin (13 : ℕ) → Bool), x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)), x3 x4 = Bool.true ∧ (x2 x4 || x2 (x4 + (1 : Fin (13 : ℕ))) || x2 (x4 + (3 : Fin (13 : ℕ))) || x2 (x4 + (9 : Fin (13 : ℕ)))) = Bool.true) ∧           ∃ (x2 : ℕ) (x3 : ℕ) (x4 : ℕ),             x1.output = (26 : ℕ) + x2 ∧               x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧                 ∀ (x5 : Bool),                   have x6 : List Bool := x1.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                   x6.getD x3 Bool.false = Bool.false ∧ x6.getD x4 Bool.false = Bool.false := by
  obtain ⟨C, cSize, cLegal, cDistinct, cOut, cOther, cEval⟩ := hCore
  obtain ⟨D, dSize, dLegal, dDistinct, k, a, b, dOut, dGate, evals⟩ :=
    hAppend C cLegal cDistinct cOut cOther
  let adj (a j : Fin 13) := a = j ∨ a = j + 1 ∨ a = j + 3 ∨ a = j + 9
  have incident2 : ∀ j : Fin 13, adj 2 j ↔ j = 1 ∨ j = 2 ∨ j = 6 ∨ j = 12 := by
    decide +kernel
  have pick (p : Fin 13 → Bool) (j : Fin 13) :
      (p j || p (j + 1) || p (j + 3) || p (j + 9)) = true ↔
        ∃ r : Fin 13, adj r j ∧ p r = true := by
    simp only [Bool.or_eq_true, adj]
    aesop
  have linePick (l : Fin 13 → Bool) :
      (l 1 || l 2 || l 6 || l 12) = true ↔
        ∃ j : Fin 13, adj 2 j ∧ l j = true := by
    simp only [Bool.or_eq_true, incident2]
    aesop
  have distribute (x y z : Bool) : ((x || y) && (x || z)) = (x || (y && z)) := by
    cases x <;> cases y <;> cases z <;> rfl
  refine ⟨D, by omega, dLegal, dDistinct, ?_, k, a, b, dOut, dGate, ?_⟩
  · intro p l
    let x : Fin 26 → Bool := (fun i : Fin (13 + 13) => Fin.addCases p l i)
    have equality := (evals x).1
    change D.eval (List.ofFn x) =
      ((C.eval (List.ofFn x) || p 2) &&
        (C.eval (List.ofFn x) || (l 1 || l 2 || l 6 || l 12))) at equality
    change D.eval (List.ofFn x) = true ↔ _
    rw [equality, distribute, Bool.or_eq_true, Bool.and_eq_true]
    change C.eval (List.ofFn ((fun i : Fin (13 + 13) => Fin.addCases p l i))) = true ∨
      (p 2 = true ∧ (l 1 || l 2 || l 6 || l 12) = true) ↔ _
    rw [cEval, linePick]
    simp only [pick]
    constructor
    · rintro (⟨j, hj, r, _, hr, inc⟩ | ⟨hp, j, inc, hj⟩)
      · exact ⟨j, hj, r, inc, hr⟩
      · exact ⟨j, hj, 2, inc, hp⟩
    · rintro ⟨j, hj, r, inc, hr⟩
      by_cases same : r = 2
      · subst r
        exact Or.inr ⟨hr, j, inc, hj⟩
      · exact Or.inl ⟨j, hj, r, same, hr, inc⟩
  · intro s
    let x : Fin 26 → Bool := fun i => decide (i.val = if s = true then 13 else 0)
    have pointCold : x 2 = false := by cases s <;> decide +kernel
    have linesCold : (x 14 || x 15 || x 19 || x 25) = false := by
      cases s <;> decide +kernel
    have cCold : C.eval (List.ofFn x) = false := by
      cases s with
      | false =>
        let p (i : Fin 13) : Bool := decide (i = 0)
        let l (_ : Fin 13) : Bool := false
        have hx : x = (fun i : Fin (13 + 13) => Fin.addCases p l i) := by decide +kernel
        rw [hx]
        cases answer : C.eval (List.ofFn ((fun i : Fin (13 + 13) => Fin.addCases p l i))) with
        | false => rfl
        | true =>
          obtain ⟨j, hj, _⟩ := (cEval p l).mp answer
          cases hj
      | true =>
        let p (_ : Fin 13) : Bool := false
        let l (i : Fin 13) : Bool := decide (i = 0)
        have hx : x = (fun i : Fin (13 + 13) => Fin.addCases p l i) := by decide +kernel
        rw [hx]
        cases answer : C.eval (List.ofFn ((fun i : Fin (13 + 13) => Fin.addCases p l i))) with
        | false => rfl
        | true =>
          obtain ⟨j, hj, r, _, hr, _⟩ := (cEval p l).mp answer
          cases hr
    obtain ⟨_, coldA, coldB⟩ := evals x
    change (D.wires (List.ofFn x)).getD a false = false ∧
      (D.wires (List.ofFn x)).getD b false = false
    rw [coldA, coldB, cCold, pointCold, linesCold]
    decide
