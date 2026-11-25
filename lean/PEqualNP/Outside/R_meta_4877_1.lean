import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A derivative bit records reachability through OR gates and enabled AND inputs.
-- This replaces a function witness at every wire with two path exclusions.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_4877_1
    (paths : let link := fun (C : Circuit) (n : ℕ) (x : Fin n → Bool) (u w : ℕ) =>
        ∃ j < C.gates.length, w = n+j ∧
          let g := NestedCover.gateAt C j
          let a := ReadTwo.in0 C j
          let b := ReadTwo.in1 C j
          (u = a ∧ (g.op = .or ∨ g.op = .and ∧ ReadTwo.wval C x b = true)) ∨
          (u = b ∧ (g.op = .or ∨ g.op = .and ∧ ReadTwo.wval C x a = true))
      ∀ (n : ℕ) (C : Circuit) (x : Fin n → Bool) (source : ℕ), source < n →
        ∃ d : ℕ → Bool,
          (∀ w < n, d w = decide (w = source)) ∧
          (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
            (g.op = .and → d (n+j) = (ReadTwo.wval C x a && d b || d a && ReadTwo.wval C x b)) ∧
            (g.op = .or → d (n+j) = (d a || d b))) ∧
          ∀ w, d w = true ↔ Relation.ReflTransGen (link C n x) source w)
    (search : let link := fun (C : Circuit) (n : ℕ) (x : Fin n → Bool) (u w : ℕ) =>
        ∃ j < C.gates.length, w = n+j ∧
          let g := NestedCover.gateAt C j
          let a := ReadTwo.in0 C j
          let b := ReadTwo.in1 C j
          (u = a ∧ (g.op = .or ∨ g.op = .and ∧ ReadTwo.wval C x b = true)) ∨
          (u = b ∧ (g.op = .or ∨ g.op = .and ∧ ReadTwo.wval C x a = true))
      let inc := fun p l : Fin 13 => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      let row := fun (P L : Fin 13 → Bool) => List.ofFn (fun i : Fin 26 => Fin.addCases P L i)
      ∃ C : Circuit, C.size ≤ 64 ∧ TopForm.IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ P L, C.eval (row P L) = true ↔ ∃ p l, P p = true ∧ L l = true ∧ inc p l) ∧
        ∀ side : Bool, ¬ Relation.ReflTransGen
          (link C 26 (fun i => decide (i.val = if side then 13 else 0)))
          (if side then 0 else 13) C.output) :
    have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ))));
      have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4;
      have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
      ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x4.size ≤ (64 : ℕ) ∧
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧
      (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧
      (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧
      (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧
      ∀ (x5 : Bool),
      ∃ (x6 : ℕ → Bool),
      (∀ x7 < (26 : ℕ), x6 x7 = Decidable.decide (x7 = if x5 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧
      (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ),
      x4.gates[x7]? = Option.some x8 →
      x8.inputs = [x9, x10] →
      have x13 : List Bool := x4.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));
      (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ((26 : ℕ) + x7) = (x13.getD x9 Bool.false && x6 x10 || x6 x9 && x13.getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 ((26 : ℕ) + x7) = (x6 x9 || x6 x10))) ∧
      x6 x4.output = Bool.false := by
  intro avoid row one
  obtain ⟨C, cost, shape, noRepeatedOperands, correct, noPath⟩ := search
  refine ⟨C, cost, shape, noRepeatedOperands, ?_, ?_, ?_⟩
  · intro p l yes
    apply (correct _ _).2
    refine ⟨p,l,by simp only [one, decide_true],by simp only [one, decide_true],?_⟩
    simp only [avoid, one, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq] at yes
    rcases yes with ((h | h) | h) | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr h.symm))
  · intro U _
    constructor
    · cases result : C.eval (row U (avoid U)) with
      | false => rfl
      | true =>
        obtain ⟨p,l,point,miss,inc⟩ := (correct _ _).1 result
        rcases inc with rfl | rfl | rfl | rfl <;> simp [avoid, point] at miss
    · let A := fun p : Fin 13 => !(U p || U (p-1) || U (p-3) || U (p-9))
      change C.eval (row A U) = false
      cases result : C.eval (row A U) with
      | false => rfl
      | true =>
        obtain ⟨p,l,miss,line,inc⟩ := (correct _ _).1 result
        rcases inc with rfl | rfl | rfl | rfl <;> simp [A, line] at miss
  · intro side
    let x : Fin 26 → Bool := fun i => decide (i.val = if side then 13 else 0)
    let source : ℕ := if side then 0 else 13
    have low : source < 26 := by cases side <;> decide
    obtain ⟨d, inputs, recurrence, reachable⟩ := paths 26 C x source low
    refine ⟨d, inputs, recurrence, ?_⟩
    cases outcome : d C.output with
    | false => rfl
    | true => exact False.elim (noPath side ((reachable C.output).1 outcome))
