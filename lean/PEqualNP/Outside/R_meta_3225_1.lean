import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- When input one is true, changing the cofactor bit does not change the extra OR input.
-- On the distinguishing rows the unique OR reader must then be false before the change.
theorem PEqualNP.Outside.R_meta_3225_1
    (saturated : let reads := fun (g : Gate) =>
      (if g.op.eval [false,false] = true then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
    ∀ (C : Circuit), FanInTwo C → C.gates.countP reads ≤ 1 →
      ∀ g ∈ C.gates, g.op = .or → 6 ∈ g.inputs →
      ∃ j < C.size, C.gates[j]? = some g ∧
        ∀ w : List Bool, w.length = 10 → C.output ≠ 6 →
          C.eval w ≠ C.eval (w.set 6 true) →
          (C.wires w).getD (10+j) false = false)
    (exclude :
      let reads := fun (g : Gate) =>
        (if g.op.eval [false,false] = true then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
      let input := fun (b : Bool) (y : Fin 8 → Bool) =>
        [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]
      let f := fun y : Fin 8 → Bool =>
        (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) ||
        (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) ||
        (y 5 && y 7) || (y 7 && y 4)
      ∀ C : Circuit, FanInTwo C → C.size = 14 → C.gates.countP reads ≤ 1 →
        (∀ y, C.eval (input false y) = f y) →
        (∃ j < C.size, ∃ g : Gate, C.gates[j]? = some g ∧ g.op = .or ∧ 6 ∈ g.inputs ∧
          ∀ y : Fin 8 → Bool, y 1 = true → y 3 = true → f y = false →
            (C.wires (input false y)).getD (10+j) false = false) →
        ∃ y : Fin 8 → Bool, C.eval (input true y) ≠ (f y || y 0 || y 3)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ));
      have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2];
      have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ));
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x8 ∈ x4.gates, x8.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x8.inputs) → (∀ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x9) = x3 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x10) ≠ (x3 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro C fan length count hasOr falseCase
  by_contra! noWitness
  let input := fun (b : Bool) (y : Fin 8 → Bool) =>
        [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]
  let f := fun y : Fin 8 → Bool =>
        (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) ||
        (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) ||
        (y 5 && y 7) || (y 7 && y 4)
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (k : ℕ) (h : k < w.length) :
      (gs.foldl step w).getD k false = w.getD k false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ h
  have out : C.output ≠ 6 := by
    intro eq
    let y : Fin 8 → Bool := fun _ => true
    have full := falseCase y
    change (C.gates.foldl step (input false y)).getD C.output false = f y at full
    rw [eq, keep _ _ _ (by decide)] at full
    exact Bool.false_ne_true full
  obtain ⟨g, mem, op, wire⟩ := hasOr
  obtain ⟨j, jb, eq, silent⟩ := saturated C fan count g mem op wire
  obtain ⟨y, hy⟩ := exclude C fan length count falseCase (by
    refine ⟨j, jb, g, eq, op, wire, ?_⟩
    intro y left right blank
    change f y = false at blank
    have flip : (input false y).set 6 true = input true y := by
      simp [input, left]
    apply silent (input false y) (by simp [input]) out
    rw [flip]
    change C.eval (input false y) ≠ C.eval (input true y)
    rw [show C.eval (input false y) = f y from falseCase y,
      show C.eval (input true y) = (f y || y 0 || y 3) from noWitness y, blank, right]
    simp)
  exact hy (noWitness y)
