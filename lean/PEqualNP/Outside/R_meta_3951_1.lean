import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The selected gate value does not depend on the input unread by the earlier gates.
-- Hence both cofactor conditions refer to one common gate value.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_3951_1
    (stable : ∀ (n : ℕ) (C : Circuit) (k r w : ℕ) (x y : List Bool),
      x.length = n → y.length = n → r < n → k ≤ C.size → n ≤ w → w < n+k →
      (∀ i ≠ r, x.getD i false = y.getD i false) →
      (∀ g ∈ C.gates.take k, r ∉ g.inputs) →
      (C.wires x).getD w false = (C.wires y).getD w false)
    (impossible :
      let edges : List (Fin 9 × Fin 9) :=
        [1,11,21,31,36,5,15,25,35,52,62,77].map fun e => (Fin.ofNat 9 (e / 9), Fin.ofNat 9 e)
      let input := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
      let f := fun (x : Fin 9 → Bool) => edges.any fun e => x e.1 && x e.2
      let neighbor := fun (r : Fin 9) (x : Fin 9 → Bool) => edges.any fun e =>
        (decide (e.1 = r) && x e.2) || (decide (e.2 = r) && x e.1)
      let F := fun r x (b : Bool) => f x || b && neighbor r x
      let rows := fun r x b => input (Function.update x r b)
      ∀ (r : Fin 9) (C : Circuit) (s w : ℕ) (b : Bool),
        r ≠ 0 → r ≠ 6 → FanInTwo C → C.size ≤ 13 →
        10 ≤ w → w < s → s ≤ 10+C.size →
        (∀ g ∈ C.gates.take (s-10), r.val ∉ g.inputs) →
        let v := fun x => (C.wires (rows r x false)).getD w false
        (∀ x : Fin 9 → Bool, x r = false → C.eval (rows r x b) = F r x b) →
        (∀ x : Fin 9 → Bool, x r = false → v x = !b → C.eval (rows r x !b) = F r x !b) →
        (∀ x : Fin 9 → Bool, x r = false → f x = false → neighbor r x = true → v x = !b) →
        False) :
    have x1 : List (Fin (9 : ℕ) × Fin (9 : ℕ)) := List.map (fun (x1 : ℕ) => (Fin.ofNat (9 : ℕ) (x1 / (9 : ℕ)), Fin.ofNat (9 : ℕ) x1)) [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)];
      have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))];
      ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ) (x7 : Bool),
      x3 ≠ (0 : Fin (9 : ℕ)) →
      x3 ≠ (6 : Fin (9 : ℕ)) →
      PEqualNP.MetaComplexity.FanInTwo x4 →
      x4.size ≤ (13 : ℕ) →
      (10 : ℕ) ≤ x6 →
      x6 < x5 →
      x5 ≤ (10 : ℕ) + x4.size →
      (∀ x15 ∈ List.take (x5 - (10 : ℕ)) x4.gates, ↑x3 ∉ x15.inputs) →
      ∃ (x16 : Fin (9 : ℕ) → Bool),
      x16 x3 = Bool.false ∧
      have x17 : Bool := x1.any fun (x17 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x16 x17.1 && x16 x17.2;
      have x18 : Bool := x1.any fun (x18 : Fin (9 : ℕ) × Fin (9 : ℕ)) => Decidable.decide (x18.1 = x3) && x16 x18.2 || Decidable.decide (x18.2 = x3) && x16 x18.1;
      have x19 : Bool → Bool := fun (x19 : Bool) => x17 || x19 && x18;
      have x20 : Bool → List Bool := fun (x20 : Bool) => x2 (Function.update x16 x3 x20);
      have x21 : Bool → Bool := fun (x21 : Bool) => (x4.wires (x20 x21)).getD x6 Bool.false;
      x4.eval (x20 x7) ≠ x19 x7 ∨ x4.eval (x20 !x7) ≠ x19 !x7 ∧ (x21 !x7) = !x7 ∨ x17 = Bool.false ∧ x18 = Bool.true ∧ x21 Bool.false = x7 := by
  dsimp only
  intro r C s w b r0 r6 fan size low before high no
  let edges : List (Fin 9 × Fin 9) :=
    [1,11,21,31,36,5,15,25,35,52,62,77].map fun e => (Fin.ofNat 9 (e / 9), Fin.ofNat 9 e)
  let input := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
  let f := fun (x : Fin 9 → Bool) => edges.any fun e => x e.1 && x e.2
  let neighbor := fun (r : Fin 9) (x : Fin 9 → Bool) => edges.any fun e =>
    (decide (e.1 = r) && x e.2) || (decide (e.2 = r) && x e.1)
  let F := fun r x (b : Bool) => f x || b && neighbor r x
  let rows := fun r x b => input (Function.update x r b)
  let v (x : Fin 9 → Bool) := (C.wires (rows r x false)).getD w false
  have inputBit (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
      (List.ofFn x).getD i false = x ⟨i,hi⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hi, dite_true, Option.getD_some]
  have same (x : Fin 9 → Bool) (t : Bool) : v x = (C.wires (rows r x t)).getD w false := by
    apply stable 10 C (s-10) r.val w (rows r x false) (rows r x t)
      (by simp [rows,input]) (by simp [rows,input]) (by have := r.isLt; omega)
      (by omega) low (by omega) ?_ no
    intro i ne
    simp only [rows, input, Function.update_of_ne (Ne.symm r0), Function.update_of_ne (Ne.symm r6)]
    by_cases bound : i < 9
    · rw [List.getD_append _ _ _ _ (by simpa using bound),
        List.getD_append _ _ _ _ (by simpa using bound), inputBit _ _ bound, inputBit _ _ bound]
      have h : (⟨i,bound⟩ : Fin 9) ≠ r := fun eq => ne (congrArg Fin.val eq)
      simp only [Function.update_of_ne h]
    · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt bound),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt bound)]
      simp only [List.length_ofFn]
  by_contra cancel
  apply impossible r C s w b r0 r6 fan size low before high no
  · intro x hx
    change C.eval (rows r x b) = F r x b
    by_contra bad
    exact cancel ⟨x, hx, Or.inl bad⟩
  · intro x hx hv
    change C.eval (rows r x !b) = F r x !b
    have tie : (C.wires (rows r x !b)).getD w false = !b := (same x !b).symm.trans hv
    by_contra bad
    exact cancel ⟨x, hx, Or.inr (Or.inl ⟨bad, tie⟩)⟩
  · intro x hx empty live
    change v x = !b
    have ne : v x ≠ b := fun eq => cancel ⟨x, hx, Or.inr (Or.inr ⟨empty, live, eq⟩)⟩
    have opposite (u t : Bool) (h : u ≠ t) : u = !t := by
      cases u <;> cases t <;> first | rfl | exact False.elim (h rfl)
    exact opposite _ _ ne
