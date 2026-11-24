import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Library.Peel

-- Separate circuit normalization from the counting argument on vertex deletion.
theorem PEqualNP.Outside.R_meta_4011_1
    (normalize :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      (∃ i j, G.Adj i j) → (∀ i j, G.Adj i j → i ∉ A) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ v ∉ A,
        let gs := C.gates.filter
          (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains ↑v)
        gs.length ≤ 3 ∧ (gs.length = 3 → ∀ g ∈ gs, g.op = GateOp.or)) →
      ∃ D : Circuit, D.size = C.size ∧ n ≤ D.output ∧ D.output + 1 = n + D.size ∧
        IsMinimalCircuit n D ∧ circuitFun n D = graphFun G A ∧
        ReadsBack n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup ∧
          g.inputs.length = (bif g.op.eval [false] then 1 else 2)) ∧
        (∀ v ∉ A,
          let gs := D.gates.filter (fun g => g.inputs.contains ↑v)
          gs.length ≤ 3 ∧ (gs.length = 3 → ∀ g ∈ gs, g.op = GateOp.or)))
    (deletion :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) →
      (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      n ≤ C.output → C.output + 1 = n + C.size → ReadsBack n C →
      (∀ g ∈ C.gates, g.inputs.Nodup ∧
        g.inputs.length = (bif g.op.eval [false] then 1 else 2)) →
      (∀ v ∉ A,
        let gs := C.gates.filter (fun g => g.inputs.contains ↑v)
        gs.length ≤ 3 ∧ (gs.length = 3 → ∀ g ∈ gs, g.op = GateOp.or)) →
      (∀ T : Finset (Fin n), Disjoint A T → (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size + 1 < A.card + G.edgeFinset.card + T.card) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (graphFun (delVerts G {v}) A) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) →
      (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
      (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) →
      (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
      PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
      PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →
      (∀ x12 ∉ x4,
      have x14 : List PEqualNP.CircuitLowerBounds.Gate :=
        List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x12) x5.gates;
      x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
      (∀ (x13 : Finset (Fin x1)), Disjoint x4 x13 → (∀ (x15 x16 : Fin x1), x2.Adj x15 x16 → x15 ∈ x13 ∨ x16 ∈ x13) → x5.size + (1 : ℕ) < x4.card + x2.edgeFinset.card + x13.card) → ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x5 (Function.update x16 x14 Bool.false)) x15 := by
  intro n G decidableAdj A C cubic girth disj edge minC valC readC budget
  obtain ⟨D, size, output, last, minD, valD, back, arity, readD⟩ :=
    normalize n G A C edge disj minC valC readC
  obtain ⟨v, hv, s, bound, circuit⟩ :=
    deletion n G A D cubic girth disj edge minD valD output last back arity readD
      (fun T disjoint cover => size ▸ budget T disjoint cover)
  refine ⟨v, hv, s, size ▸ bound, ?_⟩
  suffices funEq : (fun x => circuitFun n C (Function.update x v false)) =
      graphFun (delVerts G {v}) A by rwa [funEq]
  funext x
  rw [valC]
  have marked : (∃ a ∈ A, Function.update x v false a = true) ↔ (∃ a ∈ A, x a = true) := by
    apply exists_congr
    intro a
    constructor <;> rintro ⟨ha, value⟩ <;> refine ⟨ha, ?_⟩
    all_goals
      have ne : a ≠ v := fun eq => hv (eq ▸ ha)
      simpa [Function.update_of_ne ne] using value
  have edges :
      (∃ i j, G.Adj i j ∧ Function.update x v false i = true ∧
        Function.update x v false j = true) ↔
      (∃ i j, (delVerts G {v}).Adj i j ∧ x i = true ∧ x j = true) := by
    constructor
    · rintro ⟨i, j, hij, xi, xj⟩
      have hi : i ≠ v := by rintro rfl; simp at xi
      have hj : j ≠ v := by rintro rfl; simp at xj
      exact ⟨i, j, ⟨hij, by simpa using hi, by simpa using hj⟩,
        by simpa [Function.update_of_ne hi] using xi,
        by simpa [Function.update_of_ne hj] using xj⟩
    · rintro ⟨i, j, ⟨hij, hi, hj⟩, xi, xj⟩
      exact ⟨i, j, hij,
        by simpa [Function.update_of_ne (by simpa using hi : i ≠ v)] using xi,
        by simpa [Function.update_of_ne (by simpa using hj : j ≠ v)] using xj⟩
  unfold graphFun
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using or_congr marked edges
