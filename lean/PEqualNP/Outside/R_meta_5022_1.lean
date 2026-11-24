import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- Isolate the circuit structure of the input with exactly two OR readers.
-- In a least circuit their other operands differ, and the later OR cannot read the earlier OR.
theorem PEqualNP.Outside.R_meta_5022_1
    (readerShape : ∀ (n : ℕ) (C : Circuit) (v : Fin n), IsMinimalCircuit n C →
      (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
      let R := C.gates.filter
        (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
      R.length = 2 → (∀ g ∈ R, g.op = .or) →
      ∃ i j a b : ℕ, i < j ∧ j < C.gates.length ∧
        a < n + i ∧ b < n + j ∧ a ≠ b ∧ b ≠ n + i ∧
        (gateAt C i).op = .or ∧ (gateAt C j).op = .or ∧
        (gateAt C i).inputs.Perm [v.val, a] ∧ (gateAt C j).inputs.Perm [v.val, b])
    (counting :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A K : Finset (Fin n)) (C : Circuit),
      IsMinCover G K →
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ v ∉ A,
        let R := C.gates.filter
          (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
        2 ≤ R.length ∧ (R.length = 2 → ∀ g ∈ R, g.op = .or)) →
      (∃ v ∉ A, ∃ i j a b : ℕ, i < j ∧ j < C.gates.length ∧
        a < n + i ∧ b < n + j ∧ a ≠ b ∧ b ≠ n + i ∧
        (gateAt C i).op = .or ∧ (gateAt C j).op = .or ∧
        (gateAt C i).inputs.Perm [v.val, a] ∧ (gateAt C j).inputs.Perm [v.val, b]) →
      A.card + G.edgeSet.ncard + K.card ≤ C.size + 1) :
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (C : Circuit),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
    (∀ u v, G.Adj u v → u ∉ A) →
    (∃ u v, G.Adj u v) →
    (∀ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) → k ≤ K.card) →
    (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
    FanInTwo C → circuitFun n C = f →
    (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A, 2 ≤ (C.gates.filter
      (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length) →
    (∀ v ∉ A,
      let R := C.gates.filter
        (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
      R.length = 2 → ∀ g ∈ R, g.op = .or) →
    (∃ v ∉ A, (C.gates.filter
      (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length = 2) →
    A.card + G.edgeSet.ncard + k ≤ C.size + 1 := by
  intro n k G A f C regular girth disjoint nonempty bound defines fan computes minimal reads ors two
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have graph : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [defines x]
    change _ ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have least : IsMinimalCircuit n C := by
    refine ⟨fan, fun D dFan agree => minimal D.size ?_⟩
    exact ⟨D, dFan, le_rfl, congrFun (agree.trans computes)⟩
  have nonconst : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y := by
    obtain ⟨i, j, h⟩ := nonempty
    refine ⟨(fun _ => false), (fun _ => true), ?_⟩
    rw [computes]
    have off : f (fun _ => false) = false := by
      apply Bool.eq_false_iff.mpr
      intro on
      simpa using (defines (fun _ => false)).mp on
    have on : f (fun _ => true) = true := (defines _).mpr (Or.inr ⟨i, j, h, rfl, rfl⟩)
    rw [off, on]
    decide
  have someCover : ∃ m, ∃ K : Finset (Fin n), G.IsVertexCover (↑K) ∧ K.card = m :=
    ⟨_, Finset.univ, by simp, rfl⟩
  obtain ⟨K, cover, card⟩ := Nat.find_spec someCover
  have minCover : IsMinCover G K := by
    refine ⟨cover, fun T hT => ?_⟩
    rw [card]
    exact Nat.find_min' someCover ⟨T, hT, rfl⟩
  have lower : k ≤ K.card := bound K (fun u v h => cover h)
  have h := counting n G A K C minCover regular girth disjoint least (computes.trans graph)
    (fun v hv => ⟨reads v hv, ors v hv⟩) (by
      obtain ⟨v, hv, eq⟩ := two
      exact ⟨v, hv, readerShape n C v least nonconst eq (ors v hv eq)⟩)
  omega
