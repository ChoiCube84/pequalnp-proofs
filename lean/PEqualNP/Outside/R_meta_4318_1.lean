import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.CoverPromise

-- At an edge's first true AND, both operands trace through ORs to different endpoints.
-- Their OR supports are disjoint because the AND rejects every singleton.
theorem PEqualNP.Outside.R_meta_4318_1
    (firstCrossing : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      Monotone2 C → circuitFun n C = graphFun G ∅ →
      (∀ j < C.size, (gateAt C j).op = .and → ∀ v : Fin n,
        gateVal n C j (pairInput v v) = false) →
      ∀ u v : Fin n, G.Adj u v →
      ∃ j < C.size, (gateAt C j).op = .and ∧ gateVal n C j (pairInput u v) = true ∧
        (∀ k < j, (gateAt C k).op = .and → gateVal n C k (pairInput u v) = false) ∧
        ∃ p q, (gateAt C j).inputs = [p,q] ∧ p < n + j ∧ q < n + j ∧
          Disjoint (orIn n C p) (orIn n C q) ∧
          ((u ∈ orIn n C p ∧ v ∈ orIn n C q) ∨ (v ∈ orIn n C p ∧ u ∈ orIn n C q)))
    (counting : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      G.edgeFinset.Nonempty → ∀ C : Circuit,
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      (∀ j < C.size, (gateAt C j).op = .and → ∀ v : Fin n,
        gateVal n C j (pairInput v v) = false) →
      (∀ u v : Fin n, G.Adj u v →
        ∃ j < C.size, (gateAt C j).op = .and ∧ gateVal n C j (pairInput u v) = true ∧
          (∀ k < j, (gateAt C k).op = .and → gateVal n C k (pairInput u v) = false) ∧
          ∃ p q, (gateAt C j).inputs = [p,q] ∧ p < n + j ∧ q < n + j ∧
            Disjoint (orIn n C p) (orIn n C q) ∧
            ((u ∈ orIn n C p ∧ v ∈ orIn n C q) ∨ (v ∈ orIn n C p ∧ u ∈ orIn n C q))) →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      G.edgeFinset.Nonempty → ∀ C : Circuit,
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      (∀ j < C.size, (gateAt C j).op = .and → ∀ v : Fin n,
        gateVal n C j (pairInput v v) = false) →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  intro n G inst triangle square nonempty C least computes quiet
  exact counting n G triangle square nonempty C least computes quiet
    (firstCrossing n G C least.1 computes quiet)
