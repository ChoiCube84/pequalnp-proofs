import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Take the least-index junk witness when neither endpoint activates a junk gate alone.
-- In that case the OR supports of its two operands must reach opposite endpoints.
theorem PEqualNP.Outside.R_meta_5124_1
    (trace : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → TopForm G C → ∀ u v : Fin n, s(u,v) ∈ Ustar G C →
      (∀ j ∈ junk G C, gateVal n C j (pairInput u u) = false ∧
        gateVal n C j (pairInput v v) = false) →
      ∃ j ∈ junk G C,
        (u ∈ side C j 0 ∧ v ∈ side C j 1) ∨ (v ∈ side C j 0 ∧ u ∈ side C j 1))
    (countSingleton : ∃ c : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      ∀ H : Finset (Sym2 (Fin n)), H ⊆ Ustar G C →
      (∀ u v : Fin n, s(u,v) ∈ H → ∀ w < n + C.gates.length, v ∈ orIn n C w →
        (2 ≤ (orIn n C w).card → ∃ t ∈ orIn n C w, ¬ G.Adj u t) ∧
        (3 ≤ (orIn n C w).card → 2 ≤ ((orIn n C w).filter fun t => ¬G.Adj u t).card)) →
      (∀ e ∈ H, ∃ u ∈ e, ∃ j ∈ junk G C, gateVal n C j (pairInput u u) = true) →
      H.card ≤ c * (C.size + 1))
    (countCrossing : ∃ c : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      ∀ H : Finset (Sym2 (Fin n)), H ⊆ Ustar G C →
      (∀ u v : Fin n, s(u,v) ∈ H → ∀ w < n + C.gates.length, v ∈ orIn n C w →
        (2 ≤ (orIn n C w).card → ∃ t ∈ orIn n C w, ¬ G.Adj u t) ∧
        (3 ≤ (orIn n C w).card → 2 ≤ ((orIn n C w).filter fun t => ¬G.Adj u t).card)) →
      (∀ u v : Fin n, s(u,v) ∈ H →
        (∀ j ∈ junk G C, gateVal n C j (pairInput u u) = false ∧
          gateVal n C j (pairInput v v) = false) ∧
        ∃ j ∈ junk G C,
          (u ∈ side C j 0 ∧ v ∈ side C j 1) ∨ (v ∈ side C j 0 ∧ u ∈ side C j 1)) →
      H.card ≤ c * (C.size + 1)) :
    ∃ c : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      ∀ H : Finset (Sym2 (Fin n)), H ⊆ Ustar G C →
      (∀ u v : Fin n, s(u,v) ∈ H → ∀ w < n + C.gates.length, v ∈ orIn n C w →
        (2 ≤ (orIn n C w).card → ∃ t ∈ orIn n C w, ¬ G.Adj u t) ∧
        (3 ≤ (orIn n C w).card → 2 ≤ ((orIn n C w).filter fun t => ¬G.Adj u t).card)) →
      H.card ≤ c * (C.size + 1) := by
  classical
  obtain ⟨m, singletonBound⟩ := countSingleton
  obtain ⟨k, crossingBound⟩ := countCrossing
  refine ⟨m + k, ?_⟩
  intro n G inst girth edges C least top H sub avoid
  let fires (e : Sym2 (Fin n)) := ∃ u ∈ e, ∃ j ∈ junk G C, gateVal n C j (pairInput u u) = true
  let single := H.filter fires
  let cross := H.filter (fun e => ¬ fires e)
  have sSub : single ⊆ H := Finset.filter_subset _ _
  have cSub : cross ⊆ H := Finset.filter_subset _ _
  have sCount := singletonBound n G girth edges C least top single (sSub.trans sub)
    (fun u v huv => avoid u v (sSub huv))
    (fun e he => (Finset.mem_filter.mp he).2)
  have cCount := crossingBound n G girth edges C least top cross (cSub.trans sub)
    (fun u v huv => avoid u v (cSub huv)) (by
      intro u v huv
      have silent : ¬ fires s(u,v) := (Finset.mem_filter.mp huv).2
      have noSingle : ∀ j ∈ junk G C, gateVal n C j (pairInput u u) = false ∧
          gateVal n C j (pairInput v v) = false := by
        intro j hj
        constructor
        · exact Bool.eq_false_iff.mpr (fun hit => silent ⟨u, Sym2.mem_mk_left u v, j, hj, hit⟩)
        · exact Bool.eq_false_iff.mpr (fun hit => silent ⟨v, Sym2.mem_mk_right u v, j, hj, hit⟩)
      exact ⟨noSingle, trace n G C least top u v (sub (cSub huv)) noSingle⟩)
  have partition : single.card + cross.card = H.card :=
    Finset.card_filter_add_card_filter_not (s := H) fires
  rw [Nat.add_mul]
  omega
