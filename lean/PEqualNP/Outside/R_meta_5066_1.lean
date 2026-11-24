import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Relabel the line inputs by the inverse of the matching permutation.
-- The lower-bound premise then needs only the matching on the diagonal.
theorem PEqualNP.Outside.R_meta_5066_1
    (relabel : ∀ (m : ℕ) (τ : Fin m → Fin m) (C : Circuit), IsAO2 m C →
      ∃ D : Circuit, IsAO2 m D ∧ D.size = C.size ∧
        ∀ x : Fin m → Bool, circuitFun m D x = circuitFun m C (x ∘ τ))
    (diagonal :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : Circuit),
      n < E.card → 2*n ≤ C.size + 1 →
      (∀ a b c d : Fin n, a ≠ b → c ≠ d →
        ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) →
      (∀ i : Fin n, (i,i) ∈ E) → IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, circuitFun (n+n) C x =
        decide (∃ p l : Fin n, (p,l) ∈ E ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      ((∀ p : Fin n, ∃ l : Fin n, l ≠ p ∧ (p,l) ∈ E) ∧
        (∀ l : Fin n, ∃ p : Fin n, p ≠ l ∧ (p,l) ∈ E)) →
      E.card + n ≤ C.size + 1) :
    ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (C : Circuit),
    n < E.card → 2*n ≤ C.size + 1 →
    (∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) →
    (∀ i : Fin n, (i,σ i) ∈ E) → IsAO2 (n+n) C →
    (∀ x : Fin (n+n) → Bool, circuitFun (n+n) C x =
      decide (∃ p l : Fin n, (p,l) ∈ E ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
    ((∀ p : Fin n, ∃ l : Fin n, l ≠ σ p ∧ (p,l) ∈ E) ∧
      (∀ l : Fin n, ∃ p : Fin n, σ p ≠ l ∧ (p,l) ∈ E)) →
    E.card + n ≤ C.size + 1 := by
  intro n E σ C larger inputs c4 matchEdge legal computes neighbors
  let bij : (Fin n × Fin n) ≃ (Fin n × Fin n) := Equiv.prodCongr (Equiv.refl _) σ.symm
  let H := E.map bij.toEmbedding
  have cardH : H.card = E.card := Finset.card_map _
  have mem (a b : Fin n) : (a,b) ∈ H ↔ (a,σ b) ∈ E := by
    change (a,b) ∈ E.map bij.toEmbedding ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨ab, hab, eq⟩
      have fa : ab.1 = a := congrArg Prod.fst eq
      have fb : σ.symm ab.2 = b := congrArg Prod.snd eq
      have gb : ab.2 = σ b := by
        simpa only [Equiv.apply_symm_apply] using congrArg σ fb
      have pairEq : ab = (a,σ b) := Prod.ext fa gb
      rwa [pairEq] at hab
    · intro h
      exact ⟨(a,σ b), h, Prod.ext rfl (σ.symm_apply_apply b)⟩
  let τ : Fin (n+n) → Fin (n+n) :=
    fun i => Fin.addCases (Fin.castAdd n) (fun l => Fin.natAdd n (σ.symm l)) i
  have left (p : Fin n) : τ (Fin.castAdd n p) = Fin.castAdd n p := by
    change Fin.addCases (motive := fun _ : Fin (n+n) => Fin (n+n)) (Fin.castAdd n) (fun l => Fin.natAdd n (σ.symm l)) (Fin.castAdd n p) = _
    rw [Fin.addCases_left]
  have right (l : Fin n) : τ (Fin.natAdd n l) = Fin.natAdd n (σ.symm l) := by
    change Fin.addCases (motive := fun _ : Fin (n+n) => Fin (n+n)) (Fin.castAdd n) (fun l => Fin.natAdd n (σ.symm l)) (Fin.natAdd n l) = _
    rw [Fin.addCases_right]
  obtain ⟨D, valid, sameSize, eval⟩ := relabel (n+n) τ C legal
  have square : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬ ((a,c) ∈ H ∧ (a,d) ∈ H ∧ (b,c) ∈ H ∧ (b,d) ∈ H) := by
    intro a b c d ab cd
    rw [mem, mem, mem, mem]
    exact c4 a b (σ c) (σ d) ab (fun eq => cd (σ.injective eq))
  have value (x : Fin (n+n) → Bool) : circuitFun (n+n) D x =
      decide (∃ p l : Fin n, (p,l) ∈ H ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) := by
    rw [eval, computes]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Function.comp_apply, left, right]
    constructor
    · rintro ⟨p,l,hit,hp,hl⟩
      exact ⟨p, σ.symm l, (mem _ _).mpr (by simpa only [Equiv.apply_symm_apply] using hit), hp, hl⟩
    · rintro ⟨p,l,hit,hp,hl⟩
      exact ⟨p, σ l, (mem _ _).mp hit, hp, by simpa only [Equiv.symm_apply_apply] using hl⟩
  have other : (∀ p : Fin n, ∃ l : Fin n, l ≠ p ∧ (p,l) ∈ H) ∧
      (∀ l : Fin n, ∃ p : Fin n, p ≠ l ∧ (p,l) ∈ H) := by
    constructor
    · intro p
      obtain ⟨l, ne, hit⟩ := neighbors.1 p
      refine ⟨σ.symm l, ?_, (mem _ _).mpr (by simpa only [Equiv.apply_symm_apply] using hit)⟩
      intro eq
      exact ne (by simpa only [Equiv.apply_symm_apply] using congrArg σ eq)
    · intro l
      obtain ⟨p, ne, hit⟩ := neighbors.2 (σ l)
      exact ⟨p, (fun eq => ne (congrArg σ eq)), (mem _ _).mpr hit⟩
  have bound := diagonal n H D (cardH.symm ▸ larger) (sameSize.symm ▸ inputs) square
    (fun i => (mem i i).mpr (matchEdge i)) valid value other
  simpa only [cardH, sameSize] using bound
