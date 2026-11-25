import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each admissible negative row lies below a cap paired with all its nonneighbors.
-- A monotone circuit tested on those rows then rejects every admissible negative.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1979_1
    (cover : let D : Finset (Fin 13) := {0,1,3,9}
      let capP := fun P : Finset (Fin 13) => ∀ l : Fin 13, (P.filter fun p => p-l ∈ D).card ≤ 2
      let capL := fun L : Finset (Fin 13) => ∀ p : Fin 13, (L.filter fun l => p-l ∈ D).card ≤ 2
      let awayL := fun P : Finset (Fin 13) => Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ P, p-l ∉ D)
      let awayP := fun L : Finset (Fin 13) => Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ L, p-l ∉ D)
      ∀ P L : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ L, p-l ∉ D) → capP P → capL L →
        (∃ S, 3 ≤ S.card ∧ capP S ∧ capL (awayL S) ∧ P ⊆ S ∧ L ⊆ awayL S) ∨
        (∃ T, 3 ≤ T.card ∧ capL T ∧ capP (awayP T) ∧ L ⊆ T ∧ P ⊆ awayP T))
    (search : let D : Finset (Fin 13) := {0,1,3,9}
      let capP := fun P : Finset (Fin 13) => ∀ l : Fin 13, (P.filter fun p => p-l ∈ D).card ≤ 2
      let capL := fun L : Finset (Fin 13) => ∀ p : Fin 13, (L.filter fun l => p-l ∈ D).card ≤ 2
      let awayL := fun P : Finset (Fin 13) => Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ P, p-l ∉ D)
      let awayP := fun L : Finset (Fin 13) => Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ L, p-l ∉ D)
      let row := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
        decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l ∈ L, i = Fin.natAdd 13 l)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∀ p l : Fin 13, p-l ∈ D →
          circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) ∧
        (∀ S, 3 ≤ S.card → capP S → capL (awayL S) → circuitFun 26 C (row S (awayL S)) = false) ∧
        ∀ T, 3 ≤ T.card → capL T → capP (awayP T) → circuitFun 26 C (row (awayP T) T) = false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧
      ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, x5 - x7 ∉ x1) →
        (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) →
        (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 - x8 ∈ x1}.card ≤ (2 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x3, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ x9 ∈ x4, x8 = Fin.natAdd (13 : ℕ) x9)) = Bool.false := by
  intro D
  obtain ⟨C, mono, size, positive, leftTest, rightTest⟩ := search
  refine ⟨C, mono, size, positive, ?_⟩
  let row := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
    decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l ∈ L, i = Fin.natAdd 13 l)
  let step (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
  have grows (x y : List Bool) (g : Gate) (op : g.op = .and ∨ g.op = .or)
      (h : ∀ i, x.getD i false = true → y.getD i false = true) :
      g.op.eval (g.inputs.map fun i => x.getD i false) = true →
        g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
    rcases op with ha | ho
    · rw [ha]
      change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      exact fun old i hi => h i (old i hi)
    · rw [ho]
      change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i,hi,active⟩
      exact ⟨i,hi,h i active⟩
  have monotone (gs : List Gate) (x y : List Bool) (len : x.length = y.length)
      (h : ∀ i, x.getD i false = true → y.getD i false = true)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ∀ i, (gs.foldl step x).getD i false = true → (gs.foldl step y).getD i false = true := by
    induction gs generalizing x y with
    | nil => exact h
    | cons g gs ih =>
      apply ih (step x g) (step y g) (by simp only [step, List.length_append, List.length_singleton, len]) ?_
        (fun a ha => ops a (List.mem_cons_of_mem _ ha))
      intro i
      rcases Nat.lt_trichotomy i x.length with lo | eq | hi
      · change (x ++ [_]).getD i false = true → (y ++ [_]).getD i false = true
        rw [List.getD_append _ _ _ _ lo, List.getD_append _ _ _ _ (len ▸ lo)]
        exact h i
      · change (x ++ [_]).getD i false = true → (y ++ [_]).getD i false = true
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), eq, ← len]
        simp only [Nat.sub_self, List.getD_cons_zero]
        exact grows x y g (ops g List.mem_cons_self) h
      · intro bad
        have outside : (step x g).length ≤ i := by
          simp only [step, List.length_append, List.length_singleton]
          omega
        rw [List.getD_eq_default _ _ outside] at bad
        contradiction
  have increases (P P' L L' : Finset (Fin 13)) (points : P ⊆ P') (lines : L ⊆ L') :
      circuitFun 26 C (row P L) = true → circuitFun 26 C (row P' L') = true := by
    have nextRow (i : Fin 26) : row P L i = true → row P' L' i = true := by
      simp only [row, decide_eq_true_eq]
      rintro (⟨p, hp, eq⟩ | ⟨l, hl, eq⟩)
      · exact Or.inl ⟨p, points hp, eq⟩
      · exact Or.inr ⟨l, lines hl, eq⟩
    have start (i : ℕ) : (List.ofFn (row P L)).getD i false = true →
        (List.ofFn (row P' L')).getD i false = true := by
      by_cases hi : i < 26
      · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
        simpa only [List.getElem_ofFn] using nextRow ⟨i,hi⟩
      · intro h
        rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)] at h
        contradiction
    exact monotone C.gates _ _ (by simp only [List.length_ofFn]) start
      (fun g hg => by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (mono g hg).1) C.output
  intro P L independent pCap lCap
  change circuitFun 26 C (row P L) = false
  cases eval : circuitFun 26 C (row P L) with
  | false => rfl
  | true =>
    rcases cover P L independent pCap lCap with ⟨S,count,cs,ca,ps,ls⟩ | ⟨T,count,ct,ca,lt,pt⟩
    · have yes := increases P S L _ ps ls eval
      rw [leftTest S count cs ca] at yes
      contradiction
    · have yes := increases P _ L T pt lt eval
      rw [rightTest T count ct ca] at yes
      contradiction
