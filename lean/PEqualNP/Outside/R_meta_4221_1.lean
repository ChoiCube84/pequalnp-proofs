import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The small positive and negative tests give full incidence correctness.
-- Two disjoint positive tests force each selected wire to be internal.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_4221_1
    (complete : let inc := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let avoid := fun U : Finset (Fin 13) => (Finset.univ : Finset (Fin 13)).filter (fun l => ∀ p ∈ U, ¬inc p l)
      ∀ f : Finset (Fin 13) → Finset (Fin 13) → Bool,
        (∀ P P' L L', P ⊆ P' → L ⊆ L' → f P L = true → f P' L' = true) →
        (∀ p l, inc p l → f {p} {l} = true) →
        (∀ U : Finset (Fin 13), U.card ≤ 3 →
          f U (avoid U) = false ∧ f (avoid U) U = false) →
        ∀ P L, f P L = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l)
    (bound : let inc := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let input := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P) else decide (Fin.ofNat 13 i.val ∈ L)
      ∀ (C : Circuit) (ws : List ℕ), Monotone2 C → ws.length ≤ 2 → ws ≠ [] →
        (∀ w ∈ ws, 26 ≤ w ∧ w < 26+C.size) →
        (∀ P L, (∀ w ∈ ws, (C.wires (List.ofFn (input P L))).getD w false = true) ↔
          ∃ p ∈ P, ∃ l ∈ L, inc p l) →
        63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),
      PEqualNP.MetaComplexity.Monotone2 x1 →
      x2.length ≤ (2 : ℕ) →
      (∃ x5 ∈ x2, (26 : ℕ) ≤ x5) →
      (let x6 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x6 x7 : Fin (13 : ℕ)) => (↑x6 + ↑x7) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Fin (26 : ℕ)) => if ↑x9 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x7) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x8);
      have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x8 : Finset (Fin (13 : ℕ))) => {x9 : Fin (13 : ℕ) | ∀ x10 ∈ x8, ¬x6 x10 x9};
      have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x11 : ℕ) => (x1.wires (List.ofFn (x7 x9 x10))).getD x11 Bool.false) x2);
      (∀ (x10 x11 : Fin (13 : ℕ)), x6 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x8 x10) = Bool.false ∧ x9 (x8 x10) x10 = Bool.false) →
      (63 : ℕ) ≤ x1.size := by
  intro C ws mono length gate tests
  let inc := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let input := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P) else decide (Fin.ofNat 13 i.val ∈ L)
  let value := fun P L => GateOp.and.eval (ws.map fun w => (C.wires (List.ofFn (input P L))).getD w false)
  obtain ⟨positives, negatives⟩ := tests
  have allTrue (P L : Finset (Fin 13)) : value P L = true ↔
      ∀ w ∈ ws, (C.wires (List.ofFn (input P L))).getD w false = true := by
    change (ws.map _).all id = true ↔ _
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  let step (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
  have shape (gs : List Gate) (x : List Bool) :
      (gs.foldl step x).length = x.length + gs.length ∧
      ∀ i < x.length, (gs.foldl step x).getD i false = x.getD i false := by
    induction gs generalizing x with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step x g)).length = _ ∧ _
      have appended : (step x g).length = x.length + 1 := by
        simp only [step, List.length_append, List.length_singleton]
      obtain ⟨len, keep⟩ := ih (step x g)
      refine ⟨by rw [len, appended, List.length_cons]; omega, ?_⟩
      intro i h
      exact (keep i (by omega)).trans (List.getD_append _ _ _ _ h)
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
  have increasing (P P' L L' : Finset (Fin 13)) (pts : P ⊆ P') (lns : L ⊆ L') :
      value P L = true → value P' L' = true := by
    intro yes
    apply (allTrue P' L').2
    have inputMono (i : Fin 26) : input P L i = true → input P' L' i = true := by
      unfold input
      split <;> simp only [decide_eq_true_eq]
      · exact fun h => pts h
      · exact fun h => lns h
    have start (i : ℕ) : (List.ofFn (input P L)).getD i false = true →
        (List.ofFn (input P' L')).getD i false = true := by
      by_cases hi : i < 26
      · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
        simpa only [List.getElem_ofFn] using inputMono ⟨i,hi⟩
      · intro h
        rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)] at h
        contradiction
    exact fun w hw => monotone C.gates _ _ (by simp only [List.length_ofFn]) start
      (fun g hg => by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (mono g hg).1)
      w ((allTrue P L).1 yes w hw)
  have exactRows : ∀ P L, value P L = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l :=
    complete value increasing positives negatives
  have live (w : ℕ) (hw : w ∈ ws) : 26 ≤ w ∧ w < 26+C.size := by
    have a := (allTrue {0} {0}).1 (positives 0 0 (by decide)) w hw
    have b := (allTrue {1} {12}).1 (positives 1 12 (by decide)) w hw
    have noOverlap (i : Fin 26) : ¬ (input {0} {0} i = true ∧ input {1} {12} i = true) := by
      intro found
      by_cases hp : i.val < 13
      · simp only [input, ite_eq_left hp, decide_eq_true_eq, Finset.mem_singleton] at found
        exact (by decide : (0 : Fin 13) ≠ 1) (found.1.symm.trans found.2)
      · simp only [input, ite_eq_right hp, decide_eq_true_eq, Finset.mem_singleton] at found
        exact (by decide : (0 : Fin 13) ≠ 12) (found.1.symm.trans found.2)
    have first : 26 ≤ w := by
      by_contra bad
      have primary : w < 26 := by omega
      have h₁ := (shape C.gates (List.ofFn (input {0} {0}))).2 w (by simpa using primary)
      have h₂ := (shape C.gates (List.ofFn (input {1} {12}))).2 w (by simpa using primary)
      apply noOverlap ⟨w,primary⟩
      have p := h₁.symm.trans a
      have q := h₂.symm.trans b
      rw [List.getD_eq_getElem _ _ (by simpa using primary), List.getElem_ofFn] at p q
      exact ⟨p,q⟩
    have last : w < 26+C.size := by
      by_contra bad
      have len : (C.wires (List.ofFn (input {0} {0}))).length = 26+C.size := by
        change (C.gates.foldl step (List.ofFn (input {0} {0}))).length = 26+C.gates.length
        rw [(shape C.gates _).1, List.length_ofFn]
      rw [List.getD_eq_default _ _ (by omega)] at a
      contradiction
    exact ⟨first, last⟩
  apply bound C ws mono length (fun h => by simp only [h, List.not_mem_nil, false_and, exists_false] at gate) live
  intro P L
  exact (allTrue P L).symm.trans (exactRows P L)
