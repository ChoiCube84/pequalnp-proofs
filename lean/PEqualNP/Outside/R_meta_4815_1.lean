import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The reindexing argument follows R-meta-1890-1.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4815_1
    (single : ∀ (D : Circuit) (i : Fin 12),
      i ∈ ([0, 1, 3, 6, 8, 10, 11] : List (Fin 12)) →
      FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [pre.getD i.val false]) ≠
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
    (ordinary : ∀ (D : Circuit) (ij : Fin 12 × Fin 12),
      ij ∈ ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (0, 8), (1, 3), (1, 6), (1, 8),
          (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (6, 8), (8, 9)] : List (Fin 12 × Fin 12)) →
      FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [pre.getD ij.1.val false || pre.getD ij.2.val false]) ≠
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
    (mixed : ∀ (D : Circuit) (i : Fin 12),
      i ∈ ([0, 1, 3, 6, 8] : List (Fin 12)) →
      FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [pre.getD i.val false || pre.getD 10 false]) ≠
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (12 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ (x6 : Fin (10 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))];           x1.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin (12 : ℕ)) => x7.getD (↑x8) Bool.false) x2)]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by
  have transport :
      ∀ (n : ℕ) (C : Circuit) (p : Fin n → Fin n), FanInTwo C →
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (x : Fin n → Bool) (tail : List Bool),
            D.eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ p) ++ tail) := by
    intro n C p hfan
    let rename (i : ℕ) : ℕ := if hi : i < n then (p ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < n) : rename i < n := by simp [rename, hi]
    have late (i : ℕ) (hi : n ≤ i) : rename i = i := by simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let D : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g' hg').1, by simpa [mapGate] using (hfan g' hg').2⟩
    · exact List.length_map mapGate
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length)
        (lo : n ≤ x.length) (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have next : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [next]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases hn : i < n
            · have := early i hn
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x tail
    apply run C.gates _ _ (by simp) (by simp) _ C.output
    intro i
    by_cases hi : i < n
    · have hx : rename i < (List.ofFn x).length := by simpa using early i hi
      have hy : i < (List.ofFn (x ∘ p)).length := by simpa using hi
      rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy,
          List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
      simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      exact dite_eq_left hi
    · rw [late i (by omega), List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi)]
      simp

  intro C pins fan small pinBound
  let edges := ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10))
  let f (x : Fin 10 → Bool) := edges.any fun e => x e.1 && x e.2
  let pre (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
  let p : Fin 4 → Fin 12 → Fin 12 :=
    ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
      ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8, 10, 11],
      ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8, 10, 11],
      ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10, 11]]
  let q (k : Fin 4) (i : Fin 10) : Fin 10 := Fin.ofNat 10 (p k (i.castLE (by decide))).val
  have fInv (k : Fin 4) (x : Fin 10 → Bool) : f (x ∘ q k) = f x := by
    have checked : ∀ (j : Fin 4) (y : Fin 10 → Bool), f (y ∘ q j) = f y := by
      decide +kernel
    exact checked k x
  have andInv (k : Fin 4) (x : Fin 10 → Bool) :
      (x (q k 0) && x (q k 2)) = (x 0 && x 2) := by
    fin_cases k <;> simp [q, p, Bool.and_comm]
  have readPre (x : Fin 10 → Bool) (i : Fin 12) :
      (pre x).getD i.val false =
        if h : i.val < 10 then x ⟨i.val, h⟩ else if i.val = 10 then x 0 && x 2 else false := by
    by_cases h : i.val < 10
    · have h' : i.val < (List.ofFn x).length := by simpa using h
      rw [dite_eq_left h, List.getD_append _ _ _ _ h', List.getD_eq_getElem _ _ h']
      simp only [List.getElem_ofFn]
    · have h' : (List.ofFn x).length ≤ i.val := by simpa using Nat.le_of_not_gt h
      rw [dite_eq_right h, List.getD_append_right _ _ _ _ h', List.length_ofFn]
      by_cases h10 : i.val = 10
      · simp [h10]
      · have hh : i.val - 10 = 1 := by omega
        simp [h10, hh]
  have readInv (k : Fin 4) (x : Fin 10 → Bool) (i : Fin 12) :
      (pre (x ∘ q k)).getD i.val false = (pre x).getD (p k i).val false := by
    rw [readPre, readPre]
    fin_cases k <;> fin_cases i <;>
      simp [q, p, Function.comp_apply, Bool.and_comm] <;> rfl
  let singles := ([0, 1, 3, 6, 8, 10, 11] : List (Fin 12))
  let ordinaryPairs := ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (0, 8), (1, 3), (1, 6), (1, 8),
          (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (6, 8), (8, 9)] : List (Fin 12 × Fin 12))
  let mixedPins := ([0, 1, 3, 6, 8] : List (Fin 12))
  let cases := (singles.map fun i => (i, i)) ++ ordinaryPairs ++ (mixedPins.map fun i => (i, 10))
  let normalize (a b : Fin 12) :=
    if a = 11 then (b, b) else if b = 11 then (a, a) else if a ≤ b then (a, b) else (b, a)
  have cover : ∀ a b : Fin 12, ∃ k : Fin 4, normalize (p k a) (p k b) ∈ cases := by
    decide +kernel
  have outOfBounds (x : Fin 10 → Bool) :
      (pre x).getD (11 : Fin 12).val false = false := by
    apply List.getD_eq_default
    simp [pre]
  have normSound (x : Fin 10 → Bool) (a b : Fin 12) :
      ((pre x).getD (normalize a b).1.val false || (pre x).getD (normalize a b).2.val false)
        = ((pre x).getD a.val false || (pre x).getD b.val false) := by
    by_cases ha : a = 11
    · subst a
      simp only [normalize, ite_true, outOfBounds, Bool.false_or, Bool.or_self]
    · by_cases hb : b = 11
      · subst b
        simp only [normalize, ite_eq_right ha, ite_true, outOfBounds, Bool.or_false, Bool.or_self]
      · by_cases hab : a ≤ b
        · simp [normalize, ha, hb, hab]
        · simp [normalize, ha, hb, hab, Bool.or_comm]
  have padding : ∃ a b : Fin 12, ∀ x : Fin 10 → Bool,
      GateOp.or.eval (pins.map fun j => (pre x).getD j.val false) =
        ((pre x).getD a.val false || (pre x).getD b.val false) := by
    cases pins with
    | nil =>
      exact ⟨11, 11, fun x => by
        change false = ((pre x).getD (11 : Fin 12).val false ||
          (pre x).getD (11 : Fin 12).val false)
        rw [outOfBounds]
        rfl⟩
    | cons a rest =>
      cases rest with
      | nil =>
        refine ⟨a, 11, fun x => ?_⟩
        change ((pre x).getD a.val false || false) =
          ((pre x).getD a.val false || (pre x).getD (11 : Fin 12).val false)
        rw [outOfBounds]
      | cons b rest =>
        have hr : rest = [] := by
          simp only [List.length_cons] at pinBound
          exact List.length_eq_zero_iff.mp (by omega)
        subst rest
        refine ⟨a, b, fun x => ?_⟩
        change ((pre x).getD a.val false || ((pre x).getD b.val false || false)) = _
        rw [Bool.or_false]
  obtain ⟨a, b, pad⟩ := padding
  obtain ⟨k, hk⟩ := cover a b
  let ab := normalize (p k a) (p k b)
  obtain ⟨D, dFan, dSize, agree⟩ := transport 10 C (q k) fan
  have dBound : D.size ≤ 17 := dSize.le.trans small
  have found : ∃ x : Fin 10 → Bool,
      D.eval (pre x ++ [(pre x).getD ab.1.val false || (pre x).getD ab.2.val false]) ≠ f x := by
    change ab ∈ cases at hk
    simp only [cases, List.mem_append, List.mem_map] at hk
    rcases hk with (⟨i, hi, heq⟩ | hi) | ⟨i, hi, heq⟩
    · rw [← heq]
      simpa [pre, f, edges] using single D i hi dFan dBound
    · exact ordinary D ab hi dFan dBound
    · rw [← heq]
      exact mixed D i hi dFan dBound
  obtain ⟨x, hx⟩ := found
  refine ⟨x ∘ q k, ?_⟩
  have hf : (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) (x ∘ q k) = f (x ∘ q k) := by
    simp [f, edges, Bool.or_assoc, List.any_cons]
  change C.eval (pre (x ∘ q k) ++ [GateOp.or.eval (pins.map fun j =>
    (pre (x ∘ q k)).getD j.val false)]) ≠ _
  rw [hf, fInv, pad, readInv, readInv, ← normSound]
  let bit := (pre x).getD ab.1.val false || (pre x).getD ab.2.val false
  change C.eval (pre (x ∘ q k) ++ [bit]) ≠ f x
  have eqEval : D.eval (pre x ++ [bit]) = C.eval (pre (x ∘ q k) ++ [bit]) := by
    rw [show pre x ++ [bit] = List.ofFn x ++ [x 0 && x 2, bit] by simp [pre]]
    rw [show pre (x ∘ q k) ++ [bit] = List.ofFn (x ∘ q k) ++ [x 0 && x 2, bit] by
      simp [pre, Function.comp_apply, andInv]]
    exact agree x _
  rw [← eqEval]
  exact hx
