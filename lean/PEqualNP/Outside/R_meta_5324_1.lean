import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The covered edges have both endpoints among the inputs that determine the chosen wires.
-- Only the excess of edges plus matching edges over these endpoints needs a further bound.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_5324_1
    (support : ∀ (n : ℕ) (C : Circuit) (W : Finset ℕ), TopForm.IsAO2 n C →
      ∃ A : Finset (Fin n), A.card ≤ C.size + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ A, x i = y i) →
          ∀ w ∈ W, (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false)
    (excess : ∀ (n m : ℕ) (E H M : Finset (Fin n × Fin m)) (C : Circuit) (T : Finset (ℕ × ℕ)),
      let edge := fun (z : Fin (n+m) → Bool) =>
        ∃ u v, (u,v) ∈ E ∧ z (Fin.castAdd m u) = true ∧ z (Fin.natAdd n v) = true
      let bit := fun w z => (C.wires (List.ofFn z)).getD w false
      let pair := fun e : Fin n × Fin m =>
        fun i : Fin (n+m) => decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2)
      let V := (H.image fun e => Fin.castAdd m e.1) ∪ (H.image fun e => Fin.natAdd n e.2)
      (∀ u u' v v', u ≠ u' → v ≠ v' →
        ¬ ((u,v) ∈ E ∧ (u,v') ∈ E ∧ (u',v) ∈ E ∧ (u',v') ∈ E)) →
      TopForm.IsAO2 (n+m) C →
      (∀ j < C.gates.length, (NestedCover.gateAt C j).op = .and →
        ∃ z, bit (n+m+j) z = true ∧ ¬ edge z) →
      (∀ t ∈ T, ∀ z, bit t.1 z = true → bit t.2 z = true → edge z) →
      (∀ e ∈ H, e ∈ E ∧ ∃ t ∈ T, bit t.1 (pair e) = true ∧ bit t.2 (pair e) = true) →
      M ⊆ H → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      V.card ≤ C.size + 2*T.card → V.card < H.card + M.card →
      H.card + M.card ≤ C.size + 2*T.card) :
    ∀ (x1 x2 : ℕ) (x3 x4 x5 : Finset (Fin x1 × Fin x2)) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Finset (ℕ × ℕ)),
      (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬((x8, x10) ∈ x3 ∧ (x8, x11) ∈ x3 ∧ (x9, x10) ∈ x3 ∧ (x9, x11) ∈ x3)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x6 →
      (∀ x10 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD (x1 + x2 + x10) Bool.false = Bool.true ∧ ¬∃ (x14 : Fin x1) (x15 : Fin x2), (x14, x15) ∈ x3 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x1 x15) = Bool.true) →
      (∀ x11 ∈ x7, ∀ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD x11.1 Bool.false = Bool.true → (x6.wires (List.ofFn x13)).getD x11.2 Bool.false = Bool.true → ∃ (x16 : Fin x1) (x17 : Fin x2), (x16, x17) ∈ x3 ∧ x13 (Fin.castAdd x2 x16) = Bool.true ∧ x13 (Fin.natAdd x1 x17) = Bool.true) →
      (∀ x12 ∈ x4, x12 ∈ x3 ∧ ∃ x14 ∈ x7, (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.1 Bool.false = Bool.true ∧ (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.2 Bool.false = Bool.true) →
      x5 ⊆ x4 →
      (∀ x14 ∈ x5, ∀ x16 ∈ x5, x14.1 = x16.1 → x14 = x16) →
      (∀ x15 ∈ x5, ∀ x17 ∈ x5, x15.2 = x17.2 → x15 = x17) →
      x4.card + x5.card ≤ x6.size + (2 : ℕ) * x7.card := by
  classical
  intro n m E H M C T square ao dirty safe cover subset rows columns
  let V := (H.image fun e => Fin.castAdd m e.1) ∪ (H.image fun e => Fin.natAdd n e.2)
  let W := (T.image Prod.fst) ∪ (T.image Prod.snd)
  have cardW : W.card ≤ 2*T.card := by
    have h := Finset.card_union_le (T.image Prod.fst) (T.image Prod.snd)
    have h₁ : (T.image Prod.fst).card ≤ T.card := Finset.card_image_le
    have h₂ : (T.image Prod.snd).card ≤ T.card := Finset.card_image_le
    change W.card ≤ _ at h
    omega
  obtain ⟨A, cost, agree⟩ := support (n+m) C W ao
  let bit := fun w (z : Fin (n+m) → Bool) => (C.wires (List.ofFn z)).getD w false
  have noSingleton (t : ℕ × ℕ) (ht : t ∈ T) (k : Fin (n+m)) :
      ¬ (bit t.1 (fun i => decide (i=k)) = true ∧
        bit t.2 (fun i => decide (i=k)) = true) := by
    rintro ⟨h₁,h₂⟩
    obtain ⟨u,v,_,hu,hv⟩ := safe t ht (fun i => decide (i=k)) h₁ h₂
    have eq : Fin.castAdd m u = Fin.natAdd n v :=
      (of_decide_eq_true hu).trans (of_decide_eq_true hv).symm
    have vals : u.val = n + v.val := congrArg Fin.val eq
    have ul := u.isLt
    omega
  have included (e : Fin n × Fin m) (he : e ∈ H) :
      Fin.castAdd m e.1 ∈ A ∧ Fin.natAdd n e.2 ∈ A := by
    obtain ⟨_, t, ht, b₁, b₂⟩ := cover e he
    let p := Fin.castAdd m e.1
    let q := Fin.natAdd n e.2
    let z := fun i : Fin (n+m) => decide (i=p ∨ i=q)
    have t₁ : t.1 ∈ W := Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht)
    have t₂ : t.2 ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)
    have needed (k : Fin (n+m))
        (same : ∀ i ∈ A, z i = decide (i=k)) : False := by
      have eq₁ := agree z (fun i => decide (i=k)) same t.1 t₁
      have eq₂ := agree z (fun i => decide (i=k)) same t.2 t₂
      exact noSingleton t ht k ⟨eq₁.symm.trans b₁, eq₂.symm.trans b₂⟩
    constructor
    · by_contra absent
      apply needed q
      intro i hi
      have ne : i ≠ p := fun eq => absent (show p ∈ A from eq ▸ hi)
      simp only [z, ne, false_or]
    · by_contra absent
      apply needed p
      intro i hi
      have ne : i ≠ q := fun eq => absent (show q ∈ A from eq ▸ hi)
      simp only [z, ne, or_false]
  have contained : V ⊆ A := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h
      exact (included e he).1
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h
      exact (included e he).2
  have total : V.card ≤ C.size + 2*T.card :=
    (Finset.card_le_card contained).trans (cost.trans (Nat.add_le_add_left cardW _))
  by_cases balanced : H.card + M.card ≤ V.card
  · exact balanced.trans total
  · exact excess n m E H M C T square ao dirty safe cover subset rows columns total
      (Nat.lt_of_not_ge balanced)
