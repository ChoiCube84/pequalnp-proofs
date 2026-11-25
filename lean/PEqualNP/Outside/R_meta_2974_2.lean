import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

-- Trimming gates after a selected output preserves both kinds of evaluation.
-- The final gate can be counted assuming the bound for every earlier sound output.
set_option maxHeartbeats 2600000 in
theorem PEqualNP.Outside.R_meta_2974_2
    (trim : ∀ (n : ℕ) (C : Circuit) (w : ℕ), IsAO2 n C →
      let U : Circuit := ⟨C.gates,w⟩
      (n+C.size ≤ w → ∀ x : Fin n → Bool, circuitFun n U x = false) ∧
      ∀ k ≤ C.size, w < n+k →
        let D : Circuit := ⟨C.gates.take k,w⟩
        IsAO2 n D ∧
        (∀ x : Fin n → Bool, circuitFun n D x = circuitFun n U x) ∧
        ∀ (s : ℕ → Bool) (a b : ℕ), lineSingle D n s a b = lineSingle U n s a b)
    (core : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
    87 ≤ q → N = q^2+q+1 →
    (∀ l, Fintype.card {p // I p l}=q+1) →
    (∀ p t, p≠t → ∃! l, I p l ∧ I t l) →
    let H := fun C : Circuit => Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) = true ∧
      lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val)=false ∧
      lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val)=false)
    let Safe := fun C : Circuit => ∀ x : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
      circuitFun (N+N) C x=false
    let D := fun (C : Circuit) w => Circuit.mk (C.gates.take (w+1-(N+N))) w
    ∀ C : Circuit, IsAO2 (N+N) C → Safe C → C.output+1=N+N+C.size →
      (∀ w, N+N ≤ w → w < C.output → Safe (D C w) →
        (H (D C w)).card ≤ 24*(D C w).size) →
      (H C).card ≤ 24*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →
      (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →
      Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size := by
  intro q N I inst C large shape regular unique ao safe
  let H := fun C : Circuit => Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) = true ∧
      lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val)=false ∧
      lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val)=false)
  let Safe := fun C : Circuit => ∀ x : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
      circuitFun (N+N) C x=false
  let D := fun (C : Circuit) w => Circuit.mk (C.gates.take (w+1-(N+N))) w
  have singletonOff (B : Circuit) (valid : Safe B) (v : Fin (N+N)) :
      circuitFun (N+N) B (fun i => decide (i=v)) = false := by
    apply valid
    · rw [Fintype.card_subtype]
      apply Nat.le_trans (Finset.card_le_one.mpr ?_) (by omega)
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hb
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ha.trans hb.symm)))
    · rintro ⟨p,l,_,hp,hl⟩
      have eq := congrArg Fin.val ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at eq
      have small := p.isLt
      omega
  have cutSize (B : Circuit) (k w : ℕ) (limit : k ≤ B.size) :
      (Circuit.mk (B.gates.take k) w).size = k := by
    change (B.gates.take k).length = k
    exact List.length_take.trans (Nat.min_eq_left limit)
  have all (s : ℕ) (B : Circuit) (bs : B.size=s) (allowed : IsAO2 (N+N) B) (valid : Safe B) :
      (H B).card ≤ 24*B.size := by
    induction s using Nat.strong_induction_on generalizing B with
    | ind s smaller =>
      obtain ⟨missing, preserve⟩ := trim (N+N) B B.output allowed
      by_cases live : B.output < N+N+B.size
      · have internal : N+N ≤ B.output := by
          by_contra! primary
          let v : Fin (N+N) := ⟨B.output,primary⟩
          let one (i : Fin (N+N)) : Bool := decide (i=v)
          have off := singletonOff B valid v
          obtain ⟨_, same, _⟩ := preserve 0 (Nat.zero_le _) (by omega)
          have hit : circuitFun (N+N) ⟨B.gates.take 0, B.output⟩ one = true := by
            change (List.ofFn one).getD B.output false = true
            rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using primary)]
            simp only [List.getElem_ofFn, one, v, decide_true]
          exact Bool.noConfusion (hit.symm.trans ((same one).trans off))
        let k := B.output+1-(N+N)
        have within : k ≤ B.size := by dsimp [k]; omega
        by_cases last : k = B.size
        · apply core q N I large shape regular unique B allowed valid
          · dsimp [k] at last
            omega
          · intro w gate earlier soundD
            let m := w+1-(N+N)
            have strictly : m < B.size := by dsimp [m]; omega
            have withinD := strictly.le
            have remains : w < N+N+m := by dsimp [m]; omega
            obtain ⟨aoD, _, _⟩ := (trim (N+N) B w allowed).2 m withinD remains
            have sz : (D B w).size = m := cutSize B m w withinD
            exact smaller m (by omega) (D B w) sz aoD soundD
        · let T : Circuit := ⟨B.gates.take k, B.output⟩
          have sz := cutSize B k B.output within
          have remains : B.output < N+N+k := by dsimp [k]; omega
          obtain ⟨aoT, ev, linear⟩ := preserve k within remains
          change ∀ x : Fin (N+N) → Bool, circuitFun (N+N) T x = circuitFun (N+N) B x at ev
          change ∀ (mark : ℕ → Bool) (a b : ℕ), lineSingle T (N+N) mark a b =
            lineSingle B (N+N) mark a b at linear
          have soundT : Safe T := fun x few no => (ev x).trans (valid x few no)
          have sameH : H T = H B := by
            ext e
            simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, ev, linear]
          have small := smaller k (by omega) T sz aoT soundT
          rw [sameH] at small
          change T.size = k at sz
          omega
      · have empty : H B = ∅ := by
          ext e
          simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
          rw [missing (by omega)]
          simp only [Bool.false_eq_true, false_and, and_false]
        rw [empty, Finset.card_empty]
        exact Nat.zero_le _
  rw [Fintype.card_subtype]
  exact all C.size C rfl ao safe
