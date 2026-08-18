import AllenderOQ3.Internal.N4Structure

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# Correctness of the N4 refinement

§4 of `docs/INCIDENCE_REFINEMENT.md`.  Under a valuation of the refined circuit, the
rails of the strip of an old gate `g` carry the values of the predecessors of `g`, the
accumulator absorbs the fresh port and then one predecessor per micro-layer, and the
checkpoint node `old g` therefore carries the port-augmented value of `g`.
-/

variable {n : Nat} (c : ADRCircuit n) (F : Nat) (pred : Fin c.gateCount → List (Fin c.gateCount))

/-! ## The sources of a wire -/

theorem n4_preds_old (g : Fin c.gateCount) (w : N4Gate c.gateCount F) :
    n4Edge c F pred w (N4.old g) = true ↔
      ∃ jF k0 : Fin (F + 1), jF.val = F ∧ k0.val = 0 ∧ w = N4.node g jF k0 ∧
        (c.kind g).isComputation = true := by
  constructor
  · intro h
    obtain ⟨j, k, rfl, h1, h2, h3⟩ := n4Edge_into_old c F pred h
    exact ⟨j, k, h1, h2, rfl, h3⟩
  · rintro ⟨jF, k0, h1, h2, rfl, h3⟩
    simp only [n4Edge, decide_eq_true_eq]
    tauto

theorem n4_preds_rail_zero {g : Fin c.gateCount} {j k : Fin (F + 1)} (hj : j.val = 0)
    (hk : 1 ≤ k.val) (w : N4Gate c.gateCount F) :
    n4Edge c F pred w (N4.node g j k) = true ↔
      ∃ u : Fin c.gateCount, (pred g)[k.val - 1]? = some u ∧ w = N4.old u := by
  constructor
  · intro h
    obtain ⟨-, u, rfl, hget⟩ := n4Edge_into_node_zero c F pred hj h
    exact ⟨u, hget, rfl⟩
  · rintro ⟨u, hget, rfl⟩
    simp only [n4Edge, decide_eq_true_eq]
    tauto

theorem n4_preds_rail_succ {g : Fin c.gateCount} {j j0 k : Fin (F + 1)}
    (hj : j.val = j0.val + 1) (hk : 1 ≤ k.val) (w : N4Gate c.gateCount F) :
    n4Edge c F pred w (N4.node g j k) = true ↔
      ∃ k1 : Fin (F + 1), k1.val = k.val + 1 ∧ w = N4.node g j0 k1 ∧
        j.val + k.val - 1 < (pred g).length := by
  constructor
  · intro h
    rcases w with w | ⟨g', j', k'⟩
    · simp only [n4Edge, decide_eq_true_eq] at h
      omega
    · simp only [n4Edge, decide_eq_true_eq] at h
      obtain ⟨rfl, hjj, hcase⟩ := h
      have hj' : j' = j0 := Fin.ext (by omega)
      subst hj'
      rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2, h3⟩
      · omega
      · omega
      · exact ⟨k', h2, rfl, h3⟩
  · rintro ⟨k1, hk1, rfl, halive⟩
    simp only [n4Edge, decide_eq_true_eq]
    tauto

theorem n4_preds_acc_succ {g : Fin c.gateCount} {j j0 k : Fin (F + 1)}
    (hj : j.val = j0.val + 1) (hk : k.val = 0) (w : N4Gate c.gateCount F) :
    n4Edge c F pred w (N4.node g j k) = true ↔
      w = N4.node g j0 k ∨
        (∃ k1 : Fin (F + 1), k1.val = 1 ∧ w = N4.node g j0 k1 ∧
          j0.val < (pred g).length) := by
  constructor
  · intro h
    rcases w with w | ⟨g', j', k'⟩
    · simp only [n4Edge, decide_eq_true_eq] at h
      omega
    · simp only [n4Edge, decide_eq_true_eq] at h
      obtain ⟨rfl, hjj, hcase⟩ := h
      have hj' : j' = j0 := Fin.ext (by omega)
      subst hj'
      rcases hcase with ⟨-, h2⟩ | ⟨-, h2, h3⟩ | ⟨h1, -⟩
      · left
        have : k' = k := Fin.ext (by omega)
        rw [this]
      · exact Or.inr ⟨k', h2, rfl, h3⟩
      · omega
  · rintro (rfl | ⟨k1, hk1, rfl, hlt⟩)
    · simp only [n4Edge, decide_eq_true_eq]
      tauto
    · simp only [n4Edge, decide_eq_true_eq]
      tauto

/-! ## Reading a valuation off the labels -/

section Valuation

variable (z : Fin (n + c.gateCount) → Bool) (val : N4Gate c.gateCount F → Bool)
  (hval : SpecValuation (n4Spec c F pred) z val)

include hval

theorem n4_val_and {v : N4Gate c.gateCount F} (hkind : n4Kind c F v = .andGate) :
    (val v = true ↔ ∀ w, n4Edge c F pred w v = true → val w = true) := by
  have h := hval v
  rw [show (n4Spec c F pred).kind v = ADRGate.andGate from hkind] at h
  exact h

theorem n4_val_or {v : N4Gate c.gateCount F} (hkind : n4Kind c F v = .orGate) :
    (val v = true ↔ ∃ w, n4Edge c F pred w v = true ∧ val w = true) := by
  have h := hval v
  rw [show (n4Spec c F pred).kind v = ADRGate.orGate from hkind] at h
  exact h

theorem n4_val_lit {v : N4Gate c.gateCount F} {i : Fin (n + c.gateCount)} {b : Bool}
    (hkind : n4Kind c F v = .literal i b) :
    val v = if b then !(z i) else z i := by
  have h := hval v
  rw [show (n4Spec c F pred).kind v = ADRGate.literal i b from hkind] at h
  exact h

end Valuation

/-! ## The labels of the nodes of a strip -/

theorem n4Kind_port (g : Fin c.gateCount) {j k : Fin (F + 1)} (hj : j.val = 0)
    (hk : k.val = 0) : n4Kind c F (N4.node g j k) = .literal (Fin.natAdd n g) false := by
  simp only [n4Kind]
  rw [if_pos (show j.val = 0 ∧ k.val = 0 from ⟨hj, hk⟩)]

theorem n4Kind_rail (g : Fin c.gateCount) {j k : Fin (F + 1)} (hk : 1 ≤ k.val) :
    n4Kind c F (N4.node g j k) = .orGate := by
  simp only [n4Kind]
  rw [if_neg (by omega), if_neg (by omega)]

theorem n4Kind_acc (g : Fin c.gateCount) {j k : Fin (F + 1)} (hj : 1 ≤ j.val)
    (hk : k.val = 0) : n4Kind c F (N4.node g j k) = n4Op c g := by
  simp only [n4Kind]
  rw [if_neg (by omega), if_pos hk]

theorem n4Kind_old_comp {g : Fin c.gateCount} (hg : (c.kind g).isComputation = true) :
    n4Kind c F (N4.old g) = .orGate := by
  cases hk : c.kind g with
  | literal i b => rw [hk] at hg; exact absurd hg (by simp [ADRGate.isComputation])
  | andGate => simp only [n4Kind, hk]
  | orGate => simp only [n4Kind, hk]

theorem n4Kind_old_lit {g : Fin c.gateCount} {i : Fin n} {b : Bool} (hg : c.kind g = .literal i b) :
    n4Kind c F (N4.old g) = .literal (Fin.castAdd c.gateCount i) b := by
  simp only [n4Kind, hg]

theorem n4Op_and {g : Fin c.gateCount} (hg : c.kind g = .andGate) : n4Op c g = .andGate := by
  simp only [n4Op, hg]

theorem n4Op_or {g : Fin c.gateCount} (hg : c.kind g = .orGate) : n4Op c g = .orGate := by
  simp only [n4Op, hg]

/-! ## The values inside one strip -/

section Strip

variable {x : Fin n → Bool} {y vc : Fin c.gateCount → Bool}
  {val : N4Gate c.gateCount F → Bool} {g : Fin c.gateCount}

/-- The rails of the strip of `g` carry the values of the predecessors of `g`. -/
theorem n4_val_rail (hval : SpecValuation (n4Spec c F pred) (Fin.addCases x y) val)
    (hlen : (pred g).length ≤ F) (IH : ∀ u ∈ pred g, val (N4.old u) = vc u) :
    ∀ (jv : Nat) (j k : Fin (F + 1)) (u : Fin c.gateCount), j.val = jv → 1 ≤ k.val →
      (pred g)[jv + k.val - 1]? = some u → val (N4.node g j k) = vc u := by
  intro jv
  induction jv with
  | zero =>
      intro j k u hj hk hget
      have hget0 : (pred g)[k.val - 1]? = some u := by simpa using hget
      have hmem : u ∈ pred g := by
        obtain ⟨hlt, hval'⟩ := List.getElem?_eq_some_iff.mp hget0
        exact hval' ▸ List.getElem_mem hlt
      have hor := n4_val_or c F pred (Fin.addCases x y) val hval (n4Kind_rail c F g (j := j) hk)
      have key : val (N4.node g j k) = true ↔ val (N4.old u) = true := by
        rw [hor]
        constructor
        · rintro ⟨w, hw, hvw⟩
          rw [n4_preds_rail_zero c F pred hj hk w] at hw
          obtain ⟨u', hget', rfl⟩ := hw
          have : u' = u := Option.some.inj (hget'.symm.trans hget0)
          subst this
          exact hvw
        · intro h
          exact ⟨N4.old u, (n4_preds_rail_zero c F pred hj hk _).mpr ⟨u, hget0, rfl⟩, h⟩
      rw [Bool.eq_iff_iff, key, IH u hmem]
  | succ jv0 ih =>
      intro j k u hj hk hget
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hget
      have hjF : jv0 < F + 1 := by omega
      have hk1 : k.val + 1 < F + 1 := by omega
      have hor := n4_val_or c F pred (Fin.addCases x y) val hval (n4Kind_rail c F g (j := j) hk)
      have hj0 : (⟨jv0, hjF⟩ : Fin (F + 1)).val = jv0 := rfl
      have hidx : jv0 + (⟨k.val + 1, hk1⟩ : Fin (F + 1)).val - 1 = jv0 + 1 + k.val - 1 := by
        simp
      have hrec : val (N4.node g ⟨jv0, hjF⟩ ⟨k.val + 1, hk1⟩) = vc u := by
        refine ih ⟨jv0, hjF⟩ ⟨k.val + 1, hk1⟩ u rfl (by simp) ?_
        rw [hidx]
        exact hget
      have key : val (N4.node g j k) = true ↔
          val (N4.node g ⟨jv0, hjF⟩ ⟨k.val + 1, hk1⟩) = true := by
        rw [hor]
        constructor
        · rintro ⟨w, hw, hvw⟩
          rw [n4_preds_rail_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk w] at hw
          obtain ⟨k1, hk1', rfl, -⟩ := hw
          have : k1 = ⟨k.val + 1, hk1⟩ := Fin.ext (by simpa using hk1')
          rw [this] at hvw
          exact hvw
        · intro h
          refine ⟨N4.node g ⟨jv0, hjF⟩ ⟨k.val + 1, hk1⟩,
            (n4_preds_rail_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk _).mpr
              ⟨⟨k.val + 1, hk1⟩, rfl, rfl, ?_⟩, h⟩
          rw [hj]
          exact hlt
      rw [Bool.eq_iff_iff, key, hrec]

/-- The accumulator of the strip of an AND gate. -/
theorem n4_val_acc_and (hval : SpecValuation (n4Spec c F pred) (Fin.addCases x y) val)
    (hg : c.kind g = .andGate) (hlen : (pred g).length ≤ F)
    (IH : ∀ u ∈ pred g, val (N4.old u) = vc u) :
    ∀ (jv : Nat) (j k : Fin (F + 1)), j.val = jv → k.val = 0 →
      (val (N4.node g j k) = true ↔
        (y g = true ∧ ∀ (i : Nat) (u : Fin c.gateCount), i < jv →
          (pred g)[i]? = some u → vc u = true)) := by
  intro jv
  induction jv with
  | zero =>
      intro j k hj hk
      have hlit := n4_val_lit c F pred (Fin.addCases x y) val hval (n4Kind_port c F g hj hk)
      rw [hlit]
      simp
  | succ jv0 ih =>
      intro j k hj hk
      have hjF : jv0 < F + 1 := by omega
      have hand := n4_val_and c F pred (Fin.addCases x y) val hval
        (by rw [n4Kind_acc c F g (j := j) (k := k) (by omega) hk]; exact n4Op_and c hg)
      have hprev := ih ⟨jv0, hjF⟩ k rfl hk
      by_cases hcase : jv0 < (pred g).length
      · have hF1 : 1 < F + 1 := by omega
        obtain ⟨u0, hu0⟩ : ∃ u0, (pred g)[jv0]? = some u0 :=
          ⟨(pred g)[jv0]'hcase, List.getElem?_eq_getElem hcase⟩
        have hrail : val (N4.node g ⟨jv0, hjF⟩ ⟨1, hF1⟩) = vc u0 := by
          refine n4_val_rail c F pred hval hlen IH jv0 ⟨jv0, hjF⟩ ⟨1, hF1⟩ u0 rfl (by simp) ?_
          simpa using hu0
        have hsrc : val (N4.node g j k) = true ↔
            (val (N4.node g ⟨jv0, hjF⟩ k) = true ∧
              val (N4.node g ⟨jv0, hjF⟩ ⟨1, hF1⟩) = true) := by
          rw [hand]
          constructor
          · intro h
            refine ⟨h _ ((n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk _).mpr
              (Or.inl rfl)), h _ ((n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩)
                (by rw [hj]) hk _).mpr (Or.inr ⟨⟨1, hF1⟩, rfl, rfl, hcase⟩))⟩
          · rintro ⟨h1, h2⟩ w hw
            rw [n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk w] at hw
            rcases hw with rfl | ⟨k1, hk1, rfl, -⟩
            · exact h1
            · have : k1 = ⟨1, hF1⟩ := Fin.ext (by simpa using hk1)
              rw [this]
              exact h2
        rw [hsrc, hprev, hrail]
        constructor
        · rintro ⟨⟨hy, hall⟩, hu⟩
          refine ⟨hy, fun i u hi hgi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact hall i u hi' hgi
          · have huu : u = u0 := Option.some.inj (hgi.symm.trans hu0)
            rw [huu]
            exact hu
        · rintro ⟨hy, hall⟩
          exact ⟨⟨hy, fun i u hi hgi => hall i u (by omega) hgi⟩, hall jv0 u0 (by omega) hu0⟩
      · have hnone : (pred g)[jv0]? = none := List.getElem?_eq_none (by omega)
        have hsrc : val (N4.node g j k) = true ↔ val (N4.node g ⟨jv0, hjF⟩ k) = true := by
          rw [hand]
          constructor
          · intro h
            exact h _ ((n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk _).mpr
              (Or.inl rfl))
          · intro h1 w hw
            rw [n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk w] at hw
            rcases hw with rfl | ⟨k1, hk1, rfl, hlt'⟩
            · exact h1
            · exact absurd hlt' (by simpa using hcase)
        rw [hsrc, hprev]
        constructor
        · rintro ⟨hy, hall⟩
          refine ⟨hy, fun i u hi hgi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact hall i u hi' hgi
          · rw [hnone] at hgi
            exact absurd hgi (by simp)
        · rintro ⟨hy, hall⟩
          exact ⟨hy, fun i u hi hgi => hall i u (by omega) hgi⟩

/-- The accumulator of the strip of an OR gate. -/
theorem n4_val_acc_or (hval : SpecValuation (n4Spec c F pred) (Fin.addCases x y) val)
    (hg : c.kind g = .orGate) (hlen : (pred g).length ≤ F)
    (IH : ∀ u ∈ pred g, val (N4.old u) = vc u) :
    ∀ (jv : Nat) (j k : Fin (F + 1)), j.val = jv → k.val = 0 →
      (val (N4.node g j k) = true ↔
        (y g = true ∨ ∃ (i : Nat) (u : Fin c.gateCount), i < jv ∧
          (pred g)[i]? = some u ∧ vc u = true)) := by
  intro jv
  induction jv with
  | zero =>
      intro j k hj hk
      have hlit := n4_val_lit c F pred (Fin.addCases x y) val hval (n4Kind_port c F g hj hk)
      rw [hlit]
      simp
  | succ jv0 ih =>
      intro j k hj hk
      have hjF : jv0 < F + 1 := by omega
      have hor := n4_val_or c F pred (Fin.addCases x y) val hval
        (by rw [n4Kind_acc c F g (j := j) (k := k) (by omega) hk]; exact n4Op_or c hg)
      have hprev := ih ⟨jv0, hjF⟩ k rfl hk
      by_cases hcase : jv0 < (pred g).length
      · have hF1 : 1 < F + 1 := by omega
        obtain ⟨u0, hu0⟩ : ∃ u0, (pred g)[jv0]? = some u0 :=
          ⟨(pred g)[jv0]'hcase, List.getElem?_eq_getElem hcase⟩
        have hrail : val (N4.node g ⟨jv0, hjF⟩ ⟨1, hF1⟩) = vc u0 := by
          refine n4_val_rail c F pred hval hlen IH jv0 ⟨jv0, hjF⟩ ⟨1, hF1⟩ u0 rfl (by simp) ?_
          simpa using hu0
        have hsrc : val (N4.node g j k) = true ↔
            (val (N4.node g ⟨jv0, hjF⟩ k) = true ∨
              val (N4.node g ⟨jv0, hjF⟩ ⟨1, hF1⟩) = true) := by
          rw [hor]
          constructor
          · rintro ⟨w, hw, hvw⟩
            rw [n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk w] at hw
            rcases hw with rfl | ⟨k1, hk1, rfl, -⟩
            · exact Or.inl hvw
            · have : k1 = ⟨1, hF1⟩ := Fin.ext (by simpa using hk1)
              rw [this] at hvw
              exact Or.inr hvw
          · rintro (h1 | h2)
            · exact ⟨_, (n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk _).mpr
                (Or.inl rfl), h1⟩
            · exact ⟨_, (n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk _).mpr
                (Or.inr ⟨⟨1, hF1⟩, rfl, rfl, hcase⟩), h2⟩
        rw [hsrc, hprev, hrail]
        constructor
        · rintro ((hy | ⟨i, u, hi, hgi, hu⟩) | hu0')
          · exact Or.inl hy
          · exact Or.inr ⟨i, u, by omega, hgi, hu⟩
          · exact Or.inr ⟨jv0, u0, by omega, hu0, hu0'⟩
        · rintro (hy | ⟨i, u, hi, hgi, hu⟩)
          · exact Or.inl (Or.inl hy)
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · exact Or.inl (Or.inr ⟨i, u, hi', hgi, hu⟩)
            · have huu : u = u0 := Option.some.inj (hgi.symm.trans hu0)
              rw [huu] at hu
              exact Or.inr hu
      · have hnone : (pred g)[jv0]? = none := List.getElem?_eq_none (by omega)
        have hsrc : val (N4.node g j k) = true ↔ val (N4.node g ⟨jv0, hjF⟩ k) = true := by
          rw [hor]
          constructor
          · rintro ⟨w, hw, hvw⟩
            rw [n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk w] at hw
            rcases hw with rfl | ⟨k1, hk1, rfl, hlt'⟩
            · exact hvw
            · exact absurd hlt' (by simpa using hcase)
          · intro h1
            exact ⟨_, (n4_preds_acc_succ c F pred (j0 := ⟨jv0, hjF⟩) (by rw [hj]) hk _).mpr
              (Or.inl rfl), h1⟩
        rw [hsrc, hprev]
        constructor
        · rintro (hy | ⟨i, u, hi, hgi, hu⟩)
          · exact Or.inl hy
          · exact Or.inr ⟨i, u, by omega, hgi, hu⟩
        · rintro (hy | ⟨i, u, hi, hgi, hu⟩)
          · exact Or.inl hy
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · exact Or.inr ⟨i, u, hi', hgi, hu⟩
            · rw [hnone] at hgi
              exact absurd hgi (by simp)

end Strip


/-! ## The checkpoint values -/

section Checkpoint

variable {x : Fin n → Bool} {y vc : Fin c.gateCount → Bool}
  {val : N4Gate c.gateCount F → Bool}

/-- **§4 of `docs/INCIDENCE_REFINEMENT.md`.**  Every checkpoint node of the refined
circuit carries the port-augmented value of the corresponding old gate. -/
theorem n4_val_old (hval : SpecValuation (n4Spec c F pred) (Fin.addCases x y) val)
    (hvc : PortAugmentedADRValuation c x y vc)
    (hpred : ∀ g u, u ∈ pred g ↔ c.edge u g = true)
    (hlen : ∀ g, (pred g).length ≤ F)
    (hlay : ∀ g u, u ∈ pred g → c.layer u + 1 = c.layer g) :
    ∀ g, val (N4.old g) = vc g := by
  have hFlt : F < F + 1 := by omega
  have h0 : (0 : Nat) < F + 1 := by omega
  have main : ∀ (L : Nat) (g : Fin c.gateCount), c.layer g = L → val (N4.old g) = vc g := by
    intro L
    induction L using Nat.strong_induction_on with
    | _ L IHL =>
      intro g hgL
      have IH : ∀ u ∈ pred g, val (N4.old u) = vc u := by
        intro u hu
        have hlt := hlay g u hu
        exact IHL (c.layer u) (by omega) u rfl
      cases hk : c.kind g with
      | literal i b =>
          have hvcg : vc g = if b then !(x i) else x i := by
            have h := hvc g; rw [hk] at h; exact h
          have hlit := n4_val_lit c F pred (Fin.addCases x y) val hval (n4Kind_old_lit c F hk)
          rw [hlit, hvcg]
          simp
      | andGate =>
          have hvcg : (vc g = true ↔
              (∀ h, c.edge h g = true → vc h = true) ∧ y g = true) := by
            have h := hvc g; rw [hk] at h; exact h
          have hcomp : (c.kind g).isComputation = true := by rw [hk]; rfl
          have hor := n4_val_or c F pred (Fin.addCases x y) val hval (n4Kind_old_comp c F hcomp)
          have hsrc : val (N4.old g) = true ↔
              val (N4.node g ⟨F, hFlt⟩ ⟨0, h0⟩) = true := by
            rw [hor]
            constructor
            · rintro ⟨w, hw, hvw⟩
              rw [n4_preds_old c F pred g w] at hw
              obtain ⟨jF, k0, hjF, hk0, rfl, -⟩ := hw
              have e1 : jF = ⟨F, hFlt⟩ := Fin.ext (by simpa using hjF)
              have e2 : k0 = ⟨0, h0⟩ := Fin.ext (by simpa using hk0)
              rw [e1, e2] at hvw
              exact hvw
            · intro h
              exact ⟨_, (n4_preds_old c F pred g _).mpr
                ⟨⟨F, hFlt⟩, ⟨0, h0⟩, rfl, rfl, rfl, hcomp⟩, h⟩
          have hacc := n4_val_acc_and c F pred hval hk (hlen g) IH F ⟨F, hFlt⟩ ⟨0, h0⟩ rfl rfl
          rw [Bool.eq_iff_iff, hsrc, hacc, hvcg]
          constructor
          · rintro ⟨hy, hall⟩
            refine ⟨fun h hh => ?_, hy⟩
            obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp ((hpred g h).mpr hh)
            have := hlen g
            exact hall i h (by omega) (by rw [List.getElem?_eq_getElem hi, hgi])
          · rintro ⟨hall, hy⟩
            refine ⟨hy, fun i u hi hgi => ?_⟩
            obtain ⟨hlt', hval'⟩ := List.getElem?_eq_some_iff.mp hgi
            exact hall u ((hpred g u).mp (hval' ▸ List.getElem_mem hlt'))
      | orGate =>
          have hvcg : (vc g = true ↔
              (∃ h, c.edge h g = true ∧ vc h = true) ∨ y g = true) := by
            have h := hvc g; rw [hk] at h; exact h
          have hcomp : (c.kind g).isComputation = true := by rw [hk]; rfl
          have hor := n4_val_or c F pred (Fin.addCases x y) val hval (n4Kind_old_comp c F hcomp)
          have hsrc : val (N4.old g) = true ↔
              val (N4.node g ⟨F, hFlt⟩ ⟨0, h0⟩) = true := by
            rw [hor]
            constructor
            · rintro ⟨w, hw, hvw⟩
              rw [n4_preds_old c F pred g w] at hw
              obtain ⟨jF, k0, hjF, hk0, rfl, -⟩ := hw
              have e1 : jF = ⟨F, hFlt⟩ := Fin.ext (by simpa using hjF)
              have e2 : k0 = ⟨0, h0⟩ := Fin.ext (by simpa using hk0)
              rw [e1, e2] at hvw
              exact hvw
            · intro h
              exact ⟨_, (n4_preds_old c F pred g _).mpr
                ⟨⟨F, hFlt⟩, ⟨0, h0⟩, rfl, rfl, rfl, hcomp⟩, h⟩
          have hacc := n4_val_acc_or c F pred hval hk (hlen g) IH F ⟨F, hFlt⟩ ⟨0, h0⟩ rfl rfl
          rw [Bool.eq_iff_iff, hsrc, hacc, hvcg]
          constructor
          · rintro (hy | ⟨i, u, hi, hgi, hu⟩)
            · exact Or.inr hy
            · obtain ⟨hlt', hval'⟩ := List.getElem?_eq_some_iff.mp hgi
              exact Or.inl ⟨u, (hpred g u).mp (hval' ▸ List.getElem_mem hlt'), hu⟩
          · rintro (⟨h, hh, hvh⟩ | hy)
            · obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp ((hpred g h).mpr hh)
              have := hlen g
              exact Or.inr ⟨i, h, by omega, by rw [List.getElem?_eq_getElem hi, hgi], hvh⟩
            · exact Or.inl hy
  exact fun g => main (c.layer g) g rfl

end Checkpoint


end AllenderOQ3.Internal
