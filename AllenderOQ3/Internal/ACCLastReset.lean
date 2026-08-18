import AllenderOQ3.Internal.ACCJoin
import AllenderOQ3.Internal.ACCNot
import AllenderOQ3.Internal.ACCGadgets

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n m : Nat}

def lastMarkedValue {len : Nat} {V : Type} [LinearOrder (Fin len)]
    (mark : Fin len → (Fin n → Bool) → Bool)
    (val : Fin len → (Fin n → Bool) → V)
    (v0 : V) (x : Fin n → Bool) : V :=
  match (Finset.univ.filter (fun p : Fin len => mark p x = true)).max with
  | some p => val p x
  | none => v0

def lastMarkedKK (len : Nat) (i : Fin (len + 1)) : Nat :=
  if i.val = 0 then len else len - i.val + 2

noncomputable def lastMarkedG {n m len d size : Nat} {V : Type} [Fintype V] [DecidableEq V]
    (mark : Fin len → (Fin n → Bool) → Bool)
    (val : Fin len → (Fin n → Bool) → V)
    (v0 : V)
    (recMark : ∀ i, ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ mark i x = true)
    (recVal : ∀ i (v : V), ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ val i x = v)
    (i : Fin (len + 1)) (j : Fin (lastMarkedKK len i)) : ACCCircuit n m :=
  if hi : i.val = 0 then
    have hq : j.val < len := by
      have hj := j.isLt
      change j.val < if i.val = 0 then len else len - i.val + 2 at hj
      rw [if_pos hi] at hj
      exact hj
    accNot (Classical.choose (recMark ⟨j.val, hq⟩)) d
  else
    have hp : i.val - 1 < len := by
      have h1 : i.val > 0 := Nat.pos_of_ne_zero hi
      have h2 := i.isLt
      omega
    let p : Fin len := ⟨i.val - 1, hp⟩
    if hj0 : j.val = 0 then
      Classical.choose (recMark p)
    else if hj1 : j.val = 1 then
      Classical.choose (recVal p v0)
    else
      have hq : i.val - 1 + j.val - 1 < len := by
        have hj := j.isLt
        change j.val < if i.val = 0 then len else len - i.val + 2 at hj
        rw [if_neg hi] at hj
        omega
      let q : Fin len := ⟨i.val - 1 + j.val - 1, hq⟩
      accNot (Classical.choose (recMark q)) d

/-! ## Branch equations for `lastMarkedG` -/

section Branches

variable {len d size : Nat} {V : Type} [Fintype V] [DecidableEq V]
    (mark : Fin len → (Fin n → Bool) → Bool)
    (val : Fin len → (Fin n → Bool) → V)
    (v0 : V)
    (recMark : ∀ i, ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧
      a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ mark i x = true)
    (recVal : ∀ i (v : V), ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧
      a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ val i x = v)

/-- On the `i = 0` branch the gadget tests that position `j` is unmarked. -/
theorem lastMarkedG_eq_zero (i : Fin (len + 1)) (hi : i.val = 0)
    (j : Fin (lastMarkedKK len i)) (hq : j.val < len) :
    lastMarkedG mark val v0 recMark recVal i j
      = accNot (Classical.choose (recMark ⟨j.val, hq⟩)) d := by
  simp only [lastMarkedG, dif_pos hi]

/-- The `j = 0` conjunct of the branch `i ≥ 1` tests that position `i - 1` is marked. -/
theorem lastMarkedG_eq_mark (i : Fin (len + 1)) (hi : ¬ i.val = 0)
    (j : Fin (lastMarkedKK len i)) (hj0 : j.val = 0) (hp : i.val - 1 < len) :
    lastMarkedG mark val v0 recMark recVal i j
      = Classical.choose (recMark ⟨i.val - 1, hp⟩) := by
  simp only [lastMarkedG, dif_neg hi, dif_pos hj0]

/-- The `j = 1` conjunct of the branch `i ≥ 1` tests that position `i - 1` carries `v0`. -/
theorem lastMarkedG_eq_val (i : Fin (len + 1)) (hi : ¬ i.val = 0)
    (j : Fin (lastMarkedKK len i)) (hj0 : ¬ j.val = 0) (hj1 : j.val = 1) (hp : i.val - 1 < len) :
    lastMarkedG mark val v0 recMark recVal i j
      = Classical.choose (recVal ⟨i.val - 1, hp⟩ v0) := by
  simp only [lastMarkedG, dif_neg hi, dif_neg hj0, dif_pos hj1]

/-- The conjuncts `j ≥ 2` of the branch `i ≥ 1` test that the later positions are unmarked. -/
theorem lastMarkedG_eq_after (i : Fin (len + 1)) (hi : ¬ i.val = 0)
    (j : Fin (lastMarkedKK len i)) (hj0 : ¬ j.val = 0) (hj1 : ¬ j.val = 1)
    (hq : i.val - 1 + j.val - 1 < len) :
    lastMarkedG mark val v0 recMark recVal i j
      = accNot (Classical.choose (recMark ⟨i.val - 1 + j.val - 1, hq⟩)) d := by
  simp only [lastMarkedG, dif_neg hi, dif_neg hj0, dif_neg hj1]

end Branches

/-- Each conjunction of the gadget has at most `len + 1` conjuncts. -/
theorem lastMarkedKK_le {len : Nat} (i : Fin (len + 1)) : lastMarkedKK len i ≤ len + 1 := by
  simp only [lastMarkedKK]
  split
  · omega
  · have := i.isLt
    omega

theorem wellFormedACC_lastMarkedG {n m len d size : Nat} {V : Type} [Fintype V] [DecidableEq V]
    (mark : Fin len → (Fin n → Bool) → Bool)
    (val : Fin len → (Fin n → Bool) → V)
    (v0 : V)
    (recMark : ∀ i, ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ mark i x = true)
    (recVal : ∀ i (v : V), ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ val i x = v)
    (i : Fin (len + 1)) (j : Fin (lastMarkedKK len i)) :
    WellFormedACC (lastMarkedG mark val v0 recMark recVal i j) := by
  unfold lastMarkedG
  split
  · exact wellFormedACC_accNot (Classical.choose_spec (recMark _)).1
      (Classical.choose_spec (recMark _)).2.1
  · split
    · exact (Classical.choose_spec (recMark _)).1
    · split
      · exact (Classical.choose_spec (recVal _ _)).1
      · exact wellFormedACC_accNot (Classical.choose_spec (recMark _)).1
          (Classical.choose_spec (recMark _)).2.1

theorem lastMarkedG_layer_le {n m len d size : Nat} {V : Type} [Fintype V] [DecidableEq V]
    (mark : Fin len → (Fin n → Bool) → Bool)
    (val : Fin len → (Fin n → Bool) → V)
    (v0 : V)
    (recMark : ∀ i, ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ mark i x = true)
    (recVal : ∀ i (v : V), ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ val i x = v)
    (i : Fin (len + 1)) (j : Fin (lastMarkedKK len i)) :
    ∀ q, (lastMarkedG mark val v0 recMark recVal i j).layer q ≤ d + 1 := by
  by_cases hi : i.val = 0
  · have hq : j.val < len := by
      have hjj := j.isLt
      simp only [lastMarkedKK, if_pos hi] at hjj
      exact hjj
    rw [lastMarkedG_eq_zero mark val v0 recMark recVal i hi j hq]
    exact accNot_layer_le (Classical.choose_spec (recMark _)).2.1
  · have hp : i.val - 1 < len := by
      have := i.isLt
      omega
    by_cases hj0 : j.val = 0
    · rw [lastMarkedG_eq_mark mark val v0 recMark recVal i hi j hj0 hp]
      exact fun q => le_trans ((Classical.choose_spec (recMark _)).2.1 q) (Nat.le_succ d)
    · by_cases hj1 : j.val = 1
      · rw [lastMarkedG_eq_val mark val v0 recMark recVal i hi j hj0 hj1 hp]
        exact fun q => le_trans ((Classical.choose_spec (recVal _ _)).2.1 q) (Nat.le_succ d)
      · have hjlt := j.isLt
        simp only [lastMarkedKK, if_neg hi] at hjlt
        have hq : i.val - 1 + j.val - 1 < len := by omega
        rw [lastMarkedG_eq_after mark val v0 recMark recVal i hi j hj0 hj1 hq]
        exact accNot_layer_le (Classical.choose_spec (recMark _)).2.1

theorem lastMarkedG_gateCount_le {n m len d size : Nat} {V : Type} [Fintype V] [DecidableEq V]
    (mark : Fin len → (Fin n → Bool) → Bool)
    (val : Fin len → (Fin n → Bool) → V)
    (v0 : V)
    (recMark : ∀ i, ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ mark i x = true)
    (recVal : ∀ i (v : V), ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ val i x = v)
    (i : Fin (len + 1)) (j : Fin (lastMarkedKK len i)) :
    (lastMarkedG mark val v0 recMark recVal i j).gateCount ≤ size + 1 := by
  by_cases hi : i.val = 0
  · have hq : j.val < len := by
      have hjj := j.isLt
      simp only [lastMarkedKK, if_pos hi] at hjj
      exact hjj
    rw [lastMarkedG_eq_zero mark val v0 recMark recVal i hi j hq, accNot_gateCount]
    exact Nat.succ_le_succ (Classical.choose_spec (recMark _)).2.2.1
  · have hp : i.val - 1 < len := by
      have := i.isLt
      omega
    by_cases hj0 : j.val = 0
    · rw [lastMarkedG_eq_mark mark val v0 recMark recVal i hi j hj0 hp]
      exact le_trans (Classical.choose_spec (recMark _)).2.2.1 (Nat.le_succ size)
    · by_cases hj1 : j.val = 1
      · rw [lastMarkedG_eq_val mark val v0 recMark recVal i hi j hj0 hj1 hp]
        exact le_trans (Classical.choose_spec (recVal _ _)).2.2.1 (Nat.le_succ size)
      · have hjlt := j.isLt
        simp only [lastMarkedKK, if_neg hi] at hjlt
        have hq : i.val - 1 + j.val - 1 < len := by omega
        rw [lastMarkedG_eq_after mark val v0 recMark recVal i hi j hj0 hj1 hq, accNot_gateCount]
        exact Nat.succ_le_succ (Classical.choose_spec (recMark _)).2.2.1

theorem accAccepts_lastMarkedG {n m len d size : Nat} {V : Type} [Fintype V] [DecidableEq V]
    (mark : Fin len → (Fin n → Bool) → Bool)
    (val : Fin len → (Fin n → Bool) → V)
    (v0 : V)
    (recMark : ∀ i, ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ mark i x = true)
    (recVal : ∀ i (v : V), ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ val i x = v)
    (x : Fin n → Bool) :
    (∃ i, ∀ j, ACCAccepts (lastMarkedG mark val v0 recMark recVal i j) x) ↔
    lastMarkedValue mark val v0 x = v0 := by
  classical
  set F : Finset (Fin len) := Finset.univ.filter (fun p : Fin len => mark p x = true) with hF
  have hmemF : ∀ p : Fin len, p ∈ F ↔ mark p x = true := by
    intro p; simp [hF]
  have hMark : ∀ p : Fin len, (ACCAccepts (Classical.choose (recMark p)) x ↔ mark p x = true) :=
    fun p => (Classical.choose_spec (recMark p)).2.2.2 x
  have hVal : ∀ (p : Fin len) (v : V),
      (ACCAccepts (Classical.choose (recVal p v)) x ↔ val p x = v) :=
    fun p v => (Classical.choose_spec (recVal p v)).2.2.2 x
  have hNot : ∀ p : Fin len,
      (ACCAccepts (accNot (Classical.choose (recMark p)) d) x ↔ ¬ (mark p x = true)) := by
    intro p
    rw [accAccepts_accNot (Classical.choose_spec (recMark p)).1
      (Classical.choose_spec (recMark p)).2.1]
    exact not_congr (hMark p)
  have hLMV : lastMarkedValue mark val v0 x
      = match F.max with | some p => val p x | none => v0 := rfl
  constructor
  · rintro ⟨i, hj⟩
    by_cases hi : i.val = 0
    · have hempty : F = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        have hq : p.val < len := p.isLt
        have hjj : p.val < lastMarkedKK len i := by
          simp only [lastMarkedKK, if_pos hi]; exact hq
        have hacc := hj ⟨p.val, hjj⟩
        rw [lastMarkedG_eq_zero mark val v0 recMark recVal i hi ⟨p.val, hjj⟩ hq] at hacc
        exact (hNot _).mp hacc ((hmemF p).mp hp)
      rw [hLMV, hempty]
      rfl
    · have hp : i.val - 1 < len := by
        have := i.isLt
        omega
      set p : Fin len := ⟨i.val - 1, hp⟩ with hpdef
      have hpv : p.val = i.val - 1 := rfl
      have hkk2 : 2 ≤ lastMarkedKK len i := by
        simp only [lastMarkedKK, if_neg hi]; omega
      have hmarkp : mark p x = true := by
        have h0 : (0 : Nat) < lastMarkedKK len i := by omega
        have hacc := hj ⟨0, h0⟩
        rw [lastMarkedG_eq_mark mark val v0 recMark recVal i hi ⟨0, h0⟩ rfl hp] at hacc
        exact (hMark _).mp hacc
      have hvalp : val p x = v0 := by
        have h1 : (1 : Nat) < lastMarkedKK len i := by omega
        have hacc := hj ⟨1, h1⟩
        rw [lastMarkedG_eq_val mark val v0 recMark recVal i hi ⟨1, h1⟩ (by simp) rfl hp] at hacc
        exact (hVal _ _).mp hacc
      have hmax : F.max = (p : WithBot (Fin len)) := by
        have hpin : p ∈ F := (hmemF p).mpr hmarkp
        have hle : ∀ q ∈ F, q ≤ p := by
          intro q hq
          by_contra hlt
          have hlt' : p.val < q.val := by
            rw [Fin.le_def] at hlt; omega
          have hqlt := q.isLt
          have hjv : q.val - p.val + 1 < lastMarkedKK len i := by
            simp only [lastMarkedKK, if_neg hi]
            omega
          have hq2 : i.val - 1 + (q.val - p.val + 1) - 1 < len := by omega
          have hacc := hj ⟨q.val - p.val + 1, hjv⟩
          rw [lastMarkedG_eq_after mark val v0 recMark recVal i hi ⟨q.val - p.val + 1, hjv⟩
            (by simp) (by simp; omega) hq2] at hacc
          have heq : (⟨i.val - 1 + (q.val - p.val + 1) - 1, hq2⟩ : Fin len) = q := by
            apply Fin.ext
            simp only
            omega
          rw [heq] at hacc
          exact (hNot q).mp hacc ((hmemF q).mp hq)
        refine le_antisymm (Finset.max_le ?_) (Finset.le_max hpin)
        intro q hq
        exact WithBot.coe_le_coe.mpr (hle q hq)
      rw [hLMV, hmax]
      exact hvalp
  · intro hvalue
    by_cases hFe : F = ∅
    · refine ⟨⟨0, Nat.succ_pos len⟩, ?_⟩
      intro j
      have hq : j.val < len := by
        have hjj := j.isLt
        simp only [lastMarkedKK] at hjj
        exact hjj
      rw [lastMarkedG_eq_zero mark val v0 recMark recVal ⟨0, Nat.succ_pos len⟩ rfl j hq]
      refine (hNot _).mpr ?_
      intro hmk
      have hin : (⟨j.val, hq⟩ : Fin len) ∈ F := (hmemF _).mpr hmk
      rw [hFe] at hin
      exact absurd hin (Finset.notMem_empty _)
    · obtain ⟨p, hmax⟩ := Finset.max_of_nonempty (Finset.nonempty_of_ne_empty hFe)
      have hvalp : val p x = v0 := by rw [hLMV, hmax] at hvalue; exact hvalue
      have hpin : p ∈ F := Finset.mem_of_max hmax
      have hpl : p.val < len := p.isLt
      have hlt : p.val + 1 < len + 1 := by omega
      obtain ⟨i, hiv⟩ : ∃ i : Fin (len + 1), i.val = p.val + 1 := ⟨⟨p.val + 1, hlt⟩, rfl⟩
      refine ⟨i, ?_⟩
      intro j
      have hi : ¬ i.val = 0 := by omega
      have hp : i.val - 1 < len := by omega
      have hpe : (⟨i.val - 1, hp⟩ : Fin len) = p := by apply Fin.ext; simp only; omega
      by_cases hj0 : j.val = 0
      · rw [lastMarkedG_eq_mark mark val v0 recMark recVal i hi j hj0 hp, hpe]
        exact (hMark p).mpr ((hmemF p).mp hpin)
      · by_cases hj1 : j.val = 1
        · rw [lastMarkedG_eq_val mark val v0 recMark recVal i hi j hj0 hj1 hp, hpe]
          exact (hVal p v0).mpr hvalp
        · have hjlt := j.isLt
          simp only [lastMarkedKK, if_neg hi] at hjlt
          have hq : i.val - 1 + j.val - 1 < len := by omega
          rw [lastMarkedG_eq_after mark val v0 recMark recVal i hi j hj0 hj1 hq]
          refine (hNot _).mpr ?_
          intro hmk
          have hin : (⟨i.val - 1 + j.val - 1, hq⟩ : Fin len) ∈ F := (hmemF _).mpr hmk
          have hle : (⟨i.val - 1 + j.val - 1, hq⟩ : Fin len) ≤ p :=
            Finset.le_max_of_eq hin hmax
          rw [Fin.le_def] at hle
          simp only at hle
          omega

theorem exists_acc_lastMarked {n m len d size : Nat} (hm : 0 < m) {V : Type} [Fintype V] [DecidableEq V]
    (mark : Fin len → (Fin n → Bool) → Bool)
    (val : Fin len → (Fin n → Bool) → V)
    (recMark : ∀ i, ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ mark i x = true)
    (recVal : ∀ i (v : V), ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧ ∀ x, ACCAccepts a x ↔ val i x = v)
    (v0 : V) :
    ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ q, a.layer q ≤ d + 4) ∧
      a.gateCount ≤ (len + 1) * (len + 1) * (size + 1) * (Fintype.card V + 1) + 1 ∧
      (∀ x, ACCAccepts a x ↔ lastMarkedValue mark val v0 x = v0) := by
  refine ⟨accOrAnd (lastMarkedG mark val v0 recMark recVal) (d + 1), ?_, ?_, ?_, ?_⟩
  · exact wellFormedACC_accOrAnd (wellFormedACC_lastMarkedG _ _ _ _ _) (lastMarkedG_layer_le _ _ _ _ _)
  · intro q
    have h := accOrAnd_layer_le (lastMarkedG_layer_le mark val v0 recMark recVal) q
    omega
  · rw [accOrAnd_gateCount]
    have hinner : ∀ i : Fin (len + 1),
        (∑ j, (lastMarkedG mark val v0 recMark recVal i j).gateCount) + 1
          ≤ (len + 1) * (size + 1) + 1 := by
      intro i
      have h1 : (∑ j, (lastMarkedG mark val v0 recMark recVal i j).gateCount)
          ≤ ∑ _j : Fin (lastMarkedKK len i), (size + 1) :=
        Finset.sum_le_sum fun j _ => lastMarkedG_gateCount_le mark val v0 recMark recVal i j
      have h2 : (∑ _j : Fin (lastMarkedKK len i), (size + 1)) = lastMarkedKK len i * (size + 1) := by
        simp [Finset.sum_const, Finset.card_univ, mul_comm]
      have h3 : lastMarkedKK len i * (size + 1) ≤ (len + 1) * (size + 1) :=
        Nat.mul_le_mul_right _ (lastMarkedKK_le i)
      omega
    have houter : (∑ i : Fin (len + 1),
        ((∑ j, (lastMarkedG mark val v0 recMark recVal i j).gateCount) + 1))
          ≤ (len + 1) * ((len + 1) * (size + 1) + 1) := by
      have h1 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (len + 1)))) =>
        hinner i)
      have h2 : (∑ _i : Fin (len + 1), ((len + 1) * (size + 1) + 1))
          = (len + 1) * ((len + 1) * (size + 1) + 1) := by
        simp [Finset.sum_const, Finset.card_univ]
      omega
    have hV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v0⟩
    have hAA : len + 1 ≤ (len + 1) * (len + 1) * (size + 1) := by nlinarith
    have hC : (len + 1) * (len + 1) * (size + 1) * 2
        ≤ (len + 1) * (len + 1) * (size + 1) * (Fintype.card V + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : (len + 1) * ((len + 1) * (size + 1) + 1)
        = (len + 1) * (len + 1) * (size + 1) + (len + 1) := by ring
    omega
  · intro x
    rw [accAccepts_accOrAnd (wellFormedACC_lastMarkedG _ _ _ _ _) (lastMarkedG_layer_le _ _ _ _ _)]
    exact accAccepts_lastMarkedG mark val v0 recMark recVal x

end AllenderOQ3.Internal
