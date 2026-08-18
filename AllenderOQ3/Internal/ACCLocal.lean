import AllenderOQ3.Internal.StateChain
import AllenderOQ3.Internal.ACCSemantics

set_option autoImplicit false

/-!
# The one-step relation as a small constant-depth `ACC[2]` circuit (§B0e)

For a *fixed* pair of states `s t : State w` and a fixed layer `ell`, the local
relation

```
(∀ g computation, layer g = ell → (t (slot g) = true ↔ GateStepValue idx x s g)) ∧
(∀ j unused slot, t j = false)
```

is a predicate of the input `x` only.  This file shows that it is computed by an
`ACC[2]` circuit of depth at most `3` and of size linear in `c.gateCount`.

The construction is a depth-3 circuit:

* layer `0`: for every gate `h` of `c` that is a literal, two literal gates, one
  of each polarity (the *positive* and *negative* blocks); gates of `c` that are
  not literals get an unused dummy gate on layer `1`;
* layer `2`: one gate per gate `g` of `c`, computing the local requirement on `g`;
* layer `3`: the top `AND`.

Because the literal gates are shared between all the requirements, the size is
`3 * c.gateCount + 1`, which is linear as required.
-/

namespace AllenderOQ3.Internal

variable {n w : Nat} {c : ADRCircuit n}

/-! ## Constant ACC circuits

A single fan-in-zero gate is already a constant: an `andGate` with no inputs is
vacuously true, an `orGate` with no inputs is vacuously false.  Placing it on
layer `1` keeps the circuit well formed even when there are no inputs at all
(`n = 0`), where no literal gate exists. -/

/-- The constant ACC circuit with value `b`: one fan-in-zero gate at layer `1`. -/
def accConst (n m : Nat) (b : Bool) : ACCCircuit n m where
  gateCount := 1
  output := ⟨0, Nat.one_pos⟩
  kind := fun _ => if b then ACCGate.andGate else ACCGate.orGate
  layer := fun _ => 1
  edge := fun _ _ => false

theorem wellFormedACC_accConst (n m : Nat) (b : Bool) : WellFormedACC (accConst n m b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v h; simp [accConst] at h
  · intro g
    constructor
    · intro h; simp [accConst] at h
    · rintro ⟨i, bb, h⟩
      simp only [accConst] at h
      cases b <;> simp at h
  · intro g h
    simp only [accConst] at h
    cases b <;> simp at h

theorem accConst_layer (n m : Nat) (b : Bool) (g : Fin (accConst n m b).gateCount) :
    (accConst n m b).layer g = 1 := rfl

theorem accConst_gateCount (n m : Nat) (b : Bool) : (accConst n m b).gateCount = 1 := rfl

/-- The constant circuit accepts exactly when its Boolean parameter is `true`. -/
theorem accAccepts_accConst (n m : Nat) (b : Bool) (x : Fin n → Bool) :
    ACCAccepts (accConst n m b) x ↔ b = true := by
  constructor
  · rintro ⟨value, hval, hout⟩
    by_contra hb
    simp only [Bool.not_eq_true] at hb
    subst hb
    have hv : value (accConst n m false).output = true ↔
        ∃ h, (accConst n m false).edge h (accConst n m false).output = true ∧ value h = true :=
      hval (accConst n m false).output
    obtain ⟨h, he, -⟩ := hv.mp hout
    exact Bool.false_ne_true he
  · intro hb
    subst hb
    refine ⟨fun _ => true, ?_, rfl⟩
    intro g
    change (true = true ↔ ∀ h, (accConst n m true).edge h g = true → true = true)
    simp

/-! ## The local relation -/

/-- The local relation at layer `ell` between the fixed states `s` and `t`.
`OneStep idx x i s t` is `LocalRel idx (i+1) s t x` and `InitState idx x t` is
`LocalRel idx 0 (fun _ => false) t x`. -/
def LocalRel (idx : LayerIndexing c w) (ell : Nat) (s t : State w)
    (x : Fin n → Bool) : Prop :=
  (∀ g, (c.kind g).isComputation = true → c.layer g = ell →
      (t (idx.slot g) = true ↔ GateStepValue idx x s g)) ∧
  (∀ j : Fin w,
    (¬ ∃ g, (c.kind g).isComputation = true ∧ c.layer g = ell ∧ idx.slot g = j) →
      t j = false)

theorem oneStep_eq_localRel (idx : LayerIndexing c w) (x : Fin n → Bool) (i : Nat)
    (s t : State w) : OneStep idx x i s t ↔ LocalRel idx (i + 1) s t x := Iff.rfl

theorem initState_eq_localRel (idx : LayerIndexing c w) (x : Fin n → Bool)
    (t : State w) : InitState idx x t ↔ LocalRel idx 0 (fun _ => false) t x := Iff.rfl

/-! ## Boolean data of the construction -/

section Data

variable (idx : LayerIndexing c w) (s t : State w)

/-- The polarity required of gate `g`: the value the fixed target state assigns
to its slot. -/
def polB (g : Fin c.gateCount) : Bool := t (idx.slot g)

/-- Whether a gate of `c` is a literal. -/
def isLitB (g : Fin c.gateCount) : Bool := !(c.kind g).isComputation

/-- The requirement on `g` is a conjunction exactly when the required polarity
agrees with the gate being an `AND`. -/
def andTypeB (g : Fin c.gateCount) : Bool :=
  polB idx t g == decide (c.kind g = ADRGate.andGate)

/-- The (constant) contribution of a computation predecessor `h` of `g`. -/
def constTermB (g h : Fin c.gateCount) : Bool := s (idx.slot h) == polB idx t g

/-- All computation predecessors contribute `true`. -/
def cAndB (g : Fin c.gateCount) : Bool :=
  decide (∀ h, c.edge h g = true → isLitB h = false → constTermB idx s t g h = true)

/-- Some computation predecessor contributes `true`. -/
def cOrB (g : Fin c.gateCount) : Bool :=
  decide (∃ h, c.edge h g = true ∧ isLitB h = false ∧ constTermB idx s t g h = true)

/-- Whether the gate of the middle layer for `g` keeps its inputs (otherwise the
requirement is already decided by the constant contributions). -/
def keepB (g : Fin c.gateCount) : Bool :=
  if andTypeB idx t g = true then cAndB idx s t g else !cOrB idx s t g

/-- Whether the gate of the middle layer for `g` is an `AND`. -/
def isAndKindB (g : Fin c.gateCount) : Bool :=
  if andTypeB idx t g = true then cAndB idx s t g else cOrB idx s t g

/-- The gates whose requirement is imposed: the computation gates of layer `ell`. -/
def inGB (ell : Nat) (g : Fin c.gateCount) : Bool :=
  (c.kind g).isComputation && decide (c.layer g = ell)

/-- The contribution of a predecessor `h` to the requirement on `g`: it is `true`
exactly when the value of `h` matches the polarity required of `g`. -/
def termVal (x : Fin n → Bool) (g h : Fin c.gateCount) : Bool :=
  match c.kind h with
  | .literal j bb => if bb == polB idx t g then !(x j) else x j
  | .andGate => constTermB idx s t g h
  | .orGate => constTermB idx s t g h

/-- The requirement imposed on gate `g`. -/
def pgB (x : Fin n → Bool) (g : Fin c.gateCount) : Bool :=
  if andTypeB idx t g = true then
    decide (∀ h, c.edge h g = true → termVal idx s t x g h = true)
  else decide (∃ h, c.edge h g = true ∧ termVal idx s t x g h = true)

end Data

/-! ## The requirement is the local condition -/

theorem termVal_eq_true_iff (idx : LayerIndexing c w) (s t : State w)
    (x : Fin n → Bool) (g h : Fin c.gateCount) :
    termVal idx s t x g h = true ↔ predValue idx x s h = polB idx t g := by
  unfold termVal predValue constTermB
  cases hk : c.kind h with
  | literal j bb =>
      cases bb <;> cases hp : polB idx t g <;> cases hx : x j <;> simp
  | andGate => cases hs : s (idx.slot h) <;> cases hp : polB idx t g <;> simp
  | orGate => cases hs : s (idx.slot h) <;> cases hp : polB idx t g <;> simp

theorem pgB_of_andType (idx : LayerIndexing c w) (s t : State w)
    (x : Fin n → Bool) (g : Fin c.gateCount) (hA : andTypeB idx t g = true) :
    pgB idx s t x g = true ↔
      ∀ h, c.edge h g = true → predValue idx x s h = polB idx t g := by
  unfold pgB
  rw [if_pos hA]
  simp only [decide_eq_true_eq]
  exact forall_congr' fun h =>
    imp_congr_right fun _ => termVal_eq_true_iff idx s t x g h

theorem pgB_of_not_andType (idx : LayerIndexing c w) (s t : State w)
    (x : Fin n → Bool) (g : Fin c.gateCount) (hA : ¬ andTypeB idx t g = true) :
    pgB idx s t x g = true ↔
      ∃ h, c.edge h g = true ∧ predValue idx x s h = polB idx t g := by
  unfold pgB
  rw [if_neg hA]
  simp only [decide_eq_true_eq]
  exact exists_congr fun h =>
    and_congr_right fun _ => termVal_eq_true_iff idx s t x g h

theorem pgB_eq_true_iff (idx : LayerIndexing c w) (s t : State w)
    (x : Fin n → Bool) (g : Fin c.gateCount)
    (hcomp : (c.kind g).isComputation = true) :
    pgB idx s t x g = true ↔ (t (idx.slot g) = true ↔ GateStepValue idx x s g) := by
  have hpol : polB idx t g = t (idx.slot g) := rfl
  cases hk : c.kind g with
  | literal j b => rw [hk] at hcomp; simp [ADRGate.isComputation] at hcomp
  | andGate =>
      have hGSV : GateStepValue idx x s g =
          (∀ h, c.edge h g = true → predValue idx x s h = true) := by
        unfold GateStepValue; rw [hk]
      rw [hGSV]
      cases hp : t (idx.slot g) with
      | true =>
          have hA : andTypeB idx t g = true := by
            unfold andTypeB; rw [hpol, hp, hk]; simp
          rw [pgB_of_andType idx s t x g hA, hpol, hp]
          simp
      | false =>
          have hA : ¬ andTypeB idx t g = true := by
            unfold andTypeB; rw [hpol, hp, hk]; simp
          rw [pgB_of_not_andType idx s t x g hA, hpol, hp]
          simp only [Bool.false_eq_true, false_iff, not_forall,
            Bool.not_eq_true, exists_prop]
  | orGate =>
      have hGSV : GateStepValue idx x s g =
          (∃ h, c.edge h g = true ∧ predValue idx x s h = true) := by
        unfold GateStepValue; rw [hk]
      rw [hGSV]
      cases hp : t (idx.slot g) with
      | true =>
          have hA : ¬ andTypeB idx t g = true := by
            unfold andTypeB; rw [hpol, hp, hk]; simp
          rw [pgB_of_not_andType idx s t x g hA, hpol, hp]
          simp
      | false =>
          have hA : andTypeB idx t g = true := by
            unfold andTypeB; rw [hpol, hp, hk]; simp
          rw [pgB_of_andType idx s t x g hA, hpol, hp]
          simp only [Bool.false_eq_true, false_iff, not_exists, not_and,
            Bool.not_eq_true]

/-! ## The gates of the constructed circuit -/

/-- The gates of the constructed circuit: two literal gates per gate of `c` (one
of each polarity), one requirement gate per gate of `c`, and the top gate. -/
inductive Slot (N : Nat) where
  | pos (h : Fin N)
  | neg (h : Fin N)
  | pg (g : Fin N)
  | top

/-- The index of a slot inside `Fin (3 * N + 1)`. -/
def slotIdx {N : Nat} : Slot N → Fin (3 * N + 1)
  | .pos h => ⟨h.val, by have := h.isLt; omega⟩
  | .neg h => ⟨N + h.val, by have := h.isLt; omega⟩
  | .pg g => ⟨2 * N + g.val, by have := g.isLt; omega⟩
  | .top => ⟨3 * N, by omega⟩

/-- The slot of an index. -/
def slotOf {N : Nat} (i : Fin (3 * N + 1)) : Slot N :=
  if h1 : i.val < N then .pos ⟨i.val, h1⟩
  else if h2 : i.val < 2 * N then .neg ⟨i.val - N, by omega⟩
  else if h3 : i.val < 3 * N then .pg ⟨i.val - 2 * N, by omega⟩
  else .top

@[simp] theorem slotOf_slotIdx {N : Nat} (y : Slot N) : slotOf (slotIdx y) = y := by
  cases y with
  | pos h =>
      have h1 : (slotIdx (Slot.pos h)).val < N := h.isLt
      rw [slotOf, dif_pos h1]
      congr 1
  | neg h =>
      have hlt := h.isLt
      have h1 : ¬ (slotIdx (Slot.neg h)).val < N := by simp [slotIdx]
      have h2 : (slotIdx (Slot.neg h)).val < 2 * N := by simp [slotIdx]; omega
      rw [slotOf, dif_neg h1, dif_pos h2]
      congr 1
      apply Fin.ext
      simp [slotIdx]
  | pg g =>
      have hlt := g.isLt
      have h1 : ¬ (slotIdx (Slot.pg g)).val < N := by simp [slotIdx]; omega
      have h2 : ¬ (slotIdx (Slot.pg g)).val < 2 * N := by simp [slotIdx]
      have h3 : (slotIdx (Slot.pg g)).val < 3 * N := by simp [slotIdx]; omega
      rw [slotOf, dif_neg h1, dif_neg h2, dif_pos h3]
      congr 1
      apply Fin.ext
      simp [slotIdx]
  | top =>
      have h1 : ¬ (slotIdx (Slot.top (N := N))).val < N := by simp [slotIdx]; omega
      have h2 : ¬ (slotIdx (Slot.top (N := N))).val < 2 * N := by simp [slotIdx]; omega
      have h3 : ¬ (slotIdx (Slot.top (N := N))).val < 3 * N := by simp [slotIdx]
      rw [slotOf, dif_neg h1, dif_neg h2, dif_neg h3]

theorem slotIdx_slotOf {N : Nat} (i : Fin (3 * N + 1)) : slotIdx (slotOf i) = i := by
  rw [slotOf]
  split_ifs with h1 h2 h3 <;> apply Fin.ext <;> simp [slotIdx] <;> omega

theorem exists_slotIdx {N : Nat} (i : Fin (3 * N + 1)) : ∃ y : Slot N, i = slotIdx y :=
  ⟨slotOf i, (slotIdx_slotOf i).symm⟩

theorem forall_slot {N : Nat} {P : Fin (3 * N + 1) → Prop} :
    (∀ i, P i) ↔ ∀ y : Slot N, P (slotIdx y) := by
  constructor
  · intro h y; exact h _
  · intro h i
    obtain ⟨y, rfl⟩ := exists_slotIdx i
    exact h y

theorem exists_slot {N : Nat} {P : Fin (3 * N + 1) → Prop} :
    (∃ i, P i) ↔ ∃ y : Slot N, P (slotIdx y) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨y, rfl⟩ := exists_slotIdx i
    exact ⟨y, hi⟩
  · rintro ⟨y, hy⟩
    exact ⟨_, hy⟩

/-! ## The circuit -/

/-- The `ACC` gate of a positive-polarity literal slot. -/
def litKindPos (k : ADRGate n) : ACCGate n 2 :=
  match k with
  | .literal j bb => .literal j bb
  | _ => .orGate

/-- The `ACC` gate of a negative-polarity literal slot. -/
def litKindNeg (k : ADRGate n) : ACCGate n 2 :=
  match k with
  | .literal j bb => .literal j (!bb)
  | _ => .orGate

/-- The value of a positive-polarity literal slot. -/
def litValPos (x : Fin n → Bool) (k : ADRGate n) : Bool :=
  match k with
  | .literal j bb => if bb then !(x j) else x j
  | _ => false

/-- The value of a negative-polarity literal slot. -/
def litValNeg (x : Fin n → Bool) (k : ADRGate n) : Bool :=
  match k with
  | .literal j bb => if !bb then !(x j) else x j
  | _ => false

section Build

variable (idx : LayerIndexing c w) (s t : State w) (ell : Nat)

/-- The gate type of each slot. -/
def kindOf : Slot c.gateCount → ACCGate n 2
  | .pos h => litKindPos (c.kind h)
  | .neg h => litKindNeg (c.kind h)
  | .pg g => if isAndKindB idx s t g = true then .andGate else .orGate
  | .top => .andGate

/-- The layer of each slot. -/
def layerOf : Slot c.gateCount → Nat
  | .pos h => if (c.kind h).isComputation = true then 1 else 0
  | .neg h => if (c.kind h).isComputation = true then 1 else 0
  | .pg _ => 2
  | .top => 3

/-- The edges of the constructed circuit. -/
def edgeOf : Slot c.gateCount → Slot c.gateCount → Bool
  | .pos h, .pg g => keepB idx s t g && isLitB h && c.edge h g && polB idx t g
  | .neg h, .pg g => keepB idx s t g && isLitB h && c.edge h g && !(polB idx t g)
  | .pg g, .top => inGB ell g
  | _, _ => false

/-- The intended value of each slot. -/
def valOf (x : Fin n → Bool) : Slot c.gateCount → Bool
  | .pos h => litValPos x (c.kind h)
  | .neg h => litValNeg x (c.kind h)
  | .pg g => pgB idx s t x g
  | .top => decide (∀ g, inGB ell g = true → pgB idx s t x g = true)

/-- The depth-3 `ACC[2]` circuit computing the local relation. -/
def localACC : ACCCircuit n 2 where
  gateCount := 3 * c.gateCount + 1
  output := slotIdx .top
  kind := fun i => kindOf idx s t (slotOf i)
  layer := fun i => layerOf (slotOf i)
  edge := fun u v => edgeOf idx s t ell (slotOf u) (slotOf v)

@[simp] theorem localACC_gateCount : (localACC idx s t ell).gateCount = 3 * c.gateCount + 1 := rfl

@[simp] theorem localACC_kind (y : Slot c.gateCount) :
    (localACC idx s t ell).kind (slotIdx y) = kindOf idx s t y := by
  simp [localACC]

@[simp] theorem localACC_layer (y : Slot c.gateCount) :
    (localACC idx s t ell).layer (slotIdx y) = layerOf y := by
  simp [localACC]

@[simp] theorem localACC_edge (u v : Slot c.gateCount) :
    (localACC idx s t ell).edge (slotIdx u) (slotIdx v) = edgeOf idx s t ell u v := by
  simp [localACC]

theorem localACC_output : (localACC idx s t ell).output = slotIdx .top := rfl

@[simp] theorem valOf_pos (x : Fin n → Bool) (h : Fin c.gateCount) :
    valOf idx s t ell x (Slot.pos h) = litValPos x (c.kind h) := rfl

@[simp] theorem valOf_neg (x : Fin n → Bool) (h : Fin c.gateCount) :
    valOf idx s t ell x (Slot.neg h) = litValNeg x (c.kind h) := rfl

@[simp] theorem valOf_pg (x : Fin n → Bool) (g : Fin c.gateCount) :
    valOf idx s t ell x (Slot.pg g) = pgB idx s t x g := rfl

@[simp] theorem valOf_top (x : Fin n → Bool) :
    valOf idx s t ell x Slot.top =
      decide (∀ g, inGB ell g = true → pgB idx s t x g = true) := rfl

@[simp] theorem edgeOf_pos_right (u : Slot c.gateCount) (h : Fin c.gateCount) :
    edgeOf idx s t ell u (Slot.pos h) = false := by cases u <;> rfl

@[simp] theorem edgeOf_neg_right (u : Slot c.gateCount) (h : Fin c.gateCount) :
    edgeOf idx s t ell u (Slot.neg h) = false := by cases u <;> rfl

/-! ## Auxiliary facts -/

theorem isLitB_eq_true_iff (h : Fin c.gateCount) :
    isLitB h = true ↔ (c.kind h).isComputation = false := by
  unfold isLitB
  cases hk : (c.kind h).isComputation <;> simp

theorem predValue_of_comp (x : Fin n → Bool) (h : Fin c.gateCount)
    (hcomp : (c.kind h).isComputation = true) :
    predValue idx x s h = s (idx.slot h) := by
  unfold predValue
  cases hk : c.kind h with
  | literal j bb => rw [hk] at hcomp; simp [ADRGate.isComputation] at hcomp
  | andGate => rfl
  | orGate => rfl

theorem litValPos_eq_termVal (x : Fin n → Bool) (g h : Fin c.gateCount)
    (hlit : isLitB h = true) (hpol : polB idx t g = true) :
    litValPos x (c.kind h) = termVal idx s t x g h := by
  cases hk : c.kind h with
  | literal j bb =>
      simp only [litValPos, termVal, hk, hpol, beq_iff_eq]
  | andGate =>
      rw [isLitB_eq_true_iff, hk] at hlit
      simp [ADRGate.isComputation] at hlit
  | orGate =>
      rw [isLitB_eq_true_iff, hk] at hlit
      simp [ADRGate.isComputation] at hlit

theorem litValNeg_eq_termVal (x : Fin n → Bool) (g h : Fin c.gateCount)
    (hlit : isLitB h = true) (hpol : polB idx t g = false) :
    litValNeg x (c.kind h) = termVal idx s t x g h := by
  cases hk : c.kind h with
  | literal j bb =>
      simp only [litValNeg, termVal, hk, hpol]
      cases bb <;> simp
  | andGate =>
      rw [isLitB_eq_true_iff, hk] at hlit
      simp [ADRGate.isComputation] at hlit
  | orGate =>
      rw [isLitB_eq_true_iff, hk] at hlit
      simp [ADRGate.isComputation] at hlit

theorem constTermB_eq_true_iff (g h : Fin c.gateCount) :
    constTermB idx s t g h = true ↔ s (idx.slot h) = polB idx t g := by
  unfold constTermB
  simp

/-! ## The middle layer computes the requirement -/

theorem valOf_pg_and (x : Fin n → Bool) (g : Fin c.gateCount)
    (hk : isAndKindB idx s t g = true) :
    pgB idx s t x g = true ↔
      ∀ y : Slot c.gateCount, edgeOf idx s t ell y (Slot.pg g) = true →
        valOf idx s t ell x y = true := by
  by_cases hA : andTypeB idx t g = true
  · have hcA : cAndB idx s t g = true := by
      unfold isAndKindB at hk; rwa [if_pos hA] at hk
    have hkeep : keepB idx s t g = true := by unfold keepB; rw [if_pos hA]; exact hcA
    have hcA' := of_decide_eq_true hcA
    rw [pgB_of_andType idx s t x g hA]
    constructor
    · intro H y hy
      cases y with
      | pos h =>
          simp only [edgeOf, Bool.and_eq_true] at hy
          obtain ⟨⟨⟨-, hlit⟩, hedge⟩, hpol⟩ := hy
          rw [valOf_pos, litValPos_eq_termVal idx s t x g h hlit hpol]
          exact (termVal_eq_true_iff idx s t x g h).mpr (H h hedge)
      | neg h =>
          simp only [edgeOf, Bool.and_eq_true, Bool.not_eq_true'] at hy
          obtain ⟨⟨⟨-, hlit⟩, hedge⟩, hpol⟩ := hy
          rw [valOf_neg, litValNeg_eq_termVal idx s t x g h hlit hpol]
          exact (termVal_eq_true_iff idx s t x g h).mpr (H h hedge)
      | pg g' => simp [edgeOf] at hy
      | top => simp [edgeOf] at hy
    · intro H h hedge
      by_cases hlit : isLitB h = true
      · cases hpol : polB idx t g with
        | true =>
            have hy : edgeOf idx s t ell (Slot.pos h) (Slot.pg g) = true := by
              simp [edgeOf, hkeep, hlit, hedge, hpol]
            have := H (Slot.pos h) hy
            rw [valOf_pos, litValPos_eq_termVal idx s t x g h hlit hpol] at this
            exact ((termVal_eq_true_iff idx s t x g h).mp this).trans hpol
        | false =>
            have hy : edgeOf idx s t ell (Slot.neg h) (Slot.pg g) = true := by
              simp [edgeOf, hkeep, hlit, hedge, hpol]
            have := H (Slot.neg h) hy
            rw [valOf_neg, litValNeg_eq_termVal idx s t x g h hlit hpol] at this
            exact ((termVal_eq_true_iff idx s t x g h).mp this).trans hpol
      · have hcomp : (c.kind h).isComputation = true := by
          rw [isLitB_eq_true_iff] at hlit
          simpa using hlit
        have hlitf : isLitB h = false := by simpa using hlit
        have := (constTermB_eq_true_iff idx s t g h).mp (hcA' h hedge hlitf)
        rw [predValue_of_comp idx s x h hcomp]
        exact this
  · have hcO : cOrB idx s t g = true := by
      unfold isAndKindB at hk; rwa [if_neg hA] at hk
    have hkeep : keepB idx s t g = false := by
      unfold keepB; rw [if_neg hA, hcO]; rfl
    have hnoedge : ∀ y : Slot c.gateCount, edgeOf idx s t ell y (Slot.pg g) = false := by
      intro y
      cases y with
      | pos h => simp [edgeOf, hkeep]
      | neg h => simp [edgeOf, hkeep]
      | pg g' => rfl
      | top => rfl
    constructor
    · intro _ y hy; rw [hnoedge y] at hy; exact absurd hy (by simp)
    · intro _
      rw [pgB_of_not_andType idx s t x g hA]
      obtain ⟨h, hedge, hlitf, hconst⟩ := of_decide_eq_true hcO
      have hcomp : (c.kind h).isComputation = true := by
        unfold isLitB at hlitf
        simpa using hlitf
      exact ⟨h, hedge, by
        rw [predValue_of_comp idx s x h hcomp]
        exact (constTermB_eq_true_iff idx s t g h).mp hconst⟩

theorem valOf_pg_or (x : Fin n → Bool) (g : Fin c.gateCount)
    (hk : ¬ isAndKindB idx s t g = true) :
    pgB idx s t x g = true ↔
      ∃ y : Slot c.gateCount, edgeOf idx s t ell y (Slot.pg g) = true ∧
        valOf idx s t ell x y = true := by
  by_cases hA : andTypeB idx t g = true
  · have hcA : cAndB idx s t g = false := by
      unfold isAndKindB at hk
      rw [if_pos hA] at hk
      simpa using hk
    have hkeep : keepB idx s t g = false := by unfold keepB; rw [if_pos hA]; exact hcA
    have hnoedge : ∀ y : Slot c.gateCount, edgeOf idx s t ell y (Slot.pg g) = false := by
      intro y
      cases y with
      | pos h => simp [edgeOf, hkeep]
      | neg h => simp [edgeOf, hkeep]
      | pg g' => rfl
      | top => rfl
    have hfalse : pgB idx s t x g = true → False := by
      rw [pgB_of_andType idx s t x g hA]
      intro H
      have hnot := of_decide_eq_false hcA
      push_neg at hnot
      obtain ⟨h, hedge, hlitf, hconst⟩ := hnot
      have hcomp : (c.kind h).isComputation = true := by
        unfold isLitB at hlitf; simpa using hlitf
      have hv := H h hedge
      rw [predValue_of_comp idx s x h hcomp] at hv
      exact hconst ((constTermB_eq_true_iff idx s t g h).mpr hv)
    constructor
    · intro H; exact absurd H hfalse
    · rintro ⟨y, hy, -⟩; rw [hnoedge y] at hy; exact absurd hy (by simp)
  · have hcO : cOrB idx s t g = false := by
      unfold isAndKindB at hk
      rw [if_neg hA] at hk
      simpa using hk
    have hkeep : keepB idx s t g = true := by
      unfold keepB; rw [if_neg hA, hcO]; rfl
    have hcO' := of_decide_eq_false hcO
    push_neg at hcO'
    rw [pgB_of_not_andType idx s t x g hA]
    constructor
    · rintro ⟨h, hedge, hv⟩
      by_cases hlit : isLitB h = true
      · cases hpol : polB idx t g with
        | true =>
            refine ⟨Slot.pos h, by simp [edgeOf, hkeep, hlit, hedge, hpol], ?_⟩
            rw [valOf_pos, litValPos_eq_termVal idx s t x g h hlit hpol]
            exact (termVal_eq_true_iff idx s t x g h).mpr hv
        | false =>
            refine ⟨Slot.neg h, by simp [edgeOf, hkeep, hlit, hedge, hpol], ?_⟩
            rw [valOf_neg, litValNeg_eq_termVal idx s t x g h hlit hpol]
            exact (termVal_eq_true_iff idx s t x g h).mpr hv
      · exfalso
        have hlitf : isLitB h = false := by simpa using hlit
        have hcomp : (c.kind h).isComputation = true := by
          unfold isLitB at hlitf; simpa using hlitf
        rw [predValue_of_comp idx s x h hcomp] at hv
        exact hcO' h hedge hlitf ((constTermB_eq_true_iff idx s t g h).mpr hv)
    · rintro ⟨y, hy, hv⟩
      cases y with
      | pos h =>
          simp only [edgeOf, Bool.and_eq_true] at hy
          obtain ⟨⟨⟨-, hlit⟩, hedge⟩, hpol⟩ := hy
          rw [valOf_pos, litValPos_eq_termVal idx s t x g h hlit hpol] at hv
          exact ⟨h, hedge, (termVal_eq_true_iff idx s t x g h).mp hv⟩
      | neg h =>
          simp only [edgeOf, Bool.and_eq_true, Bool.not_eq_true'] at hy
          obtain ⟨⟨⟨-, hlit⟩, hedge⟩, hpol⟩ := hy
          rw [valOf_neg, litValNeg_eq_termVal idx s t x g h hlit hpol] at hv
          exact ⟨h, hedge, (termVal_eq_true_iff idx s t x g h).mp hv⟩
      | pg g' => simp [edgeOf] at hy
      | top => simp [edgeOf] at hy

/-! ## Well-formedness -/

theorem kindOf_ne_notGate (y : Slot c.gateCount) : kindOf idx s t y ≠ .notGate := by
  cases y with
  | pos h => cases hk : c.kind h <;> simp [kindOf, litKindPos, hk]
  | neg h => cases hk : c.kind h <;> simp [kindOf, litKindNeg, hk]
  | pg g => simp only [kindOf]; split_ifs <;> simp
  | top => simp [kindOf]

theorem layerOf_eq_zero_iff (y : Slot c.gateCount) :
    layerOf y = 0 ↔ ∃ (i : Fin n) (b : Bool), kindOf idx s t y = .literal i b := by
  cases y with
  | pos h =>
      cases hk : c.kind h <;>
        simp [layerOf, kindOf, litKindPos, hk, ADRGate.isComputation]
  | neg h =>
      cases hk : c.kind h <;>
        simp [layerOf, kindOf, litKindNeg, hk, ADRGate.isComputation]
  | pg g => simp only [layerOf, kindOf]; split_ifs <;> simp
  | top => simp [layerOf, kindOf]

theorem edgeOf_layer_lt (u v : Slot c.gateCount)
    (h : edgeOf idx s t ell u v = true) : layerOf u < layerOf v := by
  cases v with
  | pos hh => simp at h
  | neg hh => simp at h
  | pg g =>
      cases u with
      | pos hh =>
          simp only [edgeOf, Bool.and_eq_true] at h
          obtain ⟨⟨⟨-, hlit⟩, -⟩, -⟩ := h
          rw [isLitB_eq_true_iff] at hlit
          simp [layerOf, hlit]
      | neg hh =>
          simp only [edgeOf, Bool.and_eq_true] at h
          obtain ⟨⟨⟨-, hlit⟩, -⟩, -⟩ := h
          rw [isLitB_eq_true_iff] at hlit
          simp [layerOf, hlit]
      | pg g' => simp [edgeOf] at h
      | top => simp [edgeOf] at h
  | top =>
      cases u with
      | pos hh => simp [edgeOf] at h
      | neg hh => simp [edgeOf] at h
      | pg g => simp [layerOf]
      | top => simp [edgeOf] at h

theorem wellFormedACC_localACC : WellFormedACC (localACC idx s t ell) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨yu, rfl⟩ := exists_slotIdx u
    obtain ⟨yv, rfl⟩ := exists_slotIdx v
    rw [localACC_edge] at huv
    rw [localACC_layer, localACC_layer]
    exact edgeOf_layer_lt idx s t ell yu yv huv
  · intro g
    obtain ⟨y, rfl⟩ := exists_slotIdx g
    rw [localACC_layer]
    simp only [localACC_kind]
    exact layerOf_eq_zero_iff idx s t y
  · intro g hg
    obtain ⟨y, rfl⟩ := exists_slotIdx g
    rw [localACC_kind] at hg
    exact absurd hg (kindOf_ne_notGate idx s t y)

theorem localACC_layer_le (g : Fin (localACC idx s t ell).gateCount) :
    (localACC idx s t ell).layer g ≤ 3 := by
  obtain ⟨y, rfl⟩ := exists_slotIdx g
  rw [localACC_layer]
  cases y <;> simp only [layerOf] <;> (try split_ifs) <;> omega

/-! ## The circuit computes the requirement -/

theorem localACC_edge_pos_false (u : Fin (localACC idx s t ell).gateCount)
    (h : Fin c.gateCount) :
    (localACC idx s t ell).edge u (slotIdx (Slot.pos h)) = false := by
  obtain ⟨y, rfl⟩ := exists_slotIdx u
  rw [localACC_edge]
  exact edgeOf_pos_right idx s t ell y h

theorem localACC_edge_neg_false (u : Fin (localACC idx s t ell).gateCount)
    (h : Fin c.gateCount) :
    (localACC idx s t ell).edge u (slotIdx (Slot.neg h)) = false := by
  obtain ⟨y, rfl⟩ := exists_slotIdx u
  rw [localACC_edge]
  exact edgeOf_neg_right idx s t ell y h

theorem accValuation_localACC (x : Fin n → Bool) :
    ACCValuation (localACC idx s t ell) x (fun i => valOf idx s t ell x (slotOf i)) := by
  intro i
  obtain ⟨y, rfl⟩ := exists_slotIdx i
  simp only [localACC_kind, slotOf_slotIdx]
  cases y with
  | pos h =>
      cases hk : c.kind h with
      | literal j bb => simp [kindOf, litKindPos, litValPos, hk]
      | andGate =>
          simp only [kindOf, litKindPos, hk, valOf_pos, litValPos]
          simp [localACC_edge_pos_false]
      | orGate =>
          simp only [kindOf, litKindPos, hk, valOf_pos, litValPos]
          simp [localACC_edge_pos_false]
  | neg h =>
      cases hk : c.kind h with
      | literal j bb => simp [kindOf, litKindNeg, litValNeg, hk]
      | andGate =>
          simp only [kindOf, litKindNeg, hk, valOf_neg, litValNeg]
          simp [localACC_edge_neg_false]
      | orGate =>
          simp only [kindOf, litKindNeg, hk, valOf_neg, litValNeg]
          simp [localACC_edge_neg_false]
  | pg g =>
      simp only [kindOf]
      by_cases hka : isAndKindB idx s t g = true
      · rw [if_pos hka]
        simp only [valOf_pg]
        rw [valOf_pg_and idx s t ell x g hka]
        constructor
        · intro H hh hedge
          obtain ⟨z, rfl⟩ := exists_slotIdx hh
          rw [localACC_edge] at hedge
          simpa using H z hedge
        · intro H z hedge
          have := H (slotIdx z) (by rw [localACC_edge]; exact hedge)
          simpa using this
      · rw [if_neg hka]
        simp only [valOf_pg]
        rw [valOf_pg_or idx s t ell x g hka]
        constructor
        · rintro ⟨z, hedge, hv⟩
          exact ⟨slotIdx z, by rw [localACC_edge]; exact hedge, by simpa using hv⟩
        · rintro ⟨hh, hedge, hv⟩
          obtain ⟨z, rfl⟩ := exists_slotIdx hh
          rw [localACC_edge] at hedge
          exact ⟨z, hedge, by simpa using hv⟩
  | top =>
      simp only [kindOf, valOf_top, decide_eq_true_eq]
      constructor
      · intro H hh hedge
        obtain ⟨z, rfl⟩ := exists_slotIdx hh
        rw [localACC_edge] at hedge
        cases z with
        | pos h => simp [edgeOf] at hedge
        | neg h => simp [edgeOf] at hedge
        | pg g =>
            simp only [edgeOf] at hedge
            simpa using H g hedge
        | top => simp [edgeOf] at hedge
      · intro H g hin
        have := H (slotIdx (Slot.pg g)) (by rw [localACC_edge]; exact hin)
        simpa using this

theorem accAccepts_localACC (x : Fin n → Bool) :
    ACCAccepts (localACC idx s t ell) x ↔
      ∀ g, inGB ell g = true → pgB idx s t x g = true := by
  constructor
  · rintro ⟨v, hv, hout⟩
    have heq := accValuation_unique (wellFormedACC_localACC idx s t ell) hv
      (accValuation_localACC idx s t ell x)
    rw [heq, localACC_output] at hout
    simpa using hout
  · intro H
    refine ⟨_, accValuation_localACC idx s t ell x, ?_⟩
    rw [localACC_output]
    simpa using H

end Build

/-! ## The local relation has a small constant-depth `ACC[2]` circuit -/

/-- **B0e.**  For fixed states `s` and `t` and a fixed layer `ell`, the local
relation is computed by a well-formed `ACC[2]` circuit of depth at most `3`
whose size is linear in the size of `c`. -/
theorem exists_acc_localRel (idx : LayerIndexing c w) (ell : Nat) (s t : State w) :
    ∃ a : ACCCircuit n 2, WellFormedACC a ∧
      (∀ g, a.layer g ≤ 3) ∧
      a.gateCount ≤ 10 * c.gateCount + 10 ∧
      ∀ x, ACCAccepts a x ↔ LocalRel idx ell s t x := by
  by_cases hQ : ∀ j : Fin w,
      (¬ ∃ g, (c.kind g).isComputation = true ∧ c.layer g = ell ∧ idx.slot g = j) → t j = false
  · refine ⟨localACC idx s t ell, wellFormedACC_localACC idx s t ell,
      localACC_layer_le idx s t ell, ?_, ?_⟩
    · rw [localACC_gateCount]; omega
    · intro x
      rw [accAccepts_localACC]
      constructor
      · intro H
        refine ⟨?_, hQ⟩
        intro g hcomp hlayer
        refine (pgB_eq_true_iff idx s t x g hcomp).mp (H g ?_)
        simp [inGB, hcomp, hlayer]
      · rintro ⟨H1, -⟩ g hin
        rw [inGB, Bool.and_eq_true, decide_eq_true_eq] at hin
        exact (pgB_eq_true_iff idx s t x g hin.1).mpr (H1 g hin.1 hin.2)
  · refine ⟨accConst n 2 false, wellFormedACC_accConst n 2 false, ?_, ?_, ?_⟩
    · intro g; rw [accConst_layer]; omega
    · rw [accConst_gateCount]; omega
    · intro x
      rw [accAccepts_accConst]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨-, h2⟩; exact absurd h2 hQ

end AllenderOQ3.Internal
