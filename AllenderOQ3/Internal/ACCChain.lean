import AllenderOQ3.Internal.ACCCompose
import AllenderOQ3.Internal.ACCLocal

/-!
# B3c: collapsing a chain of state relations by `B`-ary rounds (§9)

`AllenderOQ3.Internal.ACCCompose` builds one `B`-ary round `accComposeMany`, of
added depth `2`, realizing the composite of `B` consecutive state relations.

This file iterates that round.  `accChainPow B R d r i` is the `ACC[M]` circuit
obtained by `r` rounds starting from the relation family `R`; it realizes the
composite of the `B ^ r` consecutive relations `R i, R (i+1), …, R (i + B^r - 1)`,
and its depth is `d + 2 * r`, i.e. the added depth is `2` per round.  Together
with `AllenderOQ3.Internal.polylogCompose_collapse`, which fixes the number of
rounds needed to collapse a chain of length `≤ C * B ^ k` to the constant `k + 1`,
this gives the §9 statement that the whole chain collapses to a single `ACC[M]`
relation of constant added depth.

The semantics is stated through the purely relational chain composite
`StepChain`, and the two combinatorial facts it needs — splitting a chain at an
intermediate point (`stepChain_add`) and regrouping a chain into `B` blocks of
length `L` (`stepChain_blocks`) — are proved here as well.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n M w : Nat}

/-! ## The relational chain composite -/

/-- `StepChain Rel k s u`: there is a run of `k` steps from `s` to `u`, whose
`j`-th step uses the relation `Rel j`. -/
def StepChain (Rel : Nat → State w → State w → Prop) : Nat → State w → State w → Prop
  | 0, s, u => s = u
  | k + 1, s, u => ∃ t, StepChain Rel k s t ∧ Rel k t u

@[simp] theorem stepChain_zero (Rel : Nat → State w → State w → Prop) (s u : State w) :
    StepChain Rel 0 s u ↔ s = u := Iff.rfl

theorem stepChain_succ (Rel : Nat → State w → State w → Prop) (k : Nat) (s u : State w) :
    StepChain Rel (k + 1) s u ↔ ∃ t, StepChain Rel k s t ∧ Rel k t u := Iff.rfl

theorem stepChain_one (Rel : Nat → State w → State w → Prop) (s u : State w) :
    StepChain Rel 1 s u ↔ Rel 0 s u := by
  rw [stepChain_succ]
  constructor
  · rintro ⟨t, rfl, h⟩; exact h
  · intro h; exact ⟨s, rfl, h⟩

/-- The chain composite only depends on the relations actually used. -/
theorem stepChain_congr {Rel Rel' : Nat → State w → State w → Prop} (k : Nat)
    (h : ∀ j, j < k → ∀ s t, Rel j s t ↔ Rel' j s t) (s u : State w) :
    StepChain Rel k s u ↔ StepChain Rel' k s u := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
      rw [stepChain_succ, stepChain_succ]
      refine exists_congr fun t => and_congr ?_ ?_
      · exact ih (fun j hj s t => h j (Nat.lt_succ_of_lt hj) s t) t
      · exact h k (Nat.lt_succ_self k) t u

/-- A chain of length `k₁ + k₂` splits at the intermediate point `k₁`. -/
theorem stepChain_add (Rel : Nat → State w → State w → Prop) (k₁ k₂ : Nat) (s u : State w) :
    StepChain Rel (k₁ + k₂) s u ↔
      ∃ t, StepChain Rel k₁ s t ∧ StepChain (fun j => Rel (k₁ + j)) k₂ t u := by
  induction k₂ generalizing u with
  | zero =>
      constructor
      · intro h; exact ⟨u, h, rfl⟩
      · rintro ⟨t, ht, rfl⟩; exact ht
  | succ k ih =>
      rw [show k₁ + (k + 1) = (k₁ + k) + 1 from rfl, stepChain_succ]
      constructor
      · rintro ⟨v, hv, hlast⟩
        obtain ⟨t, ht, htv⟩ := (ih v).1 hv
        exact ⟨t, ht, v, htv, hlast⟩
      · rintro ⟨t, ht, v, htv, hlast⟩
        exact ⟨v, (ih v).2 ⟨t, ht, htv⟩, hlast⟩

/-- A chain of length `L * B` is the same as a chain of `B` blocks, each block
being a chain of length `L`. -/
theorem stepChain_blocks (Rel : Nat → State w → State w → Prop) (L B : Nat) (s u : State w) :
    StepChain Rel (L * B) s u ↔
      StepChain (fun j => StepChain (fun m => Rel (j * L + m)) L) B s u := by
  induction B generalizing u with
  | zero => simp
  | succ B ih =>
      rw [Nat.mul_succ, stepChain_add, stepChain_succ]
      refine exists_congr fun t => and_congr (ih t) ?_
      exact stepChain_congr L (fun m _ s t => by rw [Nat.mul_comm L B]) t u

/-- The chain composite in terms of an explicit `Fin (k+1)`-indexed path, which
is the shape produced by `accAccepts_accComposeMany`. -/
theorem stepChain_iff_finPath (Rel : Nat → State w → State w → Prop) (k : Nat) (s u : State w) :
    StepChain Rel k s u ↔
      ∃ p : Fin (k + 1) → State w, p 0 = s ∧ p (Fin.last k) = u ∧
        ∀ j : Fin k, Rel j.val (p j.castSucc) (p j.succ) := by
  constructor
  · intro h
    -- first extract an `ℕ`-indexed path
    have key : ∀ (m : Nat) (v : State w), StepChain Rel m s v →
        ∃ P : Nat → State w, P 0 = s ∧ P m = v ∧ ∀ j, j < m → Rel j (P j) (P (j + 1)) := by
      intro m
      induction m with
      | zero =>
          rintro v rfl
          exact ⟨fun _ => s, rfl, rfl, by omega⟩
      | succ m ih =>
          rintro v ⟨t, ht, htv⟩
          obtain ⟨P, hP0, hPm, hPstep⟩ := ih t ht
          refine ⟨fun a => if a ≤ m then P a else v, by simpa using hP0, by simp, ?_⟩
          intro j hj
          rcases Nat.lt_or_ge j m with hjm | hjm
          · have h1 : j ≤ m := le_of_lt hjm
            have h2 : j + 1 ≤ m := hjm
            simp only [h1, h2, if_pos]
            exact hPstep j hjm
          · have hjm' : j = m := by omega
            subst hjm'
            have h2 : ¬ (j + 1 ≤ j) := by omega
            simp only [le_refl, if_pos, h2, if_neg, not_false_iff]
            rw [hPm]
            exact htv
    obtain ⟨P, hP0, hPk, hPstep⟩ := key k u h
    refine ⟨fun j => P j.val, by simpa using hP0, by simpa using hPk, fun j => ?_⟩
    simpa using hPstep j.val j.isLt
  · rintro ⟨p, hp0, hpl, hstep⟩
    have key : ∀ m, (hm : m ≤ k) → StepChain Rel m s (p ⟨m, by omega⟩) := by
      intro m
      induction m with
      | zero => intro _; simpa using hp0.symm
      | succ m ih =>
          intro hm
          refine ⟨p ⟨m, by omega⟩, ih (by omega), ?_⟩
          have := hstep ⟨m, by omega⟩
          simpa using this
    have := key k (le_refl k)
    rwa [show (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k from rfl, hpl] at this

/-! ## Iterating the `B`-ary round -/

/-- `r` rounds of the `B`-ary composition, starting at position `i` of the
relation family `R`: it realizes the composite of the `B ^ r` relations
`R i, …, R (i + B ^ r - 1)`. -/
noncomputable def accChainPow (B : Nat) (R : Nat → State w → State w → ACCCircuit n M) (d : Nat) :
    Nat → Nat → State w → State w → ACCCircuit n M
  | 0, i, s, u => R i s u
  | r + 1, i, s, u =>
      accComposeMany B (fun j : Fin B => accChainPow B R d r (i + j.val * B ^ r)) (d + 2 * r) s u

theorem accChainPow_zero (B : Nat) (R : Nat → State w → State w → ACCCircuit n M) (d i : Nat)
    (s u : State w) : accChainPow B R d 0 i s u = R i s u := rfl

theorem accChainPow_succ (B : Nat) (R : Nat → State w → State w → ACCCircuit n M) (d r i : Nat)
    (s u : State w) :
    accChainPow B R d (r + 1) i s u =
      accComposeMany B (fun j : Fin B => accChainPow B R d r (i + j.val * B ^ r)) (d + 2 * r) s u :=
  rfl

/-- Each round adds depth `2`. -/
theorem accChainPow_layer_le (B : Nat) (R : Nat → State w → State w → ACCCircuit n M) (d : Nat)
    (hdR : ∀ i s t g, (R i s t).layer g ≤ d) (r : Nat) :
    ∀ (i : Nat) (s u : State w) (g : Fin (accChainPow B R d r i s u).gateCount),
      (accChainPow B R d r i s u).layer g ≤ d + 2 * r := by
  induction r with
  | zero => intro i s u g; simpa using hdR i s u g
  | succ r ih =>
      intro i s u g
      rw [show d + 2 * (r + 1) = (d + 2 * r) + 2 by ring]
      exact accComposeMany_layer_le B _ (d + 2 * r) (fun j s t => ih _ s t) s u g

theorem wellFormedACC_accChainPow (B : Nat) (R : Nat → State w → State w → ACCCircuit n M)
    (d : Nat) (hR : ∀ i s t, WellFormedACC (R i s t)) (hdR : ∀ i s t g, (R i s t).layer g ≤ d)
    (r : Nat) : ∀ (i : Nat) (s u : State w), WellFormedACC (accChainPow B R d r i s u) := by
  induction r with
  | zero => intro i s u; exact hR i s u
  | succ r ih =>
      intro i s u
      exact wellFormedACC_accComposeMany B _ (d + 2 * r) (fun j s t => ih _ s t)
        (fun j s t g => accChainPow_layer_le B R d hdR r _ s t g) s u

/-- **B3c.**  After `r` rounds the circuit accepts exactly when the chain of the
`B ^ r` relations `R i, …, R (i + B ^ r - 1)` connects `s` to `u`. -/
theorem accAccepts_accChainPow (B : Nat) (hB : 2 ≤ B)
    (R : Nat → State w → State w → ACCCircuit n M) (d : Nat)
    (hR : ∀ i s t, WellFormedACC (R i s t)) (hdR : ∀ i s t g, (R i s t).layer g ≤ d)
    (x : Fin n → Bool) (r : Nat) :
    ∀ (i : Nat) (s u : State w),
      ACCAccepts (accChainPow B R d r i s u) x ↔
        StepChain (fun j s t => ACCAccepts (R (i + j) s t) x) (B ^ r) s u := by
  induction r with
  | zero =>
      intro i s u
      rw [accChainPow_zero, pow_zero, stepChain_one]
      simp
  | succ r ih =>
      intro i s u
      rw [accChainPow_succ,
        accAccepts_accComposeMany B hB _ (d + 2 * r)
          (fun j s t => wellFormedACC_accChainPow B R d hR hdR r _ s t)
          (fun j s t g => accChainPow_layer_le B R d hdR r _ s t g) s u x]
      have hstep : ∀ (p : Fin (B + 1) → State w) (j : Fin B),
          ACCAccepts (accChainPow B R d r (i + j.val * B ^ r) (p j.castSucc) (p j.succ)) x ↔
            StepChain (fun m s t => ACCAccepts (R (i + (j.val * B ^ r + m)) s t) x) (B ^ r)
              (p j.castSucc) (p j.succ) := by
        intro p j
        rw [ih (i + j.val * B ^ r) (p j.castSucc) (p j.succ)]
        exact stepChain_congr _ (fun m _ s t => by rw [Nat.add_assoc]) _ _
      rw [pow_succ, stepChain_blocks]
      rw [stepChain_iff_finPath
        (fun j => StepChain (fun m s t => ACCAccepts (R (i + (j * B ^ r + m)) s t) x) (B ^ r))
        B s u]
      exact exists_congr fun p =>
        and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun j => hstep p j))

/-- Size of `r` rounds: with `N` the number of candidate paths of one round and
every base relation of size `≤ G₀`, the `r`-round circuit has at most
`(N * (B + 1) + 1) ^ r * (G₀ + 1)` gates.  For fixed `w` and `r` this is
polynomial in `G₀` and in `(2 ^ w) ^ (B + 1)`. -/
theorem accChainPow_gateCount_le (B : Nat) (R : Nat → State w → State w → ACCCircuit n M)
    (d G₀ : Nat) (hG₀ : ∀ i s t, (R i s t).gateCount ≤ G₀) (r : Nat) :
    ∀ (i : Nat) (s u : State w), (accChainPow B R d r i s u).gateCount
      ≤ (Fintype.card (Fin (B + 1) → State w) * (B + 1) + 1) ^ r * (G₀ + 1) := by
  induction r with
  | zero =>
      intro i s u
      simpa using le_trans (hG₀ i s u) (Nat.le_succ G₀)
  | succ r ih =>
      intro i s u
      set N := Fintype.card (Fin (B + 1) → State w) with hN
      set X := (N * (B + 1) + 1) ^ r * (G₀ + 1) with hX
      have hXpos : 1 ≤ X := by
        have h1 : 1 ≤ (N * (B + 1) + 1) ^ r := Nat.one_le_pow _ _ (by omega)
        have h2 : 1 ≤ G₀ + 1 := Nat.le_add_left 1 G₀
        calc 1 = 1 * 1 := by ring
          _ ≤ (N * (B + 1) + 1) ^ r * (G₀ + 1) := Nat.mul_le_mul h1 h2
      have hround := accComposeMany_gateCount_le B
        (fun j : Fin B => accChainPow B R d r (i + j.val * B ^ r)) (d + 2 * r) X
        (fun j s t => ih _ s t) s u
      rw [accChainPow_succ]
      refine le_trans hround ?_
      have hstep : N + 1 ≤ (N + 1) * X := Nat.le_mul_of_pos_right _ hXpos
      have e1 : N * (B * X + 1) + 1 = N * B * X + (N + 1) := by ring
      have e2 : (N * (B + 1) + 1) ^ (r + 1) * (G₀ + 1) = N * B * X + (N + 1) * X := by
        rw [hX, pow_succ]; ring
      rw [e1, e2]
      exact Nat.add_le_add_left hstep _

/-! ## Padding a chain out to a power of `B` -/

/-- The `ACC[M]` circuit for the identity (equality) relation on states: a
constant circuit at layer `1`. -/
def accIdRel (n M : Nat) (s t : State w) : ACCCircuit n M :=
  accConst n M (decide (s = t))

theorem accAccepts_accIdRel (n M : Nat) (s t : State w) (x : Fin n → Bool) :
    ACCAccepts (accIdRel n M s t) x ↔ s = t := by
  rw [accIdRel, accAccepts_accConst]
  simp

/-- Pad a chain of `m` relations out to an infinite family by repeating the
identity relation. -/
def accChainPad (R : Nat → State w → State w → ACCCircuit n M) (m : Nat) :
    Nat → State w → State w → ACCCircuit n M :=
  fun j s t => if j < m then R j s t else accIdRel n M s t

theorem accChainPad_lt (R : Nat → State w → State w → ACCCircuit n M) {m j : Nat} (h : j < m)
    (s t : State w) : accChainPad R m j s t = R j s t := if_pos h

theorem accChainPad_ge (R : Nat → State w → State w → ACCCircuit n M) {m j : Nat} (h : ¬ j < m)
    (s t : State w) : accChainPad R m j s t = accIdRel n M s t := if_neg h

theorem wellFormedACC_accChainPad (R : Nat → State w → State w → ACCCircuit n M) (m : Nat)
    (hR : ∀ i s t, WellFormedACC (R i s t)) (j : Nat) (s t : State w) :
    WellFormedACC (accChainPad R m j s t) := by
  by_cases h : j < m
  · rw [accChainPad_lt R h]; exact hR j s t
  · rw [accChainPad_ge R h, accIdRel]; exact wellFormedACC_accConst n M _

theorem accChainPad_layer_le (R : Nat → State w → State w → ACCCircuit n M) (m d : Nat)
    (hd : 1 ≤ d) (hdR : ∀ i s t g, (R i s t).layer g ≤ d) (j : Nat) (s t : State w) :
    ∀ g, (accChainPad R m j s t).layer g ≤ d := by
  by_cases h : j < m
  · rw [accChainPad_lt R h]; exact hdR j s t
  · rw [accChainPad_ge R h, accIdRel]
    intro g
    rw [accConst_layer]
    exact hd

/-- Padding a chain with identity steps does not change what it relates. -/
theorem stepChain_accChainPad (R : Nat → State w → State w → ACCCircuit n M) (m : Nat)
    (x : Fin n → Bool) (e : Nat) (s u : State w) :
    StepChain (fun j s t => ACCAccepts (accChainPad R m j s t) x) (m + e) s u ↔
      StepChain (fun j s t => ACCAccepts (R j s t) x) m s u := by
  induction e generalizing u with
  | zero =>
      exact stepChain_congr m (fun j hj s t => by rw [accChainPad_lt R hj]) s u
  | succ e ih =>
      rw [show m + (e + 1) = (m + e) + 1 from rfl, stepChain_succ]
      constructor
      · rintro ⟨t, ht, hlast⟩
        rw [accChainPad_ge R (by omega), accAccepts_accIdRel] at hlast
        subst hlast
        exact (ih t).1 ht
      · intro h
        refine ⟨u, (ih u).2 h, ?_⟩
        rw [accChainPad_ge R (by omega), accAccepts_accIdRel]

/-- **The §9 collapse.**  A chain of `m ≤ C * B ^ k` state relations, each an
`ACC[M]` circuit of depth `≤ d`, is realized by a single `ACC[M]` circuit of
depth `≤ d + 2 * (k + 1)` — constant added depth, since the number of rounds
`k + 1` is the one fixed by `polylogCompose_collapse`. -/
theorem accAccepts_accChainCollapse (B C k m : Nat) (hB : 2 ≤ B) (hcut : 2 * C ≤ B)
    (hm : m ≤ C * B ^ k) (R : Nat → State w → State w → ACCCircuit n M) (d : Nat) (hd : 1 ≤ d)
    (hR : ∀ i s t, WellFormedACC (R i s t)) (hdR : ∀ i s t g, (R i s t).layer g ≤ d)
    (x : Fin n → Bool) (s u : State w) :
    ACCAccepts (accChainPow B (accChainPad R m) d (k + 1) 0 s u) x ↔
      StepChain (fun j s t => ACCAccepts (R j s t) x) m s u := by
  have hmB : m ≤ B ^ (k + 1) := by
    have hCB : C ≤ B := by omega
    calc m ≤ C * B ^ k := hm
      _ ≤ B * B ^ k := Nat.mul_le_mul_right _ hCB
      _ = B ^ (k + 1) := by rw [pow_succ]; ring
  rw [accAccepts_accChainPow B hB (accChainPad R m) d (wellFormedACC_accChainPad R m hR)
    (accChainPad_layer_le R m d hd hdR) x (k + 1) 0 s u]
  rw [stepChain_congr (Rel' := fun j s t => ACCAccepts (accChainPad R m j s t) x) (B ^ (k + 1))
    (fun j _ s t => by rw [Nat.zero_add]) s u]
  rw [show B ^ (k + 1) = m + (B ^ (k + 1) - m) by omega]
  exact stepChain_accChainPad R m x _ s u

/-- The collapsed circuit is well formed. -/
theorem wellFormedACC_accChainCollapse (B k m : Nat) (R : Nat → State w → State w → ACCCircuit n M)
    (d : Nat) (hd : 1 ≤ d) (hR : ∀ i s t, WellFormedACC (R i s t))
    (hdR : ∀ i s t g, (R i s t).layer g ≤ d) (s u : State w) :
    WellFormedACC (accChainPow B (accChainPad R m) d (k + 1) 0 s u) :=
  wellFormedACC_accChainPow B (accChainPad R m) d (wellFormedACC_accChainPad R m hR)
    (accChainPad_layer_le R m d hd hdR) (k + 1) 0 s u

/-- Padding does not increase the size bound (the identity relation is a single
gate). -/
theorem accChainPad_gateCount_le (R : Nat → State w → State w → ACCCircuit n M) (m G₀ : Nat)
    (hG₀ : ∀ i s t, (R i s t).gateCount ≤ G₀) (h1 : 1 ≤ G₀) (j : Nat) (s t : State w) :
    (accChainPad R m j s t).gateCount ≤ G₀ := by
  by_cases h : j < m
  · rw [accChainPad_lt R h]; exact hG₀ j s t
  · rw [accChainPad_ge R h, accIdRel, accConst_gateCount]; exact h1

/-- **Size of the §9 collapse.**  The collapsed circuit for a chain of `m`
relations, each of size `≤ G₀`, has at most
`((2 ^ w) ^ (B + 1) * (B + 1) + 1) ^ (k + 1) * (G₀ + 1)` gates. -/
theorem accChainCollapse_gateCount_le (B k m : Nat)
    (R : Nat → State w → State w → ACCCircuit n M) (d G₀ : Nat)
    (hG₀ : ∀ i s t, (R i s t).gateCount ≤ G₀) (h1 : 1 ≤ G₀) (s u : State w) :
    (accChainPow B (accChainPad R m) d (k + 1) 0 s u).gateCount
      ≤ ((2 ^ w) ^ (B + 1) * (B + 1) + 1) ^ (k + 1) * (G₀ + 1) := by
  have h := accChainPow_gateCount_le B (accChainPad R m) d G₀
    (accChainPad_gateCount_le R m G₀ hG₀ h1) (k + 1) 0 s u
  rwa [card_statePath B w] at h

/-- Arithmetic behind the polynomial size bound: with `B = ⌊log₂ (n+1)⌋` and fixed
`w`, `k`, `e₀`, the collapse bound
`((2 ^ w) ^ (B + 1) * (B + 1) + 1) ^ (k + 1) * (G₀ + 1)` is at most `(n + 1) ^ e`
for the fixed exponent `e = (2 * w + 2) * (k + 1) + e₀ + 1`. -/
theorem collapse_size_poly (w k e₀ n G₀ : Nat) (hn : 1 ≤ n) (hG : G₀ ≤ (n + 1) ^ e₀) :
    ((2 ^ w) ^ (Nat.log2 (n + 1) + 1) * (Nat.log2 (n + 1) + 1) + 1) ^ (k + 1) * (G₀ + 1)
      ≤ (n + 1) ^ ((2 * w + 2) * (k + 1) + e₀ + 1) := by
  set N := n + 1 with hNdef
  have hN : 2 ≤ N := by omega
  set L := Nat.log2 N with hLdef
  have h2L : 2 ^ L ≤ N := by
    rw [hLdef, Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 (by omega)
  have hL1 : L + 1 ≤ N := le_trans Nat.lt_two_pow_self h2L
  have ha : (2 ^ w) ^ (L + 1) ≤ N ^ (2 * w) := by
    have e : (2 ^ w) ^ (L + 1) = (2 ^ (L + 1)) ^ w := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [e]
    have h1 : 2 ^ (L + 1) ≤ N ^ 2 := by
      have h2 : (2 : Nat) ^ (L + 1) = 2 * 2 ^ L := by ring
      rw [h2, pow_two]
      exact Nat.mul_le_mul hN h2L
    calc (2 ^ (L + 1)) ^ w ≤ (N ^ 2) ^ w := Nat.pow_le_pow_left h1 w
      _ = N ^ (2 * w) := by rw [← pow_mul]
  have hb : (2 ^ w) ^ (L + 1) * (L + 1) + 1 ≤ N ^ (2 * w + 2) := by
    have h1 : (2 ^ w) ^ (L + 1) * (L + 1) ≤ N ^ (2 * w) * N := Nat.mul_le_mul ha hL1
    have h2 : N ^ (2 * w) * N = N ^ (2 * w + 1) := by rw [pow_succ]
    have h3 : N ^ (2 * w + 1) + 1 ≤ N ^ (2 * w + 2) := by
      have h4 : 1 ≤ N ^ (2 * w + 1) := Nat.one_le_pow _ _ (by omega)
      have h5 : N ^ (2 * w + 2) = N ^ (2 * w + 1) * N := by rw [pow_succ]
      have h6 : N ^ (2 * w + 1) * 2 ≤ N ^ (2 * w + 1) * N := Nat.mul_le_mul_left _ hN
      omega
    omega
  have hd : ((2 ^ w) ^ (L + 1) * (L + 1) + 1) ^ (k + 1) ≤ N ^ ((2 * w + 2) * (k + 1)) := by
    calc ((2 ^ w) ^ (L + 1) * (L + 1) + 1) ^ (k + 1)
        ≤ (N ^ (2 * w + 2)) ^ (k + 1) := Nat.pow_le_pow_left hb _
      _ = N ^ ((2 * w + 2) * (k + 1)) := by rw [← pow_mul]
  have he : G₀ + 1 ≤ N ^ (e₀ + 1) := by
    have h4 : 1 ≤ N ^ e₀ := Nat.one_le_pow _ _ (by omega)
    have h5 : N ^ (e₀ + 1) = N ^ e₀ * N := by rw [pow_succ]
    have h6 : N ^ e₀ * 2 ≤ N ^ e₀ * N := Nat.mul_le_mul_left _ hN
    omega
  calc ((2 ^ w) ^ (L + 1) * (L + 1) + 1) ^ (k + 1) * (G₀ + 1)
      ≤ N ^ ((2 * w + 2) * (k + 1)) * N ^ (e₀ + 1) := Nat.mul_le_mul hd he
    _ = N ^ ((2 * w + 2) * (k + 1) + (e₀ + 1)) := by rw [← pow_add]
    _ = N ^ ((2 * w + 2) * (k + 1) + e₀ + 1) := by ring_nf

/-- **Polynomial size of the §9 collapse.**  With the §9 blocking parameter
`B = ⌊log₂ (n+1)⌋`, a chain of relations each of size `≤ G₀ ≤ (n+1) ^ e₀` collapses,
in `k + 1` rounds, to a circuit of size `≤ (n+1) ^ e` for the fixed exponent
`e = (2 * w + 2) * (k + 1) + e₀ + 1`, which depends only on the width `w`, the
round count `k` and `e₀`. -/
theorem accChainCollapse_gateCount_poly (k m : Nat)
    (R : Nat → State w → State w → ACCCircuit n M) (d G₀ e₀ : Nat)
    (hG₀ : ∀ i s t, (R i s t).gateCount ≤ G₀) (h1 : 1 ≤ G₀) (hGpoly : G₀ ≤ (n + 1) ^ e₀)
    (hn : 1 ≤ n) (s u : State w) :
    (accChainPow (Nat.log2 (n + 1)) (accChainPad R m) d (k + 1) 0 s u).gateCount
      ≤ (n + 1) ^ ((2 * w + 2) * (k + 1) + e₀ + 1) :=
  le_trans (accChainCollapse_gateCount_le (Nat.log2 (n + 1)) k m R d G₀ hG₀ h1 s u)
    (collapse_size_poly w k e₀ n G₀ hn hGpoly)

/-- The collapsed circuit has depth `≤ d + 2 * (k + 1)`: the added depth is
constant, `2` per round. -/
theorem accChainCollapse_layer_le (B k m : Nat) (R : Nat → State w → State w → ACCCircuit n M)
    (d : Nat) (hd : 1 ≤ d) (hdR : ∀ i s t g, (R i s t).layer g ≤ d) (s u : State w)
    (g : Fin (accChainPow B (accChainPad R m) d (k + 1) 0 s u).gateCount) :
    (accChainPow B (accChainPad R m) d (k + 1) 0 s u).layer g ≤ d + 2 * (k + 1) :=
  accChainPow_layer_le B (accChainPad R m) d (accChainPad_layer_le R m d hd hdR) (k + 1) 0 s u g

/-! ## Bracketing a chain with an initial and a final test -/

/-- Extend a chain of `m` relations with an initial relation (index `0`, which
ignores its source and asserts `Init` of its target) and a final relation (index
`m + 1`, which asserts `Out` of its source and returns to the base point `z`).
The extended chain has length `m + 2`. -/
def bracketRel (Init Out : State w → Prop) (Rel : Nat → State w → State w → Prop)
    (m : Nat) (z : State w) : Nat → State w → State w → Prop :=
  fun k s t => if k = 0 then Init t else if k < m + 1 then Rel (k - 1) s t else Out s ∧ t = z

/-- **Reading acceptance off the base point.**  The bracketed chain connects the
base point `z` to itself exactly when the original chain connects some `Init`
state to some `Out` state. -/
theorem stepChain_bracketRel (Init Out : State w → Prop)
    (Rel : Nat → State w → State w → Prop) (m : Nat) (z : State w) :
    StepChain (bracketRel Init Out Rel m z) (m + 2) z z ↔
      ∃ s t, Init s ∧ StepChain Rel m s t ∧ Out t := by
  have hlen : m + 2 = 1 + (m + 1) := by omega
  have hmid : ∀ (j : Nat), j < m → ∀ a b : State w,
      bracketRel Init Out Rel m z (1 + j) a b ↔ Rel j a b := by
    intro j hj a b
    have h0 : ¬ (1 + j = 0) := by omega
    have h1 : 1 + j < m + 1 := by omega
    simp only [bracketRel, if_neg h0, if_pos h1]
    have : 1 + j - 1 = j := by omega
    rw [this]
  rw [hlen, stepChain_add]
  constructor
  · rintro ⟨a, h1, h2⟩
    rw [stepChain_one] at h1
    have hInit : Init a := by simpa [bracketRel] using h1
    rw [stepChain_succ] at h2
    obtain ⟨b, hb1, hb2⟩ := h2
    have hOut : Out b := by
      have hne : ¬ (1 + m = 0) := by omega
      have hnl : ¬ (1 + m < m + 1) := by omega
      simp only [bracketRel, if_neg hne, if_neg hnl] at hb2
      exact hb2.1
    exact ⟨a, b, hInit, (stepChain_congr m (fun j hj p q => hmid j hj p q) a b).1 hb1, hOut⟩
  · rintro ⟨s, t, hInit, hchain, hOut⟩
    refine ⟨s, ?_, ?_⟩
    · rw [stepChain_one]
      simpa [bracketRel] using hInit
    · rw [stepChain_succ]
      refine ⟨t, (stepChain_congr m (fun j hj p q => hmid j hj p q) s t).2 hchain, ?_⟩
      have hne : ¬ (1 + m = 0) := by omega
      have hnl : ¬ (1 + m < m + 1) := by omega
      simp only [bracketRel, if_neg hne, if_neg hnl]
      exact ⟨hOut, trivial⟩

/-! ## Packaging the collapse -/

/-- Turn a pointwise existence statement for the relations of a chain into a
single relation family with uniform well-formedness, depth and size bounds. -/
theorem exists_acc_relation_family (d G : Nat)
    (Rel : (Fin n → Bool) → Nat → State w → State w → Prop)
    (h : ∀ (i : Nat) (s t : State w), ∃ a : ACCCircuit n M, WellFormedACC a ∧
      (∀ g, a.layer g ≤ d) ∧ a.gateCount ≤ G ∧ ∀ x, ACCAccepts a x ↔ Rel x i s t) :
    ∃ R : Nat → State w → State w → ACCCircuit n M,
      (∀ i s t, WellFormedACC (R i s t)) ∧
      (∀ i s t g, (R i s t).layer g ≤ d) ∧
      (∀ i s t, (R i s t).gateCount ≤ G) ∧
      (∀ i s t x, ACCAccepts (R i s t) x ↔ Rel x i s t) := by
  classical
  refine ⟨fun i s t => Classical.choose (h i s t), ?_, ?_, ?_, ?_⟩
  · exact fun i s t => (Classical.choose_spec (h i s t)).1
  · exact fun i s t g => (Classical.choose_spec (h i s t)).2.1 g
  · exact fun i s t => (Classical.choose_spec (h i s t)).2.2.1
  · exact fun i s t x => (Classical.choose_spec (h i s t)).2.2.2 x

/-- **The §9 payoff, packaged.**  A chain of `m ≤ C * B ^ k` relations, each realized
by an `ACC[M]` circuit of depth `≤ d` and size `≤ G ≤ (n+1) ^ e₀`, is realized by a
single `ACC[M]` circuit of depth `≤ d + 2 * (k + 1)` and size `≤ (n+1) ^ e` for the
fixed exponent `e = (2 * w + 2) * (k + 1) + e₀ + 1`, where `B = ⌊log₂ (n+1)⌋` is the
§9 blocking parameter. -/
theorem exists_acc_stepChain (C k m d G e₀ : Nat)
    (hB : 2 ≤ Nat.log2 (n + 1)) (hcut : 2 * C ≤ Nat.log2 (n + 1))
    (hm : m ≤ C * Nat.log2 (n + 1) ^ k) (hd : 1 ≤ d) (hG : 1 ≤ G)
    (hGpoly : G ≤ (n + 1) ^ e₀) (hn : 1 ≤ n)
    (Rel : (Fin n → Bool) → Nat → State w → State w → Prop)
    (h : ∀ (i : Nat) (s t : State w), ∃ a : ACCCircuit n M, WellFormedACC a ∧
      (∀ g, a.layer g ≤ d) ∧ a.gateCount ≤ G ∧ ∀ x, ACCAccepts a x ↔ Rel x i s t)
    (s u : State w) :
    ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d + 2 * (k + 1)) ∧
      a.gateCount ≤ (n + 1) ^ ((2 * w + 2) * (k + 1) + e₀ + 1) ∧
      (∀ x, ACCAccepts a x ↔ StepChain (fun i s t => Rel x i s t) m s u) := by
  obtain ⟨R, hRwf, hRlayer, hRsize, hRsem⟩ := exists_acc_relation_family d G Rel h
  refine ⟨accChainPow (Nat.log2 (n + 1)) (accChainPad R m) d (k + 1) 0 s u,
    wellFormedACC_accChainCollapse _ k m R d hd hRwf hRlayer s u,
    fun g => accChainCollapse_layer_le _ k m R d hd hRlayer s u g,
    accChainCollapse_gateCount_poly k m R d G e₀ hRsize hG hGpoly hn s u, fun x => ?_⟩
  rw [accAccepts_accChainCollapse (Nat.log2 (n + 1)) C k m hB hcut hm R d hd hRwf hRlayer x s u]
  exact stepChain_congr m (fun i _ a b => hRsem i a b x) s u

end AllenderOQ3.Internal
