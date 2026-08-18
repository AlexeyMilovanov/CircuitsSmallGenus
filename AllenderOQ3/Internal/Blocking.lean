import AllenderOQ3.Internal.StateChain

/-!
# Blocking the relation chain (§9)

`AllenderOQ3.Internal.StateChain` reformulates acceptance of a bounded-width
layered circuit as a chain of `c.layer c.output` local one-step relations, and
provides the composition law `reach_add`.

This file performs the *blocking* step of §9: a run of length `B * q` is cut
into `q` consecutive blocks of length `B`, witnessed by a sequence of
intermediate configurations.  Combined with `adrAccepts_iff_reach` this puts
acceptance into exactly the shape the ACC construction needs — an existential
quantifier over a sequence of `q + 1` configurations (an unbounded fan-in `OR`)
of a conjunction of `q` block relations (an unbounded fan-in `AND`).

Main results:

* `reach_blocks` — `Reach idx x i (B * q) s t` iff there is a sequence of
  intermediate configurations linking `s` to `t` by `q` blocks of length `B`;
* `adrAccepts_iff_blocks` — the resulting depth-two description of acceptance.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat}

/-- **Blocking of a run.**  A run of length `B * q` is exactly a sequence of `q`
consecutive runs of length `B`.  The witnessing sequence is indexed by `Nat`
(values beyond `q` are irrelevant), which avoids all `Fin` index arithmetic. -/
theorem reach_blocks {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (B : Nat) : ∀ (q i : Nat) (s t : State w),
      Reach idx x i (B * q) s t ↔
        ∃ seq : Nat → State w, seq 0 = s ∧ seq q = t ∧
          ∀ j < q, Reach idx x (i + B * j) B (seq j) (seq (j + 1)) := by
  intro q
  induction q with
  | zero =>
      intro i s t
      simp only [Nat.mul_zero, reach_zero]
      constructor
      · rintro rfl
        exact ⟨fun _ => s, rfl, rfl, by omega⟩
      · rintro ⟨seq, h0, hq, -⟩
        rw [← h0, hq]
  | succ q ih =>
      intro i s t
      have hmul : B * (q + 1) = B * q + B := by ring
      rw [hmul, reach_add]
      constructor
      · rintro ⟨u, hsu, hut⟩
        obtain ⟨seq, h0, hq, hstep⟩ := (ih i s u).mp hsu
        refine ⟨fun j => if j ≤ q then seq j else t, by simpa using h0, by simp, ?_⟩
        intro j hj
        rcases Nat.lt_or_ge j q with hjq | hjq
        · have h1 : j ≤ q := Nat.le_of_lt hjq
          have h2 : j + 1 ≤ q := hjq
          simp only [if_pos h1, if_pos h2]
          exact hstep j hjq
        · have hjeq : j = q := by omega
          subst hjeq
          have h2 : ¬ (j + 1 ≤ j) := by omega
          simp only [if_pos (Nat.le_refl j), if_neg h2]
          rw [hq]
          exact hut
      · rintro ⟨seq, h0, hq, hstep⟩
        refine ⟨seq q, ?_, ?_⟩
        · exact (ih i s (seq q)).mpr ⟨seq, h0, rfl, fun j hj => hstep j (by omega)⟩
        · have := hstep q (by omega)
          rwa [hq] at this

/-- **Depth-two description of acceptance.**  When the output layer is a
multiple `B * q` of the block length `B`, the circuit accepts an input exactly
when there is a sequence of `q + 1` configurations starting at the initial
configuration, in which every consecutive pair is linked by a block of `B` local
steps, and whose last configuration has the output slot set.

This is an unbounded fan-in `OR` (over configuration sequences) of an unbounded
fan-in `AND` (over the `q` blocks) of constant-size relations. -/
theorem adrAccepts_iff_blocks {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) (x : Fin n → Bool) {B q : Nat}
    (hlen : c.layer c.output = B * q)
    (h_out_comp : (c.kind c.output).isComputation = true) :
    ADRAccepts c x ↔
      ∃ seq : Nat → State w, InitState idx x (seq 0) ∧
        (∀ j < q, Reach idx x (B * j) B (seq j) (seq (j + 1))) ∧
        seq q (idx.slot c.output) = true := by
  rw [adrAccepts_iff_reach hc idx x h_out_comp]
  constructor
  · rintro ⟨s, t, hinit, hreach, hout⟩
    rw [hlen] at hreach
    obtain ⟨seq, h0, hq, hstep⟩ := (reach_blocks idx x B q 0 s t).mp hreach
    refine ⟨seq, by rw [h0]; exact hinit, ?_, by rw [hq]; exact hout⟩
    intro j hj
    have := hstep j hj
    simpa using this
  · rintro ⟨seq, hinit, hstep, hout⟩
    refine ⟨seq 0, seq q, hinit, ?_, hout⟩
    rw [hlen]
    refine (reach_blocks idx x B q 0 (seq 0) (seq q)).mpr ⟨seq, rfl, rfl, ?_⟩
    intro j hj
    simpa using hstep j hj

end AllenderOQ3.Internal
