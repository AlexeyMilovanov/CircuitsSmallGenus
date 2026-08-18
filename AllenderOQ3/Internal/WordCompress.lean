import AllenderOQ3.Internal.ACCAssembleWord
import AllenderOQ3.Internal.NonCrossingSemantics

/-!
# Sparse-layer normalisation of the layer word

The route-2 word `outputWord c cert x w` is the product of the layer letters of
*every* layer index below `c.layer c.output`.  Nothing prevents a circuit from
declaring a huge output layer with almost all intermediate layers empty, so the
raw word length is not bounded by the size of the circuit.  This file removes
that slack.

* `zeroTrans w` is the constant-`false` transition; it is a **right zero** of the
  transition monoid (`mul_zeroTrans`), because in this opposite monoid
  multiplication on the right means *later* application.
* `layerTrans_eq_zeroTrans` — an empty target layer produces exactly `zeroTrans`.
* `card_nonempty_layers_le` — an interval of layer indices all of which carry a
  gate is no longer than the gate count.
* `exists_compression_index` — an input-independent split index `k` with at most
  `c.gateCount` layers above it and a degenerate layer at `k` itself.
* `outputWord_compress` — the word factors as a prefix which is either `1` or
  `zeroTrans w`, times a suffix of length at most `c.gateCount`.

So the word problem only has to be solved for words of length at most the size
of the circuit, which is what makes a polynomial-size `ACC` recogniser possible.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)

/-- The constant-`false` transition of the width-`w` transition monoid. -/
noncomputable def zeroTrans (w : Nat) : TransMonoid w := ofConfigMap (fun _ _ => false)

@[simp] theorem runTrans_zeroTrans (s : Config w) :
    runTrans (zeroTrans w) s = fun _ => false := rfl

/-- `zeroTrans` is a right zero: applying it after anything is applying it. -/
theorem mul_zeroTrans (g : TransMonoid w) : g * zeroTrans w = zeroTrans w := by
  refine transMonoid_ext (fun s => ?_)
  simp

/-- A layer with no vertices contributes the constant-`false` letter. -/
theorem layerTrans_eq_zeroTrans (x : Fin n → Bool) (ell : Nat)
    (h : (cert.layerOrder (ell + 1)).entries = []) :
    layerTrans c cert x ell = zeroTrans w := by
  refine transMonoid_ext (fun s => ?_)
  funext j
  have hj : ¬ (j.val < (cert.layerOrder (ell + 1)).entries.length) := by
    simp [h]
  simp only [layerTrans, runTrans_ofConfigMap, layerTransMap, dif_neg hj,
    runTrans_zeroTrans]

/-- An interval of layer indices, each of which carries at least one gate, is no
longer than the total number of gates. -/
theorem card_nonempty_layers_le {a b : Nat}
    (hne : ∀ ell, a ≤ ell → ell < b → ∃ g : Fin c.gateCount, c.layer g = ell) :
    b - a ≤ c.gateCount := by
  classical
  set f : Nat → Fin c.gateCount := fun ell =>
    if h : ∃ g : Fin c.gateCount, c.layer g = ell then h.choose else c.output with hf
  have hfl : ∀ ell, a ≤ ell → ell < b → c.layer (f ell) = ell := by
    intro ell h1 h2
    have hex := hne ell h1 h2
    simp only [hf, dif_pos hex]
    exact hex.choose_spec
  have hcard : (Finset.Ico a b).card ≤ (Finset.univ : Finset (Fin c.gateCount)).card := by
    refine Finset.card_le_card_of_injOn f (fun _ _ => by simp) ?_
    intro u hu v hv huv
    simp only [Finset.coe_Ico, Set.mem_Ico] at hu hv
    have h1 := hfl u hu.1 hu.2
    have h2 := hfl v hv.1 hv.2
    rw [huv, h2] at h1
    exact h1.symm
  simpa [Nat.card_Ico] using hcard

/-- The list of layer letters of `c` on input `x`, up to the output layer. -/
noncomputable def layerWord (x : Fin n → Bool) (w : Nat) : List (TransMonoid w) :=
  (List.range (c.layer c.output)).map (fun i => layerTrans c cert x i)

theorem outputWord_eq_wordEnd_layerWord (x : Fin n → Bool) (w : Nat) :
    outputWord c cert x w = wordEnd (layerWord c cert x w) := rfl

@[simp] theorem layerWord_length (x : Fin n → Bool) (w : Nat) :
    (layerWord c cert x w).length = c.layer c.output := by
  simp [layerWord]

theorem layerWord_getElem? (x : Fin n → Bool) (w : Nat) {i : Nat}
    (hi : i < c.layer c.output) :
    (layerWord c cert x w)[i]? = some (layerTrans c cert x i) := by
  simp [layerWord, hi]

/-- **An input-independent compression index.**  There is a layer index `k` below
the output layer such that at most `c.gateCount` layers lie above it, and such
that layer `k` is either the bottom layer or empty. -/
theorem exists_compression_index :
    ∃ k : Nat, k ≤ c.layer c.output ∧ c.layer c.output - k ≤ c.gateCount ∧
      (k = 0 ∨ (cert.layerOrder k).entries = []) := by
  classical
  set L := c.layer c.output with hL
  set P : Nat → Prop := fun i => i = 0 ∨ (cert.layerOrder i).entries = [] with hP
  have hP0 : P 0 := Or.inl rfl
  set k := Nat.findGreatest P L with hk
  have hkL : k ≤ L := Nat.findGreatest_le L
  have hPk : P k := Nat.findGreatest_spec (Nat.zero_le L) hP0
  have hgreat : ∀ ell, k < ell → ell ≤ L → ¬ P ell := by
    intro ell h1 h2
    exact Nat.findGreatest_is_greatest h1 h2
  clear_value k
  refine ⟨k, hkL, ?_, hPk⟩
  have hne : ∀ ell, k + 1 ≤ ell → ell < L + 1 → ∃ g : Fin c.gateCount, c.layer g = ell := by
    intro ell h1 h2
    have hnp := hgreat ell (by omega) (by omega)
    have hentries : (cert.layerOrder ell).entries ≠ [] := by
      intro hcon
      exact hnp (Or.inr hcon)
    obtain ⟨v, -⟩ := List.exists_mem_of_ne_nil _ hentries
    exact ⟨v.1, v.2⟩
  have := card_nonempty_layers_le c hne
  omega

/-- The prefix of the layer word cut off at a compression index is degenerate,
and — crucially — the same for every input. -/
theorem prefixEnd_layerWord_of_compression {k : Nat} (hkL : k ≤ c.layer c.output)
    (hk : k = 0 ∨ (cert.layerOrder k).entries = []) (w : Nat) :
    ∃ pre : TransMonoid w, (pre = 1 ∨ pre = zeroTrans w) ∧
      ∀ x : Fin n → Bool, prefixEnd (layerWord c cert x w) k = pre := by
  by_cases hk0 : k = 0
  · exact ⟨1, Or.inl rfl, fun x => by rw [hk0, prefixEnd_zero]⟩
  · obtain ⟨k', rfl⟩ : ∃ k' : Nat, k = k' + 1 := ⟨k - 1, by omega⟩
    have hk'L : k' < c.layer c.output := by omega
    have hentries : (cert.layerOrder (k' + 1)).entries = [] := by
      rcases hk with h | h
      · exact absurd h (by omega)
      · exact h
    refine ⟨zeroTrans w, Or.inr rfl, fun x => ?_⟩
    have hletter : layerTrans c cert x k' = zeroTrans w :=
      layerTrans_eq_zeroTrans c cert x k' hentries
    rw [prefixEnd_succ, layerWord_getElem? c cert x w hk'L]
    simp only [Option.toList_some, wordEnd_cons, wordEnd_nil, mul_one, hletter]
    exact mul_zeroTrans _

/-- The layer word splits at any index into its prefix and its suffix. -/
theorem outputWord_split (x : Fin n → Bool) (w k : Nat) :
    outputWord c cert x w
      = prefixEnd (layerWord c cert x w) k * wordEnd ((layerWord c cert x w).drop k) := by
  rw [outputWord_eq_wordEnd_layerWord, prefixEnd, ← wordEnd_append, List.take_append_drop]

/-- **Sparse-layer normalisation.**  The layer word of a circuit factors as a
degenerate prefix — either the identity or the constant-`false` transition —
times a suffix whose length is at most the number of gates of the circuit. -/
theorem outputWord_compress (x : Fin n → Bool) (w : Nat) :
    ∃ k : Nat, k ≤ c.layer c.output ∧
      ((layerWord c cert x w).drop k).length ≤ c.gateCount ∧
      (prefixEnd (layerWord c cert x w) k = 1 ∨
        prefixEnd (layerWord c cert x w) k = zeroTrans w) ∧
      outputWord c cert x w
        = prefixEnd (layerWord c cert x w) k * wordEnd ((layerWord c cert x w).drop k) := by
  obtain ⟨k, hkL, hlen, hk⟩ := exists_compression_index c cert
  obtain ⟨pre, hpre, hall⟩ := prefixEnd_layerWord_of_compression c cert hkL hk w
  refine ⟨k, hkL, ?_, ?_, outputWord_split c cert x w k⟩
  · simp only [List.length_drop, layerWord_length]
    omega
  · rw [hall x]; exact hpre

end AllenderOQ3.Internal
