import AllenderOQ3.Internal.LayerPath
import AllenderOQ3.Internal.TotalWidth

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# §7.2: the cylindrical core and the width drop of the remainder

For a circuit in which every gate reaches the output (an ancestor-pruned circuit), pick a
computation gate `v` of the earliest active computation layer.  The **core** through `v` is
the set of computation gates lying on a directed path from `v` to the output.

The two facts §7.2 needs are proved here:

* `exists_mem_coreSet_layer` — the core meets every layer between `v` and the output;
* `exists_core_width_lt` — consequently the *remaining* computation gates have computation
  width at most `w - 1` (stated as `card + 1 ≤ w`, which also records `1 ≤ w`).

The core is defined for arbitrary `v` and `o`; the choice of an earliest computation gate is
made inside `exists_core_width_lt`.
-/

variable {n : Nat}

/-- A gate with an incoming edge is a computation gate. -/
theorem isComputation_of_edge {c : ADRCircuit n} (hc : WellFormedADR c)
    {d z : Fin c.gateCount} (he : c.edge d z = true) : (c.kind z).isComputation = true := by
  by_contra hz
  have hz' : (c.kind z).isComputation = false := by
    cases hkind : (c.kind z).isComputation with
    | false => rfl
    | true => exact absurd hkind hz
  obtain ⟨i, b, hib⟩ := isComputation_eq_false (c.kind z) hz'
  rw [hc.2 z ⟨i, b, hib⟩ d] at he
  exact Bool.false_ne_true he

/-- A directed path that does not raise the layer is trivial. -/
theorem edgeReach_eq_of_layer_le {c : ADRCircuit n} (hc : WellFormedADR c)
    {a b : Fin c.gateCount} (h : EdgeReach c a b) (hl : c.layer b ≤ c.layer a) : a = b := by
  rcases Relation.ReflTransGen.cases_tail h with hrefl | ⟨d, hd, hedge⟩
  · exact hrefl.symm
  · exfalso
    have h1 := edgeReach_layer_le hc hd
    have h2 := hc.1 d b hedge
    omega

open Classical in
/-- The **cylindrical core** through `v`: the computation gates lying on a directed path from
`v` to `o`. -/
noncomputable def coreSet (c : ADRCircuit n) (v o : Fin c.gateCount) :
    Finset (Fin c.gateCount) :=
  Finset.univ.filter fun g =>
    (c.kind g).isComputation = true ∧ EdgeReach c v g ∧ EdgeReach c g o

theorem mem_coreSet {c : ADRCircuit n} {v o g : Fin c.gateCount} :
    g ∈ coreSet c v o ↔
      (c.kind g).isComputation = true ∧ EdgeReach c v g ∧ EdgeReach c g o := by
  classical
  simp [coreSet]

/-- The core is closed under moving forward along a directed path towards the output. -/
theorem coreSet_forward {c : ADRCircuit n} (hc : WellFormedADR c) {v o g h : Fin c.gateCount}
    (hg : g ∈ coreSet c v o) (hgh : EdgeReach c g h) (hho : EdgeReach c h o) :
    h ∈ coreSet c v o ∨ h = g := by
  rcases Relation.ReflTransGen.cases_tail hgh with hrefl | ⟨d, hd, hedge⟩
  · exact Or.inr hrefl
  · refine Or.inl (mem_coreSet.mpr ⟨isComputation_of_edge hc hedge, ?_, hho⟩)
    exact Relation.ReflTransGen.trans (mem_coreSet.mp hg).2.1 hgh

/-- **The core meets every layer it spans.**  Every layer between the layer of `v` and the
layer of `o` carries a gate of the core. -/
theorem exists_mem_coreSet_layer {c : ADRCircuit n} (hc : WellFormedADR c)
    {v o : Fin c.gateCount} (hvo : EdgeReach c v o) (hv : (c.kind v).isComputation = true)
    {l : Nat} (hlo : c.layer v ≤ l) (hhi : l ≤ c.layer o) :
    ∃ z ∈ coreSet c v o, c.layer z = l := by
  obtain ⟨z, hvz, hzo, hzl⟩ := edgeReach_meets_layer hc hvo hlo hhi
  refine ⟨z, mem_coreSet.mpr ⟨?_, hvz, hzo⟩, hzl⟩
  rcases Relation.ReflTransGen.cases_tail hvz with hrefl | ⟨d, _, hedge⟩
  · rw [hrefl]; exact hv
  · exact isComputation_of_edge hc hedge

open Classical in
/-- **§7.2 width drop.**  In a circuit where every gate reaches the output, there is a
computation gate `v` such that, at every layer, the computation gates *outside* the core
through `v` number strictly fewer than the computation width `w`. -/
theorem exists_core_width_lt {c : ADRCircuit n} (hc : WellFormedADR c) {w : Nat}
    (hw : ADRHasWidthAtMost c w)
    (hreach : ∀ g : Fin c.gateCount, EdgeReach c g c.output)
    (hex : ∃ g : Fin c.gateCount, (c.kind g).isComputation = true) :
    ∃ v : Fin c.gateCount, (c.kind v).isComputation = true ∧
      ∀ ell : Nat,
        (Finset.univ.filter fun g : Fin c.gateCount =>
          c.layer g = ell ∧ (c.kind g).isComputation = true ∧
            g ∉ coreSet c v c.output).card + 1 ≤ w := by
  classical
  obtain ⟨g₀, hg₀⟩ := hex
  set comps : Finset (Fin c.gateCount) :=
    Finset.univ.filter fun g => (c.kind g).isComputation = true with hcomps
  have hne : comps.Nonempty := ⟨g₀, by simp [hcomps, hg₀]⟩
  obtain ⟨v, hvmem, hvmin⟩ := comps.exists_min_image c.layer hne
  have hv : (c.kind v).isComputation = true := by
    simpa [hcomps] using hvmem
  have hvmin' : ∀ g : Fin c.gateCount, (c.kind g).isComputation = true → c.layer v ≤ c.layer g := by
    intro g hg
    exact hvmin g (by simp [hcomps, hg])
  refine ⟨v, hv, ?_⟩
  intro ell
  -- the full set of computation gates at layer `ell`
  set F : Finset (Fin c.gateCount) :=
    Finset.univ.filter fun g : Fin c.gateCount =>
      c.layer g = ell ∧ (c.kind g).isComputation = true with hF
  set R : Finset (Fin c.gateCount) :=
    Finset.univ.filter fun g : Fin c.gateCount =>
      c.layer g = ell ∧ (c.kind g).isComputation = true ∧
        g ∉ coreSet c v c.output with hR
  have hFw : F.card ≤ w := hw ell
  have hRF : R ⊆ F := by
    intro g hg
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hg.1, hg.2.1⟩
  by_cases hell : c.layer v ≤ ell ∧ ell ≤ c.layer c.output
  · obtain ⟨z, hz, hzl⟩ :=
      exists_mem_coreSet_layer hc (hreach v) hv hell.1 hell.2
    have hzF : z ∈ F := by
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hzl, (mem_coreSet.mp hz).1⟩
    have hzR : z ∉ R := by
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨-, -, hno⟩
      exact hno hz
    have hlt : R.card < F.card :=
      Finset.card_lt_card ⟨hRF, fun hsub => hzR (hsub hzF)⟩
    omega
  · -- no computation gate lives at this layer
    have hRempty : R = ∅ := by
      refine Finset.eq_empty_of_forall_notMem ?_
      intro g hg
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      have h1 : c.layer v ≤ c.layer g := hvmin' g hg.2.1
      have h2 : c.layer g ≤ c.layer c.output := edgeReach_layer_le hc (hreach g)
      exact hell ⟨by omega, by omega⟩
    have hvF : v ∈ Finset.univ.filter fun g : Fin c.gateCount =>
        c.layer g = c.layer v ∧ (c.kind g).isComputation = true := by
      simp [hv]
    have hw1 : 1 ≤ w := by
      have hcard := hw (c.layer v)
      have : 0 < (Finset.univ.filter fun g : Fin c.gateCount =>
          c.layer g = c.layer v ∧ (c.kind g).isComputation = true).card :=
        Finset.card_pos.mpr ⟨v, hvF⟩
      omega
    rw [hRempty]
    simpa using hw1

end AllenderOQ3.Internal
