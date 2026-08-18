import AllenderOQ3.Internal.NonCrossingShift
import AllenderOQ3.Internal.IntervalPieces
import AllenderOQ3.Internal.OptCircuitInstances
import AllenderOQ3.Internal.GroupedWordLemmas

/-!
# T1.4: cyclic source intervals occupy one contiguous block of the arc word

For a full source layer listing (length exactly `w`), the arcs whose source
coordinates lie in the cyclic interval `[start, start + len)` form one
contiguous block `P` of the common cyclic arc word: some rotation of the
source-major word is `P ++ Q`, where `P` collects exactly the arcs with
sources in the interval (in interval order) and `Q` the others.  Because the
target-major word is a rotation of the source-major word, the same holds
against the target-major grouping.

This is the single-layer geometric fact gating the component and rotation
lemmas (plan 6b/6c, iteration-31 backlog T1.4).

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {n w : Nat} {c : ADRCircuit n} {cert : IncidenceCylinder c}

/-! ## Rotating the coordinate line -/

/-- Rotating `finRange w` by `s` lists the cyclic shifts of `s` in order. -/
theorem rotate_finRange_eq (s : Fin w) :
    (List.finRange w).rotate s.val
      = (List.finRange w).map (fun k => finShift k.val s) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    rw [List.getElem_rotate, List.getElem_map, List.getElem_finRange,
      List.getElem_finRange]
    apply Fin.ext
    rw [finShift_val]
    change (i + s.val) % (List.finRange w).length = (s.val + i) % w
    rw [List.length_finRange, Nat.add_comm i s.val]

/-! ## The source-major arc word -/

/-- Every transition arc occurs in the source-major arc word. -/
theorem mem_srcWord (ell : Nat) (e : TransitionArc c ell) :
    e ∈ (cert.layerOrder ell).entries.flatMap
      ((cert.transitionOrder ell).outgoing) := by
  rw [List.mem_flatMap]
  exact ⟨arcSource e, (cert.layerOrder ell).complete _,
    ((cert.transitionOrder ell).outgoing_exact _ e).mpr rfl⟩

/-- **T1.4.**  The arcs whose sources lie in the cyclic coordinate interval
`[start, start + len)` form one contiguous block of the arc word: a rotation
of the source-major word splits as `P ++ Q` with `P` exactly the arcs from
the interval (grouped along the interval order) and `Q` the rest. -/
theorem exists_arcWord_interval_block (ell : Nat)
    (h1 : (cert.layerOrder ell).entries.length = w)
    (start : Fin w) (len : Nat) (_hlen : len ≤ w) :
    ∃ P Q : List (TransitionArc c ell),
      CyclicRotation
        ((cert.layerOrder ell).entries.flatMap
          ((cert.transitionOrder ell).outgoing))
        (P ++ Q) ∧
      (∀ e ∈ P, ∃ k, k < len ∧
        idxOfVtx c cert ell h1.le (arcSource e) = finShift k start) ∧
      (∀ e ∈ Q, ¬ ∃ k, k < len ∧
        idxOfVtx c cert ell h1.le (arcSource e) = finShift k start) ∧
      (∀ e : TransitionArc c ell,
        (∃ k, k < len ∧
          idxOfVtx c cert ell h1.le (arcSource e) = finShift k start) →
        e ∈ P) := by
  classical
  let f : Fin w → LayerVertex c ell :=
    fun k => vtxAt c cert ell h1 (finShift k.val start)
  let out := (cert.transitionOrder ell).outgoing
  let P := (((List.finRange w).take len).map f).flatMap out
  let Q := (((List.finRange w).drop len).map f).flatMap out
  have hsplit : (List.finRange w).map f
      = ((List.finRange w).take len).map f
        ++ ((List.finRange w).drop len).map f := by
    rw [← List.map_append, List.take_append_drop]
  have hrotL : CyclicRotation ((cert.layerOrder ell).entries)
      ((List.finRange w).map f) := by
    rw [entries_eq_map_vtxAt (cert := cert) ell h1,
      cyclicRotation_iff_isRotated]
    have h4 : ((List.finRange w).rotate start.val).map (vtxAt c cert ell h1)
        = (List.finRange w).map f := by
      rw [rotate_finRange_eq, List.map_map]
      rfl
    rw [← h4]
    exact List.IsRotated.map ⟨start.val, rfl⟩ _
  have hrot : CyclicRotation
      ((cert.layerOrder ell).entries.flatMap
        ((cert.transitionOrder ell).outgoing))
      (P ++ Q) := by
    have h5 := cyclicRotation_flatMap out hrotL
    rw [hsplit, List.flatMap_append] at h5
    exact h5
  have hsrcOf : ∀ (p : Fin w) (e : TransitionArc c ell), e ∈ out (f p) →
      arcSource e = vtxAt c cert ell h1 (finShift p.val start) := by
    intro p e heu
    apply Subtype.ext
    exact ((cert.transitionOrder ell).outgoing_exact _ e).mp heu
  have hP : ∀ e ∈ P, ∃ k, k < len ∧
      idxOfVtx c cert ell h1.le (arcSource e) = finShift k start := by
    intro e he
    rw [List.mem_flatMap] at he
    obtain ⟨u, hu, heu⟩ := he
    rw [List.mem_map] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    refine ⟨p.val, mem_take_finRange hp, ?_⟩
    rw [hsrcOf p e heu, idxOfVtx_vtxAt]
  have hQ : ∀ e ∈ Q, ¬ ∃ k, k < len ∧
      idxOfVtx c cert ell h1.le (arcSource e) = finShift k start := by
    intro e he
    rw [List.mem_flatMap] at he
    obtain ⟨u, hu, heu⟩ := he
    rw [List.mem_map] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    have hpk : len ≤ p.val := mem_drop_finRange hp
    rintro ⟨k, hk, hkeq⟩
    rw [hsrcOf p e heu, idxOfVtx_vtxAt] at hkeq
    have hpe := finShift_amount_inj (a := p.val) (b := k) p.isLt
      (by omega) hkeq
    omega
  refine ⟨P, Q, hrot, hP, hQ, ?_⟩
  intro e hint
  have hmem : e ∈ P ++ Q := mem_of_cyclicRotation hrot (mem_srcWord ell e)
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · exact absurd hint (hQ e h)

/-! ## The cyclic merging run -/

/-- **The cyclic merging-run lemma (word level).**  In a duplicate-free
grouped cyclic word, if a contiguous cyclic segment shows an occurrence in
the block of `v1` strictly before an occurrence in the block of `v2`, then
the listing rotates to `v1 :: T2' ++ v2 :: T3'` and the complete block of
every key of `T2'` lies inside the segment between the two occurrences. -/
theorem cyclic_merging_run {α β : Type} (key : β → α) (inc : α → List β)
    {T : List α} (hT : T.Nodup) (hnd : ∀ v, (inc v).Nodup)
    (hkey : ∀ v e, e ∈ inc v → key e = v)
    {v1 v2 : α} (hv1 : v1 ∈ T) (hv2 : v2 ∈ T) (hne : v1 ≠ v2)
    {e1 e2 : β} (he1 : e1 ∈ inc v1) (he2 : e2 ∈ inc v2)
    {S1 SM S3 R : List β}
    (hrot : CyclicRotation (T.flatMap inc)
      ((S1 ++ e1 :: (SM ++ e2 :: S3)) ++ R)) :
    ∃ T2' T3' : List α,
      CyclicRotation T (v1 :: T2' ++ v2 :: T3') ∧
      (∀ v ∈ T2', ∀ e ∈ inc v, e ∈ SM) := by
  obtain ⟨Ta, Tb, rfl⟩ := List.append_of_mem hv1
  have hv2' : v2 ∈ Tb ++ Ta := by
    rcases List.mem_append.mp hv2 with h | h
    · exact List.mem_append.mpr (Or.inr h)
    · rcases List.mem_cons.mp h with h' | h'
      · exact absurd h'.symm hne
      · exact List.mem_append.mpr (Or.inl h')
  obtain ⟨T2', T3', hTba⟩ := List.append_of_mem hv2'
  have hrotT : CyclicRotation (Ta ++ v1 :: Tb) (v1 :: T2' ++ v2 :: T3') := by
    refine ⟨Ta, v1 :: Tb, rfl, ?_⟩
    rw [List.cons_append, List.cons_append, hTba]
  have hT1 : (v1 :: T2' ++ v2 :: T3').Nodup :=
    nodup_of_cyclicRotation hrotT hT
  have hndW1 : ((v1 :: T2' ++ v2 :: T3').flatMap inc).Nodup :=
    nodup_flatMap_of_key key inc _ hT1 hnd hkey
  have hrotW1 : CyclicRotation ((Ta ++ v1 :: Tb).flatMap inc)
      ((v1 :: T2' ++ v2 :: T3').flatMap inc) :=
    cyclicRotation_flatMap inc hrotT
  have hrotS : CyclicRotation ((v1 :: T2' ++ v2 :: T3').flatMap inc)
      ((S1 ++ e1 :: (SM ++ e2 :: S3)) ++ R) :=
    cyclicRotation_trans (cyclicRotation_symm hrotW1) hrot
  obtain ⟨pp, qq, hpq1, hpq2⟩ := hrotS
  obtain ⟨A1, B1, hA1⟩ := List.append_of_mem he1
  obtain ⟨A2, B2, hA2⟩ := List.append_of_mem he2
  have hstruct : (v1 :: T2' ++ v2 :: T3').flatMap inc
      = A1 ++ e1 :: (B1 ++ (T2'.flatMap inc ++ A2)
        ++ e2 :: (B2 ++ T3'.flatMap inc)) := by
    rw [List.flatMap_append, List.flatMap_cons, List.flatMap_cons, hA1, hA2]
    simp [List.append_assoc, List.cons_append]
  have hSshape : (S1 ++ e1 :: (SM ++ e2 :: S3)) ++ R
      = S1 ++ e1 :: (SM ++ e2 :: (S3 ++ R)) := by
    simp [List.append_assoc, List.cons_append]
  have hM : B1 ++ (T2'.flatMap inc ++ A2) = SM :=
    rotation_middle_eq (p := pp) (q := qq)
      (by rw [← hpq1]; exact hndW1)
      (hpq1.symm.trans hstruct)
      (hpq2.symm.trans hSshape)
  refine ⟨T2', T3', hrotT, ?_⟩
  intro v hv e he
  rw [← hM]
  refine List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl ?_)))
  rw [List.mem_flatMap]
  exact ⟨v, hv, he⟩


end Internal
end AllenderOQ3
