import AllenderOQ3.Base
import AllenderOQ3.Incidence

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# Toolkit for finite incidence certificates

Elementary infrastructure for `AllenderOQ3.IncidenceCylinder`, used when building the
refined circuits of §7.4 (N4):

* `CyclicRotation` is exactly Mathlib's `List.IsRotated`, hence an equivalence relation;
* every finite type carries a `CyclicListing`;
* a transition whose source-major and target-major arc words are *equal* (not merely
  rotations of each other) has an `ArcOrderCertificate` — this is the shape every
  transition of the N4 construction has;
* an edge-free circuit is incidence-cylindrical.
-/

/-! ## `CyclicRotation` is `List.IsRotated` -/

theorem cyclicRotation_iff_isRotated {alpha : Type} (xs ys : List alpha) :
    CyclicRotation xs ys ↔ xs ~r ys := by
  constructor
  · rintro ⟨p, q, rfl, rfl⟩
    exact List.isRotated_append
  · intro h
    obtain ⟨k, hk, hrot⟩ := List.isRotated_iff_mod.mp h
    refine ⟨xs.take k, xs.drop k, (List.take_append_drop k xs).symm, ?_⟩
    rw [← hrot, List.rotate_eq_drop_append_take hk]

theorem cyclicRotation_refl {alpha : Type} (xs : List alpha) : CyclicRotation xs xs :=
  ⟨xs, [], by simp, by simp⟩

theorem cyclicRotation_symm {alpha : Type} {xs ys : List alpha} (h : CyclicRotation xs ys) :
    CyclicRotation ys xs := by
  rw [cyclicRotation_iff_isRotated] at h ⊢
  exact h.symm

theorem cyclicRotation_trans {alpha : Type} {xs ys zs : List alpha}
    (h₁ : CyclicRotation xs ys) (h₂ : CyclicRotation ys zs) : CyclicRotation xs zs := by
  rw [cyclicRotation_iff_isRotated] at h₁ h₂ ⊢
  exact h₁.trans h₂

/-- A cyclic rotation of equal lists. -/
theorem cyclicRotation_of_eq {alpha : Type} {xs ys : List alpha} (h : xs = ys) :
    CyclicRotation xs ys := by
  subst h
  exact cyclicRotation_refl xs

/-! ## Listings of finite types -/

/-- Every finite type carries a rooted representative of a cyclic order. -/
noncomputable def cyclicListingOfFintype (alpha : Type) [Fintype alpha] [DecidableEq alpha] :
    CyclicListing alpha where
  entries := (Finset.univ : Finset alpha).toList
  nodup := Finset.nodup_toList _
  complete := fun a => Finset.mem_toList.mpr (Finset.mem_univ a)

/-! ## Certificates from equal arc words -/

/-- If the source-major and the target-major arc words of a transition are literally
equal, the transition has an arc-order certificate. -/
def arcOrderCertificate_of_eq {n : Nat} {c : ADRCircuit n} {ell : Nat}
    {sourceOrder : CyclicListing (LayerVertex c ell)}
    {targetOrder : CyclicListing (LayerVertex c (ell + 1))}
    (outgoing : LayerVertex c ell → List (TransitionArc c ell))
    (incoming : LayerVertex c (ell + 1) → List (TransitionArc c ell))
    (hout : ∀ u, (outgoing u).Nodup) (hinc : ∀ v, (incoming v).Nodup)
    (hout_exact : ∀ u e, e ∈ outgoing u ↔ e.1.1 = u.1)
    (hinc_exact : ∀ v e, e ∈ incoming v ↔ e.1.2 = v.1)
    (heq : sourceOrder.entries.flatMap outgoing = targetOrder.entries.flatMap incoming) :
    ArcOrderCertificate c ell sourceOrder targetOrder where
  outgoing := outgoing
  incoming := incoming
  outgoing_nodup := hout
  incoming_nodup := hinc
  outgoing_exact := hout_exact
  incoming_exact := hinc_exact
  commonArcWord := cyclicRotation_of_eq heq

/-! ## Grouping a word along a listing -/

/-- `GroupedAlong key ls w` says that the word `w` decomposes into consecutive blocks, one
for every entry of `ls` in order, the block of `s` consisting of the elements with
`key = s`.  Empty blocks are allowed.  This is the combinatorial content of "the arc word
is obtained by traversing the vertices in cyclic order and writing each vertex' incidences
as one consecutive block" (`docs/INCIDENCE_REFINEMENT.md`, Lemma 1). -/
def GroupedAlong {alpha beta : Type} (key : alpha → beta) : List beta → List alpha → Prop
  | [], w => w = []
  | s :: ls, w => ∃ w₁ w₂, w = w₁ ++ w₂ ∧ (∀ a ∈ w₁, key a = s) ∧
      (∀ a ∈ w₂, key a ≠ s) ∧ GroupedAlong key ls w₂

/-- Reassembling the blocks of a grouped word returns the word. -/
theorem flatMap_filter_of_groupedAlong {alpha beta : Type} [DecidableEq beta]
    (key : alpha → beta) :
    ∀ (ls : List beta) (w : List alpha), ls.Nodup → GroupedAlong key ls w →
      ls.flatMap (fun s => w.filter (fun a => decide (key a = s))) = w := by
  intro ls
  induction ls with
  | nil => intro w _ hg; simpa using hg.symm
  | cons s ls ih =>
      intro w hnodup hg
      obtain ⟨w₁, w₂, rfl, h1, h2, hrec⟩ := hg
      have hs : s ∉ ls := (List.nodup_cons.mp hnodup).1
      have hls : ls.Nodup := (List.nodup_cons.mp hnodup).2
      have hfirst : (w₁ ++ w₂).filter (fun a => decide (key a = s)) = w₁ := by
        rw [List.filter_append]
        have e1 : w₁.filter (fun a => decide (key a = s)) = w₁ :=
          List.filter_eq_self.mpr (fun a ha => by simp [h1 a ha])
        have e2 : w₂.filter (fun a => decide (key a = s)) = [] :=
          List.filter_eq_nil_iff.mpr (fun a ha => by simp [h2 a ha])
        rw [e1, e2, List.append_nil]
      have hrest : ∀ t ∈ ls, (w₁ ++ w₂).filter (fun a => decide (key a = t))
          = w₂.filter (fun a => decide (key a = t)) := by
        intro t ht
        rw [List.filter_append]
        have e1 : w₁.filter (fun a => decide (key a = t)) = [] := by
          refine List.filter_eq_nil_iff.mpr (fun a ha => ?_)
          have : key a = s := h1 a ha
          simp only [decide_eq_true_eq, this]
          rintro rfl
          exact hs ht
        rw [e1, List.nil_append]
      rw [List.flatMap_cons, hfirst, List.flatMap_congr hrest, ih w₂ hls hrec]

/-- The canonical grouped word: concatenating, in the order of `ls`, blocks whose elements
all carry the corresponding key. -/
theorem groupedAlong_flatMap {alpha beta : Type} (key : alpha → beta) (blocks : beta → List alpha)
    (hkey : ∀ s, ∀ a ∈ blocks s, key a = s) :
    ∀ ls : List beta, ls.Nodup → GroupedAlong key ls (ls.flatMap blocks) := by
  intro ls
  induction ls with
  | nil => intro _; rfl
  | cons s ls ih =>
      intro hnodup
      have hs : s ∉ ls := (List.nodup_cons.mp hnodup).1
      refine ⟨blocks s, ls.flatMap blocks, List.flatMap_cons .., hkey s, ?_,
        ih (List.nodup_cons.mp hnodup).2⟩
      intro a ha
      obtain ⟨t, ht, hat⟩ := List.mem_flatMap.mp ha
      rw [hkey t a hat]
      rintro rfl
      exact hs ht

/-- Grouping is transported along a relabelling of letters and of keys. -/
theorem groupedAlong_map {alpha1 beta1 alpha2 beta2 : Type} (key : alpha1 → beta1)
    (key' : alpha2 → beta2) (f : alpha1 → alpha2) (g : beta1 → beta2)
    (hg : Function.Injective g) (hcomm : ∀ x, key' (f x) = g (key x)) :
    ∀ (ls : List beta1) (w : List alpha1), GroupedAlong key ls w →
      GroupedAlong key' (ls.map g) (w.map f) := by
  intro ls
  induction ls with
  | nil =>
      intro w hw
      change w = [] at hw
      subst hw
      rfl
  | cons s ls ih =>
      rintro w ⟨w₁, w₂, rfl, h1, h2, hrec⟩
      refine ⟨w₁.map f, w₂.map f, by simp, ?_, ?_, ih w₂ hrec⟩
      · intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [hcomm, h1 x hx]
      · intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [hcomm]
        exact fun hc => h2 x hx (hg hc)

/-- The empty word is grouped along any listing. -/
theorem groupedAlong_nil {alpha beta : Type} (key : alpha → beta) :
    ∀ ls : List beta, GroupedAlong key ls ([] : List alpha) := by
  intro ls
  induction ls with
  | nil => rfl
  | cons s ls ih => exact ⟨[], [], rfl, by simp, by simp, ih⟩

/-- Singleton blocks: if the keys of the letters are distinct and occur, in order, inside
the listing, the word is grouped along the listing.  This is the shape of every transition
of the refinement whose targets have exactly one incidence. -/
theorem groupedAlong_of_nodup_map_sublist {alpha beta : Type} (key : alpha → beta) :
    ∀ (ls : List beta) (w : List alpha), ls.Nodup → (w.map key).Sublist ls →
      GroupedAlong key ls w := by
  intro ls
  induction ls with
  | nil =>
      intro w _ hsub
      have hnil : w.map key = [] := List.sublist_nil.mp hsub
      change w = []
      exact List.map_eq_nil_iff.mp hnil
  | cons s ls ih =>
      intro w hnodup hsub
      have hs : s ∉ ls := (List.nodup_cons.mp hnodup).1
      have hls : ls.Nodup := (List.nodup_cons.mp hnodup).2
      cases w with
      | nil => exact groupedAlong_nil key (s :: ls)
      | cons a w =>
          rw [List.map_cons] at hsub
          cases hsub with
          | cons _ h =>
              refine ⟨[], a :: w, rfl, by simp, ?_, ih (a :: w) hls (by simpa using h)⟩
              intro b hb
              have hmem : key b ∈ (a :: w).map key := List.mem_map_of_mem hb
              have hin : key b ∈ ls := h.mem (by simpa using hmem)
              rintro rfl
              exact hs hin
          | cons₂ _ h =>
              refine ⟨[a], w, rfl, by simp, ?_, ih w hls h⟩
              intro b hb
              have hin : key b ∈ ls := h.mem (List.mem_map_of_mem hb)
              intro hc
              exact hs (hc ▸ hin)

/-! ## Certificates from one doubly grouped arc word -/

/-- The source endpoint of a transition arc, as a vertex of the source layer. -/
def arcSource {n : Nat} {c : ADRCircuit n} {ell : Nat} (e : TransitionArc c ell) :
    LayerVertex c ell := ⟨e.1.1, e.2.2.1⟩

/-- The target endpoint of a transition arc, as a vertex of the target layer. -/
def arcTarget {n : Nat} {c : ADRCircuit n} {ell : Nat} (e : TransitionArc c ell) :
    LayerVertex c (ell + 1) := ⟨e.1.2, e.2.2.2⟩

/-- **Lemma 1 of `docs/INCIDENCE_REFINEMENT.md`.**  One word listing every arc of a
transition exactly once, grouped both along the source order and along the target order,
is an arc-order certificate. -/
def arcOrderCertificate_of_doubleGrouped {n : Nat} {c : ADRCircuit n} {ell : Nat}
    {sourceOrder : CyclicListing (LayerVertex c ell)}
    {targetOrder : CyclicListing (LayerVertex c (ell + 1))}
    (word : List (TransitionArc c ell)) (hnodup : word.Nodup)
    (hcomplete : ∀ e, e ∈ word)
    (hS : GroupedAlong arcSource sourceOrder.entries word)
    (hT : GroupedAlong arcTarget targetOrder.entries word) :
    ArcOrderCertificate c ell sourceOrder targetOrder :=
  arcOrderCertificate_of_eq
    (fun u => word.filter (fun e => decide (arcSource e = u)))
    (fun v => word.filter (fun e => decide (arcTarget e = v)))
    (fun _ => hnodup.filter _) (fun _ => hnodup.filter _)
    (fun u e => by
      simp only [List.mem_filter, decide_eq_true_eq, and_iff_right (hcomplete e)]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)
    (fun v e => by
      simp only [List.mem_filter, decide_eq_true_eq, and_iff_right (hcomplete e)]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)
    (by
      rw [flatMap_filter_of_groupedAlong _ _ _ sourceOrder.nodup hS,
        flatMap_filter_of_groupedAlong _ _ _ targetOrder.nodup hT])

/-- Packaging: one doubly grouped arc word per transition makes a circuit
incidence-cylindrical. -/
theorem incidenceCylinder_of_words {n : Nat} {c : ADRCircuit n}
    (order : ∀ ell, CyclicListing (LayerVertex c ell))
    (word : ∀ ell, List (TransitionArc c ell))
    (hnodup : ∀ ell, (word ell).Nodup)
    (hcomplete : ∀ ell (e : TransitionArc c ell), e ∈ word ell)
    (hS : ∀ ell, GroupedAlong arcSource (order ell).entries (word ell))
    (hT : ∀ ell, GroupedAlong arcTarget (order (ell + 1)).entries (word ell)) :
    Nonempty (IncidenceCylinder c) :=
  ⟨{ layerOrder := order
     transitionOrder := fun ell =>
       arcOrderCertificate_of_doubleGrouped (word ell) (hnodup ell) (hcomplete ell)
         (hS ell) (hT ell) }⟩

/-! ## Rotation bookkeeping -/

/-- A rotation of the block listing rotates the concatenated word. -/
theorem cyclicRotation_flatMap {alpha beta : Type} (f : beta → List alpha) {ls ls2 : List beta}
    (h : CyclicRotation ls ls2) :
    CyclicRotation (ls.flatMap f) (ls2.flatMap f) := by
  obtain ⟨p, q, rfl, rfl⟩ := h
  exact ⟨p.flatMap f, q.flatMap f, List.flatMap_append, List.flatMap_append⟩

theorem nodup_of_cyclicRotation {alpha : Type} {xs ys : List alpha}
    (h : CyclicRotation xs ys) (hn : xs.Nodup) : ys.Nodup :=
  (((cyclicRotation_iff_isRotated xs ys).mp h).nodup_iff).mp hn

theorem mem_of_cyclicRotation {alpha : Type} {xs ys : List alpha} {a : alpha}
    (h : CyclicRotation xs ys) (ha : a ∈ xs) : a ∈ ys :=
  (((cyclicRotation_iff_isRotated xs ys).mp h).mem_iff).mp ha

/-- **Lemma 1 up to rotation.**  The two groupings of an arc word need only be along
*rotations* of the two layer listings, and the source-major and the target-major words
need only agree up to rotation.  This is the shape in which a transition of the N4
construction inherits its certificate from the given one. -/
def arcOrderCertificate_of_rotatedDoubleGrouped {n : Nat} {c : ADRCircuit n} {ell : Nat}
    {sourceOrder : CyclicListing (LayerVertex c ell)}
    {targetOrder : CyclicListing (LayerVertex c (ell + 1))}
    (sourceList : List (LayerVertex c ell)) (targetList : List (LayerVertex c (ell + 1)))
    (wordS wordT : List (TransitionArc c ell))
    (hSrot : CyclicRotation sourceOrder.entries sourceList)
    (hTrot : CyclicRotation targetOrder.entries targetList)
    (hword : CyclicRotation wordS wordT)
    (hnodup : wordS.Nodup) (hcomplete : ∀ e, e ∈ wordS)
    (hS : GroupedAlong arcSource sourceList wordS)
    (hT : GroupedAlong arcTarget targetList wordT) :
    ArcOrderCertificate c ell sourceOrder targetOrder := by
  have hnodupT : wordT.Nodup := nodup_of_cyclicRotation hword hnodup
  have hcompleteT : ∀ e, e ∈ wordT := fun e => mem_of_cyclicRotation hword (hcomplete e)
  refine
    { outgoing := fun u => wordS.filter (fun e => decide (arcSource e = u))
      incoming := fun v => wordT.filter (fun e => decide (arcTarget e = v))
      outgoing_nodup := fun _ => hnodup.filter _
      incoming_nodup := fun _ => hnodupT.filter _
      outgoing_exact := fun u e => ?_
      incoming_exact := fun v e => ?_
      commonArcWord := ?_ }
  · simp only [List.mem_filter, decide_eq_true_eq, and_iff_right (hcomplete e)]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · simp only [List.mem_filter, decide_eq_true_eq, and_iff_right (hcompleteT e)]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · have hSnodup : sourceList.Nodup := nodup_of_cyclicRotation hSrot sourceOrder.nodup
    have hTnodup : targetList.Nodup := nodup_of_cyclicRotation hTrot targetOrder.nodup
    have h1 := cyclicRotation_flatMap
      (fun u => wordS.filter (fun e => decide (arcSource e = u))) hSrot
    have h3 := cyclicRotation_flatMap
      (fun v => wordT.filter (fun e => decide (arcTarget e = v))) hTrot
    rw [flatMap_filter_of_groupedAlong arcSource sourceList wordS hSnodup hS] at h1
    rw [flatMap_filter_of_groupedAlong arcTarget targetList wordT hTnodup hT] at h3
    exact cyclicRotation_trans h1 (cyclicRotation_trans hword (cyclicRotation_symm h3))

/-- **Packaging up to rotation.**  One arc word per transition, complete and
duplicate-free, whose source grouping and target grouping are only required to
hold after a cyclic rotation of the word and of the corresponding layer
listing, still makes a circuit incidence-cylindrical.

This is the shape the necklace assembly needs: by
`not_doubleGrouped_crossing_four`, a transition whose source fibres and target
fibres interleave (for instance a planar `K_{2,2}` transition) admits *no*
single word that is grouped along both keys simultaneously, so
`incidenceCylinder_of_words` cannot be used there.  The frozen field
`ArcOrderCertificate.commonArcWord` only asks for a `CyclicRotation`, which is
exactly the slack used here. -/
theorem incidenceCylinder_of_rotatedWords {n : Nat} {c : ADRCircuit n}
    (order : ∀ ell, CyclicListing (LayerVertex c ell))
    (word : ∀ ell, List (TransitionArc c ell))
    (hnodup : ∀ ell, (word ell).Nodup)
    (hcomplete : ∀ ell (e : TransitionArc c ell), e ∈ word ell)
    (hS : ∀ ell, ∃ (sourceList : List (LayerVertex c ell))
        (wordS : List (TransitionArc c ell)),
        CyclicRotation (order ell).entries sourceList ∧
        CyclicRotation (word ell) wordS ∧
        GroupedAlong arcSource sourceList wordS)
    (hT : ∀ ell, ∃ (targetList : List (LayerVertex c (ell + 1)))
        (wordT : List (TransitionArc c ell)),
        CyclicRotation (order (ell + 1)).entries targetList ∧
        CyclicRotation (word ell) wordT ∧
        GroupedAlong arcTarget targetList wordT) :
    Nonempty (IncidenceCylinder c) := by
  classical
  choose sourceList wordS hs1 hs2 hs3 using hS
  choose targetList wordT ht1 ht2 ht3 using hT
  exact ⟨{ layerOrder := order
           transitionOrder := fun ell =>
             arcOrderCertificate_of_rotatedDoubleGrouped (sourceList ell) (targetList ell)
               (wordS ell) (wordT ell) (hs1 ell) (ht1 ell)
               (cyclicRotation_trans (cyclicRotation_symm (hs2 ell)) (ht2 ell))
               (nodup_of_cyclicRotation (hs2 ell) (hnodup ell))
               (fun e => mem_of_cyclicRotation (hs2 ell) (hcomplete ell e))
               (hs3 ell) (ht3 ell) }⟩

/-! ## The edge-free case -/

theorem flatMap_const_nil {alpha beta : Type} (l : List alpha) :
    l.flatMap (fun _ => ([] : List beta)) = [] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- A circuit without edges is incidence-cylindrical: every arc word is empty. -/
theorem incidenceCylinder_of_edgeFree {n : Nat} (c : ADRCircuit n)
    (hedge : ∀ u v, c.edge u v = false) : Nonempty (IncidenceCylinder c) := by
  classical
  have hempty : ∀ ell : Nat, ∀ e : TransitionArc c ell, False := by
    intro ell e
    have := e.2.1
    rw [hedge] at this
    exact Bool.false_ne_true this
  refine ⟨{ layerOrder := fun ell => cyclicListingOfFintype (LayerVertex c ell)
            transitionOrder := fun ell =>
              arcOrderCertificate_of_eq (fun _ => []) (fun _ => []) (fun _ => List.nodup_nil)
                (fun _ => List.nodup_nil) (fun u e => (hempty ell e).elim)
                (fun v e => (hempty ell e).elim) ?_ }⟩
  rw [flatMap_const_nil, flatMap_const_nil]

/-! ## Reading the semantics off a certificate

The incoming list of a certificate enumerates the predecessors of a target vertex without
repetition.  This is what turns the set semantics of an AND/OR gate into the ordered fold
of §3.2 of `docs/INCIDENCE_REFINEMENT.md`, and what bounds the length of a target block by
the fan-in.
-/

section Incoming

variable {n : Nat} {c : ADRCircuit n} {ell : Nat}
  {sourceOrder : CyclicListing (LayerVertex c ell)}
  {targetOrder : CyclicListing (LayerVertex c (ell + 1))}

/-- The transition arc into `v` coming from a predecessor `h`. -/
def incomingArc (hwf : ProperLayered c) (v : LayerVertex c (ell + 1)) {h : Fin c.gateCount}
    (hh : c.edge h v.1 = true) : TransitionArc c ell :=
  ⟨(h, v.1), hh, by
    have h1 := hwf h v.1 hh
    have h2 := v.2
    change c.layer h = ell
    omega, v.2⟩

@[simp] theorem incomingArc_source (hwf : ProperLayered c) (v : LayerVertex c (ell + 1))
    {h : Fin c.gateCount} (hh : c.edge h v.1 = true) :
    (incomingArc hwf v hh).1.1 = h := rfl

@[simp] theorem incomingArc_target (hwf : ProperLayered c) (v : LayerVertex c (ell + 1))
    {h : Fin c.gateCount} (hh : c.edge h v.1 = true) :
    (incomingArc hwf v hh).1.2 = v.1 := rfl

/-- The set semantics of an AND gate, read along the incoming list of a certificate. -/
theorem forall_pred_iff_forall_mem_incoming (hwf : ProperLayered c)
    (cert : ArcOrderCertificate c ell sourceOrder targetOrder)
    (v : LayerVertex c (ell + 1)) (val : Fin c.gateCount → Bool) :
    (∀ h, c.edge h v.1 = true → val h = true)
      ↔ ∀ e ∈ cert.incoming v, val e.1.1 = true := by
  constructor
  · intro H e he
    have htarget : e.1.2 = v.1 := (cert.incoming_exact v e).mp he
    exact H e.1.1 (by rw [← htarget]; exact e.2.1)
  · intro H h hh
    have hmem : incomingArc hwf v hh ∈ cert.incoming v :=
      (cert.incoming_exact v (incomingArc hwf v hh)).mpr rfl
    exact H _ hmem

/-- The set semantics of an OR gate, read along the incoming list of a certificate. -/
theorem exists_pred_iff_exists_mem_incoming (hwf : ProperLayered c)
    (cert : ArcOrderCertificate c ell sourceOrder targetOrder)
    (v : LayerVertex c (ell + 1)) (val : Fin c.gateCount → Bool) :
    (∃ h, c.edge h v.1 = true ∧ val h = true)
      ↔ ∃ e ∈ cert.incoming v, val e.1.1 = true := by
  constructor
  · rintro ⟨h, hh, hv⟩
    exact ⟨incomingArc hwf v hh, (cert.incoming_exact v _).mpr rfl, hv⟩
  · rintro ⟨e, he, hv⟩
    have htarget : e.1.2 = v.1 := (cert.incoming_exact v e).mp he
    exact ⟨e.1.1, by rw [← htarget]; exact e.2.1, hv⟩

/-- The incoming list of a certificate has exactly `predecessorCount` entries: it is the
block whose length the fan-in bound controls. -/
theorem length_incoming_eq_predecessorCount (hwf : ProperLayered c)
    (cert : ArcOrderCertificate c ell sourceOrder targetOrder)
    (v : LayerVertex c (ell + 1)) :
    (cert.incoming v).length = predecessorCount c v.1 := by
  classical
  have hinj : ∀ e ∈ cert.incoming v, ∀ f ∈ cert.incoming v,
      e.1.1 = f.1.1 → e = f := by
    intro e he f hf hef
    have h1 : e.1.2 = v.1 := (cert.incoming_exact v e).mp he
    have h2 : f.1.2 = v.1 := (cert.incoming_exact v f).mp hf
    exact Subtype.ext (Prod.ext hef (by rw [h1, h2]))
  have hmapnodup : ((cert.incoming v).map (fun e => e.1.1)).Nodup :=
    (cert.incoming_nodup v).map_on (fun e he f hf h => hinj e he f hf h)
  have hset : ((cert.incoming v).map (fun e => e.1.1)).toFinset
      = Finset.univ.filter (fun h => c.edge h v.1 = true) := by
    ext h
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨e, he, rfl⟩
      have htarget : e.1.2 = v.1 := (cert.incoming_exact v e).mp he
      rw [← htarget]
      exact e.2.1
    · intro hh
      exact ⟨incomingArc hwf v hh, (cert.incoming_exact v _).mpr rfl, rfl⟩
  calc (cert.incoming v).length
      = ((cert.incoming v).map (fun e => e.1.1)).length := by simp
    _ = ((cert.incoming v).map (fun e => e.1.1)).toFinset.card :=
        (List.toFinset_card_of_nodup hmapnodup).symm
    _ = predecessorCount c v.1 := by rw [hset]; rfl

end Incoming

end AllenderOQ3.Internal
