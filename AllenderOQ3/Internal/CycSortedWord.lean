import Mathlib.Data.List.TakeWhile
import AllenderOQ3.Base
import AllenderOQ3.Internal.IncidenceToolkit

/-!
# Cyclically source-sorted arc words

Pure list combinatorics behind the general constant-free layer builder
(`CFLayerBuilder.lean`) and the layer surgery (`LayerSurgery.lean`).

A *predecessor assignment* `P : Fin w → List (Fin w)` describes a width-`w`
layer: the target slot `p` reads the source slots `P p`.  Its **target-major
arc word** `arcPairWord P` lists the arcs `(q, p)` grouped by target, targets
in increasing order.

The layer is realisable as a *certified* (non-crossing) layer exactly when the
arc word can also be grouped by source, up to a cyclic rotation of the word —
`CycSortedSrc`.  This file develops:

* the two grouping/sorting bridges to `GroupedAlong` of `IncidenceToolkit`;
* stability of `CycSortedSrc` under deleting arcs (`cycSortedSrc_filter`);
* the **fill lemma** `exists_fill`: a cyclically sorted assignment with at
  least one arc extends to one in which *every* target has an arc, without
  disturbing the targets that already had one.  This is what makes the
  surgered layer constant-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {w : Nat}

/-! ## Arc words of a predecessor assignment -/

/-- The arcs entering target slot `p`, as `(source, target)` pairs. -/
def arcBlock (P : Fin w → List (Fin w)) (p : Fin w) : List (Fin w × Fin w) :=
  (P p).map (fun q => (q, p))

/-- The target-major arc word: targets in increasing order. -/
def arcPairWord (P : Fin w → List (Fin w)) : List (Fin w × Fin w) :=
  (List.finRange w).flatMap (arcBlock P)

/-- The target-major arc word read from target `t` onwards, cyclically. -/
def arcPairWordFrom (t : Nat) (P : Fin w → List (Fin w)) : List (Fin w × Fin w) :=
  ((List.finRange w).drop t ++ (List.finRange w).take t).flatMap (arcBlock P)

/-- A word is sorted by source. -/
def SrcSorted (W : List (Fin w × Fin w)) : Prop :=
  W.Pairwise (fun a b => a.1 ≤ b.1)

/-- A word is *cyclically* sorted by source: some rotation of it is sorted. -/
def CycSortedSrc (W : List (Fin w × Fin w)) : Prop :=
  ∃ A B : List (Fin w × Fin w), W = A ++ B ∧ SrcSorted (B ++ A)

theorem arcPairWord_eq_append_of_split (P : Fin w → List (Fin w)) (t : Nat) :
    arcPairWord P
      = ((List.finRange w).take t).flatMap (arcBlock P)
        ++ ((List.finRange w).drop t).flatMap (arcBlock P) := by
  rw [arcPairWord, ← List.flatMap_append, List.take_append_drop]

/-- A pivot at a target boundary gives cyclic sortedness. -/
theorem cycSortedSrc_of_rot {P : Fin w → List (Fin w)} {t : Nat}
    (h : SrcSorted (arcPairWordFrom t P)) : CycSortedSrc (arcPairWord P) := by
  refine ⟨((List.finRange w).take t).flatMap (arcBlock P),
    ((List.finRange w).drop t).flatMap (arcBlock P),
    arcPairWord_eq_append_of_split P t, ?_⟩
  rw [arcPairWordFrom, List.flatMap_append] at h
  exact h

theorem arcPairWord_nodup (P : Fin w → List (Fin w)) (h : ∀ p, (P p).Nodup) :
    (arcPairWord P).Nodup := by
  rw [arcPairWord, List.nodup_flatMap]
  refine ⟨fun p _ => (h p).map (fun x y hxy => (Prod.mk.inj hxy).1), ?_⟩
  refine (List.pairwise_lt_finRange w).imp ?_
  intro a b hab e he he'
  obtain ⟨q, -, hq⟩ := List.mem_map.mp he
  obtain ⟨q', -, hq'⟩ := List.mem_map.mp he'
  have h1 : e.2 = a := by rw [← hq]
  have h2 : e.2 = b := by rw [← hq']
  exact absurd (h1 ▸ h2) (Nat.ne_of_lt hab ∘ congrArg Fin.val)

/-! ## Deleting arcs -/

theorem arcPairWord_filter (P : Fin w → List (Fin w)) (Q : Fin w → Bool) :
    (arcPairWord P).filter (fun e => Q e.1) = arcPairWord (fun p => (P p).filter Q) := by
  rw [arcPairWord, arcPairWord, List.filter_flatMap]
  refine List.flatMap_congr ?_
  intro p _
  simp [arcBlock, List.filter_map, Function.comp_def]

theorem srcSorted_sublist {W V : List (Fin w × Fin w)} (h : V.Sublist W) (hW : SrcSorted W) :
    SrcSorted V := hW.sublist h

theorem cycSortedSrc_filter {W : List (Fin w × Fin w)} (Q : Fin w × Fin w → Bool)
    (h : CycSortedSrc W) : CycSortedSrc (W.filter Q) := by
  obtain ⟨A, B, rfl, hs⟩ := h
  refine ⟨A.filter Q, B.filter Q, List.filter_append .., ?_⟩
  rw [← List.filter_append]
  exact hs.sublist List.filter_sublist

/-! ## Bridges to `GroupedAlong` -/

theorem mem_of_groupedAlong {α β : Type} (key : α → β) :
    ∀ (ls : List β) (L : List α), GroupedAlong key ls L → ∀ a ∈ L, key a ∈ ls := by
  intro ls
  induction ls with
  | nil =>
    intro L h a ha
    have : L = [] := h
    subst this
    exact absurd ha (List.not_mem_nil)
  | cons s ls ih =>
    rintro L ⟨w₁, w₂, rfl, h1, _, hrec⟩ a ha
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_cons.mpr (Or.inl (h1 a h))
    · exact List.mem_cons.mpr (Or.inr (ih w₂ hrec a h))

/-- Sorted words are grouped along an increasing listing. -/
theorem groupedAlong_of_pairwise_le {α : Type} (key : α → Fin w) :
    ∀ (ls : List (Fin w)) (L : List α), ls.Pairwise (· < ·) → (∀ a ∈ L, key a ∈ ls) →
      L.Pairwise (fun a b => key a ≤ key b) → GroupedAlong key ls L := by
  intro ls
  induction ls with
  | nil =>
    intro L _ hmem _
    change L = []
    cases L with
    | nil => rfl
    | cons a t => exact absurd (hmem a List.mem_cons_self) (List.not_mem_nil)
  | cons s ls ih =>
    intro L hls hmem hpw
    classical
    set p : α → Bool := fun a => decide (key a = s) with hp
    have hsub : (L.dropWhile p).Sublist L := (List.dropWhile_suffix p).sublist
    have hpwD : (L.dropWhile p).Pairwise (fun a b => key a ≤ key b) := hpw.sublist hsub
    have hlt : ∀ t ∈ ls, s < t := (List.pairwise_cons.mp hls).1
    have hne2 : ∀ a ∈ L.dropWhile p, key a ≠ s := by
      intro a ha
      cases hD : L.dropWhile p with
      | nil => rw [hD] at ha; exact absurd ha (List.not_mem_nil)
      | cons h t =>
        have hhead : p h = false := by
          have hx := List.head?_dropWhile_not p L
          rw [hD] at hx
          simpa using hx
        have hkh : key h ≠ s := by simpa [hp] using hhead
        have hhmem : h ∈ L := hsub.mem (by rw [hD]; exact List.mem_cons_self)
        have hs_lt : s < key h := by
          rcases List.mem_cons.mp (hmem h hhmem) with h1 | h1
          · exact absurd h1 hkh
          · exact hlt _ h1
        rw [hD] at ha hpwD
        rcases List.mem_cons.mp ha with rfl | hat
        · exact hkh
        · have hle : key h ≤ key a := (List.pairwise_cons.mp hpwD).1 a hat
          intro hcon
          rw [hcon] at hle
          exact absurd (lt_of_lt_of_le hs_lt hle) (lt_irrefl s)
    refine ⟨L.takeWhile p, L.dropWhile p, (List.takeWhile_append_dropWhile ..).symm, ?_, hne2, ?_⟩
    · intro a ha
      have hpa := List.mem_takeWhile_imp ha
      simpa [hp] using hpa
    · refine ih (L.dropWhile p) (List.pairwise_cons.mp hls).2 ?_ hpwD
      intro a ha
      rcases List.mem_cons.mp (hmem a (hsub.mem ha)) with h1 | h1
      · exact absurd h1 (hne2 a ha)
      · exact h1

/-- Words grouped along an increasing listing are sorted. -/
theorem pairwise_le_of_groupedAlong {α : Type} (key : α → Fin w) :
    ∀ (ls : List (Fin w)) (L : List α), ls.Pairwise (· < ·) → GroupedAlong key ls L →
      L.Pairwise (fun a b => key a ≤ key b) := by
  intro ls
  induction ls with
  | nil =>
    intro L _ h
    have hL : L = [] := h
    subst hL
    exact List.Pairwise.nil
  | cons s ls ih =>
    rintro L hls ⟨w₁, w₂, rfl, h1, _, hrec⟩
    have hlt : ∀ t ∈ ls, s < t := (List.pairwise_cons.mp hls).1
    have hkey2 : ∀ a ∈ w₂, s < key a := fun a ha =>
      hlt _ (mem_of_groupedAlong key ls w₂ hrec a ha)
    refine List.pairwise_append.mpr
      ⟨List.pairwise_of_forall_mem_list (fun a ha b hb => ?_),
        ih w₂ (List.pairwise_cons.mp hls).2 hrec, ?_⟩
    · rw [h1 a ha, h1 b hb]
    · intro a ha b hb
      rw [h1 a ha]
      exact le_of_lt (hkey2 b hb)

/-- Extra keys may be appended to the listing of a grouped word. -/
theorem groupedAlong_append_right {α β : Type} (key : α → β) :
    ∀ (ls ms : List β) (L : List α), GroupedAlong key ls L → GroupedAlong key (ls ++ ms) L := by
  intro ls
  induction ls with
  | nil =>
    intro ms L h
    have hL : L = [] := h
    subst hL
    simpa using groupedAlong_nil key ms
  | cons s ls ih =>
    rintro ms L ⟨w₁, w₂, rfl, h1, h2, hrec⟩
    exact ⟨w₁, w₂, rfl, h1, h2, ih ms w₂ hrec⟩

/-! ## Updating a predecessor assignment -/

theorem arcBlock_update_of_ne (P : Fin w → List (Fin w)) (t : Fin w) (v : List (Fin w))
    {q : Fin w} (h : q ≠ t) : arcBlock (Function.update P t v) q = arcBlock P q := by
  rw [arcBlock, arcBlock, Function.update_of_ne h]

theorem arcBlock_update_self (P : Fin w → List (Fin w)) (t : Fin w) (v : List (Fin w)) :
    arcBlock (Function.update P t v) t = v.map (fun q => (q, t)) := by
  rw [arcBlock, Function.update_self]

/-! ## Splitting a block word -/

/-- A split of a concatenation of blocks either falls at a block boundary or
inside a single block. -/
theorem split_flatMap {alpha beta : Type} (f : alpha → List beta) :
    ∀ (l : List alpha) (A B : List beta), l.flatMap f = A ++ B →
      (∃ l₁ l₂, l = l₁ ++ l₂ ∧ A = l₁.flatMap f ∧ B = l₂.flatMap f) ∨
      (∃ l₁ x l₂ C D, l = l₁ ++ x :: l₂ ∧ f x = C ++ D ∧ C ≠ [] ∧ D ≠ [] ∧
        A = l₁.flatMap f ++ C ∧ B = D ++ l₂.flatMap f) := by
  intro l
  induction l with
  | nil =>
    intro A B h
    rw [List.flatMap_nil] at h
    have hA : A = [] := (List.append_eq_nil_iff.mp h.symm).1
    have hB : B = [] := (List.append_eq_nil_iff.mp h.symm).2
    exact Or.inl ⟨[], [], rfl, by simp [hA], by simp [hB]⟩
  | cons x l ih =>
    intro A B h
    rw [List.flatMap_cons] at h
    rcases List.append_eq_append_iff.mp h with ⟨as, hA, htail⟩ | ⟨bs, hfx, hB⟩
    · rcases ih as B htail with ⟨l₁, l₂, hl, hA', hB'⟩
        | ⟨l₁, y, l₂, C, D, hl, hfy, hC, hD, hA', hB'⟩
      · refine Or.inl ⟨x :: l₁, l₂, by rw [hl]; rfl, ?_, hB'⟩
        rw [hA, hA', List.flatMap_cons]
      · refine Or.inr ⟨x :: l₁, y, l₂, C, D, by rw [hl]; rfl, hfy, hC, hD, ?_, hB'⟩
        rw [hA, hA', List.flatMap_cons, List.append_assoc]
    · by_cases hAnil : A = []
      · refine Or.inl ⟨[], x :: l, rfl, by simp [hAnil], ?_⟩
        rw [hB, List.flatMap_cons, hfx, hAnil, List.nil_append]
      · by_cases hbnil : bs = []
        · refine Or.inl ⟨[x], l, rfl, ?_, ?_⟩
          · rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hfx, hbnil,
              List.append_nil]
          · rw [hB, hbnil, List.nil_append]
        · exact Or.inr ⟨[], x, l, A, bs, rfl, hfx, hAnil, hbnil, by simp, hB⟩

/-! ## The fill lemma -/

/-- A nonempty sorted word has a maximal source. -/
theorem exists_max_of_srcSorted : ∀ (V : List (Fin w × Fin w)), SrcSorted V → V ≠ [] →
    ∃ m ∈ V, ∀ e ∈ V, e.1 ≤ m.1 := by
  intro V
  induction V using List.reverseRecOn with
  | nil => intro _ hV; exact absurd rfl hV
  | append_singleton V' m _ =>
    intro h _
    refine ⟨m, List.mem_append_right _ List.mem_cons_self, fun e he => ?_⟩
    rcases List.mem_append.mp he with h1 | h1
    · exact (List.pairwise_append.mp h).2.2 e h1 m List.mem_cons_self
    · rw [List.mem_singleton.mp h1]

/-- **Filling along a cyclic order.**  Along a duplicate-free list of targets
whose arc word is sorted and lies between the bounds `s` and `u`, every empty
target can be given a single predecessor between `s` and `u` while keeping the
word sorted. -/
theorem exists_fill_along (P : Fin w → List (Fin w)) (u : Fin w) :
    ∀ (R : List (Fin w)), R.Nodup → ∀ s : Fin w, s ≤ u →
      SrcSorted (R.flatMap (arcBlock P)) →
      (∀ e ∈ R.flatMap (arcBlock P), s ≤ e.1 ∧ e.1 ≤ u) →
      ∃ P' : Fin w → List (Fin w),
        (∀ q, P q ≠ [] → P' q = P q) ∧
        (∀ q, P' q = P q ∨ ∃ t, s ≤ t ∧ t ≤ u ∧ P' q = [t]) ∧
        (∀ q ∈ R, P' q ≠ []) ∧
        SrcSorted (R.flatMap (arcBlock P')) ∧
        (∀ e ∈ R.flatMap (arcBlock P'), s ≤ e.1 ∧ e.1 ≤ u) := by
  intro R
  induction R with
  | nil =>
    intro _ s _ _ _
    exact ⟨P, fun _ _ => rfl, fun _ => Or.inl rfl, by simp, by simp [SrcSorted], by simp⟩
  | cons p R ih =>
    intro hnd s hs hsorted hbound
    have hpR : p ∉ R := (List.nodup_cons.mp hnd).1
    have hndR : R.Nodup := (List.nodup_cons.mp hnd).2
    rw [List.flatMap_cons] at hsorted hbound
    obtain ⟨hblk, htail, hcross⟩ := List.pairwise_append.mp hsorted
    by_cases hP : P p = []
    · have htailbound : ∀ e ∈ R.flatMap (arcBlock P), s ≤ e.1 ∧ e.1 ≤ u :=
        fun e he => hbound e (List.mem_append_right _ he)
      obtain ⟨P₁, h1, h2, h3, h4, h5⟩ := ih hndR s hs htail htailbound
      have hflat : R.flatMap (arcBlock (Function.update P₁ p [s]))
          = R.flatMap (arcBlock P₁) :=
        List.flatMap_congr (fun q hq =>
          arcBlock_update_of_ne P₁ p [s] (fun hc => hpR (hc ▸ hq)))
      have hblock : arcBlock (Function.update P₁ p [s]) p = [(s, p)] := by
        rw [arcBlock_update_self]; rfl
      refine ⟨Function.update P₁ p [s], ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        have hqp : q ≠ p := by rintro rfl; exact hq hP
        rw [Function.update_of_ne hqp]
        exact h1 q hq
      · intro q
        by_cases hqp : q = p
        · subst hqp
          exact Or.inr ⟨s, le_refl _, hs, by rw [Function.update_self]⟩
        · rw [Function.update_of_ne hqp]
          exact h2 q
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · rw [Function.update_self]; simp
        · have hqp : q ≠ p := by rintro rfl; exact hpR hq'
          rw [Function.update_of_ne hqp]
          exact h3 q hq'
      · rw [List.flatMap_cons, hblock, hflat]
        refine List.pairwise_append.mpr ⟨by simp, h4, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton.mp ha]
        exact (h5 b hb).1
      · intro e he
        rw [List.flatMap_cons, hblock, hflat] at he
        rcases List.mem_append.mp he with h' | h'
        · rw [List.mem_singleton.mp h']
          exact ⟨le_refl _, hs⟩
        · exact h5 e h'
    · have hbne : arcBlock P p ≠ [] := by
        rw [arcBlock]
        exact fun hc => hP (List.map_eq_nil_iff.mp hc)
      obtain ⟨m, hmmem, hmmax⟩ := exists_max_of_srcSorted (arcBlock P p) hblk hbne
      have hmV : m ∈ arcBlock P p ++ R.flatMap (arcBlock P) := List.mem_append_left _ hmmem
      have hsm : s ≤ m.1 := (hbound m hmV).1
      have hmu : m.1 ≤ u := (hbound m hmV).2
      have htailbound : ∀ e ∈ R.flatMap (arcBlock P), m.1 ≤ e.1 ∧ e.1 ≤ u :=
        fun e he => ⟨hcross m hmmem e he, (hbound e (List.mem_append_right _ he)).2⟩
      obtain ⟨P₁, h1, h2, h3, h4, h5⟩ := ih hndR m.1 hmu htail htailbound
      have hblockp : arcBlock P₁ p = arcBlock P p := by rw [arcBlock, arcBlock, h1 p hP]
      refine ⟨P₁, h1, ?_, ?_, ?_, ?_⟩
      · intro q
        rcases h2 q with h | ⟨t, ht1, ht2, ht3⟩
        · exact Or.inl h
        · exact Or.inr ⟨t, le_trans hsm ht1, ht2, ht3⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · rw [h1 q hP]; exact hP
        · exact h3 q hq'
      · rw [List.flatMap_cons, hblockp]
        refine List.pairwise_append.mpr ⟨hblk, h4, ?_⟩
        intro a ha b hb
        exact le_trans (hmmax a ha) (h5 b hb).1
      · intro e he
        rw [List.flatMap_cons, hblockp] at he
        rcases List.mem_append.mp he with h' | h'
        · exact hbound e (List.mem_append_left _ h')
        · exact ⟨le_trans hsm (h5 e h').1, (h5 e h').2⟩

/-- **Filling a cyclically sorted assignment.**  If at least one target has an
incoming arc, the assignment extends to one where every target has one to two
incoming arcs, the targets that already had arcs are untouched, all sources used
are sources that were already used, and cyclic sortedness is preserved. -/
theorem exists_fill (P : Fin w → List (Fin w))
    (hlen : ∀ p, (P p).length ≤ 2) (hnd : ∀ p, (P p).Nodup)
    (hsort : CycSortedSrc (arcPairWord P))
    (hne : ∃ p₀, P p₀ ≠ []) :
    ∃ P' : Fin w → List (Fin w),
      (∀ p, P p ≠ [] → P' p = P p) ∧
      (∀ p, P' p ≠ []) ∧
      (∀ p, (P' p).length ≤ 2) ∧
      (∀ p, (P' p).Nodup) ∧
      CycSortedSrc (arcPairWord P') := by
  classical
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨A, B, hAB, hBA⟩ := hsort
  have hw : 0 < w := lt_of_le_of_lt (Nat.zero_le _) p₀.isLt
  rcases split_flatMap (arcBlock P) (List.finRange w) A B hAB with
    ⟨l₁, l₂, hl, hA, hB⟩ | ⟨l₁, t, l₂, C, D, hl, hbt, hC, hD, hA, hB⟩
  · -- the split falls at a target boundary
    obtain ⟨u, hule⟩ : ∃ u : Fin w, ∀ q : Fin w, q ≤ u := by
      refine ⟨⟨w - 1, by omega⟩, fun q => ?_⟩
      rw [Fin.le_def]
      change q.val ≤ w - 1
      have := q.isLt
      omega
    have hmemR : ∀ q : Fin w, q ∈ l₂ ++ l₁ := by
      intro q
      have hq : q ∈ l₁ ++ l₂ := by rw [← hl]; exact List.mem_finRange q
      rcases List.mem_append.mp hq with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h
    have hndR : (l₂ ++ l₁).Nodup := by
      have h1 : (l₁ ++ l₂).Nodup := by rw [← hl]; exact List.nodup_finRange w
      exact (List.perm_append_comm).nodup_iff.mp h1
    have hV : (l₂ ++ l₁).flatMap (arcBlock P) = B ++ A := by
      rw [List.flatMap_append, hA, hB]
    have hVsorted : SrcSorted ((l₂ ++ l₁).flatMap (arcBlock P)) := by rw [hV]; exact hBA
    have hVne : (l₂ ++ l₁).flatMap (arcBlock P) ≠ [] := by
      intro hcon
      have hb := List.flatMap_eq_nil_iff.mp hcon p₀ (hmemR p₀)
      rw [arcBlock] at hb
      exact hp₀ (List.map_eq_nil_iff.mp hb)
    obtain ⟨e₀, V', hVeq⟩ : ∃ e₀ V', (l₂ ++ l₁).flatMap (arcBlock P) = e₀ :: V' := by
      rcases hh : (l₂ ++ l₁).flatMap (arcBlock P) with _ | ⟨e₀, V'⟩
      · exact absurd hh hVne
      · exact ⟨e₀, V', rfl⟩
    have hVs' : SrcSorted (e₀ :: V') := by rw [← hVeq]; exact hVsorted
    have hbound : ∀ e ∈ (l₂ ++ l₁).flatMap (arcBlock P), e₀.1 ≤ e.1 ∧ e.1 ≤ u := by
      intro e he
      refine ⟨?_, hule _⟩
      rw [hVeq] at he
      rcases List.mem_cons.mp he with rfl | h
      · exact le_refl _
      · exact (List.pairwise_cons.mp hVs').1 e h
    obtain ⟨P', h1, h2, h3, h4, -⟩ :=
      exists_fill_along P u (l₂ ++ l₁) hndR e₀.1 (hule _) hVsorted hbound
    refine ⟨P', h1, fun p => h3 p (hmemR p), ?_, ?_, ?_⟩
    · intro p
      rcases h2 p with h | ⟨tt, -, -, ht⟩
      · rw [h]; exact hlen p
      · rw [ht]; simp
    · intro p
      rcases h2 p with h | ⟨tt, -, -, ht⟩
      · rw [h]; exact hnd p
      · rw [ht]; simp
    · refine ⟨l₁.flatMap (arcBlock P'), l₂.flatMap (arcBlock P'), ?_, ?_⟩
      · rw [arcPairWord, hl, List.flatMap_append]
      · have hsplit : (l₂ ++ l₁).flatMap (arcBlock P')
            = l₂.flatMap (arcBlock P') ++ l₁.flatMap (arcBlock P') := List.flatMap_append ..
        rw [← hsplit]
        exact h4
  · -- the split falls inside the block of the target `t`
    have hPt : (arcBlock P t).length ≤ 2 := by rw [arcBlock, List.length_map]; exact hlen t
    have hlenCD : C.length + D.length ≤ 2 := by
      rw [hbt, List.length_append] at hPt; exact hPt
    have hC1 : C.length = 1 := by
      have h1 : 0 < C.length := List.length_pos_iff.mpr hC
      have h2 : 0 < D.length := List.length_pos_iff.mpr hD
      omega
    have hD1 : D.length = 1 := by
      have h1 : 0 < C.length := List.length_pos_iff.mpr hC
      have h2 : 0 < D.length := List.length_pos_iff.mpr hD
      omega
    obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.mp hC1
    obtain ⟨d0, hd0⟩ := List.length_eq_one_iff.mp hD1
    have hd0mem : d0 ∈ arcBlock P t := by rw [hbt, hd0]; simp
    have hd0t : d0 = (d0.1, t) := by
      rw [arcBlock] at hd0mem
      obtain ⟨q, -, hqe⟩ := List.mem_map.mp hd0mem
      rw [← hqe]
    have hPtne : P t ≠ [] := by
      intro hcon
      have : arcBlock P t = [] := by rw [arcBlock, hcon]; rfl
      rw [hbt, hc0] at this
      exact absurd this (by simp)
    have hndfr : (l₁ ++ t :: l₂).Nodup := by rw [← hl]; exact List.nodup_finRange w
    have hpermR : (t :: (l₂ ++ l₁)).Perm (l₁ ++ t :: l₂) :=
      (List.perm_append_comm.cons t).trans List.perm_middle.symm
    have hndR : (t :: (l₂ ++ l₁)).Nodup := hpermR.nodup_iff.mpr hndfr
    have htnot : t ∉ l₂ ++ l₁ := (List.nodup_cons.mp hndR).1
    have hmemR : ∀ q : Fin w, q ∈ t :: (l₂ ++ l₁) := by
      intro q
      refine hpermR.mem_iff.mpr ?_
      rw [← hl]
      exact List.mem_finRange q
    set P₀ := Function.update P t [d0.1] with hP₀def
    have hP₀ne : ∀ q, q ≠ t → P₀ q = P q := fun q h => Function.update_of_ne h _ _
    have hP₀t : arcBlock P₀ t = [d0] := by
      rw [hP₀def, arcBlock_update_self, List.map_cons, List.map_nil, ← hd0t]
    have hflat0 : (l₂ ++ l₁).flatMap (arcBlock P₀)
        = l₂.flatMap (arcBlock P) ++ l₁.flatMap (arcBlock P) := by
      rw [List.flatMap_append]
      congr 1
      · exact List.flatMap_congr (fun q hq =>
          arcBlock_update_of_ne P t _ (fun hc => htnot (hc ▸ List.mem_append_left _ hq)))
      · exact List.flatMap_congr (fun q hq =>
          arcBlock_update_of_ne P t _ (fun hc => htnot (hc ▸ List.mem_append_right _ hq)))
    have hV₀ : (t :: (l₂ ++ l₁)).flatMap (arcBlock P₀)
        = d0 :: (l₂.flatMap (arcBlock P) ++ l₁.flatMap (arcBlock P)) := by
      rw [List.flatMap_cons, hP₀t, hflat0]
      rfl
    have hBA' : B ++ A = (t :: (l₂ ++ l₁)).flatMap (arcBlock P₀) ++ [c0] := by
      rw [hV₀, hA, hB, hd0, hc0]
      simp [List.append_assoc]
    have hall : SrcSorted ((t :: (l₂ ++ l₁)).flatMap (arcBlock P₀) ++ [c0]) := by
      rw [← hBA']; exact hBA
    obtain ⟨hV₀s, -, hcrossc⟩ := List.pairwise_append.mp hall
    have hub : ∀ e ∈ (t :: (l₂ ++ l₁)).flatMap (arcBlock P₀), e.1 ≤ c0.1 :=
      fun e he => hcrossc e he c0 List.mem_cons_self
    have hlb : ∀ e ∈ (t :: (l₂ ++ l₁)).flatMap (arcBlock P₀), d0.1 ≤ e.1 := by
      intro e he
      rw [hV₀] at he
      rcases List.mem_cons.mp he with rfl | h
      · exact le_refl _
      · have hs : SrcSorted (d0 :: (l₂.flatMap (arcBlock P) ++ l₁.flatMap (arcBlock P))) := by
          rw [← hV₀]; exact hV₀s
        exact (List.pairwise_cons.mp hs).1 e h
    have hsu : d0.1 ≤ c0.1 := hub d0 (by rw [hV₀]; exact List.mem_cons_self)
    obtain ⟨P₀', k1, k2, k3, k4, k5⟩ :=
      exists_fill_along P₀ c0.1 (t :: (l₂ ++ l₁)) hndR d0.1 hsu hV₀s
        (fun e he => ⟨hlb e he, hub e he⟩)
    have hP₀tne : P₀ t ≠ [] := by rw [hP₀def, Function.update_self]; simp
    have hP₀'teq : P₀' t = P₀ t := k1 t hP₀tne
    have hP₀'t : arcBlock P₀' t = [d0] := by
      rw [arcBlock, hP₀'teq, ← arcBlock, hP₀t]
    set P' := Function.update P₀' t (P t) with hP'def
    have hP'ne : ∀ q, q ≠ t → P' q = P₀' q := fun q h => Function.update_of_ne h _ _
    have hP'block : ∀ q, q ≠ t → arcBlock P' q = arcBlock P₀' q :=
      fun q h => arcBlock_update_of_ne P₀' t _ h
    have hP'blockt : arcBlock P' t = [c0, d0] := by
      rw [hP'def, arcBlock_update_self]
      change arcBlock P t = [c0, d0]
      rw [hbt, hc0, hd0]
      rfl
    refine ⟨P', ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      by_cases hqt : q = t
      · subst hqt; rw [hP'def, Function.update_self]
      · rw [hP'ne q hqt, k1 q (by rw [hP₀ne q hqt]; exact hq), hP₀ne q hqt]
    · intro q
      by_cases hqt : q = t
      · subst hqt; rw [hP'def, Function.update_self]; exact hPtne
      · rw [hP'ne q hqt]; exact k3 q (hmemR q)
    · intro q
      by_cases hqt : q = t
      · subst hqt; rw [hP'def, Function.update_self]; exact hlen _
      · rw [hP'ne q hqt]
        rcases k2 q with h | ⟨tt, -, -, ht⟩
        · rw [h, hP₀ne q hqt]; exact hlen q
        · rw [ht]; simp
    · intro q
      by_cases hqt : q = t
      · subst hqt; rw [hP'def, Function.update_self]; exact hnd _
      · rw [hP'ne q hqt]
        rcases k2 q with h | ⟨tt, -, -, ht⟩
        · rw [h, hP₀ne q hqt]; exact hnd q
        · rw [ht]; simp
    · refine ⟨l₁.flatMap (arcBlock P') ++ [c0], d0 :: l₂.flatMap (arcBlock P'), ?_, ?_⟩
      · rw [arcPairWord, hl, List.flatMap_append, List.flatMap_cons, hP'blockt]
        simp [List.append_assoc]
      · have hfl : ∀ (L : List (Fin w)), t ∉ L →
            L.flatMap (arcBlock P') = L.flatMap (arcBlock P₀') := by
          intro L hL
          exact List.flatMap_congr (fun q hq => hP'block q (fun hc => hL (hc ▸ hq)))
        have h1 : t ∉ l₁ := fun hc => htnot (List.mem_append_right _ hc)
        have h2 : t ∉ l₂ := fun hc => htnot (List.mem_append_left _ hc)
        have hword : (d0 :: l₂.flatMap (arcBlock P')) ++ (l₁.flatMap (arcBlock P') ++ [c0])
            = (t :: (l₂ ++ l₁)).flatMap (arcBlock P₀') ++ [c0] := by
          rw [List.flatMap_cons, hP₀'t, List.flatMap_append, hfl l₁ h1, hfl l₂ h2]
          simp [List.append_assoc]
        rw [hword]
        refine List.pairwise_append.mpr ⟨k4, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton.mp hb]
        exact (k5 a ha).2

end AllenderOQ3.Internal
