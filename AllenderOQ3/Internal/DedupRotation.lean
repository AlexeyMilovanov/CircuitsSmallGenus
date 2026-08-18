import AllenderOQ3.Internal.ListContiguity

set_option autoImplicit false

/-!
# Deduplicated block words of a cyclic rotation

A word with contiguous key-fibres has one block per key, and the list of its
keys in block order is exactly `(w.map key).dedup`.  Rotating the word rotates
the block order.  This file proves that fact in the form needed to move a
grouping statement across a `CyclicRotation`:

* `dedup_append_filter` — an unconditional splitting of `(l₁ ++ l₂).dedup`;
* `dedup_append_of_contiguous` — for a *contiguous* concatenation the same
  splitting holds with the two sides exchanged;
* `cyclicRotation_dedup_of_contiguous` — hence `(P ++ Q).dedup` and
  `(Q ++ P).dedup` are cyclic rotations of one another whenever `Q ++ P` is
  contiguous;
* `groupedAlong_insert_unused_list` — a list of unused keys may be inserted
  into a listing in one go.

Nothing here mentions circuits: these are list lemmas about `List.dedup`.
-/

namespace AllenderOQ3.Internal

variable {alpha beta : Type}

/-- Contiguity of a list of keys: `KeyContiguous` for the identity key. -/
def SelfContiguous (l : List beta) : Prop :=
  KeyContiguous (fun b : beta => b) l

/-- The key word of a word with contiguous fibres is contiguous. -/
theorem selfContiguous_map (key : alpha → beta) (w : List alpha)
    (h : KeyContiguous key w) : SelfContiguous (w.map key) := by
  intro x t y hsub hxy
  obtain ⟨l', hl', hmap⟩ := List.sublist_map_iff.mp hsub
  match l', hmap with
  | [a, b, d], hmap =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
      obtain ⟨hx, ht, hy⟩ := hmap
      subst hx; subst ht; subst hy
      exact h a b d hl' hxy

/-- Unconditional splitting of the dedup of a concatenation: `List.dedup` keeps
the last occurrence, so the letters of `l₁` that reappear in `l₂` drop out. -/
theorem dedup_append_filter [DecidableEq beta] (l₁ l₂ : List beta) :
    (l₁ ++ l₂).dedup
      = (l₁.filter (fun x => decide (x ∉ l₂))).dedup ++ l₂.dedup := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
      by_cases ha : a ∈ l₂
      · have h1 : a ∈ l₁ ++ l₂ := List.mem_append_right _ ha
        rw [List.cons_append, List.dedup_cons_of_mem h1, ih,
          List.filter_cons_of_neg (by simp [ha])]
      · by_cases hb : a ∈ l₁
        · have h1 : a ∈ l₁ ++ l₂ := List.mem_append_left _ hb
          rw [List.cons_append, List.dedup_cons_of_mem h1, ih,
            List.filter_cons_of_pos (by simp [ha]),
            List.dedup_cons_of_mem (List.mem_filter.mpr ⟨hb, by simp [ha]⟩)]
        · have h1 : a ∉ l₁ ++ l₂ := by simp [ha, hb]
          rw [List.cons_append, List.dedup_cons_of_notMem h1, ih,
            List.filter_cons_of_pos (by simp [ha]),
            List.dedup_cons_of_notMem (fun h => hb (List.mem_filter.mp h).1)]
          rfl

/-- If `s :: P` is contiguous and `s` occurs again in `P`, then `P` starts with
a block of `s`, so its block word starts with `s`. -/
theorem dedup_cons_eq_of_contiguous [DecidableEq beta] (s : beta) :
    ∀ P : List beta, SelfContiguous (s :: P) → s ∈ P →
      P.dedup = s :: (P.filter (fun x => decide (x ≠ s))).dedup := by
  intro P
  induction P with
  | nil => intro _ hs; exact absurd hs (by simp)
  | cons b P ih =>
      intro hc hs
      have hb : b = s := by
        by_contra hbs
        have hsP : s ∈ P := by
          rcases List.mem_cons.mp hs with h | h
          · exact absurd h.symm hbs
          · exact h
        have hsub : [s, b, s].Sublist (s :: b :: P) :=
          List.cons_sublist_cons.mpr
            (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hsP))
        exact hbs (hc s b s hsub rfl)
      subst hb
      have hcb : SelfContiguous (b :: P) :=
        KeyContiguous.sublist hc (List.sublist_cons_self b (b :: P))
      by_cases hbP : b ∈ P
      · rw [List.dedup_cons_of_mem hbP, ih hcb hbP,
          List.filter_cons_of_neg (by simp)]
      · rw [List.dedup_cons_of_notMem hbP, List.filter_cons_of_neg (by simp),
          List.filter_eq_self.mpr (fun a ha => by
            simp only [decide_eq_true_eq]
            rintro rfl
            exact hbP ha)]

/-- **Rotated splitting.**  For a contiguous concatenation the block word of
`Q ++ P` is the block word of `Q` followed by the block word of the letters of
`P` that do not already occur in `Q`. -/
theorem dedup_append_of_contiguous [DecidableEq beta] :
    ∀ Q P : List beta, SelfContiguous (Q ++ P) →
      (Q ++ P).dedup = Q.dedup ++ (P.filter (fun x => decide (x ∉ Q))).dedup := by
  intro Q
  induction Q with
  | nil => intro P _; simp
  | cons a Q ih =>
      intro P hc
      rw [List.cons_append] at hc
      have hc' : SelfContiguous (Q ++ P) :=
        KeyContiguous.sublist hc (List.sublist_cons_self a (Q ++ P))
      by_cases ha : a ∈ Q ++ P
      · rw [List.cons_append, List.dedup_cons_of_mem ha, ih P hc']
        by_cases haQ : a ∈ Q
        · have hfil : P.filter (fun x => decide (x ∉ a :: Q))
              = P.filter (fun x => decide (x ∉ Q)) := by
            refine List.filter_congr (fun x _ => ?_)
            by_cases hxQ : x ∈ Q
            · simp [hxQ]
            · have hxa : x ≠ a := by rintro rfl; exact hxQ haQ
              simp [hxQ, hxa]
          rw [List.dedup_cons_of_mem haQ, hfil]
        · -- `a` occurs only in `P`, so contiguity forces `Q` to be empty
          have haP : a ∈ P := by
            rcases List.mem_append.mp ha with h | h
            · exact absurd h haQ
            · exact h
          have hQnil : Q = [] := by
            cases hQ : Q with
            | nil => rfl
            | cons t Q' =>
                exfalso
                have hsub : [a, t, a].Sublist (a :: (Q ++ P)) := by
                  refine List.cons_sublist_cons.mpr ?_
                  rw [hQ]
                  exact List.Sublist.append
                    (List.singleton_sublist.mpr List.mem_cons_self)
                    (List.singleton_sublist.mpr haP)
                have : t = a := hc a t a hsub rfl
                exact haQ (by rw [hQ, this]; exact List.mem_cons_self)
          subst hQnil
          have hc0 : SelfContiguous (a :: P) := by
            simpa using hc
          have h1 : P.filter (fun x => decide (x ∉ ([] : List beta))) = P :=
            List.filter_eq_self.mpr (by simp)
          have h2 : P.filter (fun x => decide (x ∉ [a]))
              = P.filter (fun x => decide (x ≠ a)) :=
            List.filter_congr (fun x _ => by simp)
          rw [h1, h2, dedup_cons_eq_of_contiguous a P hc0 haP]
          simp
      · have haQ : a ∉ Q := fun h => ha (List.mem_append_left _ h)
        have haP : a ∉ P := fun h => ha (List.mem_append_right _ h)
        rw [List.cons_append, List.dedup_cons_of_notMem ha, ih P hc',
          List.dedup_cons_of_notMem haQ, List.cons_append]
        have hfil : P.filter (fun x => decide (x ∉ a :: Q))
            = P.filter (fun x => decide (x ∉ Q)) := by
          refine List.filter_congr (fun x hx => ?_)
          have hxa : x ≠ a := by rintro rfl; exact haP hx
          simp [hxa]
        rw [hfil]

/-- **Rotating a contiguous word rotates its block word.** -/
theorem cyclicRotation_dedup_of_contiguous [DecidableEq beta] (Q P : List beta)
    (hc : SelfContiguous (Q ++ P)) :
    CyclicRotation (P ++ Q).dedup (Q ++ P).dedup :=
  ⟨(P.filter (fun x => decide (x ∉ Q))).dedup, Q.dedup,
    dedup_append_filter P Q, dedup_append_of_contiguous Q P hc⟩

/-- A whole list of unused keys may be inserted into a listing at once. -/
theorem groupedAlong_insert_unused_list (key : alpha → beta) (w : List alpha) :
    ∀ (extra ls1 ls2 : List beta), GroupedAlong key (ls1 ++ ls2) w →
      (∀ e ∈ extra, ∀ a ∈ w, key a ≠ e) →
      GroupedAlong key (ls1 ++ extra ++ ls2) w := by
  intro extra
  induction extra with
  | nil => intro ls1 ls2 hg _; simpa using hg
  | cons e extra ih =>
      intro ls1 ls2 hg hsep
      have hrec : GroupedAlong key (ls1 ++ extra ++ ls2) w :=
        ih ls1 ls2 hg (fun e' he' => hsep e' (List.mem_cons_of_mem e he'))
      have h := groupedAlong_insert_unused key e ls1 (extra ++ ls2) w
        (by rw [← List.append_assoc]; exact hrec)
        (fun a ha => hsep e List.mem_cons_self a ha)
      simpa [List.append_assoc] using h

end AllenderOQ3.Internal
