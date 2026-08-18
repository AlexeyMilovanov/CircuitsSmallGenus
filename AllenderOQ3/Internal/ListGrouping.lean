import AllenderOQ3.Internal.IncidenceToolkit

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# Generic list lemmas for grouped arc words

The incidence certificate of a refined circuit is assembled from words of the form
`l.flatMap wb`, grouped along a layer listing of the form `l.flatMap kb`.  This file
collects the purely combinatorial lemmas used for that: concatenation and `flatMap`
of grouped words, and two reindexing lemmas for `List.range'`.
-/

variable {alpha beta gamma : Type}

/-! ## Building grouped words -/

/-- A word all of whose letters carry the same key is grouped along the singleton listing. -/
theorem groupedAlong_singleton (key : alpha → beta) (s : beta) (w : List alpha)
    (h : ∀ a ∈ w, key a = s) : GroupedAlong key [s] w :=
  ⟨w, [], (List.append_nil w).symm, h, by simp, rfl⟩

/-- Concatenating two grouped words along the concatenated listings. -/
theorem groupedAlong_append (key : alpha → beta) :
    ∀ (ls1 : List beta) {ls2 : List beta} {w1 w2 : List alpha},
      GroupedAlong key ls1 w1 → GroupedAlong key ls2 w2 →
      (∀ a ∈ w2, ∀ s ∈ ls1, key a ≠ s) →
      GroupedAlong key (ls1 ++ ls2) (w1 ++ w2) := by
  intro ls1
  induction ls1 with
  | nil =>
      intro ls2 w1 w2 h1 h2 _
      change w1 = [] at h1
      subst h1
      simpa using h2
  | cons s ls1 ih =>
      rintro ls2 w1 w2 ⟨u1, u2, rfl, hk1, hk2, hrec⟩ h2 hsep
      refine ⟨u1, u2 ++ w2, by simp [List.append_assoc], hk1, ?_, ih hrec h2 ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact hk2 a h
        · exact hsep a h s (by simp)
      · intro a ha t ht
        exact hsep a ha t (by simp [ht])

/-- Blockwise grouping: a word and a listing built by `flatMap` over one and the same
index list are grouped along each other as soon as they are grouped blockwise and
different blocks use different keys. -/
theorem groupedAlong_flatMap_pair (key : alpha → beta) :
    ∀ (l : List gamma) (kb : gamma → List beta) (wb : gamma → List alpha),
      l.Nodup → (∀ x ∈ l, GroupedAlong key (kb x) (wb x)) →
      (∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∀ a ∈ wb y, ∀ s ∈ kb x, key a ≠ s) →
      GroupedAlong key (l.flatMap kb) (l.flatMap wb) := by
  intro l
  induction l with
  | nil => intro kb wb _ _ _; rfl
  | cons x t ih =>
      intro kb wb hnd hblock hsep
      have hx : x ∉ t := (List.nodup_cons.mp hnd).1
      rw [List.flatMap_cons, List.flatMap_cons]
      refine groupedAlong_append key _ (hblock x (by simp))
        (ih kb wb (List.nodup_cons.mp hnd).2 (fun y hy => hblock y (by simp [hy]))
          (fun y hy z hz hyz => hsep y (by simp [hy]) z (by simp [hz]) hyz)) ?_
      intro a ha s hs
      obtain ⟨y, hy, hay⟩ := List.mem_flatMap.mp ha
      refine hsep x (by simp) y (by simp [hy]) ?_ a hay s hs
      rintro rfl
      exact hx hy

/-! ## Nodup -/

/-- A `flatMap` of nodup blocks with pairwise disjoint blocks is nodup. -/
theorem nodup_flatMap_of_ne (l : List gamma) (f : gamma → List alpha) (hl : l.Nodup)
    (hn : ∀ x ∈ l, (f x).Nodup)
    (hd : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∀ a ∈ f x, a ∉ f y) :
    (l.flatMap f).Nodup :=
  List.nodup_flatMap.mpr ⟨hn, hl.imp_of_mem (fun hx hy hne a ha1 ha2 => hd _ hx _ hy hne a ha1 ha2)⟩

/-! ## Reindexing `List.range'` -/

/-- Shifting the index of a `flatMap` over an arithmetic range. -/
theorem flatMap_range'_shift (g : Nat → List alpha) :
    ∀ (m a : Nat), (List.range' (a + 1) m).flatMap g
      = (List.range' a m).flatMap (fun s => g (s + 1)) := by
  intro m
  induction m with
  | zero => intro a; simp
  | succ m ih =>
      intro a
      rw [List.range'_succ, List.range'_succ, List.flatMap_cons, List.flatMap_cons, ih]

/-- A `flatMap` over a list, read off by index over a long enough range. -/
theorem flatMap_range'_getElem? (f : gamma → List alpha) :
    ∀ (L : List gamma) (d : Nat),
      (List.range' 0 (L.length + d)).flatMap
          (fun s => (L[s]?).elim [] f) = L.flatMap f := by
  intro L
  induction L with
  | nil =>
      intro d
      have : ∀ s ∈ List.range' 0 (([] : List gamma).length + d),
          ((([] : List gamma))[s]?).elim [] f = [] := by
        intro s _
        simp
      rw [List.flatMap_congr this, flatMap_const_nil]
      simp
  | cons a L ih =>
      intro d
      have hlen : (a :: L).length + d = (L.length + d) + 1 := by simp [Nat.add_right_comm]
      rw [hlen, List.range'_succ, List.flatMap_cons]
      have h0 : ((a :: L)[0]?).elim [] f = f a := by simp
      rw [h0, flatMap_range'_shift]
      have hstep : ∀ s ∈ List.range' 0 (L.length + d),
          ((a :: L)[s + 1]?).elim [] f = (L[s]?).elim [] f := by
        intro s _
        rw [List.getElem?_cons_succ]
      rw [List.flatMap_congr hstep, ih d, List.flatMap_cons]

end AllenderOQ3.Internal
