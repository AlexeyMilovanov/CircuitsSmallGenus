import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Grouped-word combinatorics for the merging-run argument (T2(c) core)

Pure list lemmas about words that are concatenations of key-indexed blocks
(`T.flatMap inc`).  The centrepiece is `middle_blocks_subset`: in a
duplicate-free grouped word, the segment strictly between an occurrence in
the block of `v1` and an occurrence in the block of `v2` contains the
*complete* blocks of all keys listed strictly between `v1` and `v2`.  This is
the linear heart of the component lemma's merging-run argument (plan 6b,
iteration-31 backlog T2(c)): the intermediate target vertices between two
true witnesses have all their predecessors inside the contiguous source
block, so they evaluate to `true` and merge the two output pieces.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-! ## Unique occurrence in a duplicate-free list -/

/-- In a duplicate-free list, the decomposition around an element is
unique. -/
theorem nodup_middle_eq {β : Type} {X Y X' Y' : List β} {e : β}
    (hnd : (X ++ e :: Y).Nodup) (h : X ++ e :: Y = X' ++ e :: Y') :
    X = X' ∧ Y = Y' := by
  induction X generalizing X' with
  | nil =>
    cases X' with
    | nil =>
      rw [List.nil_append, List.nil_append] at h
      exact ⟨rfl, (List.cons.injEq _ _ _ _ ▸ h).2⟩
    | cons a X'' =>
      rw [List.nil_append, List.cons_append] at h
      obtain ⟨rfl, hY⟩ := List.cons.injEq _ _ _ _ ▸ h
      rw [List.nil_append, List.nodup_cons] at hnd
      exact absurd (by
        rw [hY]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))) hnd.1
  | cons a X ih =>
    cases X' with
    | nil =>
      rw [List.cons_append, List.nil_append] at h
      obtain ⟨rfl, hY⟩ := List.cons.injEq _ _ _ _ ▸ h
      rw [List.cons_append, List.nodup_cons] at hnd
      exact absurd (List.mem_append.mpr (Or.inr (List.mem_cons_self ..))) hnd.1
    | cons b X'' =>
      rw [List.cons_append, List.cons_append] at h
      obtain ⟨rfl, h2⟩ := List.cons.injEq _ _ _ _ ▸ h
      rw [List.cons_append, List.nodup_cons] at hnd
      obtain ⟨hX, hY⟩ := ih hnd.2 h2
      exact ⟨by rw [hX], hY⟩

/-! ## Duplicate-freeness of a grouped word -/

/-- A word grouped along a duplicate-free listing into duplicate-free blocks
with distinct keys is duplicate-free. -/
theorem nodup_flatMap_of_key {α β : Type} (key : β → α) (inc : α → List β)
    (T : List α) (hT : T.Nodup) (hnd : ∀ v, (inc v).Nodup)
    (hkey : ∀ v e, e ∈ inc v → key e = v) :
    (T.flatMap inc).Nodup := by
  induction T with
  | nil => simp
  | cons v T ih =>
    rw [List.flatMap_cons]
    rw [List.nodup_cons] at hT
    refine List.Nodup.append (hnd v) (ih hT.2) ?_
    intro e he1 he2
    rw [List.mem_flatMap] at he2
    obtain ⟨v', hv', he'⟩ := he2
    have h1 : key e = v := hkey v e he1
    have h2 : key e = v' := hkey v' e he'
    exact hT.1 (by rw [h1.symm.trans h2]; exact hv')

/-! ## The merging-run core -/

/-- **The linear merging-run lemma.**  In a duplicate-free grouped word, the
segment strictly between an occurrence `e1` in the block of `v1` and an
occurrence `e2` in the block of `v2` contains the complete block of every
key listed strictly between `v1` and `v2`. -/
theorem middle_blocks_subset {α β : Type} (inc : α → List β)
    {T1 T2 T3 : List α} {v1 v2 : α}
    (hnd : ((T1 ++ v1 :: T2 ++ v2 :: T3).flatMap inc).Nodup)
    {e1 e2 : β} {X M Y : List β}
    (he1 : e1 ∈ inc v1) (he2 : e2 ∈ inc v2)
    (hW : (T1 ++ v1 :: T2 ++ v2 :: T3).flatMap inc = X ++ e1 :: (M ++ e2 :: Y)) :
    ∀ v ∈ T2, ∀ e ∈ inc v, e ∈ M := by
  obtain ⟨A1, B1, hv1⟩ := List.append_of_mem he1
  obtain ⟨A2, B2, hv2⟩ := List.append_of_mem he2
  have hstruct : (T1 ++ v1 :: T2 ++ v2 :: T3).flatMap inc
      = (T1.flatMap inc ++ A1)
        ++ e1 :: (B1 ++ (T2.flatMap inc ++ A2) ++ e2 :: (B2 ++ T3.flatMap inc)) := by
    rw [List.flatMap_append, List.flatMap_cons, List.flatMap_append,
      List.flatMap_cons, hv1, hv2]
    simp only [List.append_assoc, List.cons_append]
  have hnd1 : ((T1.flatMap inc ++ A1)
      ++ e1 :: (B1 ++ (T2.flatMap inc ++ A2) ++ e2 :: (B2 ++ T3.flatMap inc))).Nodup := by
    rw [← hstruct]
    exact hnd
  have hsplit1 := nodup_middle_eq hnd1 (hstruct.symm.trans hW)
  have hnd2 : ((B1 ++ (T2.flatMap inc ++ A2))
      ++ e2 :: (B2 ++ T3.flatMap inc)).Nodup :=
    (List.nodup_cons.mp (List.Nodup.of_append_right hnd1)).2
  have hsplit2 : B1 ++ (T2.flatMap inc ++ A2) = M :=
    (nodup_middle_eq hnd2 hsplit1.2).1
  intro v hv e he
  rw [← hsplit2]
  refine List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl ?_)))
  rw [List.mem_flatMap]
  exact ⟨v, hv, he⟩

/-! ## Rotation invariance of the forward segment -/

/-- **The forward segment between two occurrences is rotation-invariant.**
If both linearizations `p ++ q` and `q ++ p` of a duplicate-free cyclic word
show `e1` strictly before `e2`, the segments between them coincide. -/
theorem rotation_middle_eq {β : Type} {p q : List β} {e1 e2 : β}
    {X M Y X' M' Y' : List β}
    (hnd : (p ++ q).Nodup)
    (h1 : p ++ q = X ++ e1 :: (M ++ e2 :: Y))
    (h2 : q ++ p = X' ++ e1 :: (M' ++ e2 :: Y')) :
    M = M' := by
  have hnd' : (q ++ p).Nodup := (List.perm_append_comm).nodup hnd
  have he1 : e1 ∈ p ++ q := by
    rw [h1]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  rcases List.mem_append.mp he1 with he1p | he1q
  · obtain ⟨a, t, rfl⟩ := List.append_of_mem he1p
    have hW : (a ++ e1 :: t) ++ q = a ++ e1 :: (t ++ q) := by
      simp [List.append_assoc]
    have hs1 := nodup_middle_eq (hW ▸ hnd) (hW.symm.trans h1)
    have hndtq : (t ++ q).Nodup :=
      (List.nodup_cons.mp (List.Nodup.of_append_right (hW ▸ hnd))).2
    have he2 : e2 ∈ t ++ q := by
      rw [hs1.2]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    rcases List.mem_append.mp he2 with he2t | he2q
    · obtain ⟨m, b, rfl⟩ := List.append_of_mem he2t
      have h3 : (m ++ e2 :: b) ++ q = m ++ e2 :: (b ++ q) := by
        simp [List.append_assoc]
      have hs2 := nodup_middle_eq (h3 ▸ hndtq) (h3.symm.trans hs1.2)
      have h4 : q ++ (a ++ e1 :: (m ++ e2 :: b))
          = (q ++ a) ++ e1 :: (m ++ e2 :: b) := by
        simp [List.append_assoc]
      have hs3 := nodup_middle_eq (h4 ▸ hnd') (h4.symm.trans h2)
      have hnd3 : (m ++ e2 :: b).Nodup := List.Nodup.of_append_left hndtq
      have hs4 := nodup_middle_eq hnd3 hs3.2
      exact hs2.1.symm.trans hs4.1
    · obtain ⟨m2, b2, rfl⟩ := List.append_of_mem he2q
      have h4 : (m2 ++ e2 :: b2) ++ (a ++ e1 :: t)
          = ((m2 ++ e2 :: b2) ++ a) ++ e1 :: t := by
        simp [List.append_assoc]
      have hs3 := nodup_middle_eq (h4 ▸ hnd') (h4.symm.trans h2)
      have he2t : e2 ∈ t := by
        rw [hs3.2]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      have hdisj := List.disjoint_of_nodup_append hnd
      exact absurd (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
        (hdisj (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ he2t))))
  · obtain ⟨a, t, rfl⟩ := List.append_of_mem he1q
    have h3 : p ++ (a ++ e1 :: t) = (p ++ a) ++ e1 :: t := by
      simp [List.append_assoc]
    have hs1 := nodup_middle_eq (h3 ▸ hnd) (h3.symm.trans h1)
    have h4 : (a ++ e1 :: t) ++ p = a ++ e1 :: (t ++ p) := by
      simp [List.append_assoc]
    have hs2 := nodup_middle_eq (h4 ▸ hnd') (h4.symm.trans h2)
    have h5 : t ++ p = M ++ e2 :: (Y ++ p) := by
      rw [hs1.2]
      simp [List.append_assoc]
    have hnd4 : (t ++ p).Nodup :=
      (List.nodup_cons.mp (List.Nodup.of_append_right (h4 ▸ hnd'))).2
    exact (nodup_middle_eq (h5 ▸ hnd4) (h5.symm.trans hs2.2)).1


end Internal
end AllenderOQ3
