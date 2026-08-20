import Mathlib.Data.List.TakeWhile
import AllenderOQ3.Internal.DoubleGroupingObstruction
import AllenderOQ3.Internal.IncidenceToolkit

set_option autoImplicit false

/-!
# Contiguous fibres give grouped words

`groupedAlong_contiguous` says that a grouped word has contiguous key-fibres.
This file proves the converse and the two padding lemmas needed to move from
the bare block listing `(w.map key).dedup` to a full cyclic listing of the
vertex type:

* `groupedAlong_dedup_of_contiguous` — a word whose key-fibres are contiguous
  is grouped along the list of its keys in block order;
* `groupedAlong_append_unused`, `groupedAlong_insert_unused` — keys that no
  letter of the word carries may be appended to, or inserted into, the listing;
  their blocks are empty.

Together these reduce a grouping obligation for a concrete word to the single
combinatorial fact that its fibres do not interleave.
-/

namespace AllenderOQ3.Internal

variable {alpha beta : Type}

/-- The contiguity property of `groupedAlong_contiguous`, as a predicate. -/
def KeyContiguous (key : alpha → beta) (w : List alpha) : Prop :=
  ∀ x t y : alpha, [x, t, y].Sublist w → key x = key y → key t = key x

theorem KeyContiguous.sublist {key : alpha → beta} {w v : List alpha}
    (h : KeyContiguous key w) (hv : v.Sublist w) : KeyContiguous key v :=
  fun x t y hsub hxy => h x t y (hsub.trans hv) hxy

def CyclicContiguous (key : alpha → beta) (w : List alpha) : Prop :=
  ∃ w', CyclicRotation w w' ∧ KeyContiguous key w'

/-- Deduplicating a block of equal entries followed by a list avoiding them. -/
theorem dedup_const_append [DecidableEq beta] (s : beta) :
    ∀ (l1 l2 : List beta), l1 ≠ [] → (∀ b ∈ l1, b = s) → s ∉ l2 →
      (l1 ++ l2).dedup = s :: l2.dedup := by
  intro l1
  induction l1 with
  | nil => intro _ h; exact absurd rfl h
  | cons b l1 ih =>
      intro l2 _ hall hs
      have hb : b = s := hall b (by simp)
      subst hb
      cases l1 with
      | nil => simpa using List.dedup_cons_of_notMem hs
      | cons b' l1' =>
          have hmem : b ∈ (b' :: l1') ++ l2 := by
            have : b' = b := hall b' (by simp)
            simp [this]
          rw [List.cons_append, List.dedup_cons_of_mem hmem]
          exact ih l2 (by simp) (fun x hx => hall x (by simp [hx])) hs

/-- The first letter of `dropWhile p` fails `p`. -/
theorem not_of_dropWhile_eq_cons {p : alpha → Bool} :
    ∀ (l tl : List alpha) (t : alpha), l.dropWhile p = t :: tl → p t = false := by
  intro l
  induction l with
  | nil => intro tl t h; simp at h
  | cons a l ih =>
      intro tl t h
      rw [List.dropWhile_cons] at h
      by_cases hp : p a = true
      · rw [if_pos hp] at h
        exact ih tl t h
      · rw [if_neg hp] at h
        obtain ⟨rfl, -⟩ := List.cons.inj h
        exact Bool.eq_false_iff.mpr hp

/-- **Converse of `groupedAlong_contiguous`.**  A word whose key-fibres are
contiguous is grouped along the list of its keys, in block order. -/
theorem groupedAlong_dedup_of_contiguous [DecidableEq beta] (key : alpha → beta) :
    ∀ (bound : Nat) (w : List alpha), w.length ≤ bound → KeyContiguous key w →
      GroupedAlong key ((w.map key).dedup) w := by
  intro bound
  induction bound with
  | zero =>
      intro w hlen _
      have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst this
      rfl
  | succ m ih =>
      intro w hlen hc
      cases w with
      | nil => rfl
      | cons a rest =>
          classical
          obtain ⟨w₁, w₂, hsplit, hne, h1, h2, hlen₂⟩ :
              ∃ w₁ w₂ : List alpha, w₁ ++ w₂ = a :: rest ∧ w₁ ≠ [] ∧
                (∀ z ∈ w₁, key z = key a) ∧ (∀ z ∈ w₂, key z ≠ key a) ∧
                w₂.length ≤ m := by
            refine ⟨a :: rest.takeWhile (fun z => decide (key z = key a)),
              rest.dropWhile (fun z => decide (key z = key a)), ?_, by simp, ?_, ?_, ?_⟩
            · rw [List.cons_append, List.takeWhile_append_dropWhile]
            · intro z hz
              rcases List.mem_cons.mp hz with rfl | hz'
              · rfl
              · simpa using List.mem_takeWhile_imp hz'
            · intro z hz
              cases hw : rest.dropWhile (fun z => decide (key z = key a)) with
              | nil =>
                  rw [hw] at hz
                  exact absurd hz (by simp)
              | cons t tl =>
                  have htkey : key t ≠ key a := by
                    have := not_of_dropWhile_eq_cons rest tl t hw
                    simpa using this
                  rw [hw] at hz
                  rcases List.mem_cons.mp hz with rfl | hz''
                  · exact htkey
                  · intro hzs
                    have hsuf : (t :: tl).Sublist rest := by
                      rw [← hw]
                      exact List.dropWhile_sublist _
                    have hsub : [a, t, z].Sublist (a :: rest) :=
                      List.cons_sublist_cons.mpr
                        ((List.cons_sublist_cons.mpr
                          (List.singleton_sublist.mpr hz'')).trans hsuf)
                    exact htkey (hc a t z hsub hzs.symm)
            · have hle : (rest.dropWhile (fun z => decide (key z = key a))).length
                  ≤ rest.length := (List.dropWhile_sublist _).length_le
              simp only [List.length_cons] at hlen
              omega
          have hsnot : key a ∉ w₂.map key := by
            intro hmem
            obtain ⟨z, hz, hzs⟩ := List.mem_map.mp hmem
            exact h2 z hz hzs
          have hdedup : ((a :: rest).map key).dedup = key a :: ((w₂.map key).dedup) := by
            rw [← hsplit, List.map_append]
            refine dedup_const_append (key a) (w₁.map key) (w₂.map key)
              (by simpa using hne) ?_ hsnot
            intro b hb
            obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hb
            exact h1 z hz
          have hsub₂ : w₂.Sublist (a :: rest) := by
            rw [← hsplit]
            exact List.sublist_append_right w₁ w₂
          rw [hdedup, ← hsplit]
          exact ⟨w₁, w₂, rfl, h1, h2, ih w₂ hlen₂ (hc.sublist hsub₂)⟩

/-- Unused keys may be appended to the listing: their blocks are empty. -/
theorem groupedAlong_append_unused (key : alpha → beta) :
    ∀ (ls extra : List beta) (w : List alpha), GroupedAlong key ls w →
      (∀ e ∈ extra, ∀ a ∈ w, key a ≠ e) → GroupedAlong key (ls ++ extra) w := by
  intro ls
  induction ls with
  | nil =>
      intro extra w hg _
      change w = [] at hg
      subst hg
      simpa using groupedAlong_nil key extra
  | cons s ls ih =>
      rintro extra w ⟨w₁, w₂, rfl, h1, h2, hrec⟩ hsep
      exact ⟨w₁, w₂, rfl, h1, h2, ih extra w₂ hrec
        (fun e he a ha => hsep e he a (List.mem_append_right w₁ ha))⟩

/-- An unused key may be inserted anywhere in the listing. -/
theorem groupedAlong_insert_unused (key : alpha → beta) (e : beta) :
    ∀ (ls1 ls2 : List beta) (w : List alpha), GroupedAlong key (ls1 ++ ls2) w →
      (∀ a ∈ w, key a ≠ e) → GroupedAlong key (ls1 ++ e :: ls2) w := by
  intro ls1
  induction ls1 with
  | nil =>
      intro ls2 w hg hsep
      exact ⟨[], w, rfl, by simp, hsep, hg⟩
  | cons s ls1 ih =>
      rintro ls2 w ⟨w₁, w₂, rfl, h1, h2, hrec⟩ hsep
      exact ⟨w₁, w₂, rfl, h1, h2, ih ls2 w₂ hrec
        (fun a ha => hsep a (List.mem_append_right w₁ ha))⟩

end AllenderOQ3.Internal
