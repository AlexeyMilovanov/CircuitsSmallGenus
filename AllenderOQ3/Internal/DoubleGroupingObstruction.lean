import AllenderOQ3.Internal.IncidenceToolkit

set_option autoImplicit false

/-!
# One word cannot be grouped along two interleaved partitions

`incidenceCylinder_of_words` builds an incidence certificate from *one* arc word
per transition, grouped both along the source listing and along the target
listing.  This file records the exact obstruction to that shape: a word grouped
along a key has all its key-fibres contiguous (`groupedAlong_contiguous`), and
two interleaved fibre partitions of a four-letter word cannot both be
contiguous (`not_doubleGrouped_crossing_four`).

The relevance for the Hansen assembly is the transition `K_{2,2}`: two sources
`u₁, u₂` and two targets `v₁, v₂` joined by all four arcs, embedded so that the
arc cycle reads `a = u₁v₂, b = u₁v₁, c = u₂v₁, d = u₂v₂`.  Its source fibres
are `{a,b}, {c,d}` and its target fibres are `{b,c}, {a,d}`: interleaved.  Hence
*no* single word for that transition is doubly grouped, whatever cyclic
listings are chosen, and the certificate must be assembled through the
rotation-tolerant constructor `arcOrderCertificate_of_rotatedDoubleGrouped`
(the frozen `ArcOrderCertificate.commonArcWord` only asks for a
`CyclicRotation`, which `K_{2,2}` does satisfy: rotating `a b c d` to
`b c d a` groups the targets).
-/

namespace AllenderOQ3.Internal

variable {alpha beta : Type}

/-- **Fibres of a grouped word are contiguous.**  If two letters of a grouped
word share a key, so does every letter between them. -/
theorem groupedAlong_contiguous (key : alpha → beta) :
    ∀ (ls : List beta) (w : List alpha), GroupedAlong key ls w →
      ∀ x t y : alpha, [x, t, y].Sublist w → key x = key y → key t = key x := by
  intro ls
  induction ls with
  | nil =>
      intro w hw x t y hsub _
      change w = [] at hw
      subst hw
      exact absurd (List.eq_nil_of_sublist_nil hsub) (by simp)
  | cons s ls ih =>
      rintro w ⟨w₁, w₂, rfl, h1, h2, hrec⟩ x t y hsub hxy
      obtain ⟨l₁, l₂, hsplit, hl₁, hl₂⟩ := List.sublist_append_iff.mp hsub
      cases l₁ with
      | nil =>
          rw [List.nil_append] at hsplit
          subst hsplit
          exact ih w₂ hrec x t y hl₂ hxy
      | cons p0 rest =>
          rw [List.cons_append] at hsplit
          obtain ⟨hp0, hsplit1⟩ := List.cons.inj hsplit
          subst hp0
          cases rest with
          | nil =>
              rw [List.nil_append] at hsplit1
              subst hsplit1
              have hx : x ∈ w₁ := hl₁.subset (by simp)
              have hy : y ∈ w₂ := hl₂.subset (by simp)
              exact absurd (hxy ▸ h1 x hx) (h2 y hy)
          | cons p1 rest2 =>
              rw [List.cons_append] at hsplit1
              obtain ⟨hp1, _⟩ := List.cons.inj hsplit1
              subst hp1
              have hx : x ∈ w₁ := hl₁.subset (by simp)
              have ht : t ∈ w₁ := hl₁.subset (by simp)
              rw [h1 t ht, h1 x hx]

/-! ## The interleaved four-arc transition -/

/-- Source key of the four arcs of a `K_{2,2}` transition read in cyclic order:
`a, b` leave the first vertex, `c, d` the second. -/
def crossKeyA : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- Target key of the same four arcs: `b, c` enter the first vertex, `d, a` the
second.  The two fibre partitions interleave. -/
def crossKeyB : Fin 4 → Fin 2 := ![1, 0, 0, 1]

/-- **No doubly grouped word for an interleaved transition.**  With the two
interleaved key partitions above, no listing pair groups one and the same
four-letter word along both keys. -/
theorem not_doubleGrouped_crossing_four
    (w : List (Fin 4)) (lsA lsB : List (Fin 2))
    (hperm : w.Perm [0, 1, 2, 3])
    (hA : GroupedAlong crossKeyA lsA w)
    (hB : GroupedAlong crossKeyB lsB w) : False := by
  have hcA : ∀ x t y : Fin 4, [x, t, y].Sublist w →
      crossKeyA x = crossKeyA y → crossKeyA t = crossKeyA x :=
    groupedAlong_contiguous crossKeyA lsA w hA
  have hcB : ∀ x t y : Fin 4, [x, t, y].Sublist w →
      crossKeyB x = crossKeyB y → crossKeyB t = crossKeyB x :=
    groupedAlong_contiguous crossKeyB lsB w hB
  have hlen : w.length = 4 := by
    rw [hperm.length_eq]
    rfl
  match w, hlen with
  | [x0, x1, x2, x3], _ =>
      have hmem : ∀ z : Fin 4, z ∈ [x0, x1, x2, x3] := by
        intro z
        exact hperm.mem_iff.mpr (by fin_cases z <;> simp)
      clear hA hB hperm
      revert hcA hcB hmem
      revert x0 x1 x2 x3
      decide

end AllenderOQ3.Internal
