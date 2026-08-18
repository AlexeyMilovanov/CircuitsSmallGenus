import AllenderOQ3.Internal.LocalDivisor
import AllenderOQ3.Internal.BlockAssembly

/-!
# The marked word semantics of the local divisor (semantic half of S2)

Fix an element `c` of a finite monoid `M` and a word `letter` over `M`.  Call a
position a *mark* when its letter is `c`.  Inside a window `[·, E)` the word
factors as

  `u₀ · c · u₁ · c · … · c · u_k`

with mark-free gaps `uᵢ`, and its product is `u₀ · P · u_k` where `P` is the
value of a product computed in the local divisor `LocalDivisor c`, one derived
letter `c * uᵢ * c` per mark (except the last one of the window).

This file makes that precise for `blockProd`, which is the shape in which the
circuit construction S2 (`monoidWordACCGen_compression`) needs it:

* `nextMarkPos` — the next mark after a position, capped at the window end;
* `derivLetter` — the derived `LocalDivisor c`-valued word of a window;
* `blockProd_derivLetter` — the key identity: between two marks `p ≤ q` of the
  window the ambient product over `[p, q+1)` is the value of the derived
  product over `[p, q)`.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {M : Type} [Monoid M] {n : Nat}

/-! ## The derived letters -/

/-- The derived letter `c * u * c` of the local divisor at `c`. -/
def LocalDivisor.gap {M : Type} [Monoid M] (c u : M) : LocalDivisor c :=
  ⟨c * u * c, ⟨u * c, mul_assoc c u c⟩, ⟨c * u, rfl⟩⟩

theorem LocalDivisor.gap_val {M : Type} [Monoid M] (c u : M) :
    (LocalDivisor.gap c u).val = c * u * c := rfl

/-- **Marked factorization** — the algebraic identity behind S2.  A word
`u₀ c u₁ c … c u_k` (marks `c`, gaps `uᵢ`) has product `u₀ · (∏ᵢ c uᵢ c) · u_k`,
where the middle factor is computed in the local divisor `LocalDivisor c`: only
the gaps strictly inside the window contribute derived letters, and the two
outer gaps stay in the ambient monoid. -/
theorem localDivisor_marked_factorization {M : Type} [Monoid M] (c : M) :
    ∀ (us : List (List M)) (u0 uk : List M),
      (List.intercalate [c] (u0 :: (us ++ [uk]))).prod
        = u0.prod * ((us.map (fun u => LocalDivisor.gap c u.prod)).prod).val * uk.prod := by
  intro us
  induction us with
  | nil =>
    intro u0 uk
    simp [List.intercalate, mul_assoc, LocalDivisor.one_val]
  | cons u t ih =>
    intro u0 uk
    have e1 : (List.intercalate [c] (u0 :: ((u :: t) ++ [uk]))).prod
        = u0.prod * c * (List.intercalate [c] (u :: (t ++ [uk]))).prod := by
      simp [List.intercalate, List.intersperse, mul_assoc]
    have e2 := ih u uk
    have e3 : ((LocalDivisor.gap c u.prod * (t.map (fun v => LocalDivisor.gap c v.prod)).prod)).val
        = c * u.prod * ((t.map (fun v => LocalDivisor.gap c v.prod)).prod).val :=
      LocalDivisor.mul_val (by rw [LocalDivisor.gap_val])
    rw [e1, e2]
    simp only [List.map_cons, List.prod_cons, e3]
    simp only [mul_assoc]

/-! ## Small `blockProd` facts -/

/-- A block of trivial letters has trivial product. -/
theorem blockProd_eq_one_of_all_one (f : Nat → (Fin n → Bool) → M) (x : Fin n → Bool)
    {a b : Nat} (h : ∀ i, a ≤ i → i < b → f i x = 1) : blockProd f 0 a b x = 1 := by
  unfold blockProd
  refine List.prod_eq_one ?_
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  rw [List.mem_range'_1] at hi
  exact h i (by omega) (by omega)

/-- A one-letter block. -/
theorem blockProd_single (f : Nat → (Fin n → Bool) → M) (x : Fin n → Bool) (a : Nat) :
    blockProd f 0 a (a + 1) x = f a x := by
  simp [blockProd]

/-- Blocks relative to `start` are blocks in absolute position. -/
theorem blockProd_shift_start (f : Nat → (Fin n → Bool) → M) (x : Fin n → Bool)
    (start a b : Nat) : blockProd f start a b x = blockProd f 0 (start + a) (start + b) x := by
  unfold blockProd
  have h1 : 0 + (start + a) = start + a := by omega
  have h2 : start + b - (start + a) = b - a := by omega
  rw [h1, h2]

/-! ## Marks and derived letters -/

open Classical in
/-- The first mark strictly after `i` and strictly below the window end `E`;
`E` if there is none. -/
noncomputable def nextMarkPos (c : M) (letter : Nat → (Fin n → Bool) → M)
    (x : Fin n → Bool) (E i : Nat) : Nat :=
  if h : ∃ j, i < j ∧ j < E ∧ letter j x = c then Nat.find h else E

open Classical in
/-- The derived word of the window `[·, E)`: a mark with a further mark inside
the window contributes the derived letter `c * (gap) * c`, every other position
contributes the identity of `LocalDivisor c`. -/
noncomputable def derivLetter (c : M) (letter : Nat → (Fin n → Bool) → M) (E : Nat) :
    Nat → (Fin n → Bool) → LocalDivisor c := fun i x =>
  if letter i x = c ∧ ∃ j, i < j ∧ j < E ∧ letter j x = c then
    LocalDivisor.gap c (blockProd letter 0 (i + 1) (nextMarkPos c letter x E i) x)
  else 1

theorem derivLetter_of_not_mark (c : M) (letter : Nat → (Fin n → Bool) → M) (E i : Nat)
    (x : Fin n → Bool) (h : letter i x ≠ c) : derivLetter c letter E i x = 1 := by
  classical
  simp only [derivLetter]
  rw [if_neg (fun hc : letter i x = c ∧ _ => h hc.1)]

theorem derivLetter_of_no_next (c : M) (letter : Nat → (Fin n → Bool) → M) (E i : Nat)
    (x : Fin n → Bool) (h : ¬ ∃ j, i < j ∧ j < E ∧ letter j x = c) :
    derivLetter c letter E i x = 1 := by
  classical
  simp only [derivLetter]
  rw [if_neg (fun hc : _ ∧ ∃ j, i < j ∧ j < E ∧ letter j x = c => h hc.2)]

theorem derivLetter_of_mark (c : M) (letter : Nat → (Fin n → Bool) → M) (E i : Nat)
    (x : Fin n → Bool) (hi : letter i x = c)
    (hex : ∃ j, i < j ∧ j < E ∧ letter j x = c) :
    derivLetter c letter E i x
      = LocalDivisor.gap c (blockProd letter 0 (i + 1) (nextMarkPos c letter x E i) x) := by
  classical
  simp only [derivLetter]
  rw [if_pos ⟨hi, hex⟩]

omit [Monoid M] in
theorem nextMarkPos_spec (c : M) (letter : Nat → (Fin n → Bool) → M) (x : Fin n → Bool)
    {E i : Nat} (hex : ∃ j, i < j ∧ j < E ∧ letter j x = c) :
    i < nextMarkPos c letter x E i ∧ nextMarkPos c letter x E i < E ∧
      letter (nextMarkPos c letter x E i) x = c ∧
      ∀ j, i < j → j < nextMarkPos c letter x E i → letter j x ≠ c := by
  classical
  have hdef : nextMarkPos c letter x E i = Nat.find hex := by
    simp only [nextMarkPos, dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
  refine ⟨by rw [hdef]; exact h1, by rw [hdef]; exact h2, by rw [hdef]; exact h3, ?_⟩
  intro j hij hjr hjc
  rw [hdef] at hjr
  exact Nat.find_min hex hjr ⟨hij, by omega, hjc⟩

omit [Monoid M] in
theorem nextMarkPos_le (c : M) (letter : Nat → (Fin n → Bool) → M) (x : Fin n → Bool)
    {E i q : Nat} (hiq : i < q) (hqE : q < E) (hq : letter q x = c) :
    nextMarkPos c letter x E i ≤ q := by
  classical
  have hex : ∃ j, i < j ∧ j < E ∧ letter j x = c := ⟨q, hiq, hqE, hq⟩
  have hdef : nextMarkPos c letter x E i = Nat.find hex := by
    simp only [nextMarkPos, dif_pos hex]
  rw [hdef]
  exact Nat.find_le ⟨hiq, hqE, hq⟩

/-! ## The key identity -/

/-- **Between two marks the ambient product is the value of the derived
product.**  If `p ≤ q` are marks of the window `[·, E)` then the product of the
letters of `[p, q + 1)` equals the value of the `LocalDivisor c`-product of the
derived letters of `[p, q)`. -/
theorem blockProd_derivLetter (c : M) (letter : Nat → (Fin n → Bool) → M)
    (x : Fin n → Bool) (E : Nat) :
    ∀ d p q : Nat, q - p ≤ d → p ≤ q → q < E → letter p x = c → letter q x = c →
      blockProd letter 0 p (q + 1) x = (blockProd (derivLetter c letter E) 0 p q x).val := by
  intro d
  induction d with
  | zero =>
    intro p q hd hpq _ hp _
    have hpq' : p = q := by omega
    subst hpq'
    rw [blockProd_single, hp]
    have : blockProd (derivLetter c letter E) 0 p p x = 1 := by simp
    rw [this, LocalDivisor.one_val]
  | succ d ih =>
    intro p q hd hpq hqE hp hq
    rcases eq_or_lt_of_le hpq with rfl | hlt
    · rw [blockProd_single, hp]
      have h0 : blockProd (derivLetter c letter E) 0 p p x = 1 := by simp
      rw [h0, LocalDivisor.one_val]
    · have hex : ∃ j, p < j ∧ j < E ∧ letter j x = c := ⟨q, hlt, hqE, hq⟩
      obtain ⟨hpr, hrE, hrc, hnone⟩ := nextMarkPos_spec c letter x hex
      set r := nextMarkPos c letter x E p with hrdef
      have hrq : r ≤ q := nextMarkPos_le c letter x hlt hqE hq
      -- the ambient side
      have hu : blockProd letter 0 p (q + 1) x
          = letter p x * blockProd letter 0 (p + 1) r x * blockProd letter 0 r (q + 1) x := by
        have h1 : blockProd letter 0 p (p + 1) x * blockProd letter 0 (p + 1) r x
            = blockProd letter 0 p r x :=
          blockProd_concat letter 0 x (by omega) (by omega)
        have h2 : blockProd letter 0 p r x * blockProd letter 0 r (q + 1) x
            = blockProd letter 0 p (q + 1) x :=
          blockProd_concat letter 0 x (by omega) (by omega)
        rw [← h2, ← h1, blockProd_single]
      -- the derived side
      have hd1 : blockProd (derivLetter c letter E) 0 (p + 1) r x = 1 := by
        refine blockProd_eq_one_of_all_one _ x ?_
        intro i hi1 hi2
        exact derivLetter_of_not_mark c letter E i x (hnone i (by omega) hi2)
      have hd2 : blockProd (derivLetter c letter E) 0 p q x
          = derivLetter c letter E p x * blockProd (derivLetter c letter E) 0 r q x := by
        have h1 : blockProd (derivLetter c letter E) 0 p (p + 1) x
              * blockProd (derivLetter c letter E) 0 (p + 1) r x
            = blockProd (derivLetter c letter E) 0 p r x :=
          blockProd_concat _ 0 x (by omega) (by omega)
        have h2 : blockProd (derivLetter c letter E) 0 p r x
              * blockProd (derivLetter c letter E) 0 r q x
            = blockProd (derivLetter c letter E) 0 p q x :=
          blockProd_concat _ 0 x (by omega) (by omega)
        rw [← h2, ← h1, hd1, blockProd_single, mul_one]
      have hdp : derivLetter c letter E p x
          = LocalDivisor.gap c (blockProd letter 0 (p + 1) r x) :=
        derivLetter_of_mark c letter E p x hp hex
      have hIH : blockProd letter 0 r (q + 1) x
          = (blockProd (derivLetter c letter E) 0 r q x).val :=
        ih r q (by omega) hrq hqE hrc hq
      have hval : (derivLetter c letter E p x * blockProd (derivLetter c letter E) 0 r q x).val
          = (c * blockProd letter 0 (p + 1) r x)
              * (blockProd (derivLetter c letter E) 0 r q x).val := by
        refine LocalDivisor.mul_val ?_
        rw [hdp, LocalDivisor.gap_val]
      rw [hu, hd2, hval, hIH, hp]

/-! ## The mark-free letters, and the splitting of a window -/

theorem blockProd_congr (f g : Nat → (Fin n → Bool) → M) (x : Fin n → Bool) {a b : Nat}
    (h : ∀ i, a ≤ i → i < b → f i x = g i x) :
    blockProd f 0 a b x = blockProd g 0 a b x := by
  unfold blockProd
  congr 1
  refine List.map_congr_left ?_
  intro i hi
  rw [List.mem_range'_1] at hi
  exact h i (by omega) (by omega)

theorem blockProd_submonoid_val (N : Submonoid M) (f : Nat → (Fin n → Bool) → N)
    (x : Fin n → Bool) (a b : Nat) :
    ((blockProd f 0 a b x : N) : M) = blockProd (fun i x => ((f i x : N) : M)) 0 a b x := by
  unfold blockProd
  rw [show ((List.map (fun i => f i x) (List.range' (0 + a) (b - a))).prod : M)
      = N.subtype (List.map (fun i => f i x) (List.range' (0 + a) (b - a))).prod from rfl,
    N.subtype.map_list_prod]
  simp [List.map_map, Function.comp_def]

open Classical in
/-- The value of an unmarked letter inside the submonoid `N`: a letter of `N`
that is not the mark `c` is kept, every other value is read as `1`. -/
noncomputable def unmarkedVal (c : M) (N : Submonoid M) (g : M) : N :=
  if h : g ∈ N ∧ g ≠ c then ⟨g, h.1⟩ else 1

/-- The word read inside the submonoid `N`: an unmarked letter of `N` is kept,
every other position is read as `1`. -/
noncomputable def unmarkedLetter (c : M) (N : Submonoid M) (letter : Nat → (Fin n → Bool) → M) :
    Nat → (Fin n → Bool) → N := fun i x => unmarkedVal c N (letter i x)

theorem unmarkedLetter_apply (c : M) (N : Submonoid M) (letter : Nat → (Fin n → Bool) → M)
    (i : Nat) (x : Fin n → Bool) :
    unmarkedLetter c N letter i x = unmarkedVal c N (letter i x) := rfl

theorem unmarkedLetter_val (c : M) (N : Submonoid M) (letter : Nat → (Fin n → Bool) → M)
    (i : Nat) (x : Fin n → Bool) (hmem : letter i x ∈ N) (hmark : letter i x ≠ c) :
    ((unmarkedLetter c N letter i x : N) : M) = letter i x := by
  classical
  simp only [unmarkedLetter, unmarkedVal]
  rw [dif_pos ⟨hmem, hmark⟩]

/-- On a mark-free block the `N`-valued word has the same product as the
ambient word. -/
theorem blockProd_unmarkedLetter (c : M) (N : Submonoid M) (letter : Nat → (Fin n → Bool) → M)
    (x : Fin n → Bool) {p q : Nat} (hmem : ∀ i, letter i x = c ∨ letter i x ∈ N)
    (hfree : ∀ i, p ≤ i → i < q → letter i x ≠ c) :
    ((blockProd (unmarkedLetter c N letter) 0 p q x : N) : M) = blockProd letter 0 p q x := by
  rw [blockProd_submonoid_val]
  refine blockProd_congr _ _ x ?_
  intro i hi1 hi2
  have hmark := hfree i hi1 hi2
  exact unmarkedLetter_val c N letter i x ((hmem i).resolve_left hmark) hmark

/-- **Splitting a window at its first and last mark.**  With `p'` the first
mark and `q'` the last mark of the window `[p, E)`, the product of the window
is the `N`-product of the mark-free prefix, times the value of the derived
`LocalDivisor c`-product of `[p', q')`, times the `N`-product of the mark-free
suffix. -/
theorem blockProd_marked_split (c : M) (N : Submonoid M) (letter : Nat → (Fin n → Bool) → M)
    (x : Fin n → Bool) (hmem : ∀ i, letter i x = c ∨ letter i x ∈ N)
    {p p' q' E : Nat} (hpp : p ≤ p') (hpq : p' ≤ q') (hqE : q' < E)
    (hmarkp : letter p' x = c) (hmarkq : letter q' x = c)
    (hfree1 : ∀ i, p ≤ i → i < p' → letter i x ≠ c)
    (hfree2 : ∀ i, q' < i → i < E → letter i x ≠ c) :
    blockProd letter 0 p E x
      = ((blockProd (unmarkedLetter c N letter) 0 p p' x : N) : M)
        * (blockProd (derivLetter c letter E) 0 p' q' x).val
        * ((blockProd (unmarkedLetter c N letter) 0 (q' + 1) E x : N) : M) := by
  have h1 : blockProd letter 0 p p' x * blockProd letter 0 p' (q' + 1) x
      = blockProd letter 0 p (q' + 1) x :=
    blockProd_concat letter 0 x hpp (by omega)
  have h2 : blockProd letter 0 p (q' + 1) x * blockProd letter 0 (q' + 1) E x
      = blockProd letter 0 p E x :=
    blockProd_concat letter 0 x (by omega) (by omega)
  have hmid : blockProd letter 0 p' (q' + 1) x
      = (blockProd (derivLetter c letter E) 0 p' q' x).val :=
    blockProd_derivLetter c letter x E (q' - p') p' q' le_rfl hpq hqE hmarkp hmarkq
  rw [blockProd_unmarkedLetter c N letter x hmem hfree1,
    blockProd_unmarkedLetter c N letter x hmem (fun i hi1 hi2 => hfree2 i (by omega) hi2),
    ← h2, ← h1, hmid]

end Internal
end AllenderOQ3
