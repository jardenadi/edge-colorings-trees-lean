# Statements of the formalization (proofs omitted)

Jarden & Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874). Generated from `MyResearchesLLMLean/JardenShami/Section2.lean` … `Section7.lean`, in file order, for a fidelity check against the paper.

* Theorems and lemmas: docstring and full signature, the proof replaced by `:= sorry`. Definitions, structures, classes, instances and abbreviations: docstring and full body. An `omit ... in` line or an attribute before a declaration is kept with it.
* Part A of each section: the paper's definitions and statements (including implicit claims and notation). FACT hypotheses (cited, not proved) are marked by a heading. Part B: the declarations whose docstring starts with `AUX: not in paper`. Declarations without a docstring are listed in Part C.
* Each section starts with its context (`universe`, `variable`, `namespace`, `section`, `open`, `end` lines): `variable` lines add implicit arguments to the statements below them.

| Section | Declarations | Paper (A) | of which FACT | AUX (B) | No docstring (C) |
|---|---|---|---|---|---|
| 2 | 29 | 29 | 0 | 0 | 0 |
| 3 | 14 | 6 | 1 | 8 | 0 |
| 4 | 95 | 42 | 0 | 50 | 3 |
| 5 | 29 | 7 | 1 | 22 | 0 |
| 6 | 25 | 8 | 1 | 15 | 2 |
| 7 | 26 | 9 | 0 | 17 | 0 |
| Total | 218 | 101 | 3 | 112 | 5 |

The FACT column is a subset of the Paper column (218 = 101 + 112 + 5). The 218 declarations are the
lines of the source files that start with `theorem`, `lemma`, `def`, `structure`, `instance`, `abbrev`
or `class`, possibly after an attribute or a modifier: 215 start directly with one of the first six
keywords, 2 start with `@[simp] theorem` (`Kappa.coe_mk`, `Kappa.mk_coe`, Section 4) and 1 is
`class IsTree` (Section 4).

## Section 2 (`Section2.lean`)

### Context

```lean
open Cardinal
universe v w
noncomputable section
namespace JardenShami
section LinearOrder
variable {A : Type w} [LinearOrder A] {D : Type v}
end LinearOrder
section Classes
variable {X : Type w} [LinearOrder X]
end Classes
end JardenShami
```

### A. Paper definitions and statements

#### `Pairs` (def)

```lean
/-- **Definition 2.1** (`[A]^2`). The set of 2-element subsets of `A`, encoded as the
non-diagonal unordered pairs. -/
def Pairs (A : Type w) : Type w := {z : Sym2 A // ¬ z.IsDiag}
```

#### `Pairs.mk` (def)

```lean
/-- The pair `{a, b}` as an element of `[A]^2`, for `a ≠ b`. -/
def Pairs.mk {A : Type w} (a b : A) (h : a ≠ b) : Pairs A :=
  ⟨s(a, b), by simpa [Sym2.mk_isDiag_iff] using h⟩
```

#### `Coloring` (abbrev)

```lean
/-- **Definition 2.1** (Section 2). A coloring (edge coloring) of the set `A` with colors in
the set `D`: a function `C : [A]^2 → D`. It is a coloring with `μ` colors when `#D = μ`. -/
abbrev Coloring (A : Type w) (D : Type v) : Type (max w v) := Pairs A → D
```

#### `Coloring.color` (def)

```lean
/-- **Definition 2.1** (Section 2), notation: for `a < b` in a linearly ordered `A`,
`C(a,b)` stands for `C({a,b})`. -/
def Coloring.color {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) (a b : A)
    (h : a < b) : D :=
  C (Pairs.mk a b h.ne)
```

#### `IsHomogeneous` (def)

```lean
/-- **Definition 2.2** (Section 2). `B ⊆ A` is homogeneous for `C` if `C ↾ [B]^2` is constant,
i.e. any two pairs contained in `B` get the same color. -/
def IsHomogeneous {A : Type w} {D : Type v} (C : Coloring A D) (B : Set A) : Prop :=
  ∀ p q : Pairs A, (∀ x ∈ p.1, x ∈ B) → (∀ x ∈ q.1, x ∈ B) → C p = C q
```

#### `IsAdditive` (def)

```lean
/-- **Definition 2.3** (Section 2, after [Sh42, §1]). `C : [A]^2 → D` is additive if there is
`s : D × D → D` such that `C(a,c) = s(C(a,b), C(b,c))` for all `a < b < c` in `A`. -/
def IsAdditive (C : Coloring A D) : Prop :=
  ∃ s : D × D → D, ∀ (a b c : A) (hab : a < b) (hbc : b < c),
    C.color a c (hab.trans hbc) = s (C.color a b hab, C.color b c hbc)
```

#### `IsLocallyAdditive` (def)

```lean
/-- **Definition 2.4** (Section 2). `C : [A]^2 → D` is locally-additive if for all
`a < b < c < d` in `A`: `C(b,c) = C(b,d) → C(a,c) = C(a,d)`. -/
def IsLocallyAdditive (C : Coloring A D) : Prop :=
  ∀ (a b c d : A) (hab : a < b) (hbc : b < c) (hcd : c < d),
    C.color b c hbc = C.color b d (hbc.trans hcd) →
      C.color a c (hab.trans hbc) = C.color a d ((hab.trans hbc).trans hcd)
```

#### `IsStarLocallyAdditive` (def)

```lean
/-- **Definition 2.6** (Section 2, second sentence). `C` is *-locally additive if it is
locally-additive with respect to the reverse order. The paper states this for colorings of a
cardinal `κ`; here it is stated for any linear order, and for a cardinal one takes
`A = κ.ord.ToType` (see `Kappa`). -/
def IsStarLocallyAdditive (C : Coloring A D) : Prop :=
  IsLocallyAdditive (A := Aᵒᵈ) C
```

#### `Dset` (def)

```lean
/-- **Notation 2.5** (Section 2). `D_b`: the set of colors `t` such that `C(b,c) = t` for some
`c > b`. -/
def Dset (C : Coloring A D) (b : A) : Set D :=
  {t | ∃ (c : A) (h : b < c), C.color b c h = t}
```

#### `uMap` (def)

```lean
/-- **Notation 2.5** (Section 2). For `a < b`, `u_{a,b} : D_b → D`, `u_{a,b}(C(b,c)) = C(a,c)`.
Encoded by choosing, for `t ∈ D_b`, some witness `c > b` with `C(b,c) = t`; the value does not
depend on the choice exactly when `C` is locally additive (see `uMap_wellDefined_iff`). -/
def uMap (C : Coloring A D) (a b : A) (hab : a < b) : Dset C b → D :=
  fun t => C.color a (Classical.choose t.2) (hab.trans (Classical.choose_spec t.2).fst)
```

#### `uMap_color` (theorem)

```lean
/-- **Notation 2.5** (Section 2), the defining equation `u_{a,b}(C(b,c)) = C(a,c)`, for a locally
additive `C` and `a < b < c`. (With the choice-based encoding of `uMap` this is a statement.) -/
theorem uMap_color {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    uMap C a b hab ⟨C.color b c hbc, c, hbc, rfl⟩ = C.color a c (hab.trans hbc) := sorry
```

#### `uMap_wellDefined_iff` (theorem)

```lean
/-- **Note after Notation 2.5** (Section 2, unnumbered). `u_{a,b}` is well-defined for each
`a < b` (i.e. `C(b,c) = C(b,c')` implies `C(a,c) = C(a,c')` for `c, c' > b`) if and only if `C`
is locally additive. -/
theorem uMap_wellDefined_iff (C : Coloring A D) :
    (∀ (a b c c' : A) (hab : a < b) (hbc : b < c) (hbc' : b < c'),
        C.color b c hbc = C.color b c' hbc' →
          C.color a c (hab.trans hbc) = C.color a c' (hab.trans hbc')) ↔
      IsLocallyAdditive C := sorry
```

#### `additive_isLocallyAdditive` (theorem)

```lean
/-- **Remark 2.7** (Section 2). Every additive coloring is locally-additive. -/
theorem additive_isLocallyAdditive {C : Coloring A D} (hC : IsAdditive C) :
    IsLocallyAdditive C := sorry
```

#### `uMap_comp` (theorem)

```lean
/-- **Claim 2.8** (Section 2, `\label{C^* is additive}`). For a locally additive `C` and
`a < b < c`: `u_{a,b} ∘ u_{b,c} = u_{a,c}` as functions on `D_c`. The composition makes sense
because `u_{b,c}` maps `D_c` into `D_b`; this is part of the statement. -/
theorem uMap_comp {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    ∀ t : Dset C c, ∃ h : uMap C b c hbc t ∈ Dset C b,
      uMap C a b hab ⟨uMap C b c hbc t, h⟩ = uMap C a c (hab.trans hbc) t := sorry
```

#### `Kappa` (abbrev)

```lean
/-- **Definition 2.6** (Section 2). A cardinal `κ`, as the set of ordinals below it, with its
`∈`-order. A coloring of `κ` is locally-additive if `IsLocallyAdditive` holds for it as a
coloring of `Kappa κ`, and *-locally additive if `IsStarLocallyAdditive` holds. -/
abbrev Kappa (κ : Cardinal.{w}) : Type w := κ.ord.ToType
```

#### `ColoringClass` (def)

```lean
/-- A class of colorings of subsets of the linearly ordered type `X` (used in Notation 2.9 and
Definition 2.10): a predicate on `(S, D, C)` with `S ⊆ X`, `D` the set of colors and
`C : [S]^2 → D`. `S` carries the order induced from `X`. -/
def ColoringClass (X : Type w) [LinearOrder X] : Type (max w (v + 1)) :=
  ∀ (S : Set X) (D : Type v), Coloring S D → Prop
```

#### `allColorings` (def)

```lean
/-- **Definition 2.10** (Section 2, last sentence): "`μ` for `𝔆`", the class of all colorings
with `μ` colors. -/
def allColorings (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D _ => #D = μ
```

#### `add` (def)

```lean
/-- **Notation 2.9 (1)** (Section 2). `add`: the class of additive colorings. -/
def add : ColoringClass.{v, w} X := fun _ _ C => IsAdditive C
```

#### `addEq` (def)

```lean
/-- **Notation 2.9 (2)** (Section 2). `add_μ`: additive colorings with `μ` colors. -/
def addEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsAdditive C ∧ #D = μ
```

#### `addLt` (def)

```lean
/-- **Notation 2.9 (3)** (Section 2). `add_{<μ}`: additive colorings with fewer than `μ`
colors. -/
def addLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsAdditive C ∧ #D < μ
```

#### `la` (def)

```lean
/-- **Notation 2.9 (4)** (Section 2). `la`: the class of locally-additive colorings. -/
def la : ColoringClass.{v, w} X := fun _ _ C => IsLocallyAdditive C
```

#### `laEq` (def)

```lean
/-- **Notation 2.9 (6)** (Section 2). `la_μ`: locally-additive colorings with `μ` colors. -/
def laEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsLocallyAdditive C ∧ #D = μ
```

#### `laLt` (def)

```lean
/-- **Notation 2.9 (6)** (Section 2). `la_{<μ}`: locally-additive colorings with fewer than `μ`
colors. -/
def laLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsLocallyAdditive C ∧ #D < μ
```

#### `IsRegularCardinalOrder` (def)

```lean
/-- The domain `S` of a coloring "is a regular cardinal": `S` (with the order induced from `X`)
is order-isomorphic to a regular cardinal with its `∈`-order. Used in Notation 2.9 (5). -/
def IsRegularCardinalOrder (S : Set X) : Prop :=
  ∃ κ : Cardinal.{w}, κ.IsRegular ∧ Nonempty (S ≃o Kappa κ)
```

#### `starLa` (def)

```lean
/-- **Notation 2.9 (5)** (Section 2). `*-la`: the class of *-locally additive colorings on a
regular cardinal. -/
def starLa : ColoringClass.{v, w} X :=
  fun S _ C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C
```

#### `starLaEq` (def)

```lean
/-- **Notation 2.9 (6)** (Section 2). `*-la_μ`: *-locally additive colorings on a regular
cardinal with `μ` colors. -/
def starLaEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X :=
  fun S D C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C ∧ #D = μ
```

#### `starLaLt` (def)

```lean
/-- **Notation 2.9 (6)** (Section 2). `*-la_{<μ}`: *-locally additive colorings on a regular
cardinal with fewer than `μ` colors. -/
def starLaLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X :=
  fun S D C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C ∧ #D < μ
```

#### `Arrow` (def)

```lean
/-- **Definition 2.10** (Section 2). `F₁ → (F₂)_𝔆`: for every `S ∈ F₁` and every coloring
`C ∈ 𝔆` of `S` there is `E ⊆ S` with `E ∈ F₂` and `C ↾ [E]^2` constant. -/
def Arrow (F₁ F₂ : Set (Set X)) (𝔆 : ColoringClass.{v, w} X) : Prop :=
  ∀ S ∈ F₁, ∀ (D : Type v) (C : Coloring S D), 𝔆 S D C →
    ∃ E : Set S, Subtype.val '' E ∈ F₂ ∧ IsHomogeneous C E
```

#### `bigSubsets` (def)

```lean
/-- **Definition 2.10** (Section 2, last sentence): "`κ` for `F₁`", the family of subsets of
`κ` of cardinality `κ`. -/
def bigSubsets (κ : Cardinal.{w}) : Set (Set (Kappa κ)) := {S | #S = κ}
```

### B. Auxiliary lemmas (AUX: not in paper)

None.

## Section 3 (`Section3.lean`)

### Context

```lean
open Cardinal
universe v w
noncomputable section
namespace JardenShami
section AuxPairs
end AuxPairs
section Sec3
variable {X : Type w} [LinearOrder X]
end Sec3
end JardenShami
```

### A. Paper definitions and statements

#### `arrow_la_of_arrow_add` (theorem)

```lean
/-- **Theorem 3.1** (Section 3, `\label{generalizing add to loc less than mu colors}`,
`\label{theorem generalizing add to la}`). Let `κ, μ` be cardinals with `2^μ + ℵ₀ ≤ κ` and `F` a
family of subsets of a linearly ordered set. If `F → (F)_{add_κ}` then `F → (F)_{la_μ}`. -/
theorem arrow_la_of_arrow_add (κ μ : Cardinal.{v}) (hκ : 2 ^ μ + ℵ₀ ≤ κ) (F : Set (Set X))
    (h : Arrow F F (addEq κ)) : Arrow F F (laEq μ) := sorry
```

#### `arrow_laLt_of_arrow_addLt_strongLimit` (theorem)

```lean
/-- **Corollary 3.2** (Section 3, `\label{generalizing add to loc for strong limit cardinal}`).
Let `μ` be a strong limit cardinal and `F` a family of subsets of a linearly ordered set.
If `F → (F)_{add_{<μ}}` then `F → (F)_{la_{<μ}}`. (Mathlib's `IsStrongLimit` includes `ℵ₀`.) -/
theorem arrow_laLt_of_arrow_addLt_strongLimit (μ : Cardinal.{v}) (hμ : μ.IsStrongLimit)
    (F : Set (Set X)) (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) := sorry
```

#### `arrow_laLt_aleph0_of_arrow_addLt_aleph0` (theorem)

```lean
/-- **Corollary 3.3** (Section 3, `\label{generalizing add to loc for finite}`).
If `F → (F)_{add_{<ℵ₀}}` then `F → (F)_{la_{<ℵ₀}}`. -/
theorem arrow_laLt_aleph0_of_arrow_addLt_aleph0 (F : Set (Set X))
    (h : Arrow F F (addLt (ℵ₀ : Cardinal.{v}))) : Arrow F F (laLt (ℵ₀ : Cardinal.{v})) := sorry
```

#### `denseInSomeInterval` (def)

```lean
/-- The family of subsets of `I` that are dense in some interval of `I` (Fact 3.4 and
Corollary 3.5). Interpretation: there are `a < b` in `I` such that between any two points of the
open interval `(a, b)` there is a point of `S`. (`S` is not required to lie inside `(a, b)`.) -/
def denseInSomeInterval (I : Type w) [LinearOrder I] : Set (Set I) :=
  {S | ∃ a b : I, a < b ∧ ∀ x y : I, a < x → x < y → y < b → ∃ s ∈ S, x < s ∧ s < y}
```

#### FACT hypothesis (cited, not proved): `Fact_3_4`

```lean
/-- FACT: cited, not proved in the paper. **Fact 3.4** (Section 3, `\label{fact dense}`;
[Sh42, Theorem 1.3]). Let `I` be a dense linear ordering and `F` the family of subsets of `I` that
are dense in some interval of `I`. Then `F → (F)_{add_{<ℵ₀}}`. -/
def Fact_3_4 (I : Type w) [LinearOrder I] [DenselyOrdered I] : Prop :=
  Arrow (denseInSomeInterval I) (denseInSomeInterval I) (addLt (ℵ₀ : Cardinal.{v}))
```

#### `arrow_laLt_aleph0_denseInSomeInterval` (theorem)

```lean
/-- **Corollary 3.5** (Section 3, unlabelled). Let `I` be a dense linear ordering and `F` the
family of subsets of `I` that are dense in some interval of `I`. Then `F → (F)_{la_{<ℵ₀}}`.
Depends on the cited Fact 3.4, taken as the hypothesis `hfact`. -/
theorem arrow_laLt_aleph0_denseInSomeInterval (I : Type w) [LinearOrder I] [DenselyOrdered I]
    (hfact : Fact_3_4.{v, w} I) :
    Arrow (denseInSomeInterval I) (denseInSomeInterval I) (laLt (ℵ₀ : Cardinal.{v})) := sorry
```

### B. Auxiliary lemmas (AUX: not in paper)

#### `Pairs.exists_eq_mk` (theorem)

```lean
/-- AUX: not in paper. Every element of `[A]^2` is `{a, b}` for some `a < b`. -/
theorem Pairs.exists_eq_mk {A : Type*} [LinearOrder A] (p : Pairs A) :
    ∃ (a b : A) (h : a < b), p = Pairs.mk a b h.ne := sorry
```

#### `Pairs.mk_inj` (theorem)

```lean
/-- AUX: not in paper. `{a, b} = {c, d}` with `a < b` and `c < d` forces `a = c` and `b = d`. -/
theorem Pairs.mk_inj {A : Type*} [LinearOrder A] {a b c d : A} (hab : a < b) (hcd : c < d)
    (h : Pairs.mk a b hab.ne = Pairs.mk c d hcd.ne) : a = c ∧ b = d := sorry
```

#### `isHomogeneous_iff_color` (theorem)

```lean
/-- AUX: not in paper. Homogeneity (Definition 2.2) in terms of `C(a,b)`, `a < b`. -/
theorem isHomogeneous_iff_color {A : Type*} [LinearOrder A] {D : Type*} (C : Coloring A D)
    (B : Set A) :
    IsHomogeneous C B ↔ ∀ (a b c d : A) (hab : a < b) (hcd : c < d),
      a ∈ B → b ∈ B → c ∈ B → d ∈ B → C.color a b hab = C.color c d hcd := sorry
```

#### `Pairs.map` (def)

```lean
/-- AUX: not in paper. The image of a pair under an injective map. -/
def Pairs.map {A B : Type*} (f : A → B) (hf : Function.Injective f) (p : Pairs A) : Pairs B :=
  ⟨p.1.map f, by rw [Sym2.isDiag_map hf]; exact p.2⟩
```

#### `Pairs.map_mk` (theorem)

```lean
/-- AUX: not in paper. `f {a, b} = {f a, f b}`. -/
theorem Pairs.map_mk {A B : Type*} (f : A → B) (hf : Function.Injective f) (a b : A)
    (h : a ≠ b) : Pairs.map f hf (Pairs.mk a b h) = Pairs.mk (f a) (f b) (hf.ne h) := sorry
```

#### `arrow_la_of_arrow_add_of_card` (theorem)

```lean
/-- AUX: not in paper. The argument of the paper's proof of Theorem 3.1, for a general bound on
the number of colors. `Q` bounds the colors allowed in the hypothesis (additive colorings) and
`P` those in the conclusion (locally additive colorings). If every `D` allowed by `P` and the set
of colors `D* = D → Option D` (the partial functions `u_{a,b} : D_b → D`) are allowed by `Q`,
then `F → (F)_{add, Q}` implies `F → (F)_{la, P}`. -/
theorem arrow_la_of_arrow_add_of_card (P Q : Cardinal.{v} → Prop)
    (hPQ : ∀ D : Type v, P #D → Q #D ∧ Q #(D → Option D)) (F : Set (Set X))
    (h : Arrow F F (fun _ D C => IsAdditive C ∧ Q #D)) :
    Arrow F F (fun _ D C => IsLocallyAdditive C ∧ P #D) := sorry
```

#### `arrow_laLt_of_arrow_addLt_of_card` (theorem)

```lean
/-- AUX: not in paper. The argument of the paper's proof of Theorem 3.1, for the classes
`add_{<μ}` and `la_{<μ}`: if the set of colors `D* = D → Option D` has fewer than `μ` elements
whenever `D` does, then `F → (F)_{add_{<μ}}` implies `F → (F)_{la_{<μ}}`. This is the instance
`P = Q = (· < μ)` of `arrow_la_of_arrow_add_of_card`. Corollaries 3.2 and 3.3 are proved directly
from this lemma, not from the statement of Theorem 3.1 used as a black box (for `μ = ℵ₀` the
statement of 3.1 does not apply). -/
theorem arrow_laLt_of_arrow_addLt_of_card (μ : Cardinal.{v})
    (hpow : ∀ D : Type v, #D < μ → #(D → Option D) < μ) (F : Set (Set X))
    (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) := sorry
```

#### `arrow_addLe_of_arrow_addEq` (theorem)

```lean
/-- AUX: not in paper. Enlarging the set of colors (the gap noted in row 3.1 of FIDELITY.md):
since Definition 2.1 counts the codomain, an additive coloring with at most `κ` colors is also an
additive coloring with exactly `κ` colors (compose with an injection `D ↪ D'`, `#D' = κ`), and it
has the same homogeneous sets. Hence `F₁ → (F₂)_{add_κ}` implies the same arrow for additive
colorings with `≤ κ` colors. -/
theorem arrow_addLe_of_arrow_addEq (κ : Cardinal.{v}) (F₁ F₂ : Set (Set X))
    (h : Arrow F₁ F₂ (addEq κ)) : Arrow F₁ F₂ (fun _ D C => IsAdditive C ∧ #D ≤ κ) := sorry
```

## Section 4 (`Section4.lean`)

### Context

```lean
open Cardinal
universe u v w
noncomputable section
namespace JardenShami
namespace Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
variable (T) in
variable (T) in
variable (T) in
variable (T) in
end Tree
open Tree
section History
variable {T : Type w} [PartialOrder T] [IsTree T]
variable (T) in
variable (T) in
variable (T) in
end History
section TreeOfColoring
variable {κ : Cardinal.{w}} {D : Type v}
end TreeOfColoring
section Enumeration
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
variable (κ T) in
variable (κ T) in
end Enumeration
end JardenShami
```

### A. Paper definitions and statements

#### `IsTree` (class)

```lean
/-- **Section 4, preliminaries** ("Recall ..."). A tree is a partial order `(T, ≤_T)` such that
for each `t ∈ T` the set `{s ∈ T : s <_T t}` is well-ordered by `≤_T`. -/
class IsTree (T : Type w) [PartialOrder T] : Prop where
  wellOrder_Iio : ∀ t : T, IsWellOrder (Set.Iio t) (fun x y => (x : T) < y)
```

#### `ht` (def)

```lean
/-- **Section 4, preliminaries.** `ht(t,T)`: the height of `t`, the order type of
`{s : s <_T t}`. -/
def ht (t : T) : Ordinal.{w} :=
  @Ordinal.type (Set.Iio t) (fun x y => (x : T) < y) (IsTree.wellOrder_Iio t)
```

#### `Lev` (def)

```lean
/-- **Section 4, preliminaries.** `Lev_α(T)`: the `α`-th level of `T`. -/
def Lev (α : Ordinal.{w}) : Set T := {t | ht t = α}
```

#### `LevLt` (def)

```lean
/-- **Section 4, preliminaries.** `Lev_{<α}(T)`: the nodes of level smaller than `α` (regarded
as a subtree with the induced order). -/
def LevLt (α : Ordinal.{w}) : Set T := {t | ht t < α}
```

#### `height` (def)

```lean
/-- **Section 4, preliminaries.** `ht(T)`: the first `α` such that `Lev_α(T) = ∅`. -/
def height : Ordinal.{w} := sInf {α | Lev T α = ∅}
```

#### `IsBranch` (def)

```lean
/-- **Section 4, preliminaries.** A branch: a maximal linearly ordered subset of `T`. -/
def IsBranch (b : Set T) : Prop := IsMaxChain (· ≤ ·) b
```

#### `IsCofinalBranch` (def)

```lean
/-- **Section 4, preliminaries.** A cofinal branch: a branch whose order type is the height
of `T`. -/
def IsCofinalBranch (b : Set T) : Prop :=
  IsBranch b ∧ ∃ h : IsWellOrder b (fun x y => (x : T) < y),
    @Ordinal.type b (fun x y => (x : T) < y) h = height T
```

#### `IsLeaf` (def)

```lean
/-- **Section 4, preliminaries.** A leaf: a maximal element of the tree. -/
def IsLeaf (t : T) : Prop := IsMax t
```

#### `WellPruned` (def)

```lean
/-- **Section 4, preliminaries.** `T` is well-pruned: `Lev_0(T)` has exactly one element, and
`∀ x ∈ T ∀ α [ht(x,T) < α < ht(T) → ∃ y ∈ Lev_α(T) (x <_T y)]`. -/
def WellPruned : Prop :=
  (∃! x : T, ht x = 0) ∧
    ∀ (x : T) (α : Ordinal.{w}), ht x < α → α < height T → ∃ y ∈ Lev T α, x < y
```

#### `wellPruned_noLeaves_of_isSuccLimit` (theorem)

```lean
/-- **Section 4, preliminaries** (unnumbered, "Clearly"). Every well-pruned tree of limit
ordinal height has no leaves. -/
theorem wellPruned_noLeaves_of_isSuccLimit (hT : WellPruned T)
    (hlim : Order.IsSuccLimit (height T)) : ∀ t : T, ¬ IsLeaf t := sorry
```

#### `IsKappaTree` (def)

```lean
/-- `κ`-tree (used from Definition 4.10 on; not defined in the paper, standard meaning): a tree
of height `κ` all of whose levels have size `< κ`. -/
def IsKappaTree (κ : Cardinal.{w}) (T : Type w) [PartialOrder T] [IsTree T] : Prop :=
  height T = κ.ord ∧ ∀ α : Ordinal.{w}, α < κ.ord → #(Lev T α) < κ
```

#### `histFun` (def)

```lean
/-- **Definition 4.1** (Section 4). `f_t : ht(t,T) → T`, where `f_t(α)` is the unique
`t' <_T t` in `Lev_α(T)`; encoded by its graph `{(α, t') : t' <_T t, ht(t') = α}`. -/
def histFun (t : T) : Set (Ordinal.{w} × T) := {p | p.2 < t ∧ ht p.2 = p.1}
```

#### `HistoryTree` (def)

```lean
/-- **Definition 4.1** (Section 4). The history tree of `T`: `F_T = ({f_t : t ∈ T}, ⊆)`. -/
def HistoryTree : Set (Set (Ordinal.{w} × T)) := Set.range histFun
```

#### `historyTree_isTree` (theorem)

```lean
/-- **Definition 4.1** (Section 4), implicit claim: the history tree `F_T` is a tree. -/
theorem historyTree_isTree : IsTree (HistoryTree T) := sorry
```

#### `succPart` (def)

```lean
/-- **Definition 4.2** (Section 4). `T^succ`: the subtree of `T` induced by
`{t ∈ T : ht(t,T) is a successor ordinal}`. -/
def succPart : Set T := {t | ∃ β : Ordinal.{w}, ht t = Order.succ β}
```

#### `ht_histFun` (theorem)

```lean
/-- **After Definition 4.2** (Section 4, unnumbered, "as `ht(f_t,F_T) = ht(t,T)`"). The height
of `f_t` in `F_T` equals the height of `t` in `T` (the two heights live in different universes,
hence the `lift`). -/
theorem ht_histFun (t : T) :
    ht (⟨histFun t, t, rfl⟩ : HistoryTree T) = Ordinal.lift.{w + 1} (ht t) := sorry
```

#### `mem_succPart_historyTree` (theorem)

```lean
/-- **After Definition 4.2** (Section 4, unnumbered, "Clearly"). `(F_T)^succ = ({f_t : t ∈
T^succ}, ⊆)`. -/
theorem mem_succPart_historyTree (g : HistoryTree T) :
    g ∈ succPart (HistoryTree T) ↔ ∃ t ∈ succPart T, g.1 = histFun t := sorry
```

#### `historyTree_iso_restrict_succPart` (theorem)

```lean
/-- **Remark 4.3** (Section 4, `\label{remark 3.3}`). If `g : F_T → F_S` is an isomorphism,
then `g ↾ (F_T)^succ` is an isomorphism from `(F_T)^succ` to `(F_S)^succ`. -/
theorem historyTree_iso_restrict_succPart {S : Type w} [PartialOrder S] [IsTree S]
    (g : HistoryTree T ≃o HistoryTree S) :
    ∃ g' : succPart (HistoryTree T) ≃o succPart (HistoryTree S),
      ∀ x : succPart (HistoryTree T), (g' x : HistoryTree S) = g x := sorry
```

#### `nonempty_iso_succPart_historyTree` (theorem)

```lean
/-- **Proposition 4.4** (Section 4, `\label{proposition without leaves}`). A tree without
leaves is isomorphic to `(F_T)^succ`. -/
theorem nonempty_iso_succPart_historyTree (hT : ∀ t : T, ¬ IsLeaf t) :
    Nonempty (T ≃o succPart (HistoryTree T)) := sorry
```

#### `nonempty_iso_iff_historyTree` (theorem)

```lean
/-- **Corollary 4.5** (Section 4, `\label{corollary reconstruction a tree from its history}`).
Two trees without leaves are isomorphic iff their history trees are isomorphic. -/
theorem nonempty_iso_iff_historyTree {S : Type w} [PartialOrder S] [IsTree S]
    (hT : ∀ t : T, ¬ IsLeaf t) (hS : ∀ s : S, ¬ IsLeaf s) :
    Nonempty (T ≃o S) ↔ Nonempty (HistoryTree T ≃o HistoryTree S) := sorry
```

#### `fiberRestr` (def)

```lean
/-- `C(·,δ) ↾ β` for `β ≤ δ < κ` (Definition 4.6): the function `α ↦ C(α,δ)` on `{α : α < β}`,
encoded by its graph. -/
def fiberRestr (C : Coloring (Kappa κ) D) (δ β : Kappa κ) (hβ : β ≤ δ) :
    Set (Kappa κ × D) :=
  {p | ∃ h : p.1 < β, p.2 = C.color p.1 δ (h.trans_le hβ)}
```

#### `treeOfColoring` (def)

```lean
/-- **Definition 4.6** (Section 4, `\label{definition T(C)}`, after [ri:chain, p. 7]). For
`C : [κ]^2 → D`: `T(C) := {C(·,δ) ↾ β | β ≤ δ < κ}`, ordered by `⊆`. -/
def treeOfColoring (C : Coloring (Kappa κ) D) : Set (Set (Kappa κ × D)) :=
  {g | ∃ (δ β : Kappa κ) (hβ : β ≤ δ), g = fiberRestr C δ β hβ}
```

#### `treeOfColoring_isTree` (theorem)

```lean
/-- **Definition 4.6** (Section 4), implicit claim: `T(C)` is a tree. -/
theorem treeOfColoring_isTree (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := sorry
```

#### `treeOfColoring_downwardClosed` (theorem)

```lean
/-- **Definition 4.6** (Section 4), implicit claim: `T(C)` is downward closed in
`(^{<κ}D, ⊆)`, i.e. closed under restriction to an initial segment `{α : α < γ}`. -/
theorem treeOfColoring_downwardClosed (C : Coloring (Kappa κ) D) :
    ∀ g ∈ treeOfColoring C, ∀ γ : Kappa κ, {p ∈ g | p.1 < γ} ∈ treeOfColoring C := sorry
```

#### `colorMinOf` (def)

```lean
/-- **Remark 4.7** (Section 4). For `f : κ → 2`, the coloring `C_f(α,β) = f(α)` (`α < β`). -/
def colorMinOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.inf
```

#### `colorMinOf_spec` (theorem)

```lean
/-- **Remark 4.7** (Section 4). Each `C_f` (`C_f(α,β) = f(α)`) is locally additive and
*-locally additive, and `T(C_f)` is isomorphic to `(κ, ∈)`. -/
theorem colorMinOf_spec (f : Kappa κ → Fin 2) :
    IsLocallyAdditive (colorMinOf f) ∧ IsStarLocallyAdditive (colorMinOf f) ∧
      Nonempty (treeOfColoring (colorMinOf f) ≃o Kappa κ) := sorry
```

#### `colorMaxOf` (def)

```lean
/-- **Remark 4.8** (Section 4). For `f : κ → 2`, the coloring `C_f(α,β) = f(β)` (`α < β`). -/
def colorMaxOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.sup
```

#### `colorMaxOf_spec` (theorem)

```lean
/-- **Remark 4.8** (Section 4). If `f : κ → 2` is not eventually constant, then `C_f`
(`C_f(α,β) = f(β)`) is locally additive and *-locally additive, and
`T(C_f) = ^{<κ}{0} ∪ ^{<κ}{1}` (the constant functions with domain some `β < κ`). -/
theorem colorMaxOf_spec (f : Kappa κ → Fin 2)
    (hf : ¬ ∃ (α₀ : Kappa κ) (i : Fin 2), ∀ β, α₀ ≤ β → f β = i) :
    IsLocallyAdditive (colorMaxOf f) ∧ IsStarLocallyAdditive (colorMaxOf f) ∧
      treeOfColoring (colorMaxOf f) =
        {g | ∃ (β : Kappa κ) (i : Fin 2), g = {p | p.1 < β ∧ p.2 = i}} := sorry
```

#### `Enumeration` (structure)

```lean
/-- **Definition 4.10** (Section 4, `\label{definition enumeration}`). An enumeration of a
`κ`-tree `T`: for each `α < κ` a bijective enumeration `⟨t^i_α : i < μ_α⟩` of `Lev_α(T)`.
Here `t α i` is `t^i_α` and `μ_α = |Lev_α(T)|` (as an initial ordinal). -/
structure Enumeration where
  /-- `t α i` is `t^i_α`. -/
  t : Ordinal.{w} → Ordinal.{w} → T
  bijOn : ∀ α < κ.ord, Set.BijOn (t α) (Set.Iio (#(Lev T α)).ord) (Lev T α)
```

#### `levelSup` (def)

```lean
/-- **Definition 4.11** (Section 4): `μ = sup {μ_α : α < κ}`, `μ_α = |Lev_α(T)|`. -/
def levelSup : Cardinal.{w} := ⨆ α : Kappa κ, #(Lev T (α : Ordinal.{w}))
```

#### `IsTreeColoring` (def)

```lean
/-- **Definition 4.11** (Section 4, `\label{definition C(T,e)}`). `C = C(T,e)`, where
`C(T,e) : [κ]^2 → μ` is defined by `C(T,e)(α,δ) = i` iff `α < δ` and `i < μ` is the unique
ordinal with `t^i_α ≤_T t^0_δ`. Uniqueness is automatic, so the condition reads: `i < μ_α` (so
that `t^i_α` is defined) and `t^i_α ≤_T t^0_δ`. -/
def IsTreeColoring (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T))) :
    Prop :=
  ∀ (α δ : Kappa κ) (h : α < δ),
    ((C.color α δ h : Ordinal.{w}) < (#(Lev T (α : Ordinal.{w}))).ord) ∧
      e.t α (C.color α δ h) ≤ e.t δ 0
```

#### `existsUnique_isTreeColoring` (theorem)

```lean
/-- **Definition 4.11** (Section 4), implicit claim: for a `κ`-tree `T` and an enumeration `e`,
`C(T,e)` is well defined, i.e. exactly one coloring `C : [κ]^2 → μ` satisfies the definition. -/
theorem existsUnique_isTreeColoring (hT : IsKappaTree κ T) (e : Enumeration κ T) :
    ∃! C, IsTreeColoring e C := sorry
```

#### `isLocallyAdditive_of_isTreeColoring` (theorem)

```lean
/-- **Claim 4.12** (Section 4, `\label{claim C(T,e) is locally additive}`). For a tree `T`
and an enumeration `e` of `T`, the coloring `C(T,e)` is locally additive. (The paper assumes
that `T` is a `κ`-tree; this hypothesis is not needed and is not assumed here.) -/
theorem isLocallyAdditive_of_isTreeColoring (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    IsLocallyAdditive C := sorry
```

#### `Enumeration.Covers` (def)

```lean
/-- **Definition 4.13** (Section 4). The enumeration `e` covers `T` if for every `t ∈ T` there
is `δ < κ` with `t <_T t^0_δ`. -/
def Enumeration.Covers (e : Enumeration κ T) : Prop :=
  ∀ t : T, ∃ δ < κ.ord, t < e.t δ 0
```

#### `exists_covers` (theorem)

```lean
/-- **Remark 4.14** (Section 4). For every cardinal `κ` and a well-pruned `κ`-tree `T`, there is
an enumeration `e` of `T` that covers `T`.
CHANGED w.r.t. the paper: the hypothesis `ℵ₀ ≤ κ` is added. As written ("every cardinal") the
statement is false for finite `κ ≥ 1` (a node of maximal level cannot be below any `t^0_δ`);
the paper's proof assumes `κ` regular. See FIDELITY.md. -/
theorem exists_covers (hκ : ℵ₀ ≤ κ) (hT : IsKappaTree κ T) (hwp : WellPruned T) :
    ∃ e : Enumeration κ T, e.Covers := sorry
```

#### `Enumeration.node` (def)

```lean
/-- Notation in the proof of Theorem 4.15: `t_β^{C(β,δ)}` for `β ≤ δ < κ`, with the stipulation
`C(δ,δ) = 0`. -/
def Enumeration.node (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T)))
    (β δ : Kappa κ) (_h : β ≤ δ) : T :=
  if hβ : β < δ then e.t β (C.color β δ hβ) else e.t δ 0
```

#### `treeColoring_eq_iff_mem_histFun` (theorem)

```lean
/-- **Claim 4.16** (Section 4, inside the proof of Theorem 4.15,
`\label{claim for theorem 4.21}`). For `α < β ≤ δ < κ` and `i < μ_α`:
`(C(·,δ) ↾ β)(α) = i` iff `f_{t_β^{C(β,δ)}}(α) = t^i_α`.
CHANGED w.r.t. the paper: the paper's display reads "`(C(·,δ)↾β)(α)` if and only if ..." with
the right-hand side `= i` missing; the intended `= i` (as in clause (1) of its proof) is used.
Since `α < β`, `(C(·,δ)↾β)(α) = C(α,δ)`. -/
theorem treeColoring_eq_iff_mem_histFun (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {α β δ : Kappa κ} (hαβ : α < β) (hβδ : β ≤ δ) {i : Ordinal.{w}}
    (hi : i < (#(Lev T (α : Ordinal.{w}))).ord) :
    ((C.color α δ (hαβ.trans_le hβδ) : Ordinal.{w}) = i) ↔
      ((α : Ordinal.{w}), e.t α i) ∈ histFun (e.node C β δ hβδ) := sorry
```

#### `fiberRestr_subset_iff_histFun_subset` (theorem)

```lean
/-- **Claim 4.18** (Section 4, inside the proof of Theorem 4.15). The map
`h : C(·,δ) ↾ β ↦ f_{t_β^{C(β,δ)}}` is an order-homomorphism (in both directions, as in the
paper's proof): `C(·,δ₁) ↾ β₁ ⊆ C(·,δ₂) ↾ β₂` iff
`f_{t_{β₁}^{C(β₁,δ₁)}} ⊆ f_{t_{β₂}^{C(β₂,δ₂)}}`. -/
theorem fiberRestr_subset_iff_histFun_subset (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) ⊆ histFun (e.node C β₂ δ₂ h₂) := sorry
```

#### `fiberRestr_eq_iff_histFun_eq` (theorem)

```lean
/-- **Claim 4.17** (Section 4, inside the proof of Theorem 4.15,
`\label{claim result of claim for theorem 4.21}`). For `β₁ ≤ δ₁` and `β₂ ≤ δ₂`:
`C(·,δ₁) ↾ β₁ = C(·,δ₂) ↾ β₂` iff `f_{t_{β₁}^{C(β₁,δ₁)}} = f_{t_{β₂}^{C(β₂,δ₂)}}`. -/
theorem fiberRestr_eq_iff_histFun_eq (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) = histFun (e.node C β₂ δ₂ h₂) := sorry
```

#### `exists_histFun_node_eq` (theorem)

```lean
/-- **Claim 4.19** (Section 4, inside the proof of Theorem 4.15). The map
`h : C(·,δ) ↾ β ↦ f_{t_β^{C(β,δ)}}` is surjective onto `{f_t : t ∈ T}` (when `e` covers `T`). -/
theorem exists_histFun_node_eq (hT : IsKappaTree κ T) (e : Enumeration κ T) (he : e.Covers)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) (t : T) :
    ∃ (β δ : Kappa κ) (h : β ≤ δ), histFun (e.node C β δ h) = histFun t := sorry
```

#### `nonempty_iso_treeOfColoring_historyTree` (theorem)

```lean
/-- **Theorem 4.15** (Section 4, `\label{T isomorphic to T(C(T,e))}`). Let `T` be a `κ`-tree and
`e` an enumeration of `T`. If `e` covers `T` then `T(C(T,e))` is isomorphic to the history tree
`{f_t : t ∈ T}` of `T`. -/
theorem nonempty_iso_treeOfColoring_historyTree (hT : IsKappaTree κ T) (e : Enumeration κ T)
    (he : e.Covers) {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    Nonempty (treeOfColoring C ≃o HistoryTree T) := sorry
```

#### `nonempty_iso_iff_treeOfColoring` (theorem)

```lean
/-- **Corollary 4.20** (Section 4). Let `T₁, T₂` be `κ`-trees without leaves and `e_i` an
enumeration of `T_i` that covers `T_i`. Then `T₁ ≅ T₂` iff `T(C(T₁,e₁)) ≅ T(C(T₂,e₂))`. -/
theorem nonempty_iso_iff_treeOfColoring {κ : Cardinal.{w}}
    {T₁ T₂ : Type w} [PartialOrder T₁] [IsTree T₁] [PartialOrder T₂] [IsTree T₂]
    (h₁ : IsKappaTree κ T₁) (h₂ : IsKappaTree κ T₂)
    (hl₁ : ∀ t : T₁, ¬ IsLeaf t) (hl₂ : ∀ t : T₂, ¬ IsLeaf t)
    (e₁ : Enumeration κ T₁) (e₂ : Enumeration κ T₂) (c₁ : e₁.Covers) (c₂ : e₂.Covers)
    {C₁ : Coloring (Kappa κ) (Kappa (levelSup κ T₁))} (hC₁ : IsTreeColoring e₁ C₁)
    {C₂ : Coloring (Kappa κ) (Kappa (levelSup κ T₂))} (hC₂ : IsTreeColoring e₂ C₂) :
    Nonempty (T₁ ≃o T₂) ↔ Nonempty (treeOfColoring C₁ ≃o treeOfColoring C₂) := sorry
```

### B. Auxiliary lemmas (AUX: not in paper)

#### `lt_trichotomy_of_lt` (theorem)

```lean
/-- AUX: not in paper. Two predecessors of the same node are comparable. -/
theorem lt_trichotomy_of_lt {x y t : T} (hx : x < t) (hy : y < t) : x < y ∨ x = y ∨ y < x := sorry
```

#### `le_total_of_lt` (theorem)

```lean
/-- AUX: not in paper. Two predecessors of the same node are comparable. -/
theorem le_total_of_lt {x y t : T} (hx : x < t) (hy : y < t) : x ≤ y ∨ y ≤ x := sorry
```

#### `ht_eq_typein` (theorem)

```lean
/-- AUX: not in paper. For `s < t`, `ht s` is the position of `s` in `{x : x < t}`. -/
theorem ht_eq_typein {s t : T} (h : s < t) :
    ht s = Ordinal.typein (fun x y : Set.Iio t => (x : T) < y) ⟨s, h⟩ := sorry
```

#### `ht_lt_ht` (theorem)

```lean
/-- AUX: not in paper. Heights are strictly monotone. -/
theorem ht_lt_ht {s t : T} (h : s < t) : ht s < ht t := sorry
```

#### `exists_lt_ht_eq` (theorem)

```lean
/-- AUX: not in paper. Every ordinal below `ht t` is the height of a predecessor of `t`. -/
theorem exists_lt_ht_eq {t : T} {α : Ordinal.{w}} (h : α < ht t) : ∃ s < t, ht s = α := sorry
```

#### `eq_of_le_of_le_of_ht_eq` (theorem)

```lean
/-- AUX: not in paper. Two nodes below the same node and of the same height are equal. -/
theorem eq_of_le_of_le_of_ht_eq {x y z : T} (hx : x ≤ z) (hy : y ≤ z) (h : ht x = ht y) :
    x = y := sorry
```

#### `ht_le_ht_of_le` (theorem)

```lean
/-- AUX: not in paper. Heights are monotone. -/
theorem ht_le_ht_of_le {s t : T} (h : s ≤ t) : ht s ≤ ht t := sorry
```

#### `ht_le_ht_of_Iio_subset` (theorem)

```lean
/-- AUX: not in paper. `Iio s ⊆ Iio t` implies `ht s ≤ ht t`. -/
theorem ht_le_ht_of_Iio_subset {s t : T} (h : Set.Iio s ⊆ Set.Iio t) : ht s ≤ ht t := sorry
```

#### `ht_lt_ht_of_Iio_ssubset` (theorem)

```lean
/-- AUX: not in paper. `Iio s ⊂ Iio t` implies `ht s < ht t`. -/
theorem ht_lt_ht_of_Iio_ssubset {s t : T} (h : Set.Iio s ⊂ Set.Iio t) : ht s < ht t := sorry
```

#### `exists_Iio_eq_of_ssubset` (theorem)

```lean
/-- AUX: not in paper. If `Iio s ⊂ Iio t` then `Iio s = Iio u` for some `u < t`. -/
theorem exists_Iio_eq_of_ssubset {s t : T} (h : Set.Iio s ⊂ Set.Iio t) :
    ∃ u < t, Set.Iio s = Set.Iio u := sorry
```

#### `Iio_subset_or_subset` (theorem)

```lean
/-- AUX: not in paper. Two downward closed subsets of `Iio t` are comparable. -/
theorem Iio_subset_or_subset {s₁ s₂ t : T} (h₁ : Set.Iio s₁ ⊆ Set.Iio t)
    (h₂ : Set.Iio s₂ ⊆ Set.Iio t) : Set.Iio s₁ ⊆ Set.Iio s₂ ∨ Set.Iio s₂ ⊆ Set.Iio s₁ := sorry
```

#### `(anonymous instance)` (instance)

```lean
/-- AUX: not in paper. The order of a tree is well founded. -/
instance : WellFoundedLT T := by
  refine ⟨fun t => Acc.intro t fun y hy => ?_⟩
  have key : ∀ z : Set.Iio t, Acc (· < ·) (z : T) := by
    intro z
    induction z using (IsWellOrder.wf (r := fun x y : Set.Iio t => (x : T) < y)).induction with
    | _ z ih =>
      exact Acc.intro _ fun x hx => ih ⟨x, lt_trans hx z.2⟩ hx
  exact key ⟨y, hy⟩
```

#### `ht_lt_height` (theorem)

```lean
/-- AUX: not in paper. Every node has height smaller than the height of the tree. -/
theorem ht_lt_height (t : T) : ht t < height T := sorry
```

#### `lev_nonempty` (theorem)

```lean
/-- AUX: not in paper. Levels below the height are nonempty. -/
theorem lev_nonempty {α : Ordinal.{w}} (h : α < height T) : (Lev T α).Nonempty := sorry
```

#### `isTree_of_strictMono` (theorem)

```lean
/-- AUX: not in paper. A partial order is a tree if all predecessors of a node are comparable
and there is a strictly monotone map into a well-founded order. -/
theorem isTree_of_strictMono {P : Type*} [PartialOrder P] {β : Type*} [Preorder β]
    [WellFoundedLT β] (r : P → β) (hr : StrictMono r)
    (hc : ∀ t x y : P, x < t → y < t → x ≤ y ∨ y ≤ x) : IsTree P := sorry
```

#### `mem_histFun` (theorem)

```lean
/-- AUX: not in paper. Membership in the graph of `f_s`. -/
theorem mem_histFun {s p : T} {α : Ordinal.{w}} : (α, p) ∈ histFun s ↔ p < s ∧ ht p = α := sorry
```

#### `histFun_subset_iff` (theorem)

```lean
/-- AUX: not in paper. `f_s ⊆ f_t` iff every predecessor of `s` is a predecessor of `t`. -/
theorem histFun_subset_iff {s t : T} : histFun s ⊆ histFun t ↔ Set.Iio s ⊆ Set.Iio t := sorry
```

#### `histFun_ssubset_iff` (theorem)

```lean
/-- AUX: not in paper. -/
theorem histFun_ssubset_iff {s t : T} : histFun s ⊂ histFun t ↔ Set.Iio s ⊂ Set.Iio t := sorry
```

#### `histFun_eq_iff` (theorem)

```lean
/-- AUX: not in paper. -/
theorem histFun_eq_iff {s t : T} : histFun s = histFun t ↔ Set.Iio s = Set.Iio t := sorry
```

#### `Iio_ssubset_Iio_of_lt` (theorem)

```lean
omit [IsTree T] in
/-- AUX: not in paper. For `u < t`, `Iio u ⊂ Iio t`. -/
theorem Iio_ssubset_Iio_of_lt {u t : T} (h : u < t) : Set.Iio u ⊂ Set.Iio t := sorry
```

#### `ht_orderIso` (theorem)

```lean
/-- AUX: not in paper. Order isomorphisms of trees preserve heights. -/
theorem ht_orderIso {P Q : Type u} [PartialOrder P] [IsTree P] [PartialOrder Q] [IsTree Q]
    (e : P ≃o Q) (t : P) : ht (e t) = ht t := sorry
```

#### `succNode` (def)

```lean
/-- AUX: not in paper. The node `m t`: the least node above `t` (for `t` not a leaf). -/
def succNode {t : T} (ht' : ¬ IsLeaf t) : T :=
  WellFounded.min wellFounded_lt {x | t < x} (not_isMax_iff.1 ht')
```

#### `Iio_succNode` (theorem)

```lean
/-- AUX: not in paper. The predecessors of `succNode t` are exactly the nodes `≤ t`. -/
theorem Iio_succNode {t : T} (ht' : ¬ IsLeaf t) : Set.Iio (succNode ht') = Set.Iic t := sorry
```

#### `ht_succNode` (theorem)

```lean
/-- AUX: not in paper. `ht (succNode t) = ht t + 1`. -/
theorem ht_succNode {t : T} (ht' : ¬ IsLeaf t) : ht (succNode ht') = Order.succ (ht t) := sorry
```

#### `histFun_orderIso` (theorem)

```lean
/-- AUX: not in paper. Order isomorphisms of trees induce isomorphisms of history trees. -/
theorem histFun_orderIso {S : Type w} [PartialOrder S] [IsTree S] (e : T ≃o S) (t : T) :
    histFun (e t) = Prod.map id e '' histFun t := sorry
```

#### `Kappa.coe_lt_coe` (theorem)

```lean
/-- AUX: not in paper. Elements of `Kappa κ` as ordinals: `<` is preserved. -/
theorem Kappa.coe_lt_coe {x y : Kappa κ} : (x : Ordinal.{w}) < y ↔ x < y := sorry
```

#### `Kappa.coe_le_coe` (theorem)

```lean
/-- AUX: not in paper. Elements of `Kappa κ` as ordinals: `≤` is preserved. -/
theorem Kappa.coe_le_coe {x y : Kappa κ} : (x : Ordinal.{w}) ≤ y ↔ x ≤ y := sorry
```

#### `Kappa.coe_lt_ord` (theorem)

```lean
/-- AUX: not in paper. Elements of `Kappa κ` as ordinals are `< κ.ord`. -/
theorem Kappa.coe_lt_ord (x : Kappa κ) : (x : Ordinal.{w}) < κ.ord := sorry
```

#### `Kappa.mk` (def)

```lean
/-- AUX: not in paper. The element of `Kappa κ` corresponding to an ordinal `α < κ.ord`. -/
def Kappa.mk (α : Ordinal.{w}) (h : α < κ.ord) : Kappa κ := Ordinal.ToType.mk ⟨α, h⟩
```

#### `Kappa.coe_mk` (theorem)

```lean
/-- AUX: not in paper. -/
@[simp] theorem Kappa.coe_mk (α : Ordinal.{w}) (h : α < κ.ord) :
    ((Kappa.mk α h : Kappa κ) : Ordinal.{w}) = α := sorry
```

#### `Kappa.coe_inj` (theorem)

```lean
/-- AUX: not in paper. -/
theorem Kappa.coe_inj {x y : Kappa κ} : (x : Ordinal.{w}) = y ↔ x = y := sorry
```

#### `mem_fiberRestr` (theorem)

```lean
/-- AUX: not in paper. Membership in the graph of `C(·,δ) ↾ β`. -/
theorem mem_fiberRestr {C : Coloring (Kappa κ) D} {δ β : Kappa κ} {hβ : β ≤ δ}
    {α : Kappa κ} {d : D} :
    (α, d) ∈ fiberRestr C δ β hβ ↔ ∃ h : α < β, d = C.color α δ (h.trans_le hβ) := sorry
```

#### `fiberRestr_subset_iff` (theorem)

```lean
/-- AUX: not in paper. Inclusion between the graphs `C(·,δ) ↾ β`. -/
theorem fiberRestr_subset_iff {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ} (h₁ : β₁ ≤ δ₁)
    (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ ↔
      β₁ ≤ β₂ ∧ ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
        C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂) := sorry
```

#### `fiberRestr_subset_of_subset` (theorem)

```lean
/-- AUX: not in paper. Two subgraphs of the same `C(·,δ) ↾ β` are comparable. -/
theorem fiberRestr_subset_of_subset {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ δ β : Kappa κ}
    {h₁ : β₁ ≤ δ₁} {h₂ : β₂ ≤ δ₂} {h : β ≤ δ} (s₁ : fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ β h)
    (s₂ : fiberRestr C δ₂ β₂ h₂ ⊆ fiberRestr C δ β h) (hle : β₁ ≤ β₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ := sorry
```

#### `colorMinOf_color` (theorem)

```lean
/-- AUX: not in paper. `C_f(a,b) = f(a)` for `a < b`. -/
theorem colorMinOf_color (f : Kappa κ → Fin 2) (a b : Kappa κ) (h : a < b) :
    (colorMinOf f).color a b h = f a := sorry
```

#### `colorMinOf_color_dual` (theorem)

```lean
/-- AUX: not in paper. For the reverse order: `C_f(a,b) = f(b)` for `b < a`. -/
theorem colorMinOf_color_dual (f : Kappa κ → Fin 2) (a b : (Kappa κ)ᵒᵈ) (h : a < b) :
    Coloring.color (A := (Kappa κ)ᵒᵈ) (colorMinOf f) a b h = f (OrderDual.ofDual b) := sorry
```

#### `fiberRestr_colorMinOf` (theorem)

```lean
/-- AUX: not in paper. `T(C_f)` for `C_f(α,β) = f(α)`: the graphs of `f ↾ β`. -/
theorem fiberRestr_colorMinOf (f : Kappa κ → Fin 2) (δ β : Kappa κ) (hβ : β ≤ δ) :
    fiberRestr (colorMinOf f) δ β hβ = {p | p.1 < β ∧ p.2 = f p.1} := sorry
```

#### `colorMaxOf_color` (theorem)

```lean
/-- AUX: not in paper. `C_f(a,b) = f(b)` for `a < b`. -/
theorem colorMaxOf_color (f : Kappa κ → Fin 2) (a b : Kappa κ) (h : a < b) :
    (colorMaxOf f).color a b h = f b := sorry
```

#### `colorMaxOf_color_dual` (theorem)

```lean
/-- AUX: not in paper. For the reverse order: `C_f(a,b) = f(a)` for `b < a`. -/
theorem colorMaxOf_color_dual (f : Kappa κ → Fin 2) (a b : (Kappa κ)ᵒᵈ) (h : a < b) :
    Coloring.color (A := (Kappa κ)ᵒᵈ) (colorMaxOf f) a b h = f (OrderDual.ofDual a) := sorry
```

#### `Enumeration.mem_lev` (theorem)

```lean
/-- AUX: not in paper. `t^i_α ∈ Lev_α(T)`. -/
theorem Enumeration.mem_lev (e : Enumeration κ T) {α i : Ordinal.{w}} (hα : α < κ.ord)
    (hi : i < (#(Lev T α)).ord) : e.t α i ∈ Lev T α := sorry
```

#### `Enumeration.ht_t` (theorem)

```lean
/-- AUX: not in paper. `ht(t^i_α) = α`. -/
theorem Enumeration.ht_t (e : Enumeration κ T) {α i : Ordinal.{w}} (hα : α < κ.ord)
    (hi : i < (#(Lev T α)).ord) : ht (e.t α i) = α := sorry
```

#### `zero_lt_ord_lev` (theorem)

```lean
/-- AUX: not in paper. In a `κ`-tree, `0 < μ_α` for `α < κ`. -/
theorem zero_lt_ord_lev (hT : IsKappaTree κ T) {α : Ordinal.{w}} (hα : α < κ.ord) :
    0 < (#(Lev T α)).ord := sorry
```

#### `Enumeration.exists_eq` (theorem)

```lean
/-- AUX: not in paper. Every node of `Lev_α(T)` is some `t^i_α`. -/
theorem Enumeration.exists_eq (e : Enumeration κ T) {α : Ordinal.{w}} (hα : α < κ.ord) {x : T}
    (hx : x ∈ Lev T α) : ∃ i < (#(Lev T α)).ord, e.t α i = x := sorry
```

#### `le_total_of_le` (theorem)

```lean
/-- AUX: not in paper. Two nodes below a common node are comparable. -/
theorem le_total_of_le {x y z : T} (hx : x ≤ z) (hy : y ≤ z) : x ≤ y ∨ y ≤ x := sorry
```

#### `lt_of_le_of_le_of_ht_lt` (theorem)

```lean
/-- AUX: not in paper. A node of height `α` and a node of height `β > α` below a common node:
the first is below the second. -/
theorem lt_of_le_of_le_of_ht_lt {x y z : T} (hx : x ≤ z) (hy : y ≤ z) (h : ht x < ht y) :
    x < y := sorry
```

#### `IsTreeColoring.color_eq` (theorem)

```lean
/-- AUX: not in paper. Uniqueness in Definition 4.11: if `i < μ_α` and `t^i_α ≤ t^0_δ` then
`C(T,e)(α,δ) = i`. -/
theorem IsTreeColoring.color_eq {e : Enumeration κ T}
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) {α δ : Kappa κ}
    (h : α < δ) {i : Ordinal.{w}} (hi : i < (#(Lev T (α : Ordinal.{w}))).ord)
    (hle : e.t α i ≤ e.t δ 0) : (C.color α δ h : Ordinal.{w}) = i := sorry
```

#### `card_lev_le_levelSup` (theorem)

```lean
/-- AUX: not in paper. `μ_α ≤ μ`. -/
theorem card_lev_le_levelSup (α : Kappa κ) : #(Lev T (α : Ordinal.{w})) ≤ levelSup κ T := sorry
```

#### `Kappa.mk_coe` (theorem)

```lean
/-- AUX: not in paper. -/
@[simp] theorem Kappa.mk_coe {κ : Cardinal.{w}} (x : Kappa κ) :
    Kappa.mk (x : Ordinal.{w}) (Kappa.coe_lt_ord x) = x := sorry
```

#### `exists_bijOn_ord` (theorem)

```lean
omit [PartialOrder T] [IsTree T] in
/-- AUX: not in paper. A nonempty set `L` has a bijective enumeration
`⟨f(i) : i < |L|⟩` starting with a prescribed element `c ∈ L`. -/
theorem exists_bijOn_ord {L : Set T} {c : T} (hc : c ∈ L) :
    ∃ f : Ordinal.{w} → T, Set.BijOn f (Set.Iio (#L).ord) L ∧ f 0 = c := sorry
```

#### `Enumeration.node_spec` (theorem)

```lean
/-- AUX: not in paper. `t_β^{C(β,δ)} ∈ Lev_β(T)` and `t_β^{C(β,δ)} ≤ t^0_δ`. -/
theorem Enumeration.node_spec (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β δ : Kappa κ} (h : β ≤ δ) :
    ht (e.node C β δ h) = β ∧ e.node C β δ h ≤ e.t δ 0 := sorry
```

### C. Declarations without a docstring

#### `(anonymous instance)` (instance)

```lean
instance (t : T) : IsWellOrder (Set.Iio t) (fun x y => (x : T) < y) := IsTree.wellOrder_Iio t
```

#### `(anonymous instance)` (instance)

```lean
instance : IsTree (HistoryTree T) := historyTree_isTree T
```

#### `(anonymous instance)` (instance)

```lean
instance (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := treeOfColoring_isTree C
```

## Section 5 (`Section5.lean`)

### Context

```lean
open Cardinal
universe w
noncomputable section
namespace JardenShami
open Tree
section Aux
variable {κ : Cardinal.{w}}
end Aux
namespace Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
end Tree
section TreeOfColoringAux
variable {κ : Cardinal.{w}} {D : Type w}
end TreeOfColoringAux
end JardenShami
```

### A. Paper definitions and statements

#### `IsAronszajn` (def)

```lean
/-- `κ`-Aronszajn tree (used in Fact 5.1 and Theorem 5.2; not defined in the paper, standard
meaning): a `κ`-tree with no cofinal branch. -/
def IsAronszajn (κ : Cardinal.{w}) (T : Type w) [PartialOrder T] [IsTree T] : Prop :=
  IsKappaTree κ T ∧ ¬ ∃ b : Set T, IsCofinalBranch b
```

#### `NoAronszajn` (def)

```lean
/-- "There exists no `κ`-Aronszajn tree" (Fact 5.1 (1), Theorem 5.2 (1)), for trees in the
universe of `κ`. -/
def NoAronszajn (κ : Cardinal.{w}) : Prop :=
  ∀ (T : Type w) [PartialOrder T] [IsTree T], ¬ IsAronszajn κ T
```

#### `LaArrowKappa` (def)

```lean
/-- `κ → (κ)_{la_μ}` in the sense spelled out in Theorem 5.2 (2) and Lemma 5.3 (2) ("namely"):
every locally additive coloring `C : [κ]^2 → μ` admits a homogeneous set of size `κ`. -/
def LaArrowKappa (κ μ : Cardinal.{w}) : Prop :=
  ∀ C : Coloring (Kappa κ) (Kappa μ), IsLocallyAdditive C →
    ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H
```

#### FACT hypothesis (cited, not proved): `Fact_5_1`

```lean
/-- FACT: cited, not proved in the paper. **Fact 5.1** (Section 5, unlabelled, "Recall two
equivalent definitions of a weakly compact cardinal"). For every strongly inaccessible cardinal
`κ` the following are equivalent: (1) there exists no `κ`-Aronszajn tree; (2) for every
`λ < κ`, every coloring `C : [κ]^2 → λ` admits a homogeneous set of size `κ`.
"Strongly inaccessible" is Mathlib's `Cardinal.IsInaccessible`
(uncountable, regular, strong limit). -/
def Fact_5_1 : Prop :=
  ∀ κ : Cardinal.{w}, κ.IsInaccessible →
    (NoAronszajn κ ↔
      ∀ lam : Cardinal.{w}, lam < κ → ∀ C : Coloring (Kappa κ) (Kappa lam),
        ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H)
```

#### `card_lev_treeOfColoring_le` (theorem)

```lean
/-- **Claim 5.4** (Section 5, inside the proof of Lemma 5.3, direction (1) ⇒ (2)). For an
uncountable cardinal `κ` and a locally additive `C : [κ]^2 → μ`, all the levels of `T(C)` have
size `≤ μ`. (The paper works under the hypotheses of Lemma 5.3; of these, `κ` regular and
`μ < κ` are not needed and are not assumed here.) -/
theorem card_lev_treeOfColoring_le (κ μ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := sorry
```

#### `branch_iff_laArrowKappa` (theorem)

```lean
/-- **Lemma 5.3** (Section 5, `\label{lemma 6}`, `\label{the main lemma}`). Suppose `κ` is a
regular uncountable cardinal and `μ < κ`. The following are equivalent: (1) every tree of height
`κ` whose levels have size `≤ μ` admits a `κ`-sized branch; (2) `κ → (κ)_{la_μ}`, namely every
locally additive coloring `C : [κ]^2 → μ` admits a homogeneous set of size `κ`. -/
theorem branch_iff_laArrowKappa (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ)
    (hμ : μ < κ) :
    (∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) ≤ μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) ↔
      LaArrowKappa κ μ := sorry
```

#### `noAronszajn_succ_iff_laArrowKappa` (theorem)

```lean
/-- **Theorem 5.2** (Section 5, `\label{theorem 4.2}`). For every infinite cardinal `μ` the
following are equivalent: (1) there exists no `μ⁺`-Aronszajn tree; (2) `μ⁺ → (μ⁺)_{la_μ}`, namely
every locally additive coloring `C : [μ⁺]^2 → μ` admits a homogeneous set of size `μ⁺`. -/
theorem noAronszajn_succ_iff_laArrowKappa (μ : Cardinal.{w}) (hμ : ℵ₀ ≤ μ) :
    NoAronszajn (Order.succ μ) ↔ LaArrowKappa (Order.succ μ) μ := sorry
```

### B. Auxiliary lemmas (AUX: not in paper)

#### `Kappa.mk_eq` (theorem)

```lean
/-- AUX: not in paper. `#κ = κ`. -/
theorem Kappa.mk_eq (κ : Cardinal.{w}) : #(Kappa κ) = κ := sorry
```

#### `Kappa.mk_Iic_lt` (theorem)

```lean
/-- AUX: not in paper. For infinite `κ`, every initial segment `{y : y ≤ x}` of `κ` has size
`< κ`. -/
theorem Kappa.mk_Iic_lt (hκ : ℵ₀ ≤ κ) (x : Kappa κ) : #(Set.Iic x) < κ := sorry
```

#### `Kappa.exists_gt_of_card_eq` (theorem)

```lean
/-- AUX: not in paper. For infinite `κ`, a subset of `κ` of size `κ` is unbounded. -/
theorem Kappa.exists_gt_of_card_eq (hκ : ℵ₀ ≤ κ) {S : Set (Kappa κ)} (hS : #S = κ)
    (x : Kappa κ) : ∃ y ∈ S, x < y := sorry
```

#### `Kappa.exists_gt_of_card_lt` (theorem)

```lean
/-- AUX: not in paper. For regular `κ`, a subset of `κ` of size `< κ` is bounded. -/
theorem Kappa.exists_gt_of_card_lt (hκ : κ.IsRegular) {S : Set (Kappa κ)} (hS : #S < κ) :
    ∃ x, ∀ y ∈ S, y < x := sorry
```

#### `Kappa.card_eq_of_forall_exists_gt` (theorem)

```lean
/-- AUX: not in paper. For regular `κ`, an unbounded subset of `κ` has size `κ`. -/
theorem Kappa.card_eq_of_forall_exists_gt (hκ : κ.IsRegular) {S : Set (Kappa κ)}
    (h : ∀ x, ∃ y ∈ S, x < y) : #S = κ := sorry
```

#### `Kappa.exists_sparse` (theorem)

```lean
/-- AUX: not in paper. For regular `κ`, a `κ`-sized `Γ ⊆ κ` and `F : κ → κ`, there is a
`κ`-sized `Γ' ⊆ Γ` such that `F γ₀ < γ` for all `γ₀ < γ` in `Γ'`. -/
theorem Kappa.exists_sparse (hκ : κ.IsRegular) {Γ : Set (Kappa κ)} (hΓ : #Γ = κ)
    (F : Kappa κ → Kappa κ) :
    ∃ Γ' ⊆ Γ, #Γ' = κ ∧ ∀ γ₀ ∈ Γ', ∀ γ ∈ Γ', γ₀ < γ → F γ₀ < γ := sorry
```

#### `IsLocallyAdditive.color_eq_of_le` (theorem)

```lean
/-- AUX: not in paper. For a locally additive `C`, `C(a,δ) = C(a,δ')` implies
`C(α,δ) = C(α,δ')` for all `α ≤ a`. -/
theorem IsLocallyAdditive.color_eq_of_le {A : Type w} [LinearOrder A] {D : Type*}
    {C : Coloring A D} (hC : IsLocallyAdditive C) {a δ δ' α : A} (ha : a < δ) (ha' : a < δ')
    (h : C.color a δ ha = C.color a δ' ha') (hα : α ≤ a) :
    C.color α δ (hα.trans_lt ha) = C.color α δ' (hα.trans_lt ha') := sorry
```

#### `Coloring.color_congr` (theorem)

```lean
/-- AUX: not in paper. `C(a,b)` depends only on `a` and `b`. -/
theorem Coloring.color_congr {A : Type w} [LinearOrder A] {D : Type*} (C : Coloring A D)
    {a a' b b' : A} (ha : a = a') (hb : b = b') (h : a < b) (h' : a' < b') :
    C.color a b h = C.color a' b' h' := sorry
```

#### `IsLocallyAdditive.comp_injective` (theorem)

```lean
/-- AUX: not in paper. Composing a locally additive coloring with an injective map of colors
gives a locally additive coloring. -/
theorem IsLocallyAdditive.comp_injective {A : Type w} [LinearOrder A] {D E : Type*}
    {C : Coloring A D} (hC : IsLocallyAdditive C) {ι : D → E} (hι : Function.Injective ι) :
    IsLocallyAdditive (ι ∘ C) := sorry
```

#### `lt_iff_ht_lt_of_isChain` (theorem)

```lean
/-- AUX: not in paper. On a chain, `x < y` iff `ht x < ht y`. -/
theorem lt_iff_ht_lt_of_isChain {b : Set T} (hb : IsChain (· ≤ ·) b) {x y : T} (hx : x ∈ b)
    (hy : y ∈ b) : x < y ↔ ht x < ht y := sorry
```

#### `ht_injOn_of_isChain` (theorem)

```lean
/-- AUX: not in paper. On a chain, the height is injective. -/
theorem ht_injOn_of_isChain {b : Set T} (hb : IsChain (· ≤ ·) b) : Set.InjOn ht b := sorry
```

#### `isWellOrder_of_isChain` (theorem)

```lean
/-- AUX: not in paper. A chain of a tree is well-ordered. -/
theorem isWellOrder_of_isChain {b : Set T} (hb : IsChain (· ≤ ·) b) :
    IsWellOrder b (fun x y => (x : T) < y) := sorry
```

#### `mk_le_of_isChain` (theorem)

```lean
/-- AUX: not in paper. In a tree of height `κ`, every chain has size `≤ κ`. -/
theorem mk_le_of_isChain {κ : Cardinal.{w}} (hT : height T = κ.ord) {b : Set T}
    (hb : IsChain (· ≤ ·) b) : #b ≤ κ := sorry
```

#### `isCofinalBranch_iff` (theorem)

```lean
/-- AUX: not in paper. In a tree of height `κ`, a branch is cofinal iff it has size `κ`. -/
theorem isCofinalBranch_iff {κ : Cardinal.{w}} (hT : height T = κ.ord) {b : Set T} :
    IsCofinalBranch b ↔ IsBranch b ∧ #b = κ := sorry
```

#### `fiberRestr_eq_fiberRestr` (theorem)

```lean
/-- AUX: not in paper. Equality of the graphs `C(·,δ) ↾ β`. -/
theorem fiberRestr_eq_fiberRestr {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ}
    (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) (hβ : β₁ = β₂)
    (hc : ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
      C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂)) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ := sorry
```

#### `fiberRestr_ssubset_iff` (theorem)

```lean
/-- AUX: not in paper. Strict inclusion between the graphs `C(·,δ) ↾ β`. -/
theorem fiberRestr_ssubset_iff {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ}
    (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊂ fiberRestr C δ₂ β₂ h₂ ↔
      β₁ < β₂ ∧ ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
        C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂) := sorry
```

#### `ht_fiberRestr` (theorem)

```lean
/-- AUX: not in paper. The height of `C(·,δ) ↾ β` in `T(C)` is `β`. -/
theorem ht_fiberRestr (C : Coloring (Kappa κ) D) {δ β : Kappa κ} (h : β ≤ δ) :
    ht (⟨fiberRestr C δ β h, δ, β, h, rfl⟩ : treeOfColoring C) = (β : Ordinal.{w}) := sorry
```

#### `mem_lev_treeOfColoring` (theorem)

```lean
/-- AUX: not in paper. The nodes of `Lev_α(T(C))` are the graphs `C(·,δ) ↾ β` with `β = α`. -/
theorem mem_lev_treeOfColoring {C : Coloring (Kappa κ) D} {g : treeOfColoring C}
    {α : Ordinal.{w}} :
    g ∈ Lev (treeOfColoring C) α ↔
      ∃ (δ β : Kappa κ) (h : β ≤ δ), g.1 = fiberRestr C δ β h ∧ (β : Ordinal.{w}) = α := sorry
```

#### `height_treeOfColoring` (theorem)

```lean
/-- AUX: not in paper. The height of `T(C)` is `κ`. -/
theorem height_treeOfColoring (C : Coloring (Kappa κ) D) :
    height (treeOfColoring C) = κ.ord := sorry
```

#### `card_lev_treeOfColoring_le_of_aleph0_le` (theorem)

```lean
/-- AUX: not in paper. Claim 5.4 for every infinite `κ` (neither regularity nor uncountability
nor `μ < κ` is needed; the proof of Claim 5.4 uses only that there is a color). -/
theorem card_lev_treeOfColoring_le_of_aleph0_le (κ μ : Cardinal.{w}) (hκ0 : ℵ₀ ≤ κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := sorry
```

#### `exists_enumeration` (theorem)

```lean
/-- AUX: not in paper. Every `κ`-tree (`κ ≠ 0`) has an enumeration (Definition 4.10). -/
theorem exists_enumeration {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
    (hκ : κ ≠ 0) (hT : IsKappaTree κ T) : Nonempty (Enumeration κ T) := sorry
```

#### `laArrowKappa_of_forall_branch` (theorem)

```lean
/-- AUX: not in paper. Direction (1) ⇒ (2) of Lemma 5.3 for every regular `κ` (also `κ = ℵ₀`;
the proof of Lemma 5.3 does not use that `κ` is uncountable). -/
theorem laArrowKappa_of_forall_branch (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (h1 : ∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) ≤ μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) :
    LaArrowKappa κ μ := sorry
```

## Section 6 (`Section6.lean`)

### Context

```lean
open Cardinal
universe w
noncomputable section
namespace JardenShami
open Tree
section BinTree
variable {ν : Cardinal.{w}}
end BinTree
end JardenShami
```

### A. Paper definitions and statements

#### `isTree_subtype` (theorem)

```lean
/-- Implicit in the paper ("subtree", e.g. `Lev_{<α}(T)` in the proof of Theorem 6.4 and the
well-pruned subtree in the proof of Claim 7.8): a subset of a tree, with the induced order, is a
tree. -/
theorem isTree_subtype {T : Type w} [PartialOrder T] [IsTree T] (S : Set T) : IsTree S := sorry
```

#### `Lim` (def)

```lean
/-- **Definition 6.1** (Section 6, after [Sh589]). `Lim(T)`: the set of cofinal branches of the
tree `T`. -/
def Lim (T : Type w) [PartialOrder T] [IsTree T] : Set (Set T) := {b | IsCofinalBranch b}
```

#### `treeExp` (def)

```lean
/-- **Definition 6.1** (Section 6, after [Sh589]). For infinite cardinals `μ ≤ λ`, `𝔗_{λ,μ}` is
the set of trees of height `μ` with `≤ λ` nodes, and the tree exponent is
`λ^{μ,tr} = sup {|Lim(T)| : T ∈ 𝔗_{λ,μ}}`.
The Lean definition is total; the paper uses it only for infinite `μ ≤ λ`. Trees range over
`Type w`. (The set is bounded by `2^λ`, so `sSup` is the true supremum.) -/
def treeExp (lam μ : Cardinal.{w}) : Cardinal.{w} :=
  sSup {c | ∃ (T : Type w) (_ : PartialOrder T) (_ : IsTree T),
    height T = μ.ord ∧ #T ≤ lam ∧ c = #(Lim T)}
```

#### `treeExp_le_power` (theorem)

```lean
/-- **Remark 6.2** (Section 6, `\label{remark tree exponent leq exponent}`). For every infinite
cardinal `λ` and every cardinal `μ`: `λ^{μ,tr} ≤ λ^μ`. (The paper assumes that `μ` is infinite
too; this is not needed and is not assumed here.) -/
theorem treeExp_le_power (lam μ : Cardinal.{w}) (hlam : ℵ₀ ≤ lam) :
    treeExp lam μ ≤ lam ^ μ := sorry
```

#### `IsWeaklyCompact` (def)

```lean
/-- **Section 6, between Remark 6.2 and Fact 6.3** ("Recall, that a weakly compact cardinal is a
strongly inaccessible cardinal that satisfies the tree property"). -/
def IsWeaklyCompact (κ : Cardinal.{w}) : Prop := κ.IsInaccessible ∧ NoAronszajn κ
```

#### FACT hypothesis (cited, not proved): `Fact_6_3`

```lean
/-- FACT: cited, not proved in the paper. **Fact 6.3** (Section 6, `\label{fact 6.3}`, no
citation given). Let `κ` be an uncountable cardinal. The principle `κ → (κ)_2` holds if and only if
`κ` is weakly compact.
`κ → (κ)_2` is Definition 2.10 literally: `F₁ = F₂` = the subsets of `κ` of size `κ`, `𝔆` = all
colorings with `2` colors (color sets in `Type w`). -/
def Fact_6_3 : Prop :=
  ∀ κ : Cardinal.{w}, ℵ₀ < κ →
    (Arrow (bigSubsets κ) (bigSubsets κ) (allColorings.{w, w} (2 : Cardinal.{w})) ↔
      IsWeaklyCompact κ)
```

#### `treeExp_lt_iff_isInaccessible` (theorem)

```lean
/-- **Theorem 6.4** (Section 6, `\label{theorem 5.4}`). Let `κ` be an uncountable regular cardinal.
The following are equivalent: (1) `λ^{μ,tr} < κ` for each `λ, μ < κ`; (2) `κ` is strongly
inaccessible.
In (1), `λ^{μ,tr}` is taken only where Definition 6.1 defines it: infinite `μ ≤ λ`.
The paper also assumes that `κ` satisfies the tree property, and its proof of (1) ⇒ (2) uses
Fact 6.3. Neither is needed, so this statement is stronger than Theorem 6.4 of the paper.
It is a thin wrapper around the AUX statement `treeExp_lt_iff_isInaccessible_of_isRegular`; the
proof does not follow the paper's proof. -/
theorem treeExp_lt_iff_isInaccessible (κ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (hreg : κ.IsRegular) :
    (∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      κ.IsInaccessible := sorry
```

#### `isWeaklyCompact_iff` (theorem)

```lean
/-- **Corollary 6.5** (Section 6). Let `κ` be an uncountable cardinal. Then `κ` is weakly compact
if and only if (1) `κ` is regular, (2) `κ` satisfies the tree property and (3) `λ^{μ,tr} < κ` for
each `λ, μ < κ` (as in Theorem 6.4: infinite `μ ≤ λ`).
In the paper this goes through Theorem 6.4, whose proof uses Fact 6.3. Fact 6.3 is not needed
(see `treeExp_lt_iff_isInaccessible`), so this statement, which has no Fact 6.3 hypothesis, is
stronger than Corollary 6.5 of the paper. -/
theorem isWeaklyCompact_iff (κ : Cardinal.{w}) (hunc : ℵ₀ < κ) :
    IsWeaklyCompact κ ↔
      κ.IsRegular ∧ NoAronszajn κ ∧
        ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ := sorry
```

### B. Auxiliary lemmas (AUX: not in paper)

#### `mk_lim_le` (theorem)

```lean
/-- AUX: not in paper. In a tree of height `μ`, a chain `b` is determined by the function
sending `α < μ` to the node of `b` of height `α` (if any); hence `|Lim(T)| ≤ (|T| + 1)^μ`. -/
theorem mk_lim_le {T : Type w} [PartialOrder T] [IsTree T] {μ : Cardinal.{w}}
    (hT : height T = μ.ord) : #(Lim T) ≤ (#T + 1) ^ μ := sorry
```

#### `treeExp_le_add_one_power` (theorem)

```lean
/-- AUX: not in paper. Every member of the set defining `λ^{μ,tr}` is `≤ (λ + 1)^μ`. -/
theorem treeExp_le_add_one_power (lam μ : Cardinal.{w}) : treeExp lam μ ≤ (lam + 1) ^ μ := sorry
```

#### `mk_lim_le_treeExp` (theorem)

```lean
/-- AUX: not in paper. If `T` has height `μ` and at most `λ` nodes, then `|Lim(T)| ≤ λ^{μ,tr}`. -/
theorem mk_lim_le_treeExp {T : Type w} [PartialOrder T] [IsTree T] {lam μ : Cardinal.{w}}
    (hT : height T = μ.ord) (hcard : #T ≤ lam) : #(Lim T) ≤ treeExp lam μ := sorry
```

#### `power_lt_of_isInaccessible` (theorem)

```lean
/-- AUX: not in paper. For an inaccessible `κ` and `λ, μ < κ`: `λ^μ < κ`. -/
theorem power_lt_of_isInaccessible {κ lam μ : Cardinal.{w}} (hκ : κ.IsInaccessible)
    (hlam : lam < κ) (hμ : μ < κ) : lam ^ μ < κ := sorry
```

#### `binRestr` (def)

```lean
/-- AUX: not in paper. A node of the full binary tree `2^{<ν}`: the graph of `f ↾ β`. -/
def binRestr {ν : Cardinal.{w}} (f : Kappa ν → Fin 2) (β : Kappa ν) : Set (Kappa ν × Fin 2) :=
  {p | p.1 < β ∧ p.2 = f p.1}
```

#### `binTree` (def)

```lean
/-- AUX: not in paper. The full binary tree `2^{<ν} = {f ↾ β : f : ν → 2, β < ν}`, ordered
by `⊆`. -/
def binTree (ν : Cardinal.{w}) : Set (Set (Kappa ν × Fin 2)) :=
  {g | ∃ (f : Kappa ν → Fin 2) (β : Kappa ν), g = binRestr f β}
```

#### `binRestr_subset_iff` (theorem)

```lean
/-- AUX: not in paper. Inclusion between nodes of `2^{<ν}`. -/
theorem binRestr_subset_iff {f f' : Kappa ν → Fin 2} {β β' : Kappa ν} :
    binRestr f β ⊆ binRestr f' β' ↔ β ≤ β' ∧ ∀ α < β, f α = f' α := sorry
```

#### `binRestr_eq_iff` (theorem)

```lean
/-- AUX: not in paper. Equality of nodes of `2^{<ν}`. -/
theorem binRestr_eq_iff {f f' : Kappa ν → Fin 2} {β β' : Kappa ν} :
    binRestr f β = binRestr f' β' ↔ β = β' ∧ ∀ α < β, f α = f' α := sorry
```

#### `binTree_isTree` (theorem)

```lean
/-- AUX: not in paper. `2^{<ν}` is a tree. -/
theorem binTree_isTree : IsTree (binTree ν) := sorry
```

#### `ht_binRestr` (theorem)

```lean
/-- AUX: not in paper. The height of `f ↾ β` in `2^{<ν}` is `β`. -/
theorem ht_binRestr (f : Kappa ν → Fin 2) (β : Kappa ν) :
    ht (⟨binRestr f β, f, β, rfl⟩ : binTree ν) = (β : Ordinal.{w}) := sorry
```

#### `height_binTree` (theorem)

```lean
/-- AUX: not in paper. The height of `2^{<ν}` is `ν`. -/
theorem height_binTree : height (binTree ν) = ν.ord := sorry
```

#### `mk_binTree_le` (theorem)

```lean
/-- AUX: not in paper. `|2^{<ν}| ≤ Σ_{β<ν} 2^{|β|}`. -/
theorem mk_binTree_le :
    #(binTree ν) ≤ Cardinal.sum fun β : Kappa ν => (2 : Cardinal.{w}) ^ #(Set.Iio β) := sorry
```

#### `two_power_le_mk_lim_binTree` (theorem)

```lean
/-- AUX: not in paper. For infinite `ν`, `2^{<ν}` has at least `2^ν` cofinal branches. -/
theorem two_power_le_mk_lim_binTree (hν : ℵ₀ ≤ ν) : 2 ^ ν ≤ #(Lim (binTree ν)) := sorry
```

#### `two_power_lt_of_treeExp_lt` (theorem)

```lean
/-- AUX: not in paper. Direction (1) ⇒ (2) of Theorem 6.4 without Fact 6.3 and without the tree
property: if `κ` is regular and uncountable and `λ^{μ,tr} < κ` for all infinite `μ ≤ λ < κ`,
then `2^ν < κ` for all `ν < κ` (apply the hypothesis to the full binary tree `2^{<ν}`). -/
theorem two_power_lt_of_treeExp_lt {κ : Cardinal.{w}} (hreg : κ.IsRegular)
    (h : ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) :
    ∀ ν < κ, 2 ^ ν < κ := sorry
```

#### `treeExp_lt_iff_isInaccessible_of_isRegular` (theorem)

```lean
/-- AUX: not in paper. A strengthening of Theorem 6.4: for every uncountable regular cardinal `κ`,
`λ^{μ,tr} < κ` for each `λ, μ < κ` (infinite `μ ≤ λ`, as in Theorem 6.4) iff `κ` is strongly
inaccessible.
The tree property, which is assumed in Theorem 6.4 of the paper, is omitted here; hence this
statement is stronger than Theorem 6.4. Theorem 6.4 follows from it.
Proof: (⇒) by induction on cardinals `ν < κ`, `2^ν < κ`, applying the hypothesis to the full
binary tree `2^{<ν}` (`two_power_lt_of_treeExp_lt`); Fact 6.3 is not used. (⇐) from Remark 6.2
and `λ^μ < κ` for strongly inaccessible `κ`. -/
theorem treeExp_lt_iff_isInaccessible_of_isRegular (κ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (hreg : κ.IsRegular) :
    (∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      κ.IsInaccessible := sorry
```

### C. Declarations without a docstring

#### `(anonymous instance)` (instance)

```lean
instance {T : Type w} [PartialOrder T] [IsTree T] (S : Set T) : IsTree S := isTree_subtype S
```

#### `(anonymous instance)` (instance)

```lean
instance : IsTree (binTree ν) := binTree_isTree
```

## Section 7 (`Section7.lean`)

### Context

```lean
open Cardinal
universe v w
noncomputable section
namespace JardenShami
open Tree
section TreeAux
variable {T : Type w} [PartialOrder T] [IsTree T]
end TreeAux
end JardenShami
```

### A. Paper definitions and statements

#### `Sim` (def)

```lean
/-- **Definition 7.1** (Section 7). `β ∼ γ` if for some `α` with `β, γ < α` we have
`C(β,α) = C(γ,α)` (`α` witnesses `β ∼ γ`). The paper states it for the fixed
`C : [κ]^2 → μ` of the standing assumption; here for any coloring of a linear order. -/
def Sim {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) (β γ : A) : Prop :=
  ∃ (α : A) (hβ : β < α) (hγ : γ < α), C.color β α hβ = C.color γ α hγ
```

#### `sim_witness_mono_and_equivalence` (theorem)

```lean
/-- **Remark 7.2** (Section 7, `\label{remark 7.2}`). Under the standing assumption of Subsection
7.1, except `μ < κ`, which is not needed and is not assumed here (`κ` regular,
`C : [κ]^2 → μ` *-locally additive): if `β ≠ γ`, `α₁` witnesses `β ∼ γ` and `α₁ < α₂`, then
`α₂` witnesses `β ∼ γ` as well. Hence `∼` is an equivalence relation. -/
theorem sim_witness_mono_and_equivalence (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C) :
    (∀ (β γ α₁ α₂ : Kappa κ) (hβ : β < α₁) (hγ : γ < α₁) (h₁₂ : α₁ < α₂), β ≠ γ →
        C.color β α₁ hβ = C.color γ α₁ hγ →
          C.color β α₂ (hβ.trans h₁₂) = C.color γ α₂ (hγ.trans h₁₂)) ∧
      Equivalence (Sim C) := sorry
```

#### `card_simClasses_le` (theorem)

```lean
/-- **Lemma 7.3** (Section 7, `\label{lemma number of equivalence classes}`). Under the standing
assumption of Subsection 7.1: if `μ⁺ < κ` then the number of `∼`-equivalence classes is at most
`μ`. The classes are counted as the sets `{γ : β ∼ γ}`, `β < κ`. The part `μ < κ` of the standing
assumption is not a hypothesis here (it follows from `μ⁺ < κ`). -/
theorem card_simClasses_le (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C)
    (h : Order.succ μ < κ) :
    #(Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ}) ≤ μ := sorry
```

#### `StarLaArrowKappa` (def)

```lean
/-- `κ → (κ)_{*-la_μ}` (Theorem 7.4, Proposition 7.5; written `κ →_{*-la} (κ)_μ` in the summary
at the start of Section 7), read as for `la_μ` in Section 5 (`LaArrowKappa`): every
*-locally additive coloring `C : [κ]^2 → μ` admits a homogeneous set of size `κ`. -/
def StarLaArrowKappa (κ μ : Cardinal.{w}) : Prop :=
  ∀ C : Coloring (Kappa κ) (Kappa μ), IsStarLocallyAdditive C →
    ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H
```

#### `starLaArrowKappa_of_succ_lt` (theorem)

```lean
/-- **Theorem 7.4** (Section 7, `\label{theorem shelah *-locally-additive}`, after
[Sh42, Theorem 1.1]). `κ → (κ)_{*-la_μ}` holds whenever `μ⁺ < κ = cf(κ)`. -/
theorem starLaArrowKappa_of_succ_lt (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ < κ) : StarLaArrowKappa κ μ := sorry
```

#### `not_starLaArrowKappa_of_succ_eq` (theorem)

```lean
/-- **Proposition 7.5** (Section 7, `\label{proposition mu^+<kappa can's be omitted}`).
`κ → (κ)_{*-la_μ}` does not hold if `μ⁺ = κ`. The standing assumption `κ = cf(κ)` of Subsection
7.1 is kept as `κ.IsRegular` (with Mathlib's definition this makes `κ`, hence `μ`, infinite; see
FIDELITY.md: for `μ ≤ 1` the statement without it is false). -/
theorem not_starLaArrowKappa_of_succ_eq (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ = κ) : ¬ StarLaArrowKappa κ μ := sorry
```

#### `exists_unique_extension_level` (theorem)

```lean
/-- **Claim 7.9** (Section 7, `\label{argue}`, inside Case A of the proof of Claim 7.8). Let
`λ` be regular and `T` a well-pruned `κ`-tree whose levels have size `< λ`.
For every ordinal `α < κ` with `cf(α) = λ` there is an ordinal `q(α) < α` such that for every
ordinal `β` with `q(α) < β < α` and any `a ∈ Lev_{q(α)}(T)` there are no two distinct
`b, c ∈ Lev_β(T)` with `a < b` and `a < c`. (In the paper `κ` is regular and `λ < κ`; these
hypotheses are not needed and are not assumed here.) -/
theorem exists_unique_extension_level (κ lam : Cardinal.{w})
    (hlamreg : lam.IsRegular) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hwp : WellPruned T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∀ α : Ordinal.{w}, α < κ.ord → α.cof = lam →
      ∃ q < α, ∀ β : Ordinal.{w}, q < β → β < α →
        ∀ a ∈ Lev T q, ∀ b ∈ Lev T β, ∀ c ∈ Lev T β, a < b → a < c → b = c := sorry
```

#### `not_isAronszajn_of_card_lev_lt` (theorem)

```lean
/-- **Claim 7.8** (Section 7, `\label{the exercise of kunen}`; recalled from
[Large, Proposition 7.9] and proved in the paper "for completeness"). Let `κ` and `λ` be cardinals
such that `κ` is regular and `λ < κ`. If `T` is a `κ`-tree whose levels have size `< λ`, then
`T` is not `κ`-Aronszajn. -/
theorem not_isAronszajn_of_card_lev_lt (κ lam : Cardinal.{w})
    (hκ : κ.IsRegular) (hlam : lam < κ) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ¬ IsAronszajn κ T := sorry
```

#### `laArrowKappa_of_succ_lt` (theorem)

```lean
/-- **Theorem 7.7** (Section 7, `\label{the only theorem}`). Let `κ` be a regular cardinal and
`μ` a cardinal with `μ⁺ < κ`. Then `κ → (κ)_{la_μ}` (in the sense of Section 5,
`LaArrowKappa`). -/
theorem laArrowKappa_of_succ_lt (κ μ : Cardinal.{w})
    (hκ : κ.IsRegular) (h : Order.succ μ < κ) : LaArrowKappa κ μ := sorry
```

### B. Auxiliary lemmas (AUX: not in paper)

#### `Coloring.color_dual` (theorem)

```lean
/-- AUX: not in paper. A pair read in the reverse order. -/
theorem Coloring.color_dual {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D)
    (a b : Aᵒᵈ) (h : a < b) :
    Coloring.color (A := Aᵒᵈ) C a b h =
      C.color (OrderDual.ofDual b) (OrderDual.ofDual a) h := sorry
```

#### `isStarLocallyAdditive_iff` (theorem)

```lean
/-- AUX: not in paper. *-local additivity spelled out in the original order: for
`x < y < z < w`, `C(y,z) = C(x,z)` implies `C(y,w) = C(x,w)`. -/
theorem isStarLocallyAdditive_iff {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) :
    IsStarLocallyAdditive C ↔
      ∀ (x y z w : A) (hxy : x < y) (hyz : y < z) (hzw : z < w),
        C.color y z hyz = C.color x z (hxy.trans hyz) →
          C.color y w (hyz.trans hzw) = C.color x w ((hxy.trans hyz).trans hzw) := sorry
```

#### `Kappa.exists_gt` (theorem)

```lean
/-- AUX: not in paper. For infinite `κ`, `κ` has no largest element. -/
theorem Kappa.exists_gt {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ) (x : Kappa κ) : ∃ y, x < y := sorry
```

#### `ht_subtype_of_downward` (theorem)

```lean
/-- AUX: not in paper. In a downward closed subset `S` of a tree, heights computed in `S` and
in `T` agree. -/
theorem ht_subtype_of_downward {S : Set T} (hS : ∀ s ∈ S, ∀ t < s, t ∈ S) (x : S) :
    ht x = ht (x : T) := sorry
```

#### `exists_le_ht_eq` (theorem)

```lean
/-- AUX: not in paper. Every node lies above a node of each smaller level. -/
theorem exists_le_ht_eq {t : T} {α : Ordinal.{w}} (h : α ≤ ht t) : ∃ s ≤ t, ht s = α := sorry
```

#### `exists_big_cone` (theorem)

```lean
omit [IsTree T] in
/-- AUX: not in paper. For regular `κ`: if a set `U` of size `≥ κ` is covered by the cones
`{s : y ≤ s}` of fewer than `κ` nodes `y ∈ L`, then one of these cones has size `≥ κ`. -/
theorem exists_big_cone {κ : Cardinal.{w}} (hκ : κ.IsRegular) {U L : Set T} (hU : κ ≤ #U)
    (hL : #L < κ) (hcov : ∀ s ∈ U, ∃ y ∈ L, y ≤ s) : ∃ y ∈ L, κ ≤ #(Set.Ici y) := sorry
```

#### `mk_levLt_lt` (theorem)

```lean
/-- AUX: not in paper. In a `κ`-tree (`κ` regular), the nodes of height `< α` (`α < κ`) are
fewer than `κ`. -/
theorem mk_levLt_lt {κ : Cardinal.{w}} (hκ : κ.IsRegular) (hT : IsKappaTree κ T)
    {α : Ordinal.{w}} (hα : α < κ.ord) : #{s : T | ht s < α} < κ := sorry
```

#### `exists_big_above` (theorem)

```lean
/-- AUX: not in paper. In a `κ`-tree (`κ` regular): if `x` has `≥ κ` nodes above it and
`ht x < α < κ`, then some `y ∈ Lev_α(T)` with `x < y` has `≥ κ` nodes above it. -/
theorem exists_big_above {κ : Cardinal.{w}} (hκ : κ.IsRegular) (hT : IsKappaTree κ T) {x : T}
    (hx : κ ≤ #(Set.Ici x)) {α : Ordinal.{w}} (hxα : ht x < α) (hα : α < κ.ord) :
    ∃ y ∈ Lev T α, x < y ∧ κ ≤ #(Set.Ici y) := sorry
```

#### `exists_wellPruned_subtree_downward` (theorem)

```lean
/-- AUX: not in paper. Strong form of `exists_wellPruned_subtree`: for regular `κ`, every
`κ`-tree has a downward closed subset (so heights are the same as in `T`) which is a well-pruned
`κ`-tree: the nodes above a fixed root `r` that have `κ` nodes above them. -/
theorem exists_wellPruned_subtree_downward (κ : Cardinal.{w}) (hκ : κ.IsRegular)
    (T : Type w) [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) :
    ∃ S : Set T, (∀ s ∈ S, ∀ t < s, t ∈ S) ∧ IsKappaTree κ S ∧ WellPruned S := sorry
```

#### `exists_wellPruned_subtree` (theorem)

```lean
/-- AUX: not in paper. In the proof of Claim 7.8, Case A, the paper calls this a well-known fact
("it a well-known fact that every `κ`-tree has a well-pruned subtree which is a `κ`-tree") and
does not prove it. Stated for regular `κ`, the only case used (Claim 7.8 assumes `κ` regular); for
singular `κ` it can fail. A subtree is a subset with the induced order. -/
theorem exists_wellPruned_subtree (κ : Cardinal.{w}) (hκ : κ.IsRegular)
    (T : Type w) [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) :
    ∃ S : Set T, IsKappaTree κ S ∧ WellPruned S := sorry
```

#### `le_of_le_of_le_of_ht_le` (theorem)

```lean
/-- AUX: not in paper. Two nodes below a common node: the lower one is below the other. -/
theorem le_of_le_of_le_of_ht_le {T : Type w} [PartialOrder T] [IsTree T] {u v z : T}
    (hu : u ≤ z) (hv : v ≤ z) (h : ht u ≤ ht v) : u ≤ v := sorry
```

#### `le_mk_lev_of_splitting` (theorem)

```lean
/-- AUX: not in paper. The diagonal construction in the proof of Claim 7.9, in a general form.
Let `α` be a level such that every node of smaller height has an extension in `Lev_α(T)`, and
such that fewer than `ρ` ordinals below `α` are bounded below `α`. If for every `q ∈ [α₀, α)` some
`a ∈ Lev_q(T)` has two distinct extensions `b, c` of the same height `< α`, then
`|Lev_α(T)| ≥ ρ`. (The paper builds `d_i ∈ Lev_α(T)`, `i < λ`, by induction.) -/
theorem le_mk_lev_of_splitting {T : Type w} [PartialOrder T] [IsTree T] {ρ : Cardinal.{w}}
    {α α₀ : Ordinal.{w}} (hext : ∀ x : T, ht x < α → ∃ y ∈ Lev T α, x < y)
    (hbd : ∀ (ι : Type w) (f : ι → Ordinal.{w}), #ι < ρ → (∀ i, f i < α) →
      ∃ q < α, ∀ i, f i ≤ q)
    (hα₀ : α₀ < α)
    (hsplit : ∀ q : Ordinal.{w}, α₀ ≤ q → q < α → ∃ a b c : T, ht a = q ∧ q < ht b ∧
      ht b < α ∧ ht c = ht b ∧ a < b ∧ a < c ∧ b ≠ c) :
    ρ ≤ #(Lev T α) := sorry
```

#### `mk_lev_mono` (theorem)

```lean
/-- AUX: not in paper. In a well-pruned tree, the sizes of the levels are non-decreasing (the
restriction map `Lev_β(T) → Lev_α(T)` is onto). -/
theorem mk_lev_mono {T : Type w} [PartialOrder T] [IsTree T] (hwp : WellPruned T)
    {α β : Ordinal.{w}} (hαβ : α ≤ β) (hβ : β < height T) : #(Lev T α) ≤ #(Lev T β) := sorry
```

#### `exists_mk_lev_const` (theorem)

```lean
/-- AUX: not in paper. In a well-pruned `κ`-tree (`κ` regular) whose levels have size `< λ`,
`λ < κ`, the sizes of the levels are eventually constant. -/
theorem exists_mk_lev_const {κ lam : Cardinal.{w}} (hκ : κ.IsRegular) (hlam : lam < κ)
    {T : Type w} [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) (hwp : WellPruned T)
    (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∃ α₀ < κ.ord, ∀ β : Ordinal.{w}, α₀ ≤ β → β < κ.ord → #(Lev T β) = #(Lev T α₀) := sorry
```

#### `exists_closed_level` (theorem)

```lean
/-- AUX: not in paper. For regular `ρ < κ` (`κ` regular) and any `σ` mapping `κ` to `κ`, there
is a level `α ∈ (α₀, κ)` closed under `σ` such that any fewer than `ρ` ordinals below `α` are
bounded below `α` (`α` is the supremum of a `ρ`-sequence closing off under `σ`). -/
theorem exists_closed_level {κ ρ : Cardinal.{w}} (hκ : κ.IsRegular) (hρ : ρ.IsRegular)
    (hρκ : ρ < κ) {α₀ : Ordinal.{w}} (hα₀ : α₀ < κ.ord) (σ : Ordinal.{w} → Ordinal.{w})
    (hσ : ∀ q < κ.ord, σ q < κ.ord) :
    ∃ α, α₀ < α ∧ α < κ.ord ∧ (∀ q < α, σ q < α) ∧
      ∀ (ι : Type w) (f : ι → Ordinal.{w}), #ι < ρ → (∀ i, f i < α) → ∃ q < α, ∀ i, f i ≤ q := sorry
```

#### `exists_nonsplitting` (theorem)

```lean
/-- AUX: not in paper. In a well-pruned `κ`-tree (`κ` regular) whose levels have size `< λ`,
`λ < κ`, some node `a` does not split: any two nodes above `a` of the same height are equal.
(Replaces Cases A and B of the paper's proof of Claim 7.8: the level sizes are eventually a constant
`n < λ`; for finite `n` the restriction maps are bijective, and for infinite `n` the diagonal
argument of Claim 7.9 (`le_mk_lev_of_splitting`) at a level closed under splitting and of
cofinality `≥ n⁺` (`exists_closed_level`) gives a level of size `≥ n⁺`.) -/
theorem exists_nonsplitting {κ lam : Cardinal.{w}} (hκ : κ.IsRegular) (hlam : lam < κ)
    {T : Type w} [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) (hwp : WellPruned T)
    (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∃ a : T, ∀ b c : T, a < b → a < c → ht b = ht c → b = c := sorry
```

#### `exists_isCofinalBranch_of_isChain` (theorem)

```lean
/-- AUX: not in paper. In a `κ`-tree, a chain of size `≥ κ` yields a cofinal branch. -/
theorem exists_isCofinalBranch_of_isChain {κ : Cardinal.{w}} {T : Type w} [PartialOrder T]
    [IsTree T] (hT : IsKappaTree κ T) {c : Set T} (hc : IsChain (· ≤ ·) c) (hcκ : κ ≤ #c) :
    ∃ b : Set T, IsCofinalBranch b := sorry
```
