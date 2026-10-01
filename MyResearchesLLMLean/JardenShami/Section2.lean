import Mathlib

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 2

Section 2 ("Basic Definitions"): colorings, homogeneous sets, additive, locally-additive
and *-locally-additive colorings, the maps `u_{a,b}`, the classes `add_μ`, `la_μ`, ...
and the generalized arrow notation `F₁ → (F₂)_𝔆`.

Phase 0: statements only; every proof is `sorry`.

## Encoding conventions
* `[A]^2`, the set of 2-element subsets of `A`, is `Pairs A`: the non-diagonal elements of
  `Sym2 A`. A coloring of `A` with colors in `D` is a function `Pairs A → D`; it has
  `μ` colors when `#D = μ` (the paper counts the codomain `D`, not the range).
* For `a < b` the paper writes `C(a,b)` for `C({a,b})`; here this is `C.color a b h`
  with `h : a < b`.
* Since a coloring is a function on unordered pairs, the same `C` is also a coloring of the
  reverse order `Aᵒᵈ`; this is used for *-local additivity.
* A cardinal `κ` with its `∈`-order is `κ.ord.ToType`.
* A "class of colorings" is a predicate on triples `(S, D, C)` where `S` is a subset of a fixed
  linearly ordered type `X`, `D : Type v` is the set of colors and `C` a coloring of `S`.
  Colors live in one fixed universe `v`.
-/

open Cardinal

universe v w

noncomputable section

namespace JardenShami

/-! ## Definition 2.1: colorings -/

/-- **Definition 2.1** (`[A]^2`). The set of 2-element subsets of `A`, encoded as the
non-diagonal unordered pairs. -/
def Pairs (A : Type w) : Type w := {z : Sym2 A // ¬ z.IsDiag}

/-- The pair `{a, b}` as an element of `[A]^2`, for `a ≠ b`. -/
def Pairs.mk {A : Type w} (a b : A) (h : a ≠ b) : Pairs A :=
  ⟨s(a, b), by simpa [Sym2.mk_isDiag_iff] using h⟩

/-- **Definition 2.1** (Section 2). A coloring (edge coloring) of the set `A` with colors in
the set `D`: a function `C : [A]^2 → D`. It is a coloring with `μ` colors when `#D = μ`. -/
abbrev Coloring (A : Type w) (D : Type v) : Type (max w v) := Pairs A → D

/-- **Definition 2.1** (Section 2), notation: for `a < b` in a linearly ordered `A`,
`C(a,b)` stands for `C({a,b})`. -/
def Coloring.color {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) (a b : A)
    (h : a < b) : D :=
  C (Pairs.mk a b h.ne)

/-! ## Definition 2.2: homogeneous sets -/

/-- **Definition 2.2** (Section 2). `B ⊆ A` is homogeneous for `C` if `C ↾ [B]^2` is constant,
i.e. any two pairs contained in `B` get the same color. -/
def IsHomogeneous {A : Type w} {D : Type v} (C : Coloring A D) (B : Set A) : Prop :=
  ∀ p q : Pairs A, (∀ x ∈ p.1, x ∈ B) → (∀ x ∈ q.1, x ∈ B) → C p = C q

section LinearOrder

variable {A : Type w} [LinearOrder A] {D : Type v}

/-! ## Definitions 2.3, 2.4 and 2.6: additive and locally-additive colorings -/

/-- **Definition 2.3** (Section 2, after [Sh42, §1]). `C : [A]^2 → D` is additive if there is
`s : D × D → D` such that `C(a,c) = s(C(a,b), C(b,c))` for all `a < b < c` in `A`. -/
def IsAdditive (C : Coloring A D) : Prop :=
  ∃ s : D × D → D, ∀ (a b c : A) (hab : a < b) (hbc : b < c),
    C.color a c (hab.trans hbc) = s (C.color a b hab, C.color b c hbc)

/-- **Definition 2.4** (Section 2). `C : [A]^2 → D` is locally-additive if for all
`a < b < c < d` in `A`: `C(b,c) = C(b,d) → C(a,c) = C(a,d)`. -/
def IsLocallyAdditive (C : Coloring A D) : Prop :=
  ∀ (a b c d : A) (hab : a < b) (hbc : b < c) (hcd : c < d),
    C.color b c hbc = C.color b d (hbc.trans hcd) →
      C.color a c (hab.trans hbc) = C.color a d ((hab.trans hbc).trans hcd)

/-- **Definition 2.6** (Section 2, second sentence). `C` is *-locally additive if it is
locally-additive with respect to the reverse order. The paper states this for colorings of a
cardinal `κ`; here it is stated for any linear order, and for a cardinal one takes
`A = κ.ord.ToType` (see `Kappa`). -/
def IsStarLocallyAdditive (C : Coloring A D) : Prop :=
  IsLocallyAdditive (A := Aᵒᵈ) C

/-! ## Notation 2.5: the sets `D_b` and the maps `u_{a,b}` -/

/-- **Notation 2.5** (Section 2). `D_b`: the set of colors `t` such that `C(b,c) = t` for some
`c > b`. -/
def Dset (C : Coloring A D) (b : A) : Set D :=
  {t | ∃ (c : A) (h : b < c), C.color b c h = t}

/-- **Notation 2.5** (Section 2). For `a < b`, `u_{a,b} : D_b → D`, `u_{a,b}(C(b,c)) = C(a,c)`.
Encoded by choosing, for `t ∈ D_b`, some witness `c > b` with `C(b,c) = t`; the value does not
depend on the choice exactly when `C` is locally additive (see `uMap_wellDefined_iff`). -/
def uMap (C : Coloring A D) (a b : A) (hab : a < b) : Dset C b → D :=
  fun t => C.color a (Classical.choose t.2) (hab.trans (Classical.choose_spec t.2).fst)

/-- **Notation 2.5** (Section 2), the defining equation `u_{a,b}(C(b,c)) = C(a,c)`, for a locally
additive `C` and `a < b < c`. (With the choice-based encoding of `uMap` this is a statement.) -/
theorem uMap_color {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    uMap C a b hab ⟨C.color b c hbc, c, hbc, rfl⟩ = C.color a c (hab.trans hbc) := by
  sorry

/-- **Note after Notation 2.5** (Section 2, unnumbered). `u_{a,b}` is well-defined for each
`a < b` (i.e. `C(b,c) = C(b,c')` implies `C(a,c) = C(a,c')` for `c, c' > b`) if and only if `C`
is locally additive. -/
theorem uMap_wellDefined_iff (C : Coloring A D) :
    (∀ (a b c c' : A) (hab : a < b) (hbc : b < c) (hbc' : b < c'),
        C.color b c hbc = C.color b c' hbc' →
          C.color a c (hab.trans hbc) = C.color a c' (hab.trans hbc')) ↔
      IsLocallyAdditive C := by
  sorry

/-! ## Remark 2.7 and Claim 2.8 -/

/-- **Remark 2.7** (Section 2). Every additive coloring is locally-additive. -/
theorem additive_isLocallyAdditive {C : Coloring A D} (hC : IsAdditive C) :
    IsLocallyAdditive C := by
  sorry

/-- **Claim 2.8** (Section 2, `\label{C^* is additive}`). For a locally additive `C` and
`a < b < c`: `u_{a,b} ∘ u_{b,c} = u_{a,c}` as functions on `D_c`. The composition makes sense
because `u_{b,c}` maps `D_c` into `D_b`; this is part of the statement. -/
theorem uMap_comp {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    ∀ t : Dset C c, ∃ h : uMap C b c hbc t ∈ Dset C b,
      uMap C a b hab ⟨uMap C b c hbc t, h⟩ = uMap C a c (hab.trans hbc) t := by
  sorry

end LinearOrder

/-! ## Definition 2.6: colorings of a cardinal -/

/-- **Definition 2.6** (Section 2). A cardinal `κ`, as the set of ordinals below it, with its
`∈`-order. A coloring of `κ` is locally-additive if `IsLocallyAdditive` holds for it as a
coloring of `Kappa κ`, and *-locally additive if `IsStarLocallyAdditive` holds. -/
abbrev Kappa (κ : Cardinal.{w}) : Type w := κ.ord.ToType

/-! ## Notation 2.9: classes of colorings -/

/-- A class of colorings of subsets of the linearly ordered type `X` (used in Notation 2.9 and
Definition 2.10): a predicate on `(S, D, C)` with `S ⊆ X`, `D` the set of colors and
`C : [S]^2 → D`. `S` carries the order induced from `X`. -/
def ColoringClass (X : Type w) [LinearOrder X] : Type (max w (v + 1)) :=
  ∀ (S : Set X) (D : Type v), Coloring S D → Prop

section Classes

variable {X : Type w} [LinearOrder X]

/-- **Definition 2.10** (Section 2, last sentence): "`μ` for `𝔆`", the class of all colorings
with `μ` colors. -/
def allColorings (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D _ => #D = μ

/-- **Notation 2.9 (1)** (Section 2). `add`: the class of additive colorings. -/
def add : ColoringClass.{v, w} X := fun _ _ C => IsAdditive C

/-- **Notation 2.9 (2)** (Section 2). `add_μ`: additive colorings with `μ` colors. -/
def addEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsAdditive C ∧ #D = μ

/-- **Notation 2.9 (3)** (Section 2). `add_{<μ}`: additive colorings with fewer than `μ`
colors. -/
def addLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsAdditive C ∧ #D < μ

/-- **Notation 2.9 (4)** (Section 2). `la`: the class of locally-additive colorings. -/
def la : ColoringClass.{v, w} X := fun _ _ C => IsLocallyAdditive C

/-- **Notation 2.9 (6)** (Section 2). `la_μ`: locally-additive colorings with `μ` colors. -/
def laEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsLocallyAdditive C ∧ #D = μ

/-- **Notation 2.9 (6)** (Section 2). `la_{<μ}`: locally-additive colorings with fewer than `μ`
colors. -/
def laLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsLocallyAdditive C ∧ #D < μ

/-- The domain `S` of a coloring "is a regular cardinal": `S` (with the order induced from `X`)
is order-isomorphic to a regular cardinal with its `∈`-order. Used in Notation 2.9 (5). -/
def IsRegularCardinalOrder (S : Set X) : Prop :=
  ∃ κ : Cardinal.{w}, κ.IsRegular ∧ Nonempty (S ≃o Kappa κ)

/-- **Notation 2.9 (5)** (Section 2). `*-la`: the class of *-locally additive colorings on a
regular cardinal. -/
def starLa : ColoringClass.{v, w} X :=
  fun S _ C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C

/-- **Notation 2.9 (6)** (Section 2). `*-la_μ`: *-locally additive colorings on a regular
cardinal with `μ` colors. -/
def starLaEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X :=
  fun S D C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C ∧ #D = μ

/-- **Notation 2.9 (6)** (Section 2). `*-la_{<μ}`: *-locally additive colorings on a regular
cardinal with fewer than `μ` colors. -/
def starLaLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X :=
  fun S D C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C ∧ #D < μ

/-! ## Definition 2.10: the arrow notation -/

/-- **Definition 2.10** (Section 2). `F₁ → (F₂)_𝔆`: for every `S ∈ F₁` and every coloring
`C ∈ 𝔆` of `S` there is `E ⊆ S` with `E ∈ F₂` and `C ↾ [E]^2` constant. -/
def Arrow (F₁ F₂ : Set (Set X)) (𝔆 : ColoringClass.{v, w} X) : Prop :=
  ∀ S ∈ F₁, ∀ (D : Type v) (C : Coloring S D), 𝔆 S D C →
    ∃ E : Set S, Subtype.val '' E ∈ F₂ ∧ IsHomogeneous C E

end Classes

/-- **Definition 2.10** (Section 2, last sentence): "`κ` for `F₁`", the family of subsets of
`κ` of cardinality `κ`. -/
def bigSubsets (κ : Cardinal.{w}) : Set (Set (Kappa κ)) := {S | #S = κ}

end JardenShami
