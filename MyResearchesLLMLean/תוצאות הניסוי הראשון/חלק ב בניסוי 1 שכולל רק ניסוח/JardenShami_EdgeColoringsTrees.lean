import Mathlib

/-!
# A note on edge colorings and trees  (A. Jarden, Z. Shami, arXiv:2204.06874v1)

Lean 4 / Mathlib statements of the definitions, remarks, claims, lemmas, theorems and corollaries
of the paper.  Every proof is replaced by `sorry`.  The file has NOT been compiled.

Numbering follows the paper.  Claims that appear *inside* a proof in the paper
(Claims 4.16-4.19, Claim 5.4, Claim 7.9) are considered part of that proof and are not stated.

## Modelling conventions
* A cardinal `κ` is regarded, as in the paper, as the set of ordinals below it:
  `Kappa κ := Set.Iio κ.ord`, ordered by `<` (the `∈`-order).  This lives one universe up
  (`Type (u+1)`), so sizes of subsets of `Kappa κ` and of color sets are compared with
  `up κ := Cardinal.lift κ`.
* `[A]^2 → D` is modelled by `Sym2 A → D`; only the values on non-diagonal pairs `s(a,b)`, `a ≠ b`,
  are ever used by the definitions.  `C(a,b)` for `a < b` is `C s(a,b)`.
* Trees are set-theoretic trees (`STree`); nodes have heights (ordinals), levels, etc.
* The words "isomorphic trees" are formalised as `Nonempty (T ≃o S)` (order isomorphism).
-/

open scoped Cardinal

universe u v w

noncomputable section

namespace JardenShami

/-! ## 2. Basic definitions -/

/-- **Definition 2.1.** A coloring of `A` with colors from `D` is a function `[A]^2 → D`.
(It is "with `μ` colors" when `#D = μ`.) -/
abbrev Coloring (A : Type w) (D : Type v) : Type (max w v) := Sym2 A → D

/-- Auxiliary (not in the paper): the coloring `C` with `C(a,b) = g a b` whenever `a < b`. -/
def Coloring.ofLT {A : Type w} [LinearOrder A] {D : Type v} (g : A → A → D) : Coloring A D :=
  Sym2.lift ⟨fun a b => if a ≤ b then g a b else g b a, by
    intro a b
    by_cases h : a ≤ b
    · by_cases h' : b ≤ a
      · have hab : a = b := le_antisymm h h'
        subst hab
        simp
      · simp [h, h']
    · have h' : b ≤ a := (not_le.mp h).le
      simp [h, h']⟩

/-- **Definition 2.2.** `B ⊆ A` is homogeneous for `C` if `C ↾ [B]^2` is constant. -/
def IsHomogeneous {A : Type w} {D : Type v} (C : Coloring A D) (B : Set A) : Prop :=
  ∃ d : D, ∀ x ∈ B, ∀ y ∈ B, x ≠ y → C s(x, y) = d

section basic

variable {A : Type w} [LinearOrder A] {D : Type v}

/-- **Definition 2.3.** (Shelah) additive coloring. -/
def IsAdditive (C : Coloring A D) : Prop :=
  ∃ s : D × D → D, ∀ a b c : A, a < b → b < c → C s(a, c) = s (C s(a, b), C s(b, c))

/-- **Definition 2.4.** locally additive coloring. -/
def IsLocallyAdditive (C : Coloring A D) : Prop :=
  ∀ a b c d : A, a < b → b < c → c < d → C s(b, c) = C s(b, d) → C s(a, c) = C s(a, d)

/-- **Definition 2.6 (second half).** `*`-locally additive: locally additive with respect to the
reverse order of `A`  (`a <* b <* c <* d` means `d < c < b < a`).  For a cardinal `κ`, use it for
colorings of `Kappa κ`; `IsLocallyAdditive` is then locally additive w.r.t. the `∈`-order of `κ`. -/
def IsStarLocallyAdditive (C : Coloring A D) : Prop :=
  ∀ a b c d : A, d < c → c < b → b < a → C s(b, c) = C s(b, d) → C s(a, c) = C s(a, d)

/-- **Notation 2.5.** `D_b`: the colors `t` with `C(b,c) = t` for some `c > b`. -/
def Dcol (C : Coloring A D) (b : A) : Set D := {t | ∃ c, b < c ∧ C s(b, c) = t}

/-- **Notation 2.5.** `u_{a,b} : D_b → D`, `u_{a,b}(C(b,c)) = C(a,c)`
(defined by choosing a witness `c`; it is well defined iff `C` is locally additive). -/
def uMap (C : Coloring A D) (a b : A) : Dcol C b → D :=
  fun t => C s(a, Classical.choose (show ∃ c, b < c ∧ C s(b, c) = t.1 from t.2))

/-- **Notation 2.5 (the "Note").** `u_{a,b}` is well defined for each `a < b` iff `C` is
locally additive. -/
theorem uMap_wellDefined_iff (C : Coloring A D) :
    (∀ a b : A, a < b → ∀ c c' : A, b < c → b < c' →
        C s(b, c) = C s(b, c') → C s(a, c) = C s(a, c')) ↔ IsLocallyAdditive C := by
  sorry

/-- The defining property of `u_{a,b}` (for locally additive `C`). -/
theorem uMap_spec {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    uMap C a b ⟨C s(b, c), c, hbc, rfl⟩ = C s(a, c) := by
  sorry

/-- **Remark 2.7.** Every additive coloring is locally additive. -/
theorem remark_2_7 {C : Coloring A D} (hC : IsAdditive C) : IsLocallyAdditive C := by
  sorry

/-- **Claim 2.8.** For a locally additive `C` and `a < b < c`: `u_{a,b} ∘ u_{b,c} = u_{a,c}`
(as functions on `D_c`; in particular `u_{b,c}(t) ∈ D_b`). -/
theorem claim_2_8 {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    ∀ t : Dcol C c, ∃ h : uMap C b c t ∈ Dcol C b,
      uMap C a b ⟨uMap C b c t, h⟩ = uMap C a c t := by
  sorry

end basic

/-- A "class of colorings" `𝒞` (Definition 2.10): for every subset `S` of the ambient linear order
and every set of colors `D`, a predicate on the colorings of `S` with colors in `D`. -/
def ColoringClass (X : Type w) [LinearOrder X] : Type (max w (v + 1)) :=
  ∀ (S : Set X) (D : Type v), Coloring S D → Prop

section classes

variable {X : Type w} [LinearOrder X]

/-- All colorings with `μ` colors ("we put `μ` for `𝒞`"). -/
def allColorings (μ : Cardinal.{v}) : ColoringClass X := fun _ D _ => #D = μ

/-- **Notation 2.9.** (1) `add`. -/
def addAll : ColoringClass.{w, v} X := fun _ _ C => IsAdditive C
/-- (2) `add_μ`. -/
def addEq (μ : Cardinal.{v}) : ColoringClass X := fun _ D C => IsAdditive C ∧ #D = μ
/-- (3) `add_{<μ}`. -/
def addLt (μ : Cardinal.{v}) : ColoringClass X := fun _ D C => IsAdditive C ∧ #D < μ
/-- (4) `la`. -/
def laAll : ColoringClass.{w, v} X := fun _ _ C => IsLocallyAdditive C
/-- (6) `la_μ`. -/
def laEq (μ : Cardinal.{v}) : ColoringClass X := fun _ D C => IsLocallyAdditive C ∧ #D = μ
/-- (6) `la_{<μ}`. -/
def laLt (μ : Cardinal.{v}) : ColoringClass X := fun _ D C => IsLocallyAdditive C ∧ #D < μ
/-- (5) `*-la` (in the paper: on a regular cardinal; here `X` is the ambient order). -/
def starLaAll : ColoringClass.{w, v} X := fun _ _ C => IsStarLocallyAdditive C
/-- (6) `*-la_μ`. -/
def starLaEq (μ : Cardinal.{v}) : ColoringClass X := fun _ D C => IsStarLocallyAdditive C ∧ #D = μ
/-- (6) `*-la_{<μ}`. -/
def starLaLt (μ : Cardinal.{v}) : ColoringClass X := fun _ D C => IsStarLocallyAdditive C ∧ #D < μ

/-- **Definition 2.10.** `F₁ → (F₂)_𝒞`: for every `A ∈ F₁` and every coloring `C ∈ 𝒞` of `A`
there is `E ⊆ A`, `E ∈ F₂`, with `C ↾ [E]^2` constant. -/
def Arrow (F₁ F₂ : Set (Set X)) (𝒞 : ColoringClass.{w, v} X) : Prop :=
  ∀ A ∈ F₁, ∀ (D : Type v) (C : Coloring A D), 𝒞 A D C →
    ∃ E : Set A, Subtype.val '' E ∈ F₂ ∧ IsHomogeneous C E

end classes

/-- The cardinal `κ` as a set of ordinals (ordered by `∈ = <`). -/
abbrev Kappa (κ : Cardinal.{u}) : Type (u + 1) := ↥(Set.Iio κ.ord)

/-- `Cardinal.lift` to the universe of `Kappa κ`. -/
abbrev up (μ : Cardinal.{u}) : Cardinal.{u + 1} := Cardinal.lift.{u + 1, u} μ

/-- Definition 2.10, last paragraph: the family of subsets of `κ` of cardinality `κ`. -/
def bigSubsets (κ : Cardinal.{u}) : Set (Set (Kappa κ)) := {S | #S = up κ}

/-- `κ → (κ)_𝒞` : Definition 2.10 with `F₁ = F₂ =` subsets of `κ` of size `κ`. -/
def KappaArrow (κ : Cardinal.{u}) (𝒞 : ColoringClass (Kappa κ)) : Prop :=
  Arrow (bigSubsets κ) (bigSubsets κ) 𝒞

/-- `κ → (κ)_μ` (𝒞 = all colorings with `μ` colors). -/
def PartitionRel (κ μ : Cardinal.{u}) : Prop := KappaArrow κ (allColorings (up μ))
/-- `κ → (κ)^{la}_μ`. -/
def LaArrow (κ μ : Cardinal.{u}) : Prop := KappaArrow κ (laEq (up μ))
/-- `κ →^{*-la} (κ)_μ`. -/
def StarLaArrow (κ μ : Cardinal.{u}) : Prop := KappaArrow κ (starLaEq (up μ))

/-! ## 3. Replacing additivity by local additivity -/

section sec3

variable {X : Type w} [LinearOrder X]

/-- **Theorem 3.1.** -/
theorem thm_3_1 (κ μ : Cardinal.{v}) (hκ : 2 ^ μ + ℵ₀ ≤ κ) (F : Set (Set X))
    (h : Arrow F F (addEq κ)) : Arrow F F (laEq μ) := by
  sorry

/-- **Corollary 3.2.** -/
theorem cor_3_2 (μ : Cardinal.{v}) (hμ : μ.IsStrongLimit) (F : Set (Set X))
    (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) := by
  sorry

/-- **Corollary 3.3.** -/
theorem cor_3_3 (F : Set (Set X)) (h : Arrow F F (addLt (ℵ₀ : Cardinal.{v}))) :
    Arrow F F (laLt (ℵ₀ : Cardinal.{v})) := by
  sorry

end sec3

/-- "`S` is dense in some interval of `I`" (interpretation: an order-convex set `J` with at least
two points such that between any two points of `J` there is a point of `S`). -/
def DenseInSomeInterval {I : Type w} [LinearOrder I] (S : Set I) : Prop :=
  ∃ J : Set I, J.OrdConnected ∧ (∃ x ∈ J, ∃ y ∈ J, x < y) ∧
    ∀ x ∈ J, ∀ y ∈ J, x < y → ∃ s ∈ S, x < s ∧ s < y

/-- **Fact 3.4.** [Shelah, Thm 1.3] -/
theorem fact_3_4 (I : Type w) [LinearOrder I] [DenselyOrdered I] :
    Arrow {S : Set I | DenseInSomeInterval S} {S : Set I | DenseInSomeInterval S}
      (addLt (ℵ₀ : Cardinal.{v})) := by
  sorry

/-- **Corollary 3.5.** -/
theorem cor_3_5 (I : Type w) [LinearOrder I] [DenselyOrdered I] :
    Arrow {S : Set I | DenseInSomeInterval S} {S : Set I | DenseInSomeInterval S}
      (laLt (ℵ₀ : Cardinal.{v})) := by
  sorry

/-! ## 4. Trees and colorings -/

/-- A tree: a partial order in which the set of predecessors of every node is well-ordered. -/
class STree (T : Type w) extends PartialOrder T where
  wellOrdered_predecessors :
    ∀ t : T, IsWellOrder (Set.Iio t) (fun x y => (x : T) < y)

namespace STree

/-- `ht(t, T)`: the order type of the set of predecessors of `t`. -/
def ht {T : Type w} [STree T] (t : T) : Ordinal.{w} :=
  haveI := STree.wellOrdered_predecessors t
  Ordinal.type (fun x y : Set.Iio t => (x : T) < y)

/-- `Lev_α(T)`. -/
def Lev {T : Type w} [STree T] (α : Ordinal.{w}) : Set T := {t | ht t = α}

/-- `Lev_{<α}(T)` (the nodes of level smaller than `α`; regarded as a subtree). -/
def LevLt {T : Type w} [STree T] (α : Ordinal.{w}) : Set T := {t | ht t < α}

/-- `ht(T)`: the first `α` such that `Lev_α(T) = ∅`. -/
def height (T : Type w) [STree T] : Ordinal.{w} := sInf {α | Lev (T := T) α = ∅}

/-- A leaf: a maximal element. -/
def IsLeaf {T : Type w} [STree T] (t : T) : Prop := IsMax t

/-- Well-pruned tree. -/
def WellPruned (T : Type w) [STree T] : Prop :=
  (∃! x : T, ht x = 0) ∧
    ∀ x : T, ∀ α : Ordinal.{w}, ht x < α → α < height T → ∃ y : T, ht y = α ∧ x < y

/-- Every well-pruned tree of limit ordinal height has no leaves ("Clearly"). -/
theorem wellPruned_limit_noLeaves (T : Type w) [STree T] (h : WellPruned T)
    (hl : Order.IsSuccLimit (height T)) : ∀ t : T, ¬ IsLeaf t := by
  sorry

/-- A branch: a maximal linearly ordered subset. -/
def IsBranch {T : Type w} [STree T] (b : Set T) : Prop := IsMaxChain (· ≤ ·) b

/-- A cofinal branch: a branch whose order type is the height of the tree. -/
def IsCofinalBranch {T : Type w} [STree T] (b : Set T) : Prop :=
  IsBranch b ∧ ∃ h : IsWellOrder b (fun x y => (x : T) < y),
    @Ordinal.type b (fun x y => (x : T) < y) h = height T

/-- `Lim(T)`: the set of cofinal branches of `T` (Definition 6.1). -/
def Lim (T : Type w) [STree T] : Set (Set T) := {b | IsCofinalBranch b}

/-- (Implicit in the paper.) A subset of a tree, with the induced order, is a tree. -/
instance induced {T : Type w} [STree T] (S : Set T) : STree S where
  toPartialOrder := Subtype.partialOrder _
  wellOrdered_predecessors := sorry

end STree

/-- A `κ`-tree: a tree of height `κ` all of whose levels have size `< κ`. -/
def IsKappaTree (κ : Cardinal.{w}) (T : Type w) [STree T] : Prop :=
  STree.height T = κ.ord ∧ ∀ α : Ordinal.{w}, α < κ.ord → #(STree.Lev (T := T) α) < κ

/-- A `κ`-Aronszajn tree: a `κ`-tree with no cofinal branch. -/
def IsAronszajn (κ : Cardinal.{w}) (T : Type w) [STree T] : Prop :=
  IsKappaTree κ T ∧ STree.Lim T = ∅

/-- The tree property at `κ`: there is no `κ`-Aronszajn tree. -/
def TreeProperty (κ : Cardinal.{u}) : Prop := ∀ (T : Type u) [STree T], ¬ IsAronszajn κ T

/-- Strongly inaccessible cardinal. -/
def IsStronglyInaccessible (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ κ.IsRegular ∧ κ.IsStrongLimit

/-- Weakly compact: strongly inaccessible with the tree property (as recalled in Section 6). -/
def IsWeaklyCompact (κ : Cardinal.{u}) : Prop := IsStronglyInaccessible κ ∧ TreeProperty κ

/-! ### 4.1 Reconstructing a tree from its history -/

/-- **Definition 4.1.** `f_t : ht(t,T) → T`, `f_t(α)` = the unique `t' <_T t` in `Lev_α(T)`,
written as a set of pairs `(α, t')` so that `⊆` between functions is literally `⊆`. -/
def histFun {T : Type w} [STree T] (t : T) : Set (Ordinal.{w} × T) :=
  {p | p.2 < t ∧ STree.ht p.2 = p.1}

/-- **Definition 4.1.** The history tree `F_T = ({f_t : t ∈ T}, ⊆)`. -/
abbrev historyTree (T : Type w) [STree T] : Type (w + 1) := ↥(Set.range (histFun (T := T)))

/-- (Implicit in the paper.) `F_T` is a tree. -/
instance (T : Type w) [STree T] : STree (historyTree T) where
  toPartialOrder := inferInstance
  wellOrdered_predecessors := sorry

/-- **Definition 4.2.** `T^succ`: the nodes whose height is a successor ordinal
(as a subtree via `STree.induced`). -/
def succPart (T : Type w) [STree T] : Set T := {t | ∃ β, STree.ht t = Order.succ β}

/-- `ht(f_t, F_T) = ht(t, T)` (used in Definition 4.2; the two heights live in different
universes, hence the `lift`). -/
theorem ht_historyTree {T : Type w} [STree T] (t : T) :
    STree.ht (⟨histFun t, t, rfl⟩ : historyTree T) = Ordinal.lift.{w + 1, w} (STree.ht t) := by
  sorry

/-- **Definition 4.2, "Clearly".** `(F_T)^succ = ({f_t : t ∈ T^succ}, ⊆)`. -/
theorem historyTree_succPart {T : Type w} [STree T] (g : historyTree T) :
    g ∈ succPart (historyTree T) ↔ ∃ t ∈ succPart T, g.1 = histFun t := by
  sorry

/-- **Remark 4.3.** An isomorphism `F_T → F_S` restricts to an isomorphism `(F_T)^succ → (F_S)^succ`. -/
theorem remark_4_3 {T S : Type w} [STree T] [STree S] (g : historyTree T ≃o historyTree S) :
    ∃ g' : succPart (historyTree T) ≃o succPart (historyTree S),
      ∀ x : succPart (historyTree T), ((g' x : succPart (historyTree S)) : historyTree S)
        = g (x : historyTree T) := by
  sorry

/-- **Proposition 4.4.** A tree without leaves is isomorphic to `(F_T)^succ`. -/
theorem prop_4_4 (T : Type w) [STree T] (hT : ∀ t : T, ¬ STree.IsLeaf t) :
    Nonempty (T ≃o succPart (historyTree T)) := by
  sorry

/-- **Corollary 4.5.** For trees without leaves: `T ≅ S ↔ F_T ≅ F_S`. -/
theorem cor_4_5 (T S : Type w) [STree T] [STree S]
    (hT : ∀ t : T, ¬ STree.IsLeaf t) (hS : ∀ t : S, ¬ STree.IsLeaf t) :
    Nonempty (T ≃o S) ↔ Nonempty (historyTree T ≃o historyTree S) := by
  sorry

/-! ### 4.2 The tree of a coloring -/

/-- `C(·, δ) ↾ β` (for `β ≤ δ`), written as a set of pairs `(α, C(α,δ))`, `α < β`. -/
def fiberRestr {κ : Cardinal.{u}} {D : Type v} (C : Coloring (Kappa κ) D)
    (δ : Kappa κ) (β : Ordinal.{u}) : Set (Ordinal.{u} × D) :=
  {p | ∃ α : Kappa κ, (α : Ordinal.{u}) < β ∧ p = ((α : Ordinal.{u}), C s(α, δ))}

/-- **Definition 4.6.** `T(C) := {C(·,δ) ↾ β | β ≤ δ < κ}` (downward closed subtree of `(^{<κ}D, ⊆)`).
For the paper's `C : [κ]^2 → μ` take `D = Kappa μ`. -/
def treeOfColoringSet {κ : Cardinal.{u}} {D : Type v} (C : Coloring (Kappa κ) D) :
    Set (Set (Ordinal.{u} × D)) :=
  {g | ∃ δ : Kappa κ, ∃ β : Ordinal.{u}, β ≤ (δ : Ordinal.{u}) ∧ g = fiberRestr C δ β}

/-- `T(C)` as a partially ordered set (ordered by `⊆`). -/
abbrev TreeOfColoring {κ : Cardinal.{u}} {D : Type v} (C : Coloring (Kappa κ) D) :
    Type (max (u + 1) v) := ↥(treeOfColoringSet C)

/-- (Implicit in the paper.) `T(C)` is a tree. -/
instance {κ : Cardinal.{u}} {D : Type v} (C : Coloring (Kappa κ) D) : STree (TreeOfColoring C) where
  toPartialOrder := inferInstance
  wellOrdered_predecessors := sorry

/-- **Remark 4.7.** `C_f(α,β) = f(α)`, `f : κ → 2`. -/
def Cf₁ {κ : Cardinal.{u}} (f : Kappa κ → Kappa (2 : Cardinal.{u})) :
    Coloring (Kappa κ) (Kappa (2 : Cardinal.{u})) :=
  Coloring.ofLT (fun a _ => f a)

theorem remark_4_7 (κ : Cardinal.{u}) (f : Kappa κ → Kappa (2 : Cardinal.{u})) :
    IsLocallyAdditive (Cf₁ f) ∧ IsStarLocallyAdditive (Cf₁ f) ∧
      Nonempty (TreeOfColoring (Cf₁ f) ≃o Kappa κ) := by
  sorry

/-- **Remark 4.8.** `C_f(α,β) = f(β)`, `f : κ → 2`. -/
def Cf₂ {κ : Cardinal.{u}} (f : Kappa κ → Kappa (2 : Cardinal.{u})) :
    Coloring (Kappa κ) (Kappa (2 : Cardinal.{u})) :=
  Coloring.ofLT (fun _ b => f b)

/-- `f` is not eventually constant. -/
def NotEventuallyConstant {κ : Cardinal.{u}} (f : Kappa κ → Kappa (2 : Cardinal.{u})) : Prop :=
  ¬ ∃ α₀ : Kappa κ, ∃ i : Kappa (2 : Cardinal.{u}), ∀ β : Kappa κ, α₀ ≤ β → f β = i

/-- `T(C) = ^{<κ}{0} ∪ ^{<κ}{1}`: the constant functions with domain some `β < κ`. -/
theorem remark_4_8 (κ : Cardinal.{u}) (f : Kappa κ → Kappa (2 : Cardinal.{u}))
    (hf : NotEventuallyConstant f) :
    IsLocallyAdditive (Cf₂ f) ∧ IsStarLocallyAdditive (Cf₂ f) ∧
      treeOfColoringSet (Cf₂ f) =
        {g | ∃ β : Ordinal.{u}, β < κ.ord ∧ ∃ i : Kappa (2 : Cardinal.{u}),
          g = {p | p.1 < β ∧ p.2 = i}} := by
  sorry

/-- **Question 4.9 (open).** Find a characterization of the equivalence classes of locally
additive colorings induced by the map `C ↦ T(C)`.  (Not a statement; nothing to formalise.) -/

/-! ### 4.3 The locally additive coloring of an enumerated tree -/

/-- **Definition 4.10.**  An enumeration `e` of `T`: for each level `α < κ`, a bijective enumeration
`⟨t^i_α : i < μ_α⟩` of `Lev_α(T)`, where `μ_α = |Lev_α(T)|`.  Here `t α i` is `t^i_α`. -/
structure Enumeration (κ : Cardinal.{u}) (T : Type u) [STree T] where
  t : Ordinal.{u} → Ordinal.{u} → T
  bijOn : ∀ α : Ordinal.{u}, α < κ.ord →
    Set.BijOn (t α) (Set.Iio (#(STree.Lev (T := T) α)).ord) (STree.Lev (T := T) α)

/-- `μ = sup {μ_α : α < κ}` from Definition 4.11. -/
def levelSup (κ : Cardinal.{u}) (T : Type u) [STree T] : Cardinal.{u} :=
  sSup {c : Cardinal.{u} | ∃ α : Ordinal.{u}, α < κ.ord ∧ c = #(STree.Lev (T := T) α)}

/-- **Definition 4.11.** `C(T,e)(α,δ) = i` iff `α < δ` and `i` is the unique ordinal
(`i < μ_α`) with `t^i_α ≤_T t^0_δ`.  Colors are ordinals; by `coloring_lt_levelSup` below
they are `< μ`, i.e. this is a coloring `[κ]^2 → μ`. -/
def Enumeration.coloring {κ : Cardinal.{u}} {T : Type u} [STree T] (e : Enumeration κ T) :
    Coloring (Kappa κ) Ordinal.{u} :=
  Coloring.ofLT fun α δ =>
    Classical.epsilon fun i : Ordinal.{u} =>
      i < (#(STree.Lev (T := T) (α : Ordinal.{u}))).ord ∧
        e.t (α : Ordinal.{u}) i ≤ e.t (δ : Ordinal.{u}) 0

/-- (Part of Definition 4.11: `C(T,e) : [κ]^2 → μ`.) -/
theorem Enumeration.coloring_lt_levelSup {κ : Cardinal.{u}} {T : Type u} [STree T]
    (hT : IsKappaTree κ T) (e : Enumeration κ T) (α δ : Kappa κ) (h : α < δ) :
    e.coloring s(α, δ) < (levelSup κ T).ord := by
  sorry

/-- **Claim 4.12.** `C(T,e)` is locally additive. -/
theorem claim_4_12 {κ : Cardinal.{u}} {T : Type u} [STree T] (hT : IsKappaTree κ T)
    (e : Enumeration κ T) : IsLocallyAdditive e.coloring := by
  sorry

/-- **Definition 4.13.** `e` covers `T`: every `t ∈ T` satisfies `t <_T t^0_δ` for some `δ < κ`. -/
def Enumeration.Covers {κ : Cardinal.{u}} {T : Type u} [STree T] (e : Enumeration κ T) : Prop :=
  ∀ t : T, ∃ δ : Ordinal.{u}, δ < κ.ord ∧ t < e.t δ 0

/-- **Remark 4.14.** For a regular `κ` and a well-pruned `κ`-tree there is an enumeration covering it. -/
theorem remark_4_14 {κ : Cardinal.{u}} (hκ : κ.IsRegular) {T : Type u} [STree T]
    (hT : IsKappaTree κ T) (hwp : STree.WellPruned T) :
    ∃ e : Enumeration κ T, e.Covers := by
  sorry

/-- **Theorem 4.15.** If `e` covers `T`, then `T(C(T,e))` is isomorphic to the history tree of `T`. -/
theorem thm_4_15 {κ : Cardinal.{u}} {T : Type u} [STree T] (hT : IsKappaTree κ T)
    (e : Enumeration κ T) (he : e.Covers) :
    Nonempty (TreeOfColoring e.coloring ≃o historyTree T) := by
  sorry

/-- **Corollary 4.20.** -/
theorem cor_4_20 {κ : Cardinal.{u}} {T₁ T₂ : Type u} [STree T₁] [STree T₂]
    (h₁ : IsKappaTree κ T₁) (h₂ : IsKappaTree κ T₂)
    (hl₁ : ∀ t : T₁, ¬ STree.IsLeaf t) (hl₂ : ∀ t : T₂, ¬ STree.IsLeaf t)
    (e₁ : Enumeration κ T₁) (e₂ : Enumeration κ T₂) (c₁ : e₁.Covers) (c₂ : e₂.Covers) :
    Nonempty (T₁ ≃o T₂) ↔
      Nonempty (TreeOfColoring e₁.coloring ≃o TreeOfColoring e₂.coloring) := by
  sorry

/-! ## 5. The tree property at successor cardinals -/

/-- **Fact 5.1.** For strongly inaccessible `κ`: no `κ`-Aronszajn tree iff every coloring
`[κ]^2 → λ` (`λ < κ`) has a homogeneous set of size `κ`. -/
theorem fact_5_1 (κ : Cardinal.{u}) (hκ : IsStronglyInaccessible κ) :
    TreeProperty κ ↔ ∀ lam : Cardinal.{u}, lam < κ → PartitionRel κ lam := by
  sorry

/-- **Theorem 5.2.** For an infinite cardinal `μ`: there is no `μ⁺`-Aronszajn tree iff
`μ⁺ → (μ⁺)^{la}_μ`. -/
theorem thm_5_2 (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    TreeProperty (Order.succ μ) ↔ LaArrow (Order.succ μ) μ := by
  sorry

/-- **Lemma 5.3.** `κ` regular uncountable, `μ < κ`.  TFAE:
(1) every tree of height `κ` whose levels have size `≤ μ` admits a `κ`-sized branch;
(2) `κ → (κ)^{la}_μ` (every locally additive `C : [κ]^2 → μ` has a homogeneous set of size `κ`). -/
theorem lemma_5_3 (κ μ : Cardinal.{u}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ) (hμ : μ < κ) :
    (∀ (T : Type u) [STree T], STree.height T = κ.ord →
        (∀ α : Ordinal.{u}, #(STree.Lev (T := T) α) ≤ μ) →
        ∃ b : Set T, STree.IsBranch b ∧ #b = κ) ↔
      LaArrow κ μ := by
  sorry

/-! ## 6. Strongly inaccessibles in the tree sense -/

/-- **Definition 6.1.** The tree exponent
`λ^{μ,tr} = sup {|Lim(T)| : T a tree of height μ with ≤ λ nodes}`
(for infinite cardinals `μ ≤ λ`). -/
def treeExp (lam μ : Cardinal.{u}) : Cardinal.{u} :=
  sSup {c : Cardinal.{u} | ∃ (T : Type u) (inst : STree T),
    STree.height T = μ.ord ∧ #T ≤ lam ∧ c = #(STree.Lim T)}

/-- **Remark 6.2.** `λ^{μ,tr} ≤ λ^μ`. -/
theorem remark_6_2 (lam μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (hle : μ ≤ lam) :
    treeExp lam μ ≤ lam ^ μ := by
  sorry

/-- **Fact 6.3.** For uncountable `κ`: `κ → (κ)^2` iff `κ` is weakly compact. -/
theorem fact_6_3 (κ : Cardinal.{u}) (hκ : ℵ₀ < κ) :
    PartitionRel κ 2 ↔ IsWeaklyCompact κ := by
  sorry

/-- **Theorem 6.4.** `κ` uncountable regular with the tree property.  TFAE:
(1) `λ^{μ,tr} < κ` for all `λ, μ < κ` (Definition 6.1 is for infinite `μ ≤ λ`);
(2) `κ` is strongly inaccessible. -/
theorem thm_6_4 (κ : Cardinal.{u}) (hunc : ℵ₀ < κ) (hreg : κ.IsRegular)
    (htp : TreeProperty κ) :
    (∀ lam μ : Cardinal.{u}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      IsStronglyInaccessible κ := by
  sorry

/-- **Corollary 6.5.** An uncountable `κ` is weakly compact iff (1) `κ` is regular,
(2) `κ` has the tree property and (3) `λ^{μ,tr} < κ` for all `λ, μ < κ`. -/
theorem cor_6_5 (κ : Cardinal.{u}) (hunc : ℵ₀ < κ) :
    IsWeaklyCompact κ ↔
      (κ.IsRegular ∧ TreeProperty κ ∧
        ∀ lam μ : Cardinal.{u}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) := by
  sorry

/-! ## 7. Ramsey theorems for locally-additive colorings -/

/-! ### 7.1 `*`-locally-additive colorings

Standing assumption: `μ < κ = cf(κ)` and `C : [κ]^2 → μ` is `*`-locally additive. -/

/-- **Definition 7.1.** `β ∼ γ` if some `α > β, γ` has `C(β,α) = C(γ,α)` (`α` witnesses it). -/
def Sim {κ : Cardinal.{u}} {D : Type v} (C : Coloring (Kappa κ) D) (β γ : Kappa κ) : Prop :=
  ∃ α : Kappa κ, β < α ∧ γ < α ∧ C s(β, α) = C s(γ, α)

/-- **Remark 7.2.** If `β ≠ γ`, `α₁` witnesses `β ∼ γ` and `α₁ < α₂`, then `α₂` witnesses it as
well; hence `∼` is an equivalence relation. -/
theorem remark_7_2 (κ μ : Cardinal.{u}) (hμ : μ < κ) (hκ : κ.IsRegular)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C) :
    (∀ β γ α₁ α₂ : Kappa κ, β ≠ γ → β < α₁ → γ < α₁ → C s(β, α₁) = C s(γ, α₁) →
        α₁ < α₂ → C s(β, α₂) = C s(γ, α₂)) ∧
      Equivalence (Sim C) := by
  sorry

/-- **Lemma 7.3.** If `μ⁺ < κ` then there are at most `μ` `∼`-equivalence classes. -/
theorem lemma_7_3 (κ μ : Cardinal.{u}) (hκ : κ.IsRegular) (h : Order.succ μ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C) :
    #(Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ}) ≤ up μ := by
  sorry

/-- **Theorem 7.4.** `κ →^{*-la} (κ)_μ` whenever `μ⁺ < κ = cf(κ)`. -/
theorem thm_7_4 (κ μ : Cardinal.{u}) (hκ : κ.IsRegular) (h : Order.succ μ < κ) :
    StarLaArrow κ μ := by
  sorry

/-- **Proposition 7.5.** `κ →^{*-la} (κ)_μ` fails if `μ⁺ = κ` (`μ` infinite). -/
theorem prop_7_5 (κ μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (h : Order.succ μ = κ) :
    ¬ StarLaArrow κ μ := by
  sorry

/-! ### 7.2 locally-additive colorings -/

/-- **Question 7.6 (open).** Does `μ⁺ → (μ⁺)^{la}_μ` hold? -/
def Question_7_6 : Prop := ∀ μ : Cardinal.{u}, ℵ₀ ≤ μ → LaArrow (Order.succ μ) μ

/-- **Theorem 7.7.** `κ` regular, `μ⁺ < κ`: `κ → (κ)^{la}_μ`. -/
theorem thm_7_7 (κ μ : Cardinal.{u}) (hκ : κ.IsRegular) (h : Order.succ μ < κ) :
    LaArrow κ μ := by
  sorry

/-- **Claim 7.8.** [Kanamori, Prop. 7.9]  `κ` regular, `λ < κ`.  A `κ`-tree all of whose levels
have size `< λ` is not `κ`-Aronszajn. -/
theorem claim_7_8 (κ lam : Cardinal.{u}) (hκ : κ.IsRegular) (hlam : lam < κ)
    (T : Type u) [STree T] (hT : IsKappaTree κ T)
    (hlev : ∀ α : Ordinal.{u}, #(STree.Lev (T := T) α) < lam) :
    ¬ IsAronszajn κ T := by
  sorry

end JardenShami
