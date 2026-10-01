import MyResearchesLLMLean.JardenShami.Section2

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 3

Section 3 ("Replacing Additivity by Local Additivity").

Phase 0: statements only; every proof is `sorry`. Fact 3.4 is cited from [Sh42] and is not
proved in the paper; it is a hypothesis (`Fact_3_4`) of Corollary 3.5.
-/

open Cardinal

universe v w

noncomputable section

namespace JardenShami

section Sec3

variable {X : Type w} [LinearOrder X]

/-- **Theorem 3.1** (Section 3, `\label{generalizing add to loc less than mu colors}`,
`\label{theorem generalizing add to la}`). Let `κ, μ` be cardinals with `2^μ + ℵ₀ ≤ κ` and `F` a
family of subsets of a linearly ordered set. If `F → (F)_{add_κ}` then `F → (F)_{la_μ}`. -/
theorem arrow_la_of_arrow_add (κ μ : Cardinal.{v}) (hκ : 2 ^ μ + ℵ₀ ≤ κ) (F : Set (Set X))
    (h : Arrow F F (addEq κ)) : Arrow F F (laEq μ) := by
  sorry

/-- **Corollary 3.2** (Section 3, `\label{generalizing add to loc for strong limit cardinal}`).
Let `μ` be a strong limit cardinal and `F` a family of subsets of a linearly ordered set.
If `F → (F)_{add_{<μ}}` then `F → (F)_{la_{<μ}}`. (Mathlib's `IsStrongLimit` includes `ℵ₀`.) -/
theorem arrow_laLt_of_arrow_addLt_strongLimit (μ : Cardinal.{v}) (hμ : μ.IsStrongLimit)
    (F : Set (Set X)) (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) := by
  sorry

/-- **Corollary 3.3** (Section 3, `\label{generalizing add to loc for finite}`).
If `F → (F)_{add_{<ℵ₀}}` then `F → (F)_{la_{<ℵ₀}}`. -/
theorem arrow_laLt_aleph0_of_arrow_addLt_aleph0 (F : Set (Set X))
    (h : Arrow F F (addLt (ℵ₀ : Cardinal.{v}))) : Arrow F F (laLt (ℵ₀ : Cardinal.{v})) := by
  sorry

end Sec3

/-- The family of subsets of `I` that are dense in some interval of `I` (Fact 3.4 and
Corollary 3.5). Interpretation: there are `a < b` in `I` such that between any two points of the
open interval `(a, b)` there is a point of `S`. (`S` is not required to lie inside `(a, b)`.) -/
def denseInSomeInterval (I : Type w) [LinearOrder I] : Set (Set I) :=
  {S | ∃ a b : I, a < b ∧ ∀ x y : I, a < x → x < y → y < b → ∃ s ∈ S, x < s ∧ s < y}

/-- FACT: cited, not proved in the paper. **Fact 3.4** (Section 3, `\label{fact dense}`;
[Sh42, Theorem 1.3]). Let `I` be a dense linear ordering and `F` the family of subsets of `I` that
are dense in some interval of `I`. Then `F → (F)_{add_{<ℵ₀}}`. -/
def Fact_3_4 (I : Type w) [LinearOrder I] [DenselyOrdered I] : Prop :=
  Arrow (denseInSomeInterval I) (denseInSomeInterval I) (addLt (ℵ₀ : Cardinal.{v}))

/-- **Corollary 3.5** (Section 3, unlabelled). Let `I` be a dense linear ordering and `F` the
family of subsets of `I` that are dense in some interval of `I`. Then `F → (F)_{la_{<ℵ₀}}`.
Depends on the cited Fact 3.4, taken as the hypothesis `hfact`. -/
theorem arrow_laLt_aleph0_denseInSomeInterval (I : Type w) [LinearOrder I] [DenselyOrdered I]
    (hfact : Fact_3_4.{v, w} I) :
    Arrow (denseInSomeInterval I) (denseInSomeInterval I) (laLt (ℵ₀ : Cardinal.{v})) := by
  sorry

end JardenShami
