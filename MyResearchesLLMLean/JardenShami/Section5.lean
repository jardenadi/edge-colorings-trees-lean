import MyResearchesLLMLean.JardenShami.Section4

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 5

Section 5 ("The Tree Property at Successor Cardinals",
`\label{section the tree property at successor cardinals}`).

Phase 0: statements only; every proof is `sorry`.

Numbering (active text only, one counter per section): 5.1 Fact (cited, "Recall"), 5.2 Theorem,
5.3 Lemma, 5.4 Claim (inside the proof of Lemma 5.3).

Fact 5.1 is recalled without proof; it is the hypothesis-style `def Fact_5_1 : Prop`. No result of
the paper depends on it (it is motivation for Theorem 5.2).
-/

open Cardinal

universe w

noncomputable section

namespace JardenShami

open Tree

/-- `κ`-Aronszajn tree (used in Fact 5.1 and Theorem 5.2; not defined in the paper, standard
meaning): a `κ`-tree with no cofinal branch. -/
def IsAronszajn (κ : Cardinal.{w}) (T : Type w) [PartialOrder T] [IsTree T] : Prop :=
  IsKappaTree κ T ∧ ¬ ∃ b : Set T, IsCofinalBranch b

/-- "There exists no `κ`-Aronszajn tree" (Fact 5.1 (1), Theorem 5.2 (1)), for trees in the
universe of `κ`. -/
def NoAronszajn (κ : Cardinal.{w}) : Prop :=
  ∀ (T : Type w) [PartialOrder T] [IsTree T], ¬ IsAronszajn κ T

/-- `κ → (κ)_{la_μ}` in the sense spelled out in Theorem 5.2 (2) and Lemma 5.3 (2) ("namely"):
every locally additive coloring `C : [κ]^2 → μ` admits a homogeneous set of size `κ`. -/
def LaArrowKappa (κ μ : Cardinal.{w}) : Prop :=
  ∀ C : Coloring (Kappa κ) (Kappa μ), IsLocallyAdditive C →
    ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H

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

/-- **Theorem 5.2** (Section 5, `\label{theorem 4.2}`). For every infinite cardinal `μ` the
following are equivalent: (1) there exists no `μ⁺`-Aronszajn tree; (2) `μ⁺ → (μ⁺)_{la_μ}`, namely
every locally additive coloring `C : [μ⁺]^2 → μ` admits a homogeneous set of size `μ⁺`. -/
theorem noAronszajn_succ_iff_laArrowKappa (μ : Cardinal.{w}) (hμ : ℵ₀ ≤ μ) :
    NoAronszajn (Order.succ μ) ↔ LaArrowKappa (Order.succ μ) μ := by
  sorry

/-- **Lemma 5.3** (Section 5, `\label{lemma 6}`, `\label{the main lemma}`). Suppose `κ` is a
regular uncountable cardinal and `μ < κ`. The following are equivalent: (1) every tree of height
`κ` whose levels have size `≤ μ` admits a `κ`-sized branch; (2) `κ → (κ)_{la_μ}`, namely every
locally additive coloring `C : [κ]^2 → μ` admits a homogeneous set of size `κ`. -/
theorem branch_iff_laArrowKappa (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ)
    (hμ : μ < κ) :
    (∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) ≤ μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) ↔
      LaArrowKappa κ μ := by
  sorry

/-- **Claim 5.4** (Section 5, inside the proof of Lemma 5.3, direction (1) ⇒ (2)). Under the
hypotheses of Lemma 5.3, for a locally additive `C : [κ]^2 → μ`, all the levels of `T(C)` have
size `≤ μ`. -/
theorem card_lev_treeOfColoring_le (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ)
    (hμ : μ < κ) (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := by
  sorry

end JardenShami
