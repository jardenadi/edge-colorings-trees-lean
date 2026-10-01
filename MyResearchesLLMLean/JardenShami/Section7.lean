import MyResearchesLLMLean.JardenShami.Section6

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 7

Section 7 ("Ramsey Theorems for locally-additive colorings"): `κ → (κ)_{*-la_μ}` for
`μ⁺ < κ = cf(κ)` (after [Sh42, Theorem 1.1]), its failure for `μ⁺ = κ`, and `κ → (κ)_{la_μ}` for
regular `κ > μ⁺`.

Phase 0: statements only; every proof is `sorry`.

Numbering (active text only, one counter per section): 7.1 Def (`∼`), 7.2 Remark
(`remark 7.2`), 7.3 Lemma (`lemma number of equivalence classes`), 7.4 Theorem
(`theorem shelah *-locally-additive`), 7.5 Proposition
(`proposition mu^+<kappa can's be omitted`), 7.6 Question (not formalized), 7.7 Theorem
(`the only theorem`), 7.8 Claim (`the exercise of kunen`, recalled from [Large, Proposition 7.9]
and proved in the paper "for completeness"), 7.9 Claim (`argue`, inside the proof of Claim 7.8,
Case A).

Standing assumption of Subsection 7.1 ("For the rest of this subsection"): `μ < κ = cf(κ)` and
`C : [κ]^2 → μ` is *-locally additive. It is repeated as explicit hypotheses of 7.2–7.5
(`κ = cf(κ)` is `κ.IsRegular`; Mathlib's `IsRegular` includes `ℵ₀ ≤ κ`).

The well-known fact used in the proof of Claim 7.8 ("every `κ`-tree has a well-pruned subtree
which is a `κ`-tree") is the hypothesis-style `def Fact_wellPrunedSubtree : Prop`; Claim 7.8 and
Theorem 7.7 take it as an explicit hypothesis.
-/

open Cardinal

universe v w

noncomputable section

namespace JardenShami

open Tree

/-! ## 7.1 *-locally-additive colorings -/

/-- **Definition 7.1** (Section 7). `β ∼ γ` if for some `α` with `β, γ < α` we have
`C(β,α) = C(γ,α)` (`α` witnesses `β ∼ γ`). The paper states it for the fixed
`C : [κ]^2 → μ` of the standing assumption; here for any coloring of a linear order. -/
def Sim {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) (β γ : A) : Prop :=
  ∃ (α : A) (hβ : β < α) (hγ : γ < α), C.color β α hβ = C.color γ α hγ

/-- **Remark 7.2** (Section 7, `\label{remark 7.2}`). Under the standing assumption of Subsection
7.1: if `β ≠ γ`, `α₁` witnesses `β ∼ γ` and `α₁ < α₂`, then `α₂` witnesses `β ∼ γ` as well.
Hence `∼` is an equivalence relation. -/
theorem sim_witness_mono_and_equivalence (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C) :
    (∀ (β γ α₁ α₂ : Kappa κ) (hβ : β < α₁) (hγ : γ < α₁) (h₁₂ : α₁ < α₂), β ≠ γ →
        C.color β α₁ hβ = C.color γ α₁ hγ →
          C.color β α₂ (hβ.trans h₁₂) = C.color γ α₂ (hγ.trans h₁₂)) ∧
      Equivalence (Sim C) := by
  sorry

/-- **Lemma 7.3** (Section 7, `\label{lemma number of equivalence classes}`). Under the standing
assumption of Subsection 7.1: if `μ⁺ < κ` then the number of `∼`-equivalence classes is at most
`μ`. The classes are counted as the sets `{γ : β ∼ γ}`, `β < κ`. -/
theorem card_simClasses_le (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C)
    (h : Order.succ μ < κ) :
    #(Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ}) ≤ μ := by
  sorry

/-- `κ → (κ)_{*-la_μ}` (Theorem 7.4, Proposition 7.5; written `κ →_{*-la} (κ)_μ` in the summary
at the start of Section 7), read as for `la_μ` in Section 5 (`LaArrowKappa`): every
*-locally additive coloring `C : [κ]^2 → μ` admits a homogeneous set of size `κ`. -/
def StarLaArrowKappa (κ μ : Cardinal.{w}) : Prop :=
  ∀ C : Coloring (Kappa κ) (Kappa μ), IsStarLocallyAdditive C →
    ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H

/-- **Theorem 7.4** (Section 7, `\label{theorem shelah *-locally-additive}`, after
[Sh42, Theorem 1.1]). `κ → (κ)_{*-la_μ}` holds whenever `μ⁺ < κ = cf(κ)`. -/
theorem starLaArrowKappa_of_succ_lt (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ < κ) : StarLaArrowKappa κ μ := by
  sorry

/-- **Proposition 7.5** (Section 7, `\label{proposition mu^+<kappa can's be omitted}`).
`κ → (κ)_{*-la_μ}` does not hold if `μ⁺ = κ`. The standing assumption `κ = cf(κ)` of Subsection
7.1 is kept as `κ.IsRegular` (with Mathlib's definition this makes `κ`, hence `μ`, infinite; see
FIDELITY.md: for `μ ≤ 1` the statement without it is false). -/
theorem not_starLaArrowKappa_of_succ_eq (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ = κ) : ¬ StarLaArrowKappa κ μ := by
  sorry

/-! ## 7.2 locally-additive colorings -/

-- Question 7.6 (open problem: does `μ⁺ → (μ⁺)_{la_μ}` hold?) is not formalized.

/-- FACT: cited, not proved in the paper. **Section 7, proof of Claim 7.8, Case A** ("it a
well-known fact that every `κ`-tree has a well-pruned subtree which is a `κ`-tree"). Stated for
regular `κ`, the only case used (Claim 7.8 assumes `κ` regular); for singular `κ` it can fail.
A subtree is a subset with the induced order. -/
def Fact_wellPrunedSubtree : Prop :=
  ∀ κ : Cardinal.{w}, κ.IsRegular →
    ∀ (T : Type w) [PartialOrder T] [IsTree T], IsKappaTree κ T →
      ∃ S : Set T, IsKappaTree κ S ∧ WellPruned S

/-- **Claim 7.9** (Section 7, `\label{argue}`, inside Case A of the proof of Claim 7.8). Let
`κ` be regular, `λ < κ` regular, and `T` a well-pruned `κ`-tree whose levels have size `< λ`.
For every ordinal `α < κ` with `cf(α) = λ` there is an ordinal `q(α) < α` such that for every
ordinal `β` with `q(α) < β < α` and any `a ∈ Lev_{q(α)}(T)` there are no two distinct
`b, c ∈ Lev_β(T)` with `a < b` and `a < c`. -/
theorem exists_unique_extension_level (κ lam : Cardinal.{w}) (hκ : κ.IsRegular)
    (hlamreg : lam.IsRegular) (hlam : lam < κ) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hwp : WellPruned T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∀ α : Ordinal.{w}, α < κ.ord → α.cof = lam →
      ∃ q < α, ∀ β : Ordinal.{w}, q < β → β < α →
        ∀ a ∈ Lev T q, ∀ b ∈ Lev T β, ∀ c ∈ Lev T β, a < b → a < c → b = c := by
  sorry

/-- **Claim 7.8** (Section 7, `\label{the exercise of kunen}`; recalled from
[Large, Proposition 7.9] and proved in the paper "for completeness"). Let `κ` and `λ` be cardinals
such that `κ` is regular and `λ < κ`. If `T` is a `κ`-tree whose levels have size `< λ`, then
`T` is not `κ`-Aronszajn.
The well-known fact used in its proof (`Fact_wellPrunedSubtree`) is an explicit hypothesis. -/
theorem not_isAronszajn_of_card_lev_lt (hF : Fact_wellPrunedSubtree.{w}) (κ lam : Cardinal.{w})
    (hκ : κ.IsRegular) (hlam : lam < κ) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ¬ IsAronszajn κ T := by
  sorry

/-- **Theorem 7.7** (Section 7, `\label{the only theorem}`). Let `κ` be a regular cardinal and
`μ` a cardinal with `μ⁺ < κ`. Then `κ → (κ)_{la_μ}` (in the sense of Section 5,
`LaArrowKappa`).
`Fact_wellPrunedSubtree` (used through Claim 7.8) is an explicit hypothesis. -/
theorem laArrowKappa_of_succ_lt (hF : Fact_wellPrunedSubtree.{w}) (κ μ : Cardinal.{w})
    (hκ : κ.IsRegular) (h : Order.succ μ < κ) : LaArrowKappa κ μ := by
  sorry

end JardenShami
