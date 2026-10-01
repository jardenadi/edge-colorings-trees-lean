import MyResearchesLLMLean.JardenShami.Section5

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 6

Section 6 ("Strongly Inaccessibles in the tree sense", `\label{section strongly inaccessibles}`):
the tree exponent `λ^{μ,tr}` and a characterization of weakly compact cardinals.

Phase 0: statements only; every proof is `sorry`.

Numbering (active text only, one counter per section): 6.1 Def (tree exponent, after [Sh589]),
6.2 Remark (`remark tree exponent leq exponent`), 6.3 Fact (`fact 6.3`, cited, no proof),
6.4 Theorem (`theorem 5.4`, a stale label), 6.5 Corollary (unlabelled). Between 6.2 and 6.3 the
paper recalls the definition of a weakly compact cardinal (`IsWeaklyCompact`).

Fact 6.3 is the hypothesis-style `def Fact_6_3 : Prop`; Theorem 6.4 and Corollary 6.5 take it as
an explicit hypothesis.

## Encoding conventions
* Trees are as in Section 4 (`IsTree`); a tree of the paper ranges over trees `T : Type w` in the
  universe of the cardinals involved.
* "The tree property at `κ`" is `NoAronszajn κ` (Section 5): there is no `κ`-Aronszajn tree.
* "Strongly inaccessible" is Mathlib's `Cardinal.IsInaccessible` (uncountable, regular, strong
  limit), as in Fact 5.1.
-/

open Cardinal

universe w

noncomputable section

namespace JardenShami

open Tree

/-- Implicit in the paper ("subtree", e.g. `Lev_{<α}(T)` in the proof of Theorem 6.4 and the
well-pruned subtree in the proof of Claim 7.8): a subset of a tree, with the induced order, is a
tree. -/
theorem isTree_subtype {T : Type w} [PartialOrder T] [IsTree T] (S : Set T) : IsTree S := by
  sorry

instance {T : Type w} [PartialOrder T] [IsTree T] (S : Set T) : IsTree S := isTree_subtype S

/-! ## Definition 6.1: the tree exponent -/

/-- **Definition 6.1** (Section 6, after [Sh589]). `Lim(T)`: the set of cofinal branches of the
tree `T`. -/
def Lim (T : Type w) [PartialOrder T] [IsTree T] : Set (Set T) := {b | IsCofinalBranch b}

/-- **Definition 6.1** (Section 6, after [Sh589]). For infinite cardinals `μ ≤ λ`, `𝔗_{λ,μ}` is
the set of trees of height `μ` with `≤ λ` nodes, and the tree exponent is
`λ^{μ,tr} = sup {|Lim(T)| : T ∈ 𝔗_{λ,μ}}`.
The Lean definition is total; the paper uses it only for infinite `μ ≤ λ`. Trees range over
`Type w`. (The set is bounded by `2^λ`, so `sSup` is the true supremum.) -/
def treeExp (lam μ : Cardinal.{w}) : Cardinal.{w} :=
  sSup {c | ∃ (T : Type w) (_ : PartialOrder T) (_ : IsTree T),
    height T = μ.ord ∧ #T ≤ lam ∧ c = #(Lim T)}

/-- **Remark 6.2** (Section 6, `\label{remark tree exponent leq exponent}`). For every two infinite
cardinals `λ` and `μ`: `λ^{μ,tr} ≤ λ^μ`. -/
theorem treeExp_le_power (lam μ : Cardinal.{w}) (hlam : ℵ₀ ≤ lam) (hμ : ℵ₀ ≤ μ) :
    treeExp lam μ ≤ lam ^ μ := by
  sorry

/-! ## Weakly compact cardinals -/

/-- **Section 6, between Remark 6.2 and Fact 6.3** ("Recall, that a weakly compact cardinal is a
strongly inaccessible cardinal that satisfies the tree property"). -/
def IsWeaklyCompact (κ : Cardinal.{w}) : Prop := κ.IsInaccessible ∧ NoAronszajn κ

/-- FACT: cited, not proved in the paper. **Fact 6.3** (Section 6, `\label{fact 6.3}`, no
citation given). Let `κ` be an uncountable cardinal. The principle `κ → (κ)_2` holds if and only if
`κ` is weakly compact.
`κ → (κ)_2` is Definition 2.10 literally: `F₁ = F₂` = the subsets of `κ` of size `κ`, `𝔆` = all
colorings with `2` colors (color sets in `Type w`). -/
def Fact_6_3 : Prop :=
  ∀ κ : Cardinal.{w}, ℵ₀ < κ →
    (Arrow (bigSubsets κ) (bigSubsets κ) (allColorings.{w, w} (2 : Cardinal.{w})) ↔
      IsWeaklyCompact κ)

/-- **Theorem 6.4** (Section 6, `\label{theorem 5.4}`). Let `κ` be an uncountable regular cardinal
that satisfies the tree property. The following are equivalent: (1) `λ^{μ,tr} < κ` for each
`λ, μ < κ`; (2) `κ` is strongly inaccessible.
In (1), `λ^{μ,tr}` is taken only where Definition 6.1 defines it: infinite `μ ≤ λ`.
Fact 6.3 (used in the proof of (1) ⇒ (2)) is an explicit hypothesis. -/
theorem treeExp_lt_iff_isInaccessible (hF : Fact_6_3.{w}) (κ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (hreg : κ.IsRegular) (htp : NoAronszajn κ) :
    (∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      κ.IsInaccessible := by
  sorry

/-- **Corollary 6.5** (Section 6). Let `κ` be an uncountable cardinal. Then `κ` is weakly compact
if and only if (1) `κ` is regular, (2) `κ` satisfies the tree property and (3) `λ^{μ,tr} < κ` for
each `λ, μ < κ` (as in Theorem 6.4: infinite `μ ≤ λ`).
Fact 6.3 (used through Theorem 6.4) is an explicit hypothesis. -/
theorem isWeaklyCompact_iff (hF : Fact_6_3.{w}) (κ : Cardinal.{w}) (hunc : ℵ₀ < κ) :
    IsWeaklyCompact κ ↔
      κ.IsRegular ∧ NoAronszajn κ ∧
        ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ := by
  sorry

end JardenShami
