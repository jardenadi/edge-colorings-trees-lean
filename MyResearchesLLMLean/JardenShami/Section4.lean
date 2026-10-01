import MyResearchesLLMLean.JardenShami.Section2
import Mathlib.Data.Sym.Sym2.Order

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 4

Section 4 ("Trees and Colorings"): basic notions on trees, the history tree `F_T` of a tree,
the tree `T(C)` of a coloring, and the locally additive coloring `C(T,e)` of an enumerated
`κ`-tree.

Phase 0: statements only; every proof is `sorry`.

Numbering (active text only, one counter per section): 4.1 Def (history tree), 4.2 Def
(`T^succ`), 4.3 Remark, 4.4 Proposition, 4.5 Corollary, 4.6 Def (`T(C)`), 4.7 Remark,
4.8 Remark, 4.9 Question (not formalized), 4.10 Def (enumeration), 4.11 Def (`C(T,e)`),
4.12 Claim, 4.13 Def (covers), 4.14 Remark, 4.15 Theorem, 4.16–4.19 Claims (inside the proof of
4.15), 4.20 Corollary.

## Encoding conventions
* A tree is a partial order in which the set of predecessors of each node is well-ordered
  (`IsTree`). Heights `ht t` are ordinals in the universe of the tree.
* Functions with ordinal domain (the history functions `f_t`, the nodes of `T(C)`) are encoded
  by their graphs, so that `⊆` between functions is literally `⊆` between sets.
* For `C : [κ]^2 → D` the domain is `Kappa κ = κ.ord.ToType` (Section 2); elements of `Kappa κ`
  coerce to ordinals `< κ.ord`.
* `C(T,e)` (Definition 4.11) is given by a predicate `IsTreeColoring e C` ("`C` is `C(T,e)`")
  together with the statement that exactly one such `C` exists.
-/

open Cardinal

universe v w

noncomputable section

namespace JardenShami

/-! ## Trees: basic notions (Section 4, opening paragraphs, "Recall ...") -/

/-- **Section 4, preliminaries** ("Recall ..."). A tree is a partial order `(T, ≤_T)` such that
for each `t ∈ T` the set `{s ∈ T : s <_T t}` is well-ordered by `≤_T`. -/
class IsTree (T : Type w) [PartialOrder T] : Prop where
  wellOrder_Iio : ∀ t : T, IsWellOrder (Set.Iio t) (fun x y => (x : T) < y)

namespace Tree

variable {T : Type w} [PartialOrder T] [IsTree T]

/-- **Section 4, preliminaries.** `ht(t,T)`: the height of `t`, the order type of
`{s : s <_T t}`. -/
def ht (t : T) : Ordinal.{w} :=
  @Ordinal.type (Set.Iio t) (fun x y => (x : T) < y) (IsTree.wellOrder_Iio t)

variable (T) in
/-- **Section 4, preliminaries.** `Lev_α(T)`: the `α`-th level of `T`. -/
def Lev (α : Ordinal.{w}) : Set T := {t | ht t = α}

variable (T) in
/-- **Section 4, preliminaries.** `Lev_{<α}(T)`: the nodes of level smaller than `α` (regarded
as a subtree with the induced order). -/
def LevLt (α : Ordinal.{w}) : Set T := {t | ht t < α}

variable (T) in
/-- **Section 4, preliminaries.** `ht(T)`: the first `α` such that `Lev_α(T) = ∅`. -/
def height : Ordinal.{w} := sInf {α | Lev T α = ∅}

/-- **Section 4, preliminaries.** A branch: a maximal linearly ordered subset of `T`. -/
def IsBranch (b : Set T) : Prop := IsMaxChain (· ≤ ·) b

/-- **Section 4, preliminaries.** A cofinal branch: a branch whose order type is the height
of `T`. -/
def IsCofinalBranch (b : Set T) : Prop :=
  IsBranch b ∧ ∃ h : IsWellOrder b (fun x y => (x : T) < y),
    @Ordinal.type b (fun x y => (x : T) < y) h = height T

/-- **Section 4, preliminaries.** A leaf: a maximal element of the tree. -/
def IsLeaf (t : T) : Prop := IsMax t

variable (T) in
/-- **Section 4, preliminaries.** `T` is well-pruned: `Lev_0(T)` has exactly one element, and
`∀ x ∈ T ∀ α [ht(x,T) < α < ht(T) → ∃ y ∈ Lev_α(T) (x <_T y)]`. -/
def WellPruned : Prop :=
  (∃! x : T, ht x = 0) ∧
    ∀ (x : T) (α : Ordinal.{w}), ht x < α → α < height T → ∃ y ∈ Lev T α, x < y

/-- **Section 4, preliminaries** (unnumbered, "Clearly"). Every well-pruned tree of limit
ordinal height has no leaves. -/
theorem wellPruned_noLeaves_of_isSuccLimit (hT : WellPruned T)
    (hlim : Order.IsSuccLimit (height T)) : ∀ t : T, ¬ IsLeaf t := by
  sorry

end Tree

open Tree

/-- `κ`-tree (used from Definition 4.10 on; not defined in the paper, standard meaning): a tree
of height `κ` all of whose levels have size `< κ`. -/
def IsKappaTree (κ : Cardinal.{w}) (T : Type w) [PartialOrder T] [IsTree T] : Prop :=
  height T = κ.ord ∧ ∀ α : Ordinal.{w}, α < κ.ord → #(Lev T α) < κ

/-! ## 4.1 Reconstructing a tree from its history -/

section History

variable {T : Type w} [PartialOrder T] [IsTree T]

/-- **Definition 4.1** (Section 4). `f_t : ht(t,T) → T`, where `f_t(α)` is the unique
`t' <_T t` in `Lev_α(T)`; encoded by its graph `{(α, t') : t' <_T t, ht(t') = α}`. -/
def histFun (t : T) : Set (Ordinal.{w} × T) := {p | p.2 < t ∧ ht p.2 = p.1}

variable (T) in
/-- **Definition 4.1** (Section 4). The history tree of `T`: `F_T = ({f_t : t ∈ T}, ⊆)`. -/
def HistoryTree : Set (Set (Ordinal.{w} × T)) := Set.range histFun

variable (T) in
/-- **Definition 4.1** (Section 4), implicit claim: the history tree `F_T` is a tree. -/
theorem historyTree_isTree : IsTree (HistoryTree T) := by
  sorry

instance : IsTree (HistoryTree T) := historyTree_isTree T

variable (T) in
/-- **Definition 4.2** (Section 4). `T^succ`: the subtree of `T` induced by
`{t ∈ T : ht(t,T) is a successor ordinal}`. -/
def succPart : Set T := {t | ∃ β : Ordinal.{w}, ht t = Order.succ β}

/-- **After Definition 4.2** (Section 4, unnumbered, "as `ht(f_t,F_T) = ht(t,T)`"). The height
of `f_t` in `F_T` equals the height of `t` in `T` (the two heights live in different universes,
hence the `lift`). -/
theorem ht_histFun (t : T) :
    ht (⟨histFun t, t, rfl⟩ : HistoryTree T) = Ordinal.lift.{w + 1} (ht t) := by
  sorry

/-- **After Definition 4.2** (Section 4, unnumbered, "Clearly"). `(F_T)^succ = ({f_t : t ∈
T^succ}, ⊆)`. -/
theorem mem_succPart_historyTree (g : HistoryTree T) :
    g ∈ succPart (HistoryTree T) ↔ ∃ t ∈ succPart T, g.1 = histFun t := by
  sorry

/-- **Remark 4.3** (Section 4, `\label{remark 3.3}`). If `g : F_T → F_S` is an isomorphism,
then `g ↾ (F_T)^succ` is an isomorphism from `(F_T)^succ` to `(F_S)^succ`. -/
theorem historyTree_iso_restrict_succPart {S : Type w} [PartialOrder S] [IsTree S]
    (g : HistoryTree T ≃o HistoryTree S) :
    ∃ g' : succPart (HistoryTree T) ≃o succPart (HistoryTree S),
      ∀ x : succPart (HistoryTree T), (g' x : HistoryTree S) = g x := by
  sorry

/-- **Proposition 4.4** (Section 4, `\label{proposition without leaves}`). A tree without
leaves is isomorphic to `(F_T)^succ`. -/
theorem nonempty_iso_succPart_historyTree (hT : ∀ t : T, ¬ IsLeaf t) :
    Nonempty (T ≃o succPart (HistoryTree T)) := by
  sorry

/-- **Corollary 4.5** (Section 4, `\label{corollary reconstruction a tree from its history}`).
Two trees without leaves are isomorphic iff their history trees are isomorphic. -/
theorem nonempty_iso_iff_historyTree {S : Type w} [PartialOrder S] [IsTree S]
    (hT : ∀ t : T, ¬ IsLeaf t) (hS : ∀ s : S, ¬ IsLeaf s) :
    Nonempty (T ≃o S) ↔ Nonempty (HistoryTree T ≃o HistoryTree S) := by
  sorry

end History

/-! ## 4.2 The tree of a coloring -/

section TreeOfColoring

variable {κ : Cardinal.{w}} {D : Type v}

/-- `C(·,δ) ↾ β` for `β ≤ δ < κ` (Definition 4.6): the function `α ↦ C(α,δ)` on `{α : α < β}`,
encoded by its graph. -/
def fiberRestr (C : Coloring (Kappa κ) D) (δ β : Kappa κ) (hβ : β ≤ δ) :
    Set (Kappa κ × D) :=
  {p | ∃ h : p.1 < β, p.2 = C.color p.1 δ (h.trans_le hβ)}

/-- **Definition 4.6** (Section 4, `\label{definition T(C)}`, after [ri:chain, p. 7]). For
`C : [κ]^2 → D`: `T(C) := {C(·,δ) ↾ β | β ≤ δ < κ}`, ordered by `⊆`. -/
def treeOfColoring (C : Coloring (Kappa κ) D) : Set (Set (Kappa κ × D)) :=
  {g | ∃ (δ β : Kappa κ) (hβ : β ≤ δ), g = fiberRestr C δ β hβ}

/-- **Definition 4.6** (Section 4), implicit claim: `T(C)` is a tree. -/
theorem treeOfColoring_isTree (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := by
  sorry

instance (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := treeOfColoring_isTree C

/-- **Definition 4.6** (Section 4), implicit claim: `T(C)` is downward closed in
`(^{<κ}D, ⊆)`, i.e. closed under restriction to an initial segment `{α : α < γ}`. -/
theorem treeOfColoring_downwardClosed (C : Coloring (Kappa κ) D) :
    ∀ g ∈ treeOfColoring C, ∀ γ : Kappa κ, {p ∈ g | p.1 < γ} ∈ treeOfColoring C := by
  sorry

/-- **Remark 4.7** (Section 4). For `f : κ → 2`, the coloring `C_f(α,β) = f(α)` (`α < β`). -/
def colorMinOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.inf

/-- **Remark 4.7** (Section 4). Each `C_f` (`C_f(α,β) = f(α)`) is locally additive and
*-locally additive, and `T(C_f)` is isomorphic to `(κ, ∈)`. -/
theorem colorMinOf_spec (f : Kappa κ → Fin 2) :
    IsLocallyAdditive (colorMinOf f) ∧ IsStarLocallyAdditive (colorMinOf f) ∧
      Nonempty (treeOfColoring (colorMinOf f) ≃o Kappa κ) := by
  sorry

/-- **Remark 4.8** (Section 4). For `f : κ → 2`, the coloring `C_f(α,β) = f(β)` (`α < β`). -/
def colorMaxOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.sup

/-- **Remark 4.8** (Section 4). If `f : κ → 2` is not eventually constant, then `C_f`
(`C_f(α,β) = f(β)`) is locally additive and *-locally additive, and
`T(C_f) = ^{<κ}{0} ∪ ^{<κ}{1}` (the constant functions with domain some `β < κ`). -/
theorem colorMaxOf_spec (f : Kappa κ → Fin 2)
    (hf : ¬ ∃ (α₀ : Kappa κ) (i : Fin 2), ∀ β, α₀ ≤ β → f β = i) :
    IsLocallyAdditive (colorMaxOf f) ∧ IsStarLocallyAdditive (colorMaxOf f) ∧
      treeOfColoring (colorMaxOf f) =
        {g | ∃ (β : Kappa κ) (i : Fin 2), g = {p | p.1 < β ∧ p.2 = i}} := by
  sorry

-- Question 4.9 (open problem) is not formalized.

end TreeOfColoring

/-! ## 4.3 The locally additive coloring of an enumerated tree -/

section Enumeration

variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]

variable (κ T) in
/-- **Definition 4.10** (Section 4, `\label{definition enumeration}`). An enumeration of a
`κ`-tree `T`: for each `α < κ` a bijective enumeration `⟨t^i_α : i < μ_α⟩` of `Lev_α(T)`.
Here `t α i` is `t^i_α` and `μ_α = |Lev_α(T)|` (as an initial ordinal). -/
structure Enumeration where
  /-- `t α i` is `t^i_α`. -/
  t : Ordinal.{w} → Ordinal.{w} → T
  bijOn : ∀ α < κ.ord, Set.BijOn (t α) (Set.Iio (#(Lev T α)).ord) (Lev T α)

variable (κ T) in
/-- **Definition 4.11** (Section 4): `μ = sup {μ_α : α < κ}`, `μ_α = |Lev_α(T)|`. -/
def levelSup : Cardinal.{w} := ⨆ α : Kappa κ, #(Lev T (α : Ordinal.{w}))

/-- **Definition 4.11** (Section 4, `\label{definition C(T,e)}`). `C = C(T,e)`, where
`C(T,e) : [κ]^2 → μ` is defined by `C(T,e)(α,δ) = i` iff `α < δ` and `i < μ` is the unique
ordinal with `t^i_α ≤_T t^0_δ`. Uniqueness is automatic, so the condition reads: `i < μ_α` (so
that `t^i_α` is defined) and `t^i_α ≤_T t^0_δ`. -/
def IsTreeColoring (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T))) :
    Prop :=
  ∀ (α δ : Kappa κ) (h : α < δ),
    ((C.color α δ h : Ordinal.{w}) < (#(Lev T (α : Ordinal.{w}))).ord) ∧
      e.t α (C.color α δ h) ≤ e.t δ 0

/-- **Definition 4.11** (Section 4), implicit claim: for a `κ`-tree `T` and an enumeration `e`,
`C(T,e)` is well defined, i.e. exactly one coloring `C : [κ]^2 → μ` satisfies the definition. -/
theorem existsUnique_isTreeColoring (hT : IsKappaTree κ T) (e : Enumeration κ T) :
    ∃! C, IsTreeColoring e C := by
  sorry

/-- **Claim 4.12** (Section 4, `\label{claim C(T,e) is locally additive}`). For a `κ`-tree `T`
and an enumeration `e` of `T`, the coloring `C(T,e)` is locally additive. -/
theorem isLocallyAdditive_of_isTreeColoring (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    IsLocallyAdditive C := by
  sorry

/-- **Definition 4.13** (Section 4). The enumeration `e` covers `T` if for every `t ∈ T` there
is `δ < κ` with `t <_T t^0_δ`. -/
def Enumeration.Covers (e : Enumeration κ T) : Prop :=
  ∀ t : T, ∃ δ < κ.ord, t < e.t δ 0

/-- **Remark 4.14** (Section 4). For every cardinal `κ` and a well-pruned `κ`-tree `T`, there is
an enumeration `e` of `T` that covers `T`.
CHANGED w.r.t. the paper: the hypothesis `ℵ₀ ≤ κ` is added. As written ("every cardinal") the
statement is false for finite `κ ≥ 1` (a node of maximal level cannot be below any `t^0_δ`);
the paper's proof assumes `κ` regular. See FIDELITY.md. -/
theorem exists_covers (hκ : ℵ₀ ≤ κ) (hT : IsKappaTree κ T) (hwp : WellPruned T) :
    ∃ e : Enumeration κ T, e.Covers := by
  sorry

/-- **Theorem 4.15** (Section 4, `\label{T isomorphic to T(C(T,e))}`). Let `T` be a `κ`-tree and
`e` an enumeration of `T`. If `e` covers `T` then `T(C(T,e))` is isomorphic to the history tree
`{f_t : t ∈ T}` of `T`. -/
theorem nonempty_iso_treeOfColoring_historyTree (hT : IsKappaTree κ T) (e : Enumeration κ T)
    (he : e.Covers) {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    Nonempty (treeOfColoring C ≃o HistoryTree T) := by
  sorry

/-- Notation in the proof of Theorem 4.15: `t_β^{C(β,δ)}` for `β ≤ δ < κ`, with the stipulation
`C(δ,δ) = 0`. -/
def Enumeration.node (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T)))
    (β δ : Kappa κ) (_h : β ≤ δ) : T :=
  if hβ : β < δ then e.t β (C.color β δ hβ) else e.t δ 0

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
      ((α : Ordinal.{w}), e.t α i) ∈ histFun (e.node C β δ hβδ) := by
  sorry

/-- **Claim 4.17** (Section 4, inside the proof of Theorem 4.15,
`\label{claim result of claim for theorem 4.21}`). For `β₁ ≤ δ₁` and `β₂ ≤ δ₂`:
`C(·,δ₁) ↾ β₁ = C(·,δ₂) ↾ β₂` iff `f_{t_{β₁}^{C(β₁,δ₁)}} = f_{t_{β₂}^{C(β₂,δ₂)}}`. -/
theorem fiberRestr_eq_iff_histFun_eq (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) = histFun (e.node C β₂ δ₂ h₂) := by
  sorry

/-- **Claim 4.18** (Section 4, inside the proof of Theorem 4.15). The map
`h : C(·,δ) ↾ β ↦ f_{t_β^{C(β,δ)}}` is an order-homomorphism (in both directions, as in the
paper's proof): `C(·,δ₁) ↾ β₁ ⊆ C(·,δ₂) ↾ β₂` iff
`f_{t_{β₁}^{C(β₁,δ₁)}} ⊆ f_{t_{β₂}^{C(β₂,δ₂)}}`. -/
theorem fiberRestr_subset_iff_histFun_subset (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) ⊆ histFun (e.node C β₂ δ₂ h₂) := by
  sorry

/-- **Claim 4.19** (Section 4, inside the proof of Theorem 4.15). The map
`h : C(·,δ) ↾ β ↦ f_{t_β^{C(β,δ)}}` is surjective onto `{f_t : t ∈ T}` (when `e` covers `T`). -/
theorem exists_histFun_node_eq (hT : IsKappaTree κ T) (e : Enumeration κ T) (he : e.Covers)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) (t : T) :
    ∃ (β δ : Kappa κ) (h : β ≤ δ), histFun (e.node C β δ h) = histFun t := by
  sorry

end Enumeration

/-- **Corollary 4.20** (Section 4). Let `T₁, T₂` be `κ`-trees without leaves and `e_i` an
enumeration of `T_i` that covers `T_i`. Then `T₁ ≅ T₂` iff `T(C(T₁,e₁)) ≅ T(C(T₂,e₂))`. -/
theorem nonempty_iso_iff_treeOfColoring {κ : Cardinal.{w}}
    {T₁ T₂ : Type w} [PartialOrder T₁] [IsTree T₁] [PartialOrder T₂] [IsTree T₂]
    (h₁ : IsKappaTree κ T₁) (h₂ : IsKappaTree κ T₂)
    (hl₁ : ∀ t : T₁, ¬ IsLeaf t) (hl₂ : ∀ t : T₂, ¬ IsLeaf t)
    (e₁ : Enumeration κ T₁) (e₂ : Enumeration κ T₂) (c₁ : e₁.Covers) (c₂ : e₂.Covers)
    {C₁ : Coloring (Kappa κ) (Kappa (levelSup κ T₁))} (hC₁ : IsTreeColoring e₁ C₁)
    {C₂ : Coloring (Kappa κ) (Kappa (levelSup κ T₂))} (hC₂ : IsTreeColoring e₂ C₂) :
    Nonempty (T₁ ≃o T₂) ↔ Nonempty (treeOfColoring C₁ ≃o treeOfColoring C₂) := by
  sorry

end JardenShami
