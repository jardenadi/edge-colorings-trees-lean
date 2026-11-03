import MyResearchesLLMLean.JardenShami.Section3
import Mathlib.Data.Sym.Sym2.Order

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 4

Section 4 ("Trees and Colorings"): basic notions on trees, the history tree `F_T` of a tree,
the tree `T(C)` of a coloring, and the locally additive coloring `C(T,e)` of an enumerated
`κ`-tree.

Phase 1: all statements are proved. Auxiliary lemmas (AUX: not in paper) are marked as such.

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

universe u v w

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

/-! ### Auxiliary lemmas on trees (AUX: not in paper) -/

instance (t : T) : IsWellOrder (Set.Iio t) (fun x y => (x : T) < y) := IsTree.wellOrder_Iio t

/-- AUX: not in paper. Two predecessors of the same node are comparable. -/
theorem lt_trichotomy_of_lt {x y t : T} (hx : x < t) (hy : y < t) : x < y ∨ x = y ∨ y < x := by
  by_cases h1 : x < y
  · exact Or.inl h1
  by_cases h2 : y < x
  · exact Or.inr (Or.inr h2)
  exact Or.inr (Or.inl (congrArg Subtype.val
    (Std.Trichotomous.trichotomous (r := fun a b : Set.Iio t => (a : T) < b) ⟨x, hx⟩ ⟨y, hy⟩
      h1 h2)))

/-- AUX: not in paper. Two predecessors of the same node are comparable. -/
theorem le_total_of_lt {x y t : T} (hx : x < t) (hy : y < t) : x ≤ y ∨ y ≤ x := by
  rcases lt_trichotomy_of_lt hx hy with h | rfl | h
  · exact Or.inl h.le
  · exact Or.inl le_rfl
  · exact Or.inr h.le

/-- AUX: not in paper. For `s < t`, `ht s` is the position of `s` in `{x : x < t}`. -/
theorem ht_eq_typein {s t : T} (h : s < t) :
    ht s = Ordinal.typein (fun x y : Set.Iio t => (x : T) < y) ⟨s, h⟩ := by
  rw [← Ordinal.type_subrel]
  refine RelIso.ordinalType_congr ?_
  exact
    { toFun := fun x => ⟨⟨x.1, lt_trans x.2 h⟩, x.2⟩
      invFun := fun y => ⟨y.1.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

/-- AUX: not in paper. Heights are strictly monotone. -/
theorem ht_lt_ht {s t : T} (h : s < t) : ht s < ht t := by
  rw [ht_eq_typein h]
  exact Ordinal.typein_lt_type _ _

/-- AUX: not in paper. Every ordinal below `ht t` is the height of a predecessor of `t`. -/
theorem exists_lt_ht_eq {t : T} {α : Ordinal.{w}} (h : α < ht t) : ∃ s < t, ht s = α := by
  obtain ⟨⟨s, hs⟩, rfl⟩ := Ordinal.typein_surj (fun x y : Set.Iio t => (x : T) < y) h
  exact ⟨s, hs, ht_eq_typein hs⟩

/-- AUX: not in paper. Two nodes below the same node and of the same height are equal. -/
theorem eq_of_le_of_le_of_ht_eq {x y z : T} (hx : x ≤ z) (hy : y ≤ z) (h : ht x = ht y) :
    x = y := by
  rcases hx.lt_or_eq with hx | rfl
  · rcases hy.lt_or_eq with hy | rfl
    · rcases lt_trichotomy_of_lt hx hy with h' | h' | h'
      · exact absurd h (ht_lt_ht h').ne
      · exact h'
      · exact absurd h (ht_lt_ht h').ne'
    · exact absurd h (ht_lt_ht hx).ne
  · rcases hy.lt_or_eq with hy | rfl
    · exact absurd h (ht_lt_ht hy).ne'
    · rfl

/-- AUX: not in paper. Heights are monotone. -/
theorem ht_le_ht_of_le {s t : T} (h : s ≤ t) : ht s ≤ ht t :=
  h.lt_or_eq.elim (fun h => (ht_lt_ht h).le) (fun h => h ▸ le_rfl)

/-- AUX: not in paper. `Iio s ⊆ Iio t` implies `ht s ≤ ht t`. -/
theorem ht_le_ht_of_Iio_subset {s t : T} (h : Set.Iio s ⊆ Set.Iio t) : ht s ≤ ht t := by
  by_contra hc
  obtain ⟨u, hu, hu'⟩ := exists_lt_ht_eq (lt_of_not_ge hc)
  exact (ht_lt_ht (h hu)).ne hu'

/-- AUX: not in paper. `Iio s ⊂ Iio t` implies `ht s < ht t`. -/
theorem ht_lt_ht_of_Iio_ssubset {s t : T} (h : Set.Iio s ⊂ Set.Iio t) : ht s < ht t := by
  obtain ⟨u, hut, hus⟩ := Set.exists_of_ssubset h
  have hsub : Set.Iio s ⊆ Set.Iio u := by
    intro x hx
    rcases lt_trichotomy_of_lt (h.1 hx) hut with h' | rfl | h'
    · exact h'
    · exact absurd hx hus
    · exact absurd (lt_trans h' hx) hus
  exact (ht_le_ht_of_Iio_subset hsub).trans_lt (ht_lt_ht hut)

/-- AUX: not in paper. If `Iio s ⊂ Iio t` then `Iio s = Iio u` for some `u < t`. -/
theorem exists_Iio_eq_of_ssubset {s t : T} (h : Set.Iio s ⊂ Set.Iio t) :
    ∃ u < t, Set.Iio s = Set.Iio u := by
  obtain ⟨u, hut, hu⟩ := exists_lt_ht_eq (ht_lt_ht_of_Iio_ssubset h)
  have hsub : Set.Iio s ⊆ Set.Iio u := by
    intro x hx
    rcases lt_trichotomy_of_lt (h.1 hx) hut with h' | rfl | h'
    · exact h'
    · exact absurd hu (ht_lt_ht hx).ne
    · exact absurd hu (ht_lt_ht (lt_trans h' hx)).ne
  refine ⟨u, hut, hsub.antisymm ?_⟩
  by_contra hc
  exact (ht_lt_ht_of_Iio_ssubset (hsub.ssubset_of_not_subset hc)).ne hu.symm

/-- AUX: not in paper. Two downward closed subsets of `Iio t` are comparable. -/
theorem Iio_subset_or_subset {s₁ s₂ t : T} (h₁ : Set.Iio s₁ ⊆ Set.Iio t)
    (h₂ : Set.Iio s₂ ⊆ Set.Iio t) : Set.Iio s₁ ⊆ Set.Iio s₂ ∨ Set.Iio s₂ ⊆ Set.Iio s₁ := by
  by_contra hc
  simp only [not_or, Set.not_subset] at hc
  obtain ⟨⟨x, hx₁, hx₂⟩, ⟨y, hy₂, hy₁⟩⟩ := hc
  rcases le_total_of_lt (h₁ hx₁) (h₂ hy₂) with h | h
  · exact hx₂ (lt_of_le_of_lt h hy₂)
  · exact hy₁ (lt_of_le_of_lt h hx₁)

/-- AUX: not in paper. The order of a tree is well founded. -/
instance : WellFoundedLT T := by
  refine ⟨fun t => Acc.intro t fun y hy => ?_⟩
  have key : ∀ z : Set.Iio t, Acc (· < ·) (z : T) := by
    intro z
    induction z using (IsWellOrder.wf (r := fun x y : Set.Iio t => (x : T) < y)).induction with
    | _ z ih =>
      exact Acc.intro _ fun x hx => ih ⟨x, lt_trans hx z.2⟩ hx
  exact key ⟨y, hy⟩

/-- AUX: not in paper. Every node has height smaller than the height of the tree. -/
theorem ht_lt_height (t : T) : ht t < height T := by
  have hne : {α | Lev T α = ∅}.Nonempty := by
    obtain ⟨b, hb⟩ := Ordinal.bddAbove_of_small (s := Set.range (ht : T → Ordinal.{w}))
    refine ⟨Order.succ b, Set.eq_empty_of_forall_notMem fun x hx => ?_⟩
    exact (Order.lt_succ_iff.2 (hb ⟨x, rfl⟩)).ne hx
  rw [height, ← Order.succ_le_iff]
  refine le_csInf hne fun α hα => Order.succ_le_of_lt ?_
  by_contra hc
  rcases (not_lt.1 hc).lt_or_eq with h | h
  · obtain ⟨s, -, hs⟩ := exists_lt_ht_eq h
    exact (Set.eq_empty_iff_forall_notMem.1 hα) s hs
  · exact (Set.eq_empty_iff_forall_notMem.1 hα) t h.symm

/-- AUX: not in paper. Levels below the height are nonempty. -/
theorem lev_nonempty {α : Ordinal.{w}} (h : α < height T) : (Lev T α).Nonempty := by
  by_contra hc
  exact (csInf_le' (s := {β : Ordinal.{w} | Lev T β = ∅})
    (Set.not_nonempty_iff_eq_empty.1 hc)).not_gt h

/-- AUX: not in paper. A partial order is a tree if all predecessors of a node are comparable
and there is a strictly monotone map into a well-founded order. -/
theorem isTree_of_strictMono {P : Type*} [PartialOrder P] {β : Type*} [Preorder β]
    [WellFoundedLT β] (r : P → β) (hr : StrictMono r)
    (hc : ∀ t x y : P, x < t → y < t → x ≤ y ∨ y ≤ x) : IsTree P := by
  refine ⟨fun t => ?_⟩
  have : Std.Trichotomous (fun x y : Set.Iio t => (x : P) < y) := ⟨fun a b hab hba => by
    rcases hc t a b a.2 b.2 with h | h
    · exact Subtype.ext ((h.lt_or_eq.resolve_left hab))
    · exact Subtype.ext ((h.lt_or_eq.resolve_left hba).symm)⟩
  exact @IsWellOrder.mk _ _ _
    (Subrelation.wf (fun {a b} h => hr h) (InvImage.wf (fun x : Set.Iio t => r x) wellFounded_lt))

/-- **Section 4, preliminaries** (unnumbered, "Clearly"). Every well-pruned tree of limit
ordinal height has no leaves. -/
theorem wellPruned_noLeaves_of_isSuccLimit (hT : WellPruned T)
    (hlim : Order.IsSuccLimit (height T)) : ∀ t : T, ¬ IsLeaf t := by
  intro t ht'
  obtain ⟨y, -, hy⟩ := hT.2 t (Order.succ (ht t)) (Order.lt_succ_of_not_isMax (not_isMax _))
    (hlim.succ_lt (ht_lt_height t))
  exact ht'.not_lt hy

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

/-- AUX: not in paper. Membership in the graph of `f_s`. -/
theorem mem_histFun {s p : T} {α : Ordinal.{w}} : (α, p) ∈ histFun s ↔ p < s ∧ ht p = α :=
  Iff.rfl

/-- AUX: not in paper. `f_s ⊆ f_t` iff every predecessor of `s` is a predecessor of `t`. -/
theorem histFun_subset_iff {s t : T} : histFun s ⊆ histFun t ↔ Set.Iio s ⊆ Set.Iio t := by
  constructor
  · intro h x hx
    exact (h (show (ht x, x) ∈ histFun s from ⟨hx, rfl⟩)).1
  · rintro h ⟨α, p⟩ ⟨hp, hα⟩
    exact ⟨h hp, hα⟩

/-- AUX: not in paper. -/
theorem histFun_ssubset_iff {s t : T} : histFun s ⊂ histFun t ↔ Set.Iio s ⊂ Set.Iio t := by
  simp only [Set.ssubset_def, histFun_subset_iff]

/-- AUX: not in paper. -/
theorem histFun_eq_iff {s t : T} : histFun s = histFun t ↔ Set.Iio s = Set.Iio t := by
  simp only [subset_antisymm_iff, histFun_subset_iff]

omit [IsTree T] in
/-- AUX: not in paper. For `u < t`, `Iio u ⊂ Iio t`. -/
theorem Iio_ssubset_Iio_of_lt {u t : T} (h : u < t) : Set.Iio u ⊂ Set.Iio t :=
  ⟨fun _ hx => lt_trans hx h, fun hs => lt_irrefl u (hs h)⟩

variable (T) in
/-- **Definition 4.1** (Section 4). The history tree of `T`: `F_T = ({f_t : t ∈ T}, ⊆)`. -/
def HistoryTree : Set (Set (Ordinal.{w} × T)) := Set.range histFun

variable (T) in
/-- **Definition 4.1** (Section 4), implicit claim: the history tree `F_T` is a tree. -/
theorem historyTree_isTree : IsTree (HistoryTree T) := by
  classical
  refine isTree_of_strictMono (fun g : HistoryTree T => ht g.2.choose) ?_ ?_
  · intro g g' h
    have h' : histFun g.2.choose ⊂ histFun g'.2.choose := by
      rw [g.2.choose_spec, g'.2.choose_spec]
      exact h
    exact ht_lt_ht_of_Iio_ssubset (histFun_ssubset_iff.1 h')
  · rintro ⟨_, t, rfl⟩ ⟨_, x, rfl⟩ ⟨_, y, rfl⟩ hx hy
    have hx' : histFun x ⊂ histFun t := hx
    have hy' : histFun y ⊂ histFun t := hy
    rcases Iio_subset_or_subset (histFun_ssubset_iff.1 hx').1 (histFun_ssubset_iff.1 hy').1 with
      h | h
    · exact Or.inl (histFun_subset_iff.2 h)
    · exact Or.inr (histFun_subset_iff.2 h)

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
  let g : HistoryTree T := ⟨histFun t, t, rfl⟩
  have hsurj : ∀ y : Set.Iio g, ∃ u : Set.Iio t, (y : HistoryTree T).1 = histFun u.1 := by
    rintro ⟨⟨_, s, rfl⟩, hs⟩
    obtain ⟨u, hu, hsu⟩ := exists_Iio_eq_of_ssubset (histFun_ssubset_iff.1 hs)
    exact ⟨⟨u, hu⟩, histFun_eq_iff.2 hsu⟩
  let f : (fun x y : Set.Iio t => (x : T) < y) ↪r
      (fun x y : Set.Iio g => (x : HistoryTree T) < y) :=
    RelEmbedding.ofMonotone
      (fun u => ⟨⟨histFun u.1, u.1, rfl⟩, show histFun u.1 ⊂ histFun t from
        histFun_ssubset_iff.2 (Iio_ssubset_Iio_of_lt u.2)⟩)
      (fun a b h => show histFun a.1 ⊂ histFun b.1 from
        histFun_ssubset_iff.2 (Iio_ssubset_Iio_of_lt h))
  have e := RelIso.ofSurjective f (by
    intro y
    obtain ⟨u, hu⟩ := hsurj y
    exact ⟨u, Subtype.ext (Subtype.ext hu.symm)⟩)
  have := e.ordinal_lift_type_eq
  unfold ht
  rw [this, Ordinal.lift_id'.{w, w + 1}]

/-- **After Definition 4.2** (Section 4, unnumbered, "Clearly"). `(F_T)^succ = ({f_t : t ∈
T^succ}, ⊆)`. -/
theorem mem_succPart_historyTree (g : HistoryTree T) :
    g ∈ succPart (HistoryTree T) ↔ ∃ t ∈ succPart T, g.1 = histFun t := by
  obtain ⟨_, s, rfl⟩ := g
  have hls : ∀ a : Ordinal.{w}, Ordinal.lift.{w + 1} (Order.succ a) =
      Order.succ (Ordinal.lift.{w + 1} a) := by
    intro a
    rw [Order.succ_eq_add_one, Order.succ_eq_add_one, Ordinal.lift_add_one]
  have key : (∃ β, Ordinal.lift.{w + 1} (ht s) = Order.succ β) ↔ ∃ β, ht s = Order.succ β := by
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨β', rfl⟩ := Ordinal.mem_range_lift_of_le (hβ ▸ (Order.le_succ β))
      exact ⟨β', Ordinal.lift_inj.1 (by rw [hβ, hls])⟩
    · rintro ⟨β, hβ⟩
      exact ⟨Ordinal.lift.{w + 1} β, by rw [hβ, hls]⟩
  constructor
  · rintro ⟨β, hβ⟩
    rw [ht_histFun] at hβ
    exact ⟨s, key.1 ⟨β, hβ⟩, rfl⟩
  · rintro ⟨t, ⟨β, hβ⟩, hst⟩
    have hg : (⟨histFun s, s, rfl⟩ : HistoryTree T) = ⟨histFun t, t, rfl⟩ := Subtype.ext hst
    change ∃ β, _ = _
    rw [hg, ht_histFun]
    exact ⟨Ordinal.lift.{w + 1} β, by rw [hβ, hls]⟩

/-- AUX: not in paper. Order isomorphisms of trees preserve heights. -/
theorem ht_orderIso {P Q : Type u} [PartialOrder P] [IsTree P] [PartialOrder Q] [IsTree Q]
    (e : P ≃o Q) (t : P) : ht (e t) = ht t := by
  unfold ht
  refine (RelIso.ordinalType_congr ?_).symm
  exact
    { toFun := fun x => ⟨e x.1, e.lt_iff_lt.2 x.2⟩
      invFun := fun y => ⟨e.symm y.1, by simpa using e.symm.lt_iff_lt.2 y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_rel_iff' := e.lt_iff_lt }

/-- AUX: not in paper. The node `m t`: the least node above `t` (for `t` not a leaf). -/
def succNode {t : T} (ht' : ¬ IsLeaf t) : T :=
  WellFounded.min wellFounded_lt {x | t < x} (not_isMax_iff.1 ht')

/-- AUX: not in paper. The predecessors of `succNode t` are exactly the nodes `≤ t`. -/
theorem Iio_succNode {t : T} (ht' : ¬ IsLeaf t) : Set.Iio (succNode ht') = Set.Iic t := by
  have hm : t < succNode ht' := WellFounded.min_mem _ {x | t < x} _
  ext x
  constructor
  · intro hx
    rcases lt_trichotomy_of_lt hx hm with h | rfl | h
    · exact h.le
    · exact le_rfl
    · exact absurd hx (WellFounded.not_lt_min wellFounded_lt {x | t < x} h)
  · intro hx
    exact lt_of_le_of_lt hx hm

/-- AUX: not in paper. `ht (succNode t) = ht t + 1`. -/
theorem ht_succNode {t : T} (ht' : ¬ IsLeaf t) : ht (succNode ht') = Order.succ (ht t) := by
  have hm : t < succNode ht' := WellFounded.min_mem _ {x | t < x} _
  refine le_antisymm ?_ (Order.succ_le_of_lt (ht_lt_ht hm))
  by_contra hc
  obtain ⟨s, hs, hs'⟩ := exists_lt_ht_eq (lt_of_not_ge hc)
  have hst : s ∈ Set.Iio (succNode ht') := hs
  rw [Iio_succNode] at hst
  have := ht_le_ht_of_le hst
  rw [hs'] at this
  exact (Order.lt_succ_of_not_isMax (not_isMax _)).not_ge this

/-- AUX: not in paper. Order isomorphisms of trees induce isomorphisms of history trees. -/
theorem histFun_orderIso {S : Type w} [PartialOrder S] [IsTree S] (e : T ≃o S) (t : T) :
    histFun (e t) = Prod.map id e '' histFun t := by
  ext ⟨α, q⟩
  constructor
  · rintro ⟨hq, hα⟩
    refine ⟨(α, e.symm q), ⟨?_, ?_⟩, by simp⟩
    · simpa using e.symm.lt_iff_lt.2 hq
    · rw [← hα, ← ht_orderIso e (e.symm q), e.apply_symm_apply]
  · rintro ⟨⟨β, p⟩, ⟨hp, hβ⟩, h⟩
    simp only [Prod.map, id, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨e.lt_iff_lt.2 hp, by rw [ht_orderIso e p, hβ]⟩

/-- **Remark 4.3** (Section 4, `\label{remark 3.3}`). If `g : F_T → F_S` is an isomorphism,
then `g ↾ (F_T)^succ` is an isomorphism from `(F_T)^succ` to `(F_S)^succ`. -/
theorem historyTree_iso_restrict_succPart {S : Type w} [PartialOrder S] [IsTree S]
    (g : HistoryTree T ≃o HistoryTree S) :
    ∃ g' : succPart (HistoryTree T) ≃o succPart (HistoryTree S),
      ∀ x : succPart (HistoryTree T), (g' x : HistoryTree S) = g x := by
  have hg : ∀ x, x ∈ succPart (HistoryTree T) ↔ g x ∈ succPart (HistoryTree S) := by
    intro x
    change (∃ β, ht x = Order.succ β) ↔ ∃ β, ht (g x) = Order.succ β
    rw [ht_orderIso]
  exact ⟨{ toEquiv := g.toEquiv.subtypeEquiv hg, map_rel_iff' := g.le_iff_le }, fun _ => rfl⟩

/-- **Proposition 4.4** (Section 4, `\label{proposition without leaves}`). A tree without
leaves is isomorphic to `(F_T)^succ`. -/
theorem nonempty_iso_succPart_historyTree (hT : ∀ t : T, ¬ IsLeaf t) :
    Nonempty (T ≃o succPart (HistoryTree T)) := by
  classical
  have hmem : ∀ t : T, (⟨histFun (succNode (hT t)), _, rfl⟩ : HistoryTree T) ∈
      succPart (HistoryTree T) :=
    fun t => (mem_succPart_historyTree _).2
      ⟨succNode (hT t), ⟨ht t, ht_succNode (hT t)⟩, rfl⟩
  let h : T → succPart (HistoryTree T) := fun t => ⟨_, hmem t⟩
  have hle : ∀ a b, h a ≤ h b ↔ a ≤ b := by
    intro a b
    change histFun (succNode (hT a)) ⊆ histFun (succNode (hT b)) ↔ a ≤ b
    rw [histFun_subset_iff, Iio_succNode, Iio_succNode, Set.Iic_subset_Iic]
  refine ⟨RelIso.ofSurjective (OrderEmbedding.ofMapLEIff h hle) ?_⟩
  rintro ⟨⟨_, s, rfl⟩, hy⟩
  obtain ⟨t', ⟨β, hβ⟩, hst⟩ := (mem_succPart_historyTree _).1 hy
  rw [histFun_eq_iff] at hst
  have hsucc : ht s = Order.succ β := by
    rw [← hβ]
    exact le_antisymm (ht_le_ht_of_Iio_subset hst.le) (ht_le_ht_of_Iio_subset hst.ge)
  obtain ⟨p, hp, hpβ⟩ := exists_lt_ht_eq (hsucc ▸ Order.lt_succ_of_not_isMax (not_isMax β))
  have hIio : Set.Iio s = Set.Iic p := by
    ext x
    constructor
    · intro hx
      rcases lt_trichotomy_of_lt hx hp with h' | rfl | h'
      · exact h'.le
      · exact le_rfl
      · have := ht_lt_ht h'
        have := ht_lt_ht hx
        rw [hpβ] at *
        rw [hsucc] at this
        exact absurd (Order.lt_succ_iff.1 this) (not_le.2 ‹β < ht x›)
    · intro hx
      exact lt_of_le_of_lt hx hp
  refine ⟨p, Subtype.ext (Subtype.ext ?_)⟩
  change histFun (succNode (hT p)) = histFun s
  rw [histFun_eq_iff, Iio_succNode, hIio]

/-- **Corollary 4.5** (Section 4, `\label{corollary reconstruction a tree from its history}`).
Two trees without leaves are isomorphic iff their history trees are isomorphic. -/
theorem nonempty_iso_iff_historyTree {S : Type w} [PartialOrder S] [IsTree S]
    (hT : ∀ t : T, ¬ IsLeaf t) (hS : ∀ s : S, ¬ IsLeaf s) :
    Nonempty (T ≃o S) ↔ Nonempty (HistoryTree T ≃o HistoryTree S) := by
  constructor
  · rintro ⟨e⟩
    have hmapT : ∀ g : HistoryTree T, Prod.map id e '' g.1 ∈ HistoryTree S := by
      rintro ⟨_, t, rfl⟩
      exact ⟨e t, histFun_orderIso e t⟩
    have hmapS : ∀ g : HistoryTree S, Prod.map id e.symm '' g.1 ∈ HistoryTree T := by
      rintro ⟨_, t, rfl⟩
      exact ⟨e.symm t, histFun_orderIso e.symm t⟩
    have hinj : Function.Injective (Prod.map id e : Ordinal.{w} × T → Ordinal.{w} × S) :=
      Function.injective_id.prodMap e.injective
    refine ⟨
      { toFun := fun g => ⟨_, hmapT g⟩
        invFun := fun g => ⟨_, hmapS g⟩
        left_inv := ?_
        right_inv := ?_
        map_rel_iff' := ?_ }⟩
    · rintro ⟨g, hg⟩
      apply Subtype.ext
      change Prod.map id e.symm '' (Prod.map id e '' g) = g
      rw [Set.image_image]
      conv_rhs => rw [← Set.image_id g]
      congr 1
      funext x
      exact Prod.ext rfl (e.symm_apply_apply _)
    · rintro ⟨g, hg⟩
      apply Subtype.ext
      change Prod.map id e '' (Prod.map id e.symm '' g) = g
      rw [Set.image_image]
      conv_rhs => rw [← Set.image_id g]
      congr 1
      funext x
      exact Prod.ext rfl (e.apply_symm_apply _)
    · intro a b
      exact Set.image_subset_image_iff hinj
  · rintro ⟨g⟩
    obtain ⟨g', -⟩ := historyTree_iso_restrict_succPart g
    obtain ⟨eT⟩ := nonempty_iso_succPart_historyTree hT
    obtain ⟨eS⟩ := nonempty_iso_succPart_historyTree hS
    exact ⟨(eT.trans g').trans eS.symm⟩

end History

/-! ## 4.2 The tree of a coloring -/

section TreeOfColoring

variable {κ : Cardinal.{w}} {D : Type v}

/-- AUX: not in paper. Elements of `Kappa κ` as ordinals: `<` is preserved. -/
theorem Kappa.coe_lt_coe {x y : Kappa κ} : (x : Ordinal.{w}) < y ↔ x < y :=
  Subtype.coe_lt_coe.trans Ordinal.ToType.mk.symm.lt_iff_lt

/-- AUX: not in paper. Elements of `Kappa κ` as ordinals: `≤` is preserved. -/
theorem Kappa.coe_le_coe {x y : Kappa κ} : (x : Ordinal.{w}) ≤ y ↔ x ≤ y :=
  Subtype.coe_le_coe.trans Ordinal.ToType.mk.symm.le_iff_le

/-- AUX: not in paper. Elements of `Kappa κ` as ordinals are `< κ.ord`. -/
theorem Kappa.coe_lt_ord (x : Kappa κ) : (x : Ordinal.{w}) < κ.ord :=
  (Ordinal.ToType.mk.symm x).2

/-- AUX: not in paper. The element of `Kappa κ` corresponding to an ordinal `α < κ.ord`. -/
def Kappa.mk (α : Ordinal.{w}) (h : α < κ.ord) : Kappa κ := Ordinal.ToType.mk ⟨α, h⟩

/-- AUX: not in paper. -/
@[simp] theorem Kappa.coe_mk (α : Ordinal.{w}) (h : α < κ.ord) :
    ((Kappa.mk α h : Kappa κ) : Ordinal.{w}) = α := by
  simp [Kappa.mk]

/-- AUX: not in paper. -/
theorem Kappa.coe_inj {x y : Kappa κ} : (x : Ordinal.{w}) = y ↔ x = y := by
  simp only [le_antisymm_iff, Kappa.coe_le_coe]

/-- `C(·,δ) ↾ β` for `β ≤ δ < κ` (Definition 4.6): the function `α ↦ C(α,δ)` on `{α : α < β}`,
encoded by its graph. -/
def fiberRestr (C : Coloring (Kappa κ) D) (δ β : Kappa κ) (hβ : β ≤ δ) :
    Set (Kappa κ × D) :=
  {p | ∃ h : p.1 < β, p.2 = C.color p.1 δ (h.trans_le hβ)}

/-- AUX: not in paper. Membership in the graph of `C(·,δ) ↾ β`. -/
theorem mem_fiberRestr {C : Coloring (Kappa κ) D} {δ β : Kappa κ} {hβ : β ≤ δ}
    {α : Kappa κ} {d : D} :
    (α, d) ∈ fiberRestr C δ β hβ ↔ ∃ h : α < β, d = C.color α δ (h.trans_le hβ) :=
  Iff.rfl

/-- AUX: not in paper. Inclusion between the graphs `C(·,δ) ↾ β`. -/
theorem fiberRestr_subset_iff {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ} (h₁ : β₁ ≤ δ₁)
    (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ ↔
      β₁ ≤ β₂ ∧ ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
        C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂) := by
  constructor
  · intro h
    have hle : β₁ ≤ β₂ := by
      by_contra hc
      obtain ⟨hlt, -⟩ := h (show (β₂, C.color β₂ δ₁ ((lt_of_not_ge hc).trans_le h₁)) ∈
        fiberRestr C δ₁ β₁ h₁ from ⟨lt_of_not_ge hc, rfl⟩)
      exact lt_irrefl _ hlt
    refine ⟨hle, fun α hα₁ hα₂ => ?_⟩
    have hm := h (show (α, C.color α δ₁ (hα₁.trans_le h₁)) ∈ fiberRestr C δ₁ β₁ h₁ from
      ⟨hα₁, rfl⟩)
    obtain ⟨_, hm'⟩ := hm
    exact hm'
  · rintro ⟨hle, hc⟩ ⟨α, d⟩ ⟨hα, hd⟩
    exact ⟨hα.trans_le hle, hd.trans (hc α hα (hα.trans_le hle))⟩

/-- AUX: not in paper. Two subgraphs of the same `C(·,δ) ↾ β` are comparable. -/
theorem fiberRestr_subset_of_subset {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ δ β : Kappa κ}
    {h₁ : β₁ ≤ δ₁} {h₂ : β₂ ≤ δ₂} {h : β ≤ δ} (s₁ : fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ β h)
    (s₂ : fiberRestr C δ₂ β₂ h₂ ⊆ fiberRestr C δ β h) (hle : β₁ ≤ β₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ := by
  rw [fiberRestr_subset_iff] at s₁ s₂ ⊢
  exact ⟨hle, fun α hα₁ hα₂ => (s₁.2 α hα₁ (hα₁.trans_le s₁.1)).trans
    (s₂.2 α hα₂ (hα₂.trans_le s₂.1)).symm⟩

/-- **Definition 4.6** (Section 4, `\label{definition T(C)}`, after [ri:chain, p. 7]). For
`C : [κ]^2 → D`: `T(C) := {C(·,δ) ↾ β | β ≤ δ < κ}`, ordered by `⊆`. -/
def treeOfColoring (C : Coloring (Kappa κ) D) : Set (Set (Kappa κ × D)) :=
  {g | ∃ (δ β : Kappa κ) (hβ : β ≤ δ), g = fiberRestr C δ β hβ}

/-- **Definition 4.6** (Section 4), implicit claim: `T(C)` is a tree. -/
theorem treeOfColoring_isTree (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := by
  classical
  let β : treeOfColoring C → Kappa κ := fun g => Classical.choose (Classical.choose_spec g.2)
  have hβ : ∀ g : treeOfColoring C, ∃ h, g.1 = fiberRestr C g.2.choose (β g) h :=
    fun g => Classical.choose_spec (Classical.choose_spec g.2)
  refine isTree_of_strictMono β ?_ ?_
  · intro g g' hlt
    obtain ⟨h, hg⟩ := hβ g
    obtain ⟨h', hg'⟩ := hβ g'
    have hss : g.1 ⊂ g'.1 := hlt
    rw [hg, hg'] at hss
    have hs := (fiberRestr_subset_iff _ _).1 hss.1
    refine lt_of_le_of_ne hs.1 fun heq => hss.2 ?_
    rw [fiberRestr_subset_iff]
    exact ⟨heq.ge, fun α hα₁ hα₂ => (hs.2 α hα₂ hα₁).symm⟩
  · intro g x y hx hy
    obtain ⟨h, hg⟩ := hβ g
    obtain ⟨hx', hxe⟩ := hβ x
    obtain ⟨hy', hye⟩ := hβ y
    have sx : x.1 ⊆ g.1 := (show x.1 ⊂ g.1 from hx).1
    have sy : y.1 ⊆ g.1 := (show y.1 ⊂ g.1 from hy).1
    rw [hg, hxe] at sx
    rw [hg, hye] at sy
    rcases le_total (β x) (β y) with hle | hle
    · left
      change x.1 ⊆ y.1
      rw [hxe, hye]
      exact fiberRestr_subset_of_subset sx sy hle
    · right
      change y.1 ⊆ x.1
      rw [hxe, hye]
      exact fiberRestr_subset_of_subset sy sx hle

instance (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := treeOfColoring_isTree C

/-- **Definition 4.6** (Section 4), implicit claim: `T(C)` is downward closed in
`(^{<κ}D, ⊆)`, i.e. closed under restriction to an initial segment `{α : α < γ}`. -/
theorem treeOfColoring_downwardClosed (C : Coloring (Kappa κ) D) :
    ∀ g ∈ treeOfColoring C, ∀ γ : Kappa κ, {p ∈ g | p.1 < γ} ∈ treeOfColoring C := by
  rintro g ⟨δ, β, hβ, rfl⟩ γ
  refine ⟨δ, min β γ, (min_le_left β γ).trans hβ, ?_⟩
  ext ⟨α, d⟩
  simp only [Set.mem_ofPred_eq, mem_fiberRestr, lt_min_iff]
  constructor
  · rintro ⟨⟨h, rfl⟩, hγ⟩
    exact ⟨⟨h, hγ⟩, rfl⟩
  · rintro ⟨⟨h, hγ⟩, rfl⟩
    exact ⟨⟨h, rfl⟩, hγ⟩

/-- **Remark 4.7** (Section 4). For `f : κ → 2`, the coloring `C_f(α,β) = f(α)` (`α < β`). -/
def colorMinOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.inf

/-- AUX: not in paper. `C_f(a,b) = f(a)` for `a < b`. -/
theorem colorMinOf_color (f : Kappa κ → Fin 2) (a b : Kappa κ) (h : a < b) :
    (colorMinOf f).color a b h = f a := by
  change f (Sym2.inf s(a, b)) = f a
  rw [Sym2.inf_mk, inf_of_le_left h.le]

/-- AUX: not in paper. For the reverse order: `C_f(a,b) = f(b)` for `b < a`. -/
theorem colorMinOf_color_dual (f : Kappa κ → Fin 2) (a b : (Kappa κ)ᵒᵈ) (h : a < b) :
    Coloring.color (A := (Kappa κ)ᵒᵈ) (colorMinOf f) a b h = f (OrderDual.ofDual b) := by
  change f (Sym2.inf s(OrderDual.ofDual a, OrderDual.ofDual b)) = _
  rw [Sym2.inf_mk, inf_of_le_right (show OrderDual.ofDual b ≤ OrderDual.ofDual a from h.le)]

/-- AUX: not in paper. `T(C_f)` for `C_f(α,β) = f(α)`: the graphs of `f ↾ β`. -/
theorem fiberRestr_colorMinOf (f : Kappa κ → Fin 2) (δ β : Kappa κ) (hβ : β ≤ δ) :
    fiberRestr (colorMinOf f) δ β hβ = {p | p.1 < β ∧ p.2 = f p.1} := by
  ext ⟨α, d⟩
  simp only [mem_fiberRestr, colorMinOf_color, Set.mem_ofPred_eq]
  exact ⟨fun ⟨h, hd⟩ => ⟨h, hd⟩, fun ⟨h, hd⟩ => ⟨h, hd⟩⟩

/-- **Remark 4.7** (Section 4). Each `C_f` (`C_f(α,β) = f(α)`) is locally additive and
*-locally additive, and `T(C_f)` is isomorphic to `(κ, ∈)`. -/
theorem colorMinOf_spec (f : Kappa κ → Fin 2) :
    IsLocallyAdditive (colorMinOf f) ∧ IsStarLocallyAdditive (colorMinOf f) ∧
      Nonempty (treeOfColoring (colorMinOf f) ≃o Kappa κ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d hab hbc hcd _
    rw [colorMinOf_color, colorMinOf_color]
  · intro a b c d hab hbc hcd h
    rw [colorMinOf_color_dual, colorMinOf_color_dual] at h ⊢
    exact h
  · let φ : Kappa κ → treeOfColoring (colorMinOf f) :=
      fun β => ⟨fiberRestr (colorMinOf f) β β le_rfl, β, β, le_rfl, rfl⟩
    have hφ : ∀ a b, φ a ≤ φ b ↔ a ≤ b := by
      intro a b
      change fiberRestr _ a a le_rfl ⊆ fiberRestr _ b b le_rfl ↔ a ≤ b
      rw [fiberRestr_subset_iff]
      refine ⟨fun h => h.1, fun h => ⟨h, fun α _ _ => ?_⟩⟩
      rw [colorMinOf_color, colorMinOf_color]
    refine ⟨(RelIso.ofSurjective (OrderEmbedding.ofMapLEIff φ hφ) ?_).symm⟩
    rintro ⟨_, δ, β, hβ, rfl⟩
    refine ⟨β, Subtype.ext ?_⟩
    change fiberRestr _ β β le_rfl = fiberRestr _ δ β hβ
    rw [fiberRestr_colorMinOf, fiberRestr_colorMinOf]

/-- **Remark 4.8** (Section 4). For `f : κ → 2`, the coloring `C_f(α,β) = f(β)` (`α < β`). -/
def colorMaxOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.sup

/-- AUX: not in paper. `C_f(a,b) = f(b)` for `a < b`. -/
theorem colorMaxOf_color (f : Kappa κ → Fin 2) (a b : Kappa κ) (h : a < b) :
    (colorMaxOf f).color a b h = f b := by
  change f (Sym2.sup s(a, b)) = f b
  rw [Sym2.sup_mk, sup_of_le_right h.le]

/-- AUX: not in paper. For the reverse order: `C_f(a,b) = f(a)` for `b < a`. -/
theorem colorMaxOf_color_dual (f : Kappa κ → Fin 2) (a b : (Kappa κ)ᵒᵈ) (h : a < b) :
    Coloring.color (A := (Kappa κ)ᵒᵈ) (colorMaxOf f) a b h = f (OrderDual.ofDual a) := by
  change f (Sym2.sup s(OrderDual.ofDual a, OrderDual.ofDual b)) = _
  rw [Sym2.sup_mk, sup_of_le_left (show OrderDual.ofDual b ≤ OrderDual.ofDual a from h.le)]

/-- **Remark 4.8** (Section 4). If `f : κ → 2` is not eventually constant, then `C_f`
(`C_f(α,β) = f(β)`) is locally additive and *-locally additive, and
`T(C_f) = ^{<κ}{0} ∪ ^{<κ}{1}` (the constant functions with domain some `β < κ`). -/
theorem colorMaxOf_spec (f : Kappa κ → Fin 2)
    (hf : ¬ ∃ (α₀ : Kappa κ) (i : Fin 2), ∀ β, α₀ ≤ β → f β = i) :
    IsLocallyAdditive (colorMaxOf f) ∧ IsStarLocallyAdditive (colorMaxOf f) ∧
      treeOfColoring (colorMaxOf f) =
        {g | ∃ (β : Kappa κ) (i : Fin 2), g = {p | p.1 < β ∧ p.2 = i}} := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d hab hbc hcd h
    rw [colorMaxOf_color, colorMaxOf_color] at h ⊢
    exact h
  · intro a b c d hab hbc hcd _
    rw [colorMaxOf_color_dual, colorMaxOf_color_dual]
  · have hfr : ∀ (δ β : Kappa κ) (hβ : β ≤ δ),
        fiberRestr (colorMaxOf f) δ β hβ = {p | p.1 < β ∧ p.2 = f δ} := by
      intro δ β hβ
      ext ⟨α, d⟩
      simp only [mem_fiberRestr, colorMaxOf_color, Set.mem_ofPred_eq]
      exact ⟨fun ⟨h, hd⟩ => ⟨h, hd⟩, fun ⟨h, hd⟩ => ⟨h, hd⟩⟩
    ext g
    constructor
    · rintro ⟨δ, β, hβ, rfl⟩
      exact ⟨β, f δ, hfr δ β hβ⟩
    · rintro ⟨β, i, rfl⟩
      obtain ⟨δ, hδ, hfδ⟩ : ∃ δ, β ≤ δ ∧ f δ = i := by
        by_contra hc
        push Not at hc
        have key : ∀ i j : Fin 2, j ≠ i → j = i + 1 := by decide
        exact hf ⟨β, i + 1, fun δ hδ => key i _ (hc δ hδ)⟩
      exact ⟨δ, β, hδ, by rw [hfr, hfδ]⟩

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

/-- AUX: not in paper. `t^i_α ∈ Lev_α(T)`. -/
theorem Enumeration.mem_lev (e : Enumeration κ T) {α i : Ordinal.{w}} (hα : α < κ.ord)
    (hi : i < (#(Lev T α)).ord) : e.t α i ∈ Lev T α :=
  (e.bijOn α hα).mapsTo hi

/-- AUX: not in paper. `ht(t^i_α) = α`. -/
theorem Enumeration.ht_t (e : Enumeration κ T) {α i : Ordinal.{w}} (hα : α < κ.ord)
    (hi : i < (#(Lev T α)).ord) : ht (e.t α i) = α :=
  e.mem_lev hα hi

/-- AUX: not in paper. In a `κ`-tree, `0 < μ_α` for `α < κ`. -/
theorem zero_lt_ord_lev (hT : IsKappaTree κ T) {α : Ordinal.{w}} (hα : α < κ.ord) :
    0 < (#(Lev T α)).ord := by
  rw [Cardinal.ord_pos, pos_iff_ne_zero, Cardinal.mk_ne_zero_iff]
  exact (lev_nonempty (hT.1 ▸ hα)).to_subtype

/-- AUX: not in paper. Every node of `Lev_α(T)` is some `t^i_α`. -/
theorem Enumeration.exists_eq (e : Enumeration κ T) {α : Ordinal.{w}} (hα : α < κ.ord) {x : T}
    (hx : x ∈ Lev T α) : ∃ i < (#(Lev T α)).ord, e.t α i = x :=
  (e.bijOn α hα).surjOn hx

/-- AUX: not in paper. Two nodes below a common node are comparable. -/
theorem le_total_of_le {x y z : T} (hx : x ≤ z) (hy : y ≤ z) : x ≤ y ∨ y ≤ x := by
  rcases hx.lt_or_eq with hx | rfl
  · rcases hy.lt_or_eq with hy | rfl
    · exact le_total_of_lt hx hy
    · exact Or.inl hx.le
  · exact Or.inr hy

/-- AUX: not in paper. A node of height `α` and a node of height `β > α` below a common node:
the first is below the second. -/
theorem lt_of_le_of_le_of_ht_lt {x y z : T} (hx : x ≤ z) (hy : y ≤ z) (h : ht x < ht y) :
    x < y := by
  rcases le_total_of_le hx hy with h' | h'
  · exact h'.lt_of_ne fun hxy => h.ne (congrArg ht hxy)
  · exact absurd (ht_le_ht_of_le h') (not_le.2 h)

/-- **Definition 4.11** (Section 4, `\label{definition C(T,e)}`). `C = C(T,e)`, where
`C(T,e) : [κ]^2 → μ` is defined by `C(T,e)(α,δ) = i` iff `α < δ` and `i < μ` is the unique
ordinal with `t^i_α ≤_T t^0_δ`. Uniqueness is automatic, so the condition reads: `i < μ_α` (so
that `t^i_α` is defined) and `t^i_α ≤_T t^0_δ`. -/
def IsTreeColoring (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T))) :
    Prop :=
  ∀ (α δ : Kappa κ) (h : α < δ),
    ((C.color α δ h : Ordinal.{w}) < (#(Lev T (α : Ordinal.{w}))).ord) ∧
      e.t α (C.color α δ h) ≤ e.t δ 0

/-- AUX: not in paper. Uniqueness in Definition 4.11: if `i < μ_α` and `t^i_α ≤ t^0_δ` then
`C(T,e)(α,δ) = i`. -/
theorem IsTreeColoring.color_eq {e : Enumeration κ T}
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) {α δ : Kappa κ}
    (h : α < δ) {i : Ordinal.{w}} (hi : i < (#(Lev T (α : Ordinal.{w}))).ord)
    (hle : e.t α i ≤ e.t δ 0) : (C.color α δ h : Ordinal.{w}) = i := by
  obtain ⟨hj, hjle⟩ := hC α δ h
  have hα := Kappa.coe_lt_ord α
  refine (e.bijOn α hα).injOn hj hi (eq_of_le_of_le_of_ht_eq hjle hle ?_)
  rw [e.ht_t hα hj, e.ht_t hα hi]

/-- AUX: not in paper. `μ_α ≤ μ`. -/
theorem card_lev_le_levelSup (α : Kappa κ) : #(Lev T (α : Ordinal.{w})) ≤ levelSup κ T :=
  le_ciSup (Cardinal.bddAbove_of_small (s := Set.range fun α : Kappa κ => #(Lev T α))) α

/-- **Definition 4.11** (Section 4), implicit claim: for a `κ`-tree `T` and an enumeration `e`,
`C(T,e)` is well defined, i.e. exactly one coloring `C : [κ]^2 → μ` satisfies the definition. -/
theorem existsUnique_isTreeColoring (hT : IsKappaTree κ T) (e : Enumeration κ T) :
    ∃! C, IsTreeColoring e C := by
  classical
  have hex : ∀ p : Pairs (Kappa κ), ∃ x : Kappa (levelSup κ T), ∀ (α δ : Kappa κ) (h : α < δ),
      p = Pairs.mk α δ h.ne → (x : Ordinal.{w}) < (#(Lev T (α : Ordinal.{w}))).ord ∧
        e.t α x ≤ e.t δ 0 := by
    intro p
    obtain ⟨α, δ, h, rfl⟩ := p.exists_eq_mk
    have hδ := Kappa.coe_lt_ord δ
    have hα := Kappa.coe_lt_ord α
    have hz := e.ht_t hδ (zero_lt_ord_lev hT hδ)
    have hαz : (α : Ordinal.{w}) < ht (e.t δ 0) := by
      rw [hz]
      exact Kappa.coe_lt_coe.2 h
    obtain ⟨s, hs, hsα⟩ := exists_lt_ht_eq hαz
    obtain ⟨i, hi, rfl⟩ := e.exists_eq hα hsα
    have hiμ : i < (levelSup κ T).ord :=
      hi.trans_le (Cardinal.ord_le_ord.2 (card_lev_le_levelSup α))
    refine ⟨Kappa.mk i hiμ, fun α' δ' h' hp => ?_⟩
    obtain ⟨rfl, rfl⟩ := Pairs.mk_inj h h' hp
    rw [Kappa.coe_mk]
    exact ⟨hi, hs.le⟩
  choose C hC using hex
  refine ⟨C, fun α δ h => hC _ α δ h rfl, fun C' hC' => ?_⟩
  funext p
  obtain ⟨α, δ, h, rfl⟩ := p.exists_eq_mk
  change Coloring.color C' α δ h = Coloring.color C α δ h
  obtain ⟨hi, hle⟩ := hC _ α δ h rfl
  exact Kappa.coe_inj.1 (hC'.color_eq h hi hle)

/-- **Claim 4.12** (Section 4, `\label{claim C(T,e) is locally additive}`). For a tree `T`
and an enumeration `e` of `T`, the coloring `C(T,e)` is locally additive. (The paper assumes
that `T` is a `κ`-tree; this hypothesis is not needed and is not assumed here.) -/
theorem isLocallyAdditive_of_isTreeColoring (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    IsLocallyAdditive C := by
  intro a b c d hab hbc hcd h
  have ha := Kappa.coe_lt_ord a
  have hb := Kappa.coe_lt_ord b
  obtain ⟨hi, hic⟩ := hC b c hbc
  obtain ⟨-, hid⟩ := hC b d (hbc.trans hcd)
  rw [← h] at hid
  obtain ⟨hj, hjc⟩ := hC a c (hab.trans hbc)
  have hlt : e.t a (C.color a c (hab.trans hbc)) < e.t b (C.color b c hbc) := by
    refine lt_of_le_of_le_of_ht_lt hjc hic ?_
    rw [e.ht_t ha hj, e.ht_t hb hi]
    exact Kappa.coe_lt_coe.2 hab
  exact Kappa.coe_inj.1 (hC.color_eq _ hj (hlt.le.trans hid)).symm

/-- **Definition 4.13** (Section 4). The enumeration `e` covers `T` if for every `t ∈ T` there
is `δ < κ` with `t <_T t^0_δ`. -/
def Enumeration.Covers (e : Enumeration κ T) : Prop :=
  ∀ t : T, ∃ δ < κ.ord, t < e.t δ 0

/-- AUX: not in paper. -/
@[simp] theorem Kappa.mk_coe {κ : Cardinal.{w}} (x : Kappa κ) :
    Kappa.mk (x : Ordinal.{w}) (Kappa.coe_lt_ord x) = x :=
  Ordinal.ToType.mk.apply_symm_apply x

omit [PartialOrder T] [IsTree T] in
/-- AUX: not in paper. A nonempty set `L` has a bijective enumeration
`⟨f(i) : i < |L|⟩` starting with a prescribed element `c ∈ L`. -/
theorem exists_bijOn_ord {L : Set T} {c : T} (hc : c ∈ L) :
    ∃ f : Ordinal.{w} → T, Set.BijOn f (Set.Iio (#L).ord) L ∧ f 0 = c := by
  classical
  have h0 : (0 : Ordinal.{w}) < (#L).ord := by
    rw [Cardinal.ord_pos, pos_iff_ne_zero, Cardinal.mk_ne_zero_iff]
    exact ⟨⟨c, hc⟩⟩
  obtain ⟨b⟩ : Nonempty (Set.Iio (#L).ord ≃ L) := by
    rw [← Cardinal.lift_mk_eq'.{w + 1, w}, Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
    simp
  let b' : Set.Iio (#L).ord ≃ L := (Equiv.swap ⟨0, h0⟩ (b.symm ⟨c, hc⟩)).trans b
  have hb'0 : b' ⟨0, h0⟩ = ⟨c, hc⟩ := by simp [b']
  refine ⟨fun x => if h : x < (#L).ord then (b' ⟨x, h⟩ : T) else c, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [dite_eq_left_of_eq_true (eq_true (show x < (#L).ord from hx))]
    exact (b' ⟨x, hx⟩).2
  · intro x hx y hy hxy
    simp only [dite_eq_left_of_eq_true (eq_true (show x < (#L).ord from hx)),
      dite_eq_left_of_eq_true (eq_true (show y < (#L).ord from hy))] at hxy
    exact congrArg Subtype.val (b'.injective (Subtype.ext hxy))
  · intro y hy
    have hx := (b'.symm ⟨y, hy⟩).2
    refine ⟨b'.symm ⟨y, hy⟩, hx, ?_⟩
    simp only [dite_eq_left_of_eq_true
      (eq_true (show (b'.symm ⟨y, hy⟩ : Ordinal.{w}) < (#L).ord from hx))]
    exact congrArg Subtype.val (b'.apply_symm_apply ⟨y, hy⟩)
  · simp only [dite_eq_left_of_eq_true (eq_true h0), hb'0]

/-- **Remark 4.14** (Section 4). For every cardinal `κ` and a well-pruned `κ`-tree `T`, there is
an enumeration `e` of `T` that covers `T`.
CHANGED w.r.t. the paper: the hypothesis `ℵ₀ ≤ κ` is added. As written ("every cardinal") the
statement is false for finite `κ ≥ 1` (a node of maximal level cannot be below any `t^0_δ`);
the paper's proof assumes `κ` regular. See FIDELITY.md. -/
theorem exists_covers (hκ : ℵ₀ ≤ κ) (hT : IsKappaTree κ T) (hwp : WellPruned T) :
    ∃ e : Enumeration κ T, e.Covers := by
  classical
  have hκ0 : (0 : Ordinal.{w}) < κ.ord := by
    rw [Cardinal.ord_pos]
    exact Cardinal.aleph0_pos.trans_le hκ
  obtain ⟨t₀, -⟩ := lev_nonempty (hT.1 ▸ hκ0 : (0 : Ordinal.{w}) < height T)
  have : Nonempty T := ⟨t₀⟩
  have hK : #(Kappa κ) = κ := by rw [Cardinal.mk_toType, Cardinal.card_ord]
  -- `|T| ≤ κ`
  have hcardT : #T ≤ κ := by
    have hU : (⋃ α : Kappa κ, Lev T (α : Ordinal.{w})) = Set.univ := by
      refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 ?_
      refine ⟨Kappa.mk (ht t) (hT.1 ▸ ht_lt_height t), ?_⟩
      exact (Kappa.coe_mk _ _).symm
    rw [← Cardinal.mk_univ, ← hU]
    refine (Cardinal.mk_iUnion_le _).trans ?_
    rw [hK]
    calc κ * ⨆ α : Kappa κ, #(Lev T (α : Ordinal.{w})) ≤ κ * κ := by
          gcongr
          exact ciSup_le' fun α => (hT.2 _ (Kappa.coe_lt_ord α)).le
      _ = κ := Cardinal.mul_eq_self hκ
  -- a surjection `ρ : κ → T` and a bijection `E : κ ≃ κ × κ`
  obtain ⟨j⟩ : Nonempty (T ↪ Kappa κ) := by
    rw [← Cardinal.le_def, hK]
    exact hcardT
  let ρ : Kappa κ → T := Function.invFun j
  have hρ : Function.Surjective ρ := Function.invFun_surjective j.injective
  obtain ⟨E⟩ : Nonempty (Kappa κ ≃ Kappa κ × Kappa κ) := by
    rw [← Cardinal.eq, Cardinal.mk_prod, Cardinal.lift_id, hK, Cardinal.mul_eq_self hκ]
  let σ : Kappa κ → T := fun x => ρ (E x).2
  -- every node `t` is `σ δ` for some `δ > ht t`
  have hσ : ∀ t : T, ∃ δ : Kappa κ, ht t < (δ : Ordinal.{w}) ∧ σ δ = t := by
    intro t
    obtain ⟨k, hk⟩ := hρ t
    have htκ : ht t < κ.ord := hT.1 ▸ ht_lt_height t
    let x₀ : Kappa κ := Kappa.mk (ht t) htκ
    by_contra hc
    push Not at hc
    have hle : ∀ γ : Kappa κ, E.symm (γ, k) ≤ x₀ := by
      intro γ
      rw [← Kappa.coe_le_coe, Kappa.coe_mk]
      by_contra h'
      refine hc _ (lt_of_not_ge h') ?_
      simp [σ, hk]
    have hinj : Function.Injective fun γ : Kappa κ => (⟨E.symm (γ, k), hle γ⟩ : Set.Iic x₀) := by
      intro γ γ' h
      have := E.symm.injective (congrArg Subtype.val h)
      exact (Prod.mk.inj this).1
    have h1 := Cardinal.mk_le_of_injective hinj
    rw [hK, ← Set.Iio_insert] at h1
    have h2 : #(Set.Iio x₀) < κ := by
      have := Cardinal.mk_Iio_lt x₀ (by rw [hK, Ordinal.type_toType])
      rwa [hK] at this
    have h3 := (Cardinal.mk_insert_le (a := x₀) (s := Set.Iio x₀)).trans_lt
      (Cardinal.add_lt_of_lt hκ h2 (Cardinal.one_lt_aleph0.trans_le hκ))
    exact absurd (h1.trans_lt h3) (lt_irrefl κ)
  -- the nodes `t^0_δ`
  have hc : ∀ δ : Kappa κ, ∃ y ∈ Lev T (δ : Ordinal.{w}),
      ht (σ δ) < (δ : Ordinal.{w}) → σ δ < y := by
    intro δ
    have hδ : (δ : Ordinal.{w}) < height T := by rw [hT.1]; exact Kappa.coe_lt_ord δ
    by_cases h : ht (σ δ) < (δ : Ordinal.{w})
    · obtain ⟨y, hy, hlt⟩ := hwp.2 (σ δ) δ h hδ
      exact ⟨y, hy, fun _ => hlt⟩
    · obtain ⟨y, hy⟩ := lev_nonempty hδ
      exact ⟨y, hy, fun h' => absurd h' h⟩
  choose c hcL hcσ using hc
  -- the enumeration
  have hf : ∀ α : Ordinal.{w}, ∃ f : Ordinal.{w} → T, ∀ hα : α < κ.ord,
      Set.BijOn f (Set.Iio (#(Lev T α)).ord) (Lev T α) ∧ f 0 = c (Kappa.mk α hα) := by
    intro α
    by_cases hα : α < κ.ord
    · have hmem : c (Kappa.mk α hα) ∈ Lev T α := by
        simpa using hcL (Kappa.mk α hα)
      obtain ⟨f, hf, hf0⟩ := exists_bijOn_ord hmem
      exact ⟨f, fun _ => ⟨hf, hf0⟩⟩
    · exact ⟨fun _ => t₀, fun h => absurd h hα⟩
  choose tf htf using hf
  refine ⟨⟨tf, fun α hα => (htf α hα).1⟩, fun t => ?_⟩
  obtain ⟨δ, hδ, hσδ⟩ := hσ t
  refine ⟨δ, Kappa.coe_lt_ord δ, ?_⟩
  change t < tf δ 0
  rw [(htf δ (Kappa.coe_lt_ord δ)).2, Kappa.mk_coe, ← hσδ]
  exact hcσ δ (by rw [hσδ]; exact hδ)

/-- Notation in the proof of Theorem 4.15: `t_β^{C(β,δ)}` for `β ≤ δ < κ`, with the stipulation
`C(δ,δ) = 0`. -/
def Enumeration.node (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T)))
    (β δ : Kappa κ) (_h : β ≤ δ) : T :=
  if hβ : β < δ then e.t β (C.color β δ hβ) else e.t δ 0

/-- AUX: not in paper. `t_β^{C(β,δ)} ∈ Lev_β(T)` and `t_β^{C(β,δ)} ≤ t^0_δ`. -/
theorem Enumeration.node_spec (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β δ : Kappa κ} (h : β ≤ δ) :
    ht (e.node C β δ h) = β ∧ e.node C β δ h ≤ e.t δ 0 := by
  unfold Enumeration.node
  split_ifs with hβ
  · obtain ⟨hi, hle⟩ := hC β δ hβ
    exact ⟨e.ht_t (Kappa.coe_lt_ord β) hi, hle⟩
  · obtain rfl : β = δ := le_antisymm h (not_lt.1 hβ)
    exact ⟨e.ht_t (Kappa.coe_lt_ord β) (zero_lt_ord_lev hT (Kappa.coe_lt_ord β)), le_rfl⟩

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
  obtain ⟨hn, hnle⟩ := e.node_spec hT hC hβδ
  have hα := Kappa.coe_lt_ord α
  have hαβ' : (α : Ordinal.{w}) < β := Kappa.coe_lt_coe.2 hαβ
  constructor
  · intro hc
    obtain ⟨-, hle⟩ := hC α δ (hαβ.trans_le hβδ)
    rw [hc] at hle
    refine ⟨lt_of_le_of_le_of_ht_lt hle hnle ?_, e.ht_t hα hi⟩
    rw [e.ht_t hα hi, hn]
    exact hαβ'
  · rintro ⟨hlt, -⟩
    exact hC.color_eq _ hi (hlt.le.trans hnle)

/-- **Claim 4.18** (Section 4, inside the proof of Theorem 4.15). The map
`h : C(·,δ) ↾ β ↦ f_{t_β^{C(β,δ)}}` is an order-homomorphism (in both directions, as in the
paper's proof): `C(·,δ₁) ↾ β₁ ⊆ C(·,δ₂) ↾ β₂` iff
`f_{t_{β₁}^{C(β₁,δ₁)}} ⊆ f_{t_{β₂}^{C(β₂,δ₂)}}`. -/
theorem fiberRestr_subset_iff_histFun_subset (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) ⊆ histFun (e.node C β₂ δ₂ h₂) := by
  obtain ⟨hn₁, hn₁le⟩ := e.node_spec hT hC h₁
  obtain ⟨hn₂, hn₂le⟩ := e.node_spec hT hC h₂
  rw [fiberRestr_subset_iff, histFun_subset_iff]
  constructor
  · rintro ⟨hle, hc⟩ x hx
    have hxβ : ht x < β₁ := hn₁ ▸ ht_lt_ht hx
    have hxκ : ht x < κ.ord := hxβ.trans (Kappa.coe_lt_ord β₁)
    obtain ⟨α, hαx⟩ : ∃ α : Kappa κ, ht x = (α : Ordinal.{w}) :=
      ⟨Kappa.mk (ht x) hxκ, (Kappa.coe_mk _ _).symm⟩
    have hαβ₁ : α < β₁ := Kappa.coe_lt_coe.1 (hαx ▸ hxβ)
    have hαβ₂ : α < β₂ := hαβ₁.trans_le hle
    obtain ⟨i, hi, hix⟩ := e.exists_eq (Kappa.coe_lt_ord α) (show x ∈ Lev T α from hαx)
    rw [← hix] at hx ⊢
    have h1 := (treeColoring_eq_iff_mem_histFun hT e hC hαβ₁ h₁ hi).2
      ⟨hx, e.ht_t (Kappa.coe_lt_ord α) hi⟩
    rw [hc α hαβ₁ hαβ₂] at h1
    exact ((treeColoring_eq_iff_mem_histFun hT e hC hαβ₂ h₂ hi).1 h1).1
  · intro hsub
    have hle : β₁ ≤ β₂ := by
      rw [← Kappa.coe_le_coe, ← hn₁, ← hn₂]
      exact ht_le_ht_of_Iio_subset hsub
    refine ⟨hle, fun α hα₁ hα₂ => ?_⟩
    obtain ⟨hi, -⟩ := hC α δ₁ (hα₁.trans_le h₁)
    have m1 := (treeColoring_eq_iff_mem_histFun hT e hC hα₁ h₁ hi).1 rfl
    have m2 : ((α : Ordinal.{w}), e.t α (C.color α δ₁ (hα₁.trans_le h₁))) ∈
        histFun (e.node C β₂ δ₂ h₂) := ⟨hsub m1.1, m1.2⟩
    exact (Kappa.coe_inj.1 ((treeColoring_eq_iff_mem_histFun hT e hC hα₂ h₂ hi).2 m2)).symm

/-- **Claim 4.17** (Section 4, inside the proof of Theorem 4.15,
`\label{claim result of claim for theorem 4.21}`). For `β₁ ≤ δ₁` and `β₂ ≤ δ₂`:
`C(·,δ₁) ↾ β₁ = C(·,δ₂) ↾ β₂` iff `f_{t_{β₁}^{C(β₁,δ₁)}} = f_{t_{β₂}^{C(β₂,δ₂)}}`. -/
theorem fiberRestr_eq_iff_histFun_eq (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) = histFun (e.node C β₂ δ₂ h₂) := by
  rw [subset_antisymm_iff, subset_antisymm_iff,
    fiberRestr_subset_iff_histFun_subset hT e hC, fiberRestr_subset_iff_histFun_subset hT e hC]

/-- **Claim 4.19** (Section 4, inside the proof of Theorem 4.15). The map
`h : C(·,δ) ↾ β ↦ f_{t_β^{C(β,δ)}}` is surjective onto `{f_t : t ∈ T}` (when `e` covers `T`). -/
theorem exists_histFun_node_eq (hT : IsKappaTree κ T) (e : Enumeration κ T) (he : e.Covers)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) (t : T) :
    ∃ (β δ : Kappa κ) (h : β ≤ δ), histFun (e.node C β δ h) = histFun t := by
  obtain ⟨δ, hδ, htδ⟩ := he t
  have htκ : ht t < κ.ord := (ht_lt_ht htδ).trans_eq (e.ht_t hδ (zero_lt_ord_lev hT hδ))
    |>.trans hδ
  let δ' : Kappa κ := Kappa.mk δ hδ
  let β : Kappa κ := Kappa.mk (ht t) htκ
  have hβδ : β ≤ δ' := by
    rw [← Kappa.coe_le_coe, Kappa.coe_mk, Kappa.coe_mk]
    exact ((ht_lt_ht htδ).trans_eq (e.ht_t hδ (zero_lt_ord_lev hT hδ))).le
  refine ⟨β, δ', hβδ, congrArg histFun ?_⟩
  obtain ⟨hn, hnle⟩ := e.node_spec hT hC hβδ
  have hδ' : ((δ' : Ordinal.{w})) = δ := Kappa.coe_mk _ _
  rw [hδ'] at hnle
  refine eq_of_le_of_le_of_ht_eq hnle htδ.le ?_
  rw [hn, Kappa.coe_mk]

/-- **Theorem 4.15** (Section 4, `\label{T isomorphic to T(C(T,e))}`). Let `T` be a `κ`-tree and
`e` an enumeration of `T`. If `e` covers `T` then `T(C(T,e))` is isomorphic to the history tree
`{f_t : t ∈ T}` of `T`. -/
theorem nonempty_iso_treeOfColoring_historyTree (hT : IsKappaTree κ T) (e : Enumeration κ T)
    (he : e.Covers) {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    Nonempty (treeOfColoring C ≃o HistoryTree T) := by
  classical
  let δ : treeOfColoring C → Kappa κ := fun g => g.2.choose
  let β : treeOfColoring C → Kappa κ := fun g => Classical.choose (Classical.choose_spec g.2)
  have hβ : ∀ g : treeOfColoring C, ∃ h, g.1 = fiberRestr C (δ g) (β g) h :=
    fun g => Classical.choose_spec (Classical.choose_spec g.2)
  let hβδ : ∀ g, β g ≤ δ g := fun g => (hβ g).choose
  have hg : ∀ g : treeOfColoring C, g.1 = fiberRestr C (δ g) (β g) (hβδ g) :=
    fun g => (hβ g).choose_spec
  let Φ : treeOfColoring C → HistoryTree T :=
    fun g => ⟨histFun (e.node C (β g) (δ g) (hβδ g)), _, rfl⟩
  have hΦ : ∀ a b, Φ a ≤ Φ b ↔ a ≤ b := by
    intro a b
    change histFun _ ⊆ histFun _ ↔ a.1 ⊆ b.1
    rw [hg a, hg b, fiberRestr_subset_iff_histFun_subset hT e hC]
  refine ⟨RelIso.ofSurjective (OrderEmbedding.ofMapLEIff Φ hΦ) ?_⟩
  rintro ⟨_, t, rfl⟩
  obtain ⟨β₀, δ₀, h₀, hh⟩ := exists_histFun_node_eq hT e he hC t
  let g : treeOfColoring C := ⟨fiberRestr C δ₀ β₀ h₀, δ₀, β₀, h₀, rfl⟩
  refine ⟨g, Subtype.ext ?_⟩
  change histFun (e.node C (β g) (δ g) (hβδ g)) = histFun t
  rw [← hh, ← fiberRestr_eq_iff_histFun_eq hT e hC]
  exact (hg g).symm

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
  obtain ⟨i₁⟩ := nonempty_iso_treeOfColoring_historyTree h₁ e₁ c₁ hC₁
  obtain ⟨i₂⟩ := nonempty_iso_treeOfColoring_historyTree h₂ e₂ c₂ hC₂
  rw [nonempty_iso_iff_historyTree hl₁ hl₂]
  constructor
  · rintro ⟨f⟩
    exact ⟨(i₁.trans f).trans i₂.symm⟩
  · rintro ⟨f⟩
    exact ⟨(i₁.symm.trans f).trans i₂⟩

end JardenShami
