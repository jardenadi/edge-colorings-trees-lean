import MyResearchesLLMLean.JardenShami.Section5

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 6

Section 6 ("Strongly Inaccessibles in the tree sense", `\label{section strongly inaccessibles}`):
the tree exponent `λ^{μ,tr}` and a characterization of weakly compact cardinals.

Phase 1: all statements are proved. Theorem 6.4 is proved from a stronger AUX statement
(`treeExp_lt_iff_isInaccessible_of_isRegular`, without the tree property and without Fact 6.3),
not along the paper's proof.

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
  exact isTree_of_strictMono (fun x : S => ht (x : T))
    (fun x y h => ht_lt_ht (show (x : T) < y from h))
    (fun _ x y hx hy => le_total_of_lt (T := T) hx hy)

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

/-- AUX: not in paper. In a tree of height `μ`, a chain `b` is determined by the function
sending `α < μ` to the node of `b` of height `α` (if any); hence `|Lim(T)| ≤ (|T| + 1)^μ`. -/
theorem mk_lim_le {T : Type w} [PartialOrder T] [IsTree T] {μ : Cardinal.{w}}
    (hT : height T = μ.ord) : #(Lim T) ≤ (#T + 1) ^ μ := by
  classical
  let Φ : Lim T → (Kappa μ → Option T) := fun b α =>
    if h : ∃ x ∈ b.1, ht x = (α : Ordinal.{w}) then some h.choose else none
  have hsub : ∀ b b' : Lim T, Φ b = Φ b' → b.1 ⊆ b'.1 := by
    intro b b' e x hx
    have hlt : ht x < μ.ord := hT ▸ ht_lt_height x
    let α : Kappa μ := Kappa.mk (ht x) hlt
    have hex : ∃ y ∈ b.1, ht y = (α : Ordinal.{w}) := ⟨x, hx, (Kappa.coe_mk _ _).symm⟩
    have hy : hex.choose = x := ht_injOn_of_isChain b.2.1.1 hex.choose_spec.1 hx
      (hex.choose_spec.2.trans (Kappa.coe_mk _ _))
    have h1 : Φ b α = some x := by
      simp only [Φ, dite_eq_left_of_eq_true (eq_true hex), hy]
    rw [e] at h1
    by_cases hex' : ∃ y ∈ b'.1, ht y = (α : Ordinal.{w})
    · simp only [Φ, dite_eq_left_of_eq_true (eq_true hex'), Option.some.injEq] at h1
      exact h1 ▸ hex'.choose_spec.1
    · simp [Φ, hex'] at h1
  have hinj : Function.Injective Φ := fun b b' e =>
    Subtype.ext ((hsub b b' e).antisymm (hsub b' b e.symm))
  calc #(Lim T) ≤ #(Kappa μ → Option T) := Cardinal.mk_le_of_injective hinj
    _ = (#T + 1) ^ μ := by rw [← Cardinal.power_def, Cardinal.mk_option, Kappa.mk_eq]

/-- AUX: not in paper. Every member of the set defining `λ^{μ,tr}` is `≤ (λ + 1)^μ`. -/
theorem treeExp_le_add_one_power (lam μ : Cardinal.{w}) : treeExp lam μ ≤ (lam + 1) ^ μ := by
  refine csSup_le' ?_
  rintro c ⟨T, _, _, hT, hcard, rfl⟩
  exact (mk_lim_le hT).trans (Cardinal.power_le_power_right (by gcongr))

/-- **Remark 6.2** (Section 6, `\label{remark tree exponent leq exponent}`). For every two infinite
cardinals `λ` and `μ`: `λ^{μ,tr} ≤ λ^μ`. -/
theorem treeExp_le_power (lam μ : Cardinal.{w}) (hlam : ℵ₀ ≤ lam) (hμ : ℵ₀ ≤ μ) :
    treeExp lam μ ≤ lam ^ μ := by
  calc treeExp lam μ ≤ (lam + 1) ^ μ := treeExp_le_add_one_power lam μ
    _ = lam ^ μ := by rw [Cardinal.add_one_of_aleph0_le hlam]

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

/-! ## Auxiliary lemmas for Theorem 6.4 (AUX: not in paper) -/

/-- AUX: not in paper. If `T` has height `μ` and at most `λ` nodes, then `|Lim(T)| ≤ λ^{μ,tr}`. -/
theorem mk_lim_le_treeExp {T : Type w} [PartialOrder T] [IsTree T] {lam μ : Cardinal.{w}}
    (hT : height T = μ.ord) (hcard : #T ≤ lam) : #(Lim T) ≤ treeExp lam μ := by
  refine le_csSup ⟨(lam + 1) ^ μ, ?_⟩ ⟨T, inferInstance, inferInstance, hT, hcard, rfl⟩
  rintro c ⟨T', _, _, hT', hcard', rfl⟩
  exact (mk_lim_le hT').trans (Cardinal.power_le_power_right (by gcongr))

/-- AUX: not in paper. For an inaccessible `κ` and `λ, μ < κ`: `λ^μ < κ`. -/
theorem power_lt_of_isInaccessible {κ lam μ : Cardinal.{w}} (hκ : κ.IsInaccessible)
    (hlam : lam < κ) (hμ : μ < κ) : lam ^ μ < κ := by
  calc lam ^ μ ≤ (2 ^ lam) ^ μ := Cardinal.power_le_power_right (Cardinal.cantor lam).le
    _ = 2 ^ (lam * μ) := Cardinal.power_mul.symm
    _ < κ := hκ.isStrongPrelimit (Cardinal.mul_lt_of_lt hκ.aleph0_lt.le hlam hμ)

/-- AUX: not in paper. A node of the full binary tree `2^{<ν}`: the graph of `f ↾ β`. -/
def binRestr {ν : Cardinal.{w}} (f : Kappa ν → Fin 2) (β : Kappa ν) : Set (Kappa ν × Fin 2) :=
  {p | p.1 < β ∧ p.2 = f p.1}

/-- AUX: not in paper. The full binary tree `2^{<ν} = {f ↾ β : f : ν → 2, β < ν}`, ordered
by `⊆`. -/
def binTree (ν : Cardinal.{w}) : Set (Set (Kappa ν × Fin 2)) :=
  {g | ∃ (f : Kappa ν → Fin 2) (β : Kappa ν), g = binRestr f β}

section BinTree

variable {ν : Cardinal.{w}}

/-- AUX: not in paper. Inclusion between nodes of `2^{<ν}`. -/
theorem binRestr_subset_iff {f f' : Kappa ν → Fin 2} {β β' : Kappa ν} :
    binRestr f β ⊆ binRestr f' β' ↔ β ≤ β' ∧ ∀ α < β, f α = f' α := by
  constructor
  · intro h
    have hle : β ≤ β' := by
      by_contra hc
      exact lt_irrefl _ (h (show (β', f β') ∈ binRestr f β from ⟨lt_of_not_ge hc, rfl⟩)).1
    exact ⟨hle, fun α hα => (h (show (α, f α) ∈ binRestr f β from ⟨hα, rfl⟩)).2⟩
  · rintro ⟨hle, hc⟩ ⟨α, d⟩ ⟨hα, hd⟩
    exact ⟨hα.trans_le hle, hd.trans (hc α hα)⟩

/-- AUX: not in paper. Equality of nodes of `2^{<ν}`. -/
theorem binRestr_eq_iff {f f' : Kappa ν → Fin 2} {β β' : Kappa ν} :
    binRestr f β = binRestr f' β' ↔ β = β' ∧ ∀ α < β, f α = f' α := by
  rw [Set.Subset.antisymm_iff, binRestr_subset_iff, binRestr_subset_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, -⟩
    exact ⟨le_antisymm h1 h3, h2⟩
  · rintro ⟨rfl, h⟩
    exact ⟨⟨le_rfl, h⟩, le_rfl, fun α hα => (h α hα).symm⟩

/-- AUX: not in paper. `2^{<ν}` is a tree. -/
theorem binTree_isTree : IsTree (binTree ν) := by
  classical
  let β : binTree ν → Kappa ν := fun g => Classical.choose (Classical.choose_spec g.2)
  have hβ : ∀ g : binTree ν, g.1 = binRestr g.2.choose (β g) :=
    fun g => Classical.choose_spec (Classical.choose_spec g.2)
  refine isTree_of_strictMono β ?_ ?_
  · intro g g' hlt
    have hss : g.1 ⊂ g'.1 := hlt
    rw [hβ g, hβ g'] at hss
    have hs := binRestr_subset_iff.1 hss.1
    refine lt_of_le_of_ne hs.1 fun heq => hss.2 ?_
    exact (binRestr_eq_iff.2 ⟨heq, hs.2⟩).symm.le
  · intro g x y hx hy
    have sx : x.1 ⊆ g.1 := (show x.1 ⊂ g.1 from hx).1
    have sy : y.1 ⊆ g.1 := (show y.1 ⊂ g.1 from hy).1
    rw [hβ g, hβ x] at sx
    rw [hβ g, hβ y] at sy
    have ax := binRestr_subset_iff.1 sx
    have ay := binRestr_subset_iff.1 sy
    rcases le_total (β x) (β y) with hle | hle
    · left
      change x.1 ⊆ y.1
      rw [hβ x, hβ y]
      exact binRestr_subset_iff.2
        ⟨hle, fun α hα => (ax.2 α hα).trans (ay.2 α (hα.trans_le hle)).symm⟩
    · right
      change y.1 ⊆ x.1
      rw [hβ x, hβ y]
      exact binRestr_subset_iff.2
        ⟨hle, fun α hα => (ay.2 α hα).trans (ax.2 α (hα.trans_le hle)).symm⟩

instance : IsTree (binTree ν) := binTree_isTree

/-- AUX: not in paper. The height of `f ↾ β` in `2^{<ν}` is `β`. -/
theorem ht_binRestr (f : Kappa ν → Fin 2) (β : Kappa ν) :
    ht (⟨binRestr f β, f, β, rfl⟩ : binTree ν) = (β : Ordinal.{w}) := by
  let g : binTree ν := ⟨binRestr f β, f, β, rfl⟩
  have hk : ∀ a : Set.Iio (β : Ordinal.{w}), (a : Ordinal.{w}) < ν.ord :=
    fun a => a.2.trans (Kappa.coe_lt_ord β)
  have hkl : ∀ a : Set.Iio (β : Ordinal.{w}), Kappa.mk a (hk a) < β := fun a =>
    Kappa.coe_lt_coe.1 (by rw [Kappa.coe_mk]; exact a.2)
  have hss : ∀ {a b : Kappa ν}, a < b → binRestr f a ⊂ binRestr f b := fun {a b} h =>
    ⟨binRestr_subset_iff.2 ⟨h.le, fun _ _ => rfl⟩,
      fun h' => h.not_ge (binRestr_subset_iff.1 h').1⟩
  let F : (fun x y : Set.Iio (β : Ordinal.{w}) => x < y) ↪r
      (fun x y : Set.Iio g => (x : binTree ν) < y) :=
    RelEmbedding.ofMonotone
      (fun a => ⟨⟨binRestr f (Kappa.mk a (hk a)), f, _, rfl⟩,
        show binRestr f _ ⊂ binRestr f β from hss (hkl a)⟩)
      (fun a b hab => show binRestr f _ ⊂ binRestr f _ from
        hss (by rw [← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk]; exact hab))
  have e := RelIso.ofSurjective F (by
    rintro ⟨⟨_, f', β', rfl⟩, hlt⟩
    have hs : binRestr f' β' ⊂ binRestr f β := hlt
    obtain ⟨hββ, hag⟩ := binRestr_subset_iff.1 hs.1
    have hββ' : β' < β := hββ.lt_of_ne fun he =>
      hs.2 (binRestr_eq_iff.2 ⟨he, hag⟩).symm.le
    refine ⟨⟨β', Kappa.coe_lt_coe.2 hββ'⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact binRestr_eq_iff.2 ⟨Kappa.mk_coe β', fun α hα => (hag α (by
      rwa [Kappa.mk_coe] at hα)).symm⟩)
  have := e.ordinal_lift_type_eq
  unfold ht
  rw [Ordinal.type_lt_Iio, Ordinal.lift_lift] at this
  exact (Ordinal.lift_inj.1 this).symm

/-- AUX: not in paper. The height of `2^{<ν}` is `ν`. -/
theorem height_binTree : height (binTree ν) = ν.ord := by
  refine IsLeast.csInf_eq ⟨?_, fun α hα => ?_⟩
  · refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    obtain ⟨_, f, β, rfl⟩ := g
    have h : ht (⟨binRestr f β, f, β, rfl⟩ : binTree ν) = ν.ord := hg
    rw [ht_binRestr] at h
    exact (Kappa.coe_lt_ord β).ne h
  · by_contra hc
    have hlt := lt_of_not_ge hc
    let b : Kappa ν := Kappa.mk α hlt
    have hmem : (⟨binRestr (fun _ => 0) b, _, b, rfl⟩ : binTree ν) ∈ Lev (binTree ν) α := by
      change ht _ = α
      rw [ht_binRestr, Kappa.coe_mk]
    have hα' : Lev (binTree ν) α = ∅ := hα
    rw [hα'] at hmem
    exact hmem

/-- AUX: not in paper. `|2^{<ν}| ≤ Σ_{β<ν} 2^{|β|}`. -/
theorem mk_binTree_le :
    #(binTree ν) ≤ Cardinal.sum fun β : Kappa ν => (2 : Cardinal.{w}) ^ #(Set.Iio β) := by
  classical
  have hU : binTree ν = ⋃ β : Kappa ν, Set.range fun f : Kappa ν → Fin 2 => binRestr f β := by
    ext g
    simp only [binTree, Set.mem_iUnion, Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨f, β, rfl⟩
      exact ⟨β, f, rfl⟩
    · rintro ⟨β, f, rfl⟩
      exact ⟨f, β, rfl⟩
  rw [hU]
  refine (Cardinal.mk_iUnion_le_sum_mk).trans (Cardinal.sum_le_sum _ _ fun β => ?_)
  -- `f ↾ β` depends only on `f` on `{α : α < β}`
  let R : (Set.Iio β → Fin 2) → Set (Kappa ν × Fin 2) := fun h =>
    {p | ∃ hp : p.1 < β, p.2 = h ⟨p.1, hp⟩}
  have hsub : (Set.range fun f : Kappa ν → Fin 2 => binRestr f β) ⊆ Set.range R := by
    rintro _ ⟨f, rfl⟩
    refine ⟨fun a => f a, ?_⟩
    ext ⟨α, d⟩
    simp only [R, binRestr, Set.mem_ofPred_eq]
    exact ⟨fun ⟨h, e⟩ => ⟨h, e⟩, fun ⟨h, e⟩ => ⟨h, e⟩⟩
  calc #(Set.range fun f : Kappa ν → Fin 2 => binRestr f β) ≤ #(Set.range R) :=
        Cardinal.mk_le_mk_of_subset hsub
    _ ≤ #(Set.Iio β → Fin 2) := Cardinal.mk_range_le
    _ = 2 ^ #(Set.Iio β) := by simp

/-- AUX: not in paper. For infinite `ν`, `2^{<ν}` has at least `2^ν` cofinal branches. -/
theorem two_power_le_mk_lim_binTree (hν : ℵ₀ ≤ ν) : 2 ^ ν ≤ #(Lim (binTree ν)) := by
  classical
  have hgt : ∀ α : Kappa ν, ∃ β : Kappa ν, α < β := fun α => by
    obtain ⟨β, -, h⟩ := Kappa.exists_gt_of_card_eq hν
      (show #(Set.univ : Set (Kappa ν)) = ν by rw [Cardinal.mk_univ, Kappa.mk_eq]) α
    exact ⟨β, h⟩
  let node : (Kappa ν → Fin 2) → Kappa ν → binTree ν := fun f β => ⟨binRestr f β, f, β, rfl⟩
  have hnode_inj : ∀ f, Function.Injective (node f) := fun f β β' h =>
    (binRestr_eq_iff.1 (congrArg Subtype.val h)).1
  let br : (Kappa ν → Fin 2) → Set (binTree ν) := fun f => Set.range (node f)
  have hchain : ∀ f, IsChain (· ≤ ·) (br f) := by
    rintro f _ ⟨β, rfl⟩ _ ⟨β', rfl⟩ -
    rcases le_total β β' with h | h
    · exact Or.inl (show binRestr f β ⊆ binRestr f β' from
        binRestr_subset_iff.2 ⟨h, fun _ _ => rfl⟩)
    · exact Or.inr (show binRestr f β' ⊆ binRestr f β from
        binRestr_subset_iff.2 ⟨h, fun _ _ => rfl⟩)
  have hbranch : ∀ f, IsBranch (br f) := by
    intro f
    refine ⟨hchain f, fun c hc hsub => hsub.antisymm fun x hx => ?_⟩
    obtain ⟨_, f', β', rfl⟩ := x
    obtain ⟨β'', hβ''⟩ := hgt β'
    have hy : node f β'' ∈ c := hsub ⟨β'', rfl⟩
    have hne : (⟨binRestr f' β', f', β', rfl⟩ : binTree ν) ≠ node f β'' := fun h =>
      hβ''.ne (binRestr_eq_iff.1 (congrArg Subtype.val h)).1
    rcases hc hx hy hne with h | h
    · have hs : binRestr f' β' ⊆ binRestr f β'' := h
      obtain ⟨-, hag⟩ := binRestr_subset_iff.1 hs
      exact ⟨β', Subtype.ext (binRestr_eq_iff.2 ⟨rfl, fun α hα => (hag α hα).symm⟩)⟩
    · have hs : binRestr f β'' ⊆ binRestr f' β' := h
      exact absurd (binRestr_subset_iff.1 hs).1 (not_le.2 hβ'')
  have hlim : ∀ f, br f ∈ Lim (binTree ν) := by
    intro f
    refine (isCofinalBranch_iff height_binTree).2 ⟨hbranch f, ?_⟩
    rw [Cardinal.mk_range_eq _ (hnode_inj f), Kappa.mk_eq]
  let Φ : (Kappa ν → Fin 2) → Lim (binTree ν) := fun f => ⟨br f, hlim f⟩
  have hΦ : Function.Injective Φ := by
    intro f f' h
    funext α
    obtain ⟨β, hβ⟩ := hgt α
    have hmem : node f β ∈ br f' := by
      have := congrArg Subtype.val h
      change br f = br f' at this
      rw [← this]
      exact ⟨β, rfl⟩
    obtain ⟨β', hβ'⟩ := hmem
    have := (binRestr_eq_iff.1 (congrArg Subtype.val hβ')).2
    exact (this α (hβ.trans_le (binRestr_eq_iff.1 (congrArg Subtype.val hβ')).1.ge)).symm
  calc 2 ^ ν = #(Kappa ν → Fin 2) := by simp
    _ ≤ #(Lim (binTree ν)) := Cardinal.mk_le_of_injective hΦ

end BinTree

/-- AUX: not in paper. Direction (1) ⇒ (2) of Theorem 6.4 without Fact 6.3 and without the tree
property: if `κ` is regular and uncountable and `λ^{μ,tr} < κ` for all infinite `μ ≤ λ < κ`,
then `2^ν < κ` for all `ν < κ` (apply the hypothesis to the full binary tree `2^{<ν}`). -/
theorem two_power_lt_of_treeExp_lt {κ : Cardinal.{w}} (hreg : κ.IsRegular)
    (h : ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) :
    ∀ ν < κ, 2 ^ ν < κ := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases lt_or_ge ν ℵ₀ with hfin | hinf
  · exact (Cardinal.power_lt_aleph0 (by exact_mod_cast Cardinal.natCast_lt_aleph0 (n := 2))
      hfin).trans_le hreg.aleph0_le
  · have hcard : #(binTree ν) < κ := by
      refine mk_binTree_le.trans_lt (Cardinal.sum_lt_of_isRegular hreg ?_ fun β => ?_)
      · rwa [Kappa.mk_eq]
      · have hβ : #(Set.Iio β) < ν := by
          have := Cardinal.mk_Iio_lt β (by rw [Kappa.mk_eq, Ordinal.type_toType])
          rwa [Kappa.mk_eq] at this
        exact IH _ hβ (hβ.trans hν)
    calc 2 ^ ν ≤ #(Lim (binTree ν)) := two_power_le_mk_lim_binTree hinf
      _ ≤ treeExp (max ν #(binTree ν)) ν := mk_lim_le_treeExp height_binTree (le_max_right _ _)
      _ < κ := h _ _ hinf (le_max_left _ _) (max_lt hν hcard)

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
      κ.IsInaccessible := by
  constructor
  · intro h
    refine Cardinal.isInaccessible_def.2 ⟨hunc, hreg, ⟨(Cardinal.aleph0_pos.trans hunc).ne', ?_⟩⟩
    exact fun ν hν => two_power_lt_of_treeExp_lt hreg h ν hν
  · intro hκ lam μ hμ hμlam hlam
    exact (treeExp_le_power lam μ (hμ.trans hμlam) hμ).trans_lt
      (power_lt_of_isInaccessible hκ hlam (hμlam.trans_lt hlam))

/-- **Theorem 6.4** (Section 6, `\label{theorem 5.4}`). Let `κ` be an uncountable regular cardinal
that satisfies the tree property. The following are equivalent: (1) `λ^{μ,tr} < κ` for each
`λ, μ < κ`; (2) `κ` is strongly inaccessible.
In (1), `λ^{μ,tr}` is taken only where Definition 6.1 defines it: infinite `μ ≤ λ`.
Fact 6.3 (used in the paper's proof of (1) ⇒ (2)) is an explicit hypothesis.
Phase 1: proved from the stronger AUX statement `treeExp_lt_iff_isInaccessible_of_isRegular`, not
along the paper's proof; the hypotheses `hF` (Fact 6.3) and `htp` (the tree property) are not
used. -/
theorem treeExp_lt_iff_isInaccessible (hF : Fact_6_3.{w}) (κ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (hreg : κ.IsRegular) (htp : NoAronszajn κ) :
    (∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      κ.IsInaccessible := by
  exact treeExp_lt_iff_isInaccessible_of_isRegular κ hunc hreg

/-- **Corollary 6.5** (Section 6). Let `κ` be an uncountable cardinal. Then `κ` is weakly compact
if and only if (1) `κ` is regular, (2) `κ` satisfies the tree property and (3) `λ^{μ,tr} < κ` for
each `λ, μ < κ` (as in Theorem 6.4: infinite `μ ≤ λ`).
Fact 6.3 (used through Theorem 6.4) is an explicit hypothesis. -/
theorem isWeaklyCompact_iff (hF : Fact_6_3.{w}) (κ : Cardinal.{w}) (hunc : ℵ₀ < κ) :
    IsWeaklyCompact κ ↔
      κ.IsRegular ∧ NoAronszajn κ ∧
        ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ := by
  constructor
  · rintro ⟨hκ, htp⟩
    exact ⟨hκ.isRegular, htp,
      (treeExp_lt_iff_isInaccessible hF κ hunc hκ.isRegular htp).2 hκ⟩
  · rintro ⟨hreg, htp, h⟩
    exact ⟨(treeExp_lt_iff_isInaccessible hF κ hunc hreg htp).1 h, htp⟩

end JardenShami
