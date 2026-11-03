import MyResearchesLLMLean.JardenShami.Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 5

Section 5 ("The Tree Property at Successor Cardinals",
`\label{section the tree property at successor cardinals}`).

Phase 1: all statements are proved. The file order is 5.4, 5.3, 5.2 (each proof uses the next
statement of the paper); auxiliary lemmas (`AUX: not in paper`) come first.

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

/-! ## Auxiliary lemmas (AUX: not in paper) -/

section Aux

/-- AUX: not in paper. `#κ = κ`. -/
theorem Kappa.mk_eq (κ : Cardinal.{w}) : #(Kappa κ) = κ := by
  rw [Cardinal.mk_toType, Cardinal.card_ord]

variable {κ : Cardinal.{w}}

/-- AUX: not in paper. For infinite `κ`, every initial segment `{y : y ≤ x}` of `κ` has size
`< κ`. -/
theorem Kappa.mk_Iic_lt (hκ : ℵ₀ ≤ κ) (x : Kappa κ) : #(Set.Iic x) < κ := by
  rw [← Set.Iio_insert]
  have h2 : #(Set.Iio x) < κ := by
    have := Cardinal.mk_Iio_lt x (by rw [Kappa.mk_eq, Ordinal.type_toType])
    rwa [Kappa.mk_eq] at this
  exact (Cardinal.mk_insert_le (a := x) (s := Set.Iio x)).trans_lt
    (Cardinal.add_lt_of_lt hκ h2 (Cardinal.one_lt_aleph0.trans_le hκ))

/-- AUX: not in paper. For infinite `κ`, a subset of `κ` of size `κ` is unbounded. -/
theorem Kappa.exists_gt_of_card_eq (hκ : ℵ₀ ≤ κ) {S : Set (Kappa κ)} (hS : #S = κ)
    (x : Kappa κ) : ∃ y ∈ S, x < y := by
  by_contra h
  push Not at h
  have h1 : #S ≤ #(Set.Iic x) := Cardinal.mk_le_mk_of_subset fun y hy => h y hy
  rw [hS] at h1
  exact (h1.trans_lt (Kappa.mk_Iic_lt hκ x)).false

/-- AUX: not in paper. For regular `κ`, a subset of `κ` of size `< κ` is bounded. -/
theorem Kappa.exists_gt_of_card_lt (hκ : κ.IsRegular) {S : Set (Kappa κ)} (hS : #S < κ) :
    ∃ x, ∀ y ∈ S, y < x := by
  by_contra h
  have hc : IsCofinal S := by
    by_contra h'
    exact h (not_isCofinal_iff.1 h')
  have := Order.cof_le hc
  rw [Ordinal.cof_toType, hκ.cof_ord] at this
  exact this.not_gt hS

/-- AUX: not in paper. For regular `κ`, an unbounded subset of `κ` has size `κ`. -/
theorem Kappa.card_eq_of_forall_exists_gt (hκ : κ.IsRegular) {S : Set (Kappa κ)}
    (h : ∀ x, ∃ y ∈ S, x < y) : #S = κ := by
  refine le_antisymm ((Cardinal.mk_set_le S).trans (Kappa.mk_eq κ).le) ?_
  by_contra hS
  obtain ⟨x, hx⟩ := Kappa.exists_gt_of_card_lt hκ (lt_of_not_ge hS)
  obtain ⟨y, hy, hxy⟩ := h x
  exact (hx y hy).not_gt hxy

/-- AUX: not in paper. For regular `κ`, a `κ`-sized `Γ ⊆ κ` and `F : κ → κ`, there is a
`κ`-sized `Γ' ⊆ Γ` such that `F γ₀ < γ` for all `γ₀ < γ` in `Γ'`. -/
theorem Kappa.exists_sparse (hκ : κ.IsRegular) {Γ : Set (Kappa κ)} (hΓ : #Γ = κ)
    (F : Kappa κ → Kappa κ) :
    ∃ Γ' ⊆ Γ, #Γ' = κ ∧ ∀ γ₀ ∈ Γ', ∀ γ ∈ Γ', γ₀ < γ → F γ₀ < γ := by
  obtain ⟨P, hP⟩ : ∃ P : Kappa κ → Prop,
      ∀ γ, P γ ↔ γ ∈ Γ ∧ ∀ γ₀ (_ : γ₀ < γ), P γ₀ → F γ₀ < γ :=
    ⟨wellFounded_lt.fix fun γ ih => γ ∈ Γ ∧ ∀ γ₀ (h : γ₀ < γ), ih γ₀ h → F γ₀ < γ,
      fun γ => by rw [WellFounded.fix_eq]⟩
  refine ⟨{γ | P γ}, fun γ hγ => ((hP γ).1 hγ).1, ?_,
    fun γ₀ h₀ γ hγ hlt => ((hP γ).1 hγ).2 γ₀ hlt h₀⟩
  refine Kappa.card_eq_of_forall_exists_gt hκ fun x => ?_
  by_contra hc
  push Not at hc
  have hsmall : #{γ | P γ} < κ :=
    (Cardinal.mk_le_mk_of_subset fun y hy => hc y hy).trans_lt
      (Kappa.mk_Iic_lt hκ.aleph0_le x)
  obtain ⟨z, hz⟩ := Kappa.exists_gt_of_card_lt hκ
    (Cardinal.mk_image_le.trans_lt hsmall : #(F '' {γ | P γ}) < κ)
  obtain ⟨γ, hγΓ, hγ⟩ := Kappa.exists_gt_of_card_eq hκ.aleph0_le hΓ (max x z)
  have hPγ : P γ := (hP γ).2 ⟨hγΓ, fun γ₀ _ h₀ =>
    (hz _ ⟨γ₀, h₀, rfl⟩).trans ((le_max_right _ _).trans_lt hγ)⟩
  exact (hc γ hPγ).not_gt ((le_max_left _ _).trans_lt hγ)

/-- AUX: not in paper. For a locally additive `C`, `C(a,δ) = C(a,δ')` implies
`C(α,δ) = C(α,δ')` for all `α ≤ a`. -/
theorem IsLocallyAdditive.color_eq_of_le {A : Type w} [LinearOrder A] {D : Type*}
    {C : Coloring A D} (hC : IsLocallyAdditive C) {a δ δ' α : A} (ha : a < δ) (ha' : a < δ')
    (h : C.color a δ ha = C.color a δ' ha') (hα : α ≤ a) :
    C.color α δ (hα.trans_lt ha) = C.color α δ' (hα.trans_lt ha') := by
  rcases hα.lt_or_eq with hα | rfl
  · rcases lt_trichotomy δ δ' with hd | rfl | hd
    · exact hC α a δ δ' hα ha hd h
    · rfl
    · exact (hC α a δ' δ hα ha' hd h.symm).symm
  · exact h

/-- AUX: not in paper. `C(a,b)` depends only on `a` and `b`. -/
theorem Coloring.color_congr {A : Type w} [LinearOrder A] {D : Type*} (C : Coloring A D)
    {a a' b b' : A} (ha : a = a') (hb : b = b') (h : a < b) (h' : a' < b') :
    C.color a b h = C.color a' b' h' := by
  subst ha hb
  rfl

/-- AUX: not in paper. Composing a locally additive coloring with an injective map of colors
gives a locally additive coloring. -/
theorem IsLocallyAdditive.comp_injective {A : Type w} [LinearOrder A] {D E : Type*}
    {C : Coloring A D} (hC : IsLocallyAdditive C) {ι : D → E} (hι : Function.Injective ι) :
    IsLocallyAdditive (ι ∘ C) := fun a b c d hab hbc hcd h =>
  congrArg ι (hC a b c d hab hbc hcd (hι h))

end Aux

namespace Tree

variable {T : Type w} [PartialOrder T] [IsTree T]

/-- AUX: not in paper. On a chain, `x < y` iff `ht x < ht y`. -/
theorem lt_iff_ht_lt_of_isChain {b : Set T} (hb : IsChain (· ≤ ·) b) {x y : T} (hx : x ∈ b)
    (hy : y ∈ b) : x < y ↔ ht x < ht y := by
  refine ⟨ht_lt_ht, fun h => ?_⟩
  rcases hb.total hx hy with h' | h'
  · exact h'.lt_of_ne fun e => h.ne (congrArg ht e)
  · exact absurd (ht_le_ht_of_le h') (not_le.2 h)

/-- AUX: not in paper. On a chain, the height is injective. -/
theorem ht_injOn_of_isChain {b : Set T} (hb : IsChain (· ≤ ·) b) : Set.InjOn ht b := by
  intro x hx y hy h
  rcases hb.total hx hy with h' | h'
  · exact eq_of_le_of_le_of_ht_eq h' le_rfl h
  · exact (eq_of_le_of_le_of_ht_eq h' le_rfl h.symm).symm

/-- AUX: not in paper. A chain of a tree is well-ordered. -/
theorem isWellOrder_of_isChain {b : Set T} (hb : IsChain (· ≤ ·) b) :
    IsWellOrder b (fun x y => (x : T) < y) := by
  have : Std.Trichotomous (fun x y : b => (x : T) < y) := ⟨fun x y hxy hyx => by
    rcases hb.total x.2 y.2 with h | h
    · exact Subtype.ext (h.lt_or_eq.resolve_left hxy)
    · exact Subtype.ext (h.lt_or_eq.resolve_left hyx).symm⟩
  exact @IsWellOrder.mk _ _ _ (InvImage.wf (fun x : b => (x : T)) wellFounded_lt)

/-- AUX: not in paper. In a tree of height `κ`, every chain has size `≤ κ`. -/
theorem mk_le_of_isChain {κ : Cardinal.{w}} (hT : height T = κ.ord) {b : Set T}
    (hb : IsChain (· ≤ ·) b) : #b ≤ κ := by
  have hlt : ∀ x : b, ht (x : T) < κ.ord := fun x => hT ▸ ht_lt_height (x : T)
  rw [← Kappa.mk_eq κ]
  refine Cardinal.mk_le_of_injective (f := fun x : b => Kappa.mk (ht (x : T)) (hlt x)) ?_
  intro x y h
  have := congrArg (fun z : Kappa κ => (z : Ordinal.{w})) h
  simp only [Kappa.coe_mk] at this
  exact Subtype.ext (ht_injOn_of_isChain hb x.2 y.2 this)

/-- AUX: not in paper. In a tree of height `κ`, a branch is cofinal iff it has size `κ`. -/
theorem isCofinalBranch_iff {κ : Cardinal.{w}} (hT : height T = κ.ord) {b : Set T} :
    IsCofinalBranch b ↔ IsBranch b ∧ #b = κ := by
  constructor
  · rintro ⟨hb, h, htype⟩
    refine ⟨hb, ?_⟩
    rw [← @Ordinal.card_type _ _ h, htype, hT, Cardinal.card_ord]
  · rintro ⟨hb, hcard⟩
    have := isWellOrder_of_isChain hb.1
    refine ⟨hb, inferInstance, le_antisymm ?_ ?_⟩
    · have hlt : ∀ x : b, ht (x : T) < κ.ord := fun x => hT ▸ ht_lt_height (x : T)
      rw [hT, ← Ordinal.type_toType κ.ord]
      refine Ordinal.type_le_iff'.2 ⟨⟨⟨fun x => Kappa.mk (ht (x : T)) (hlt x), ?_⟩, ?_⟩⟩
      · intro x y h
        have := congrArg (fun z : Kappa κ => (z : Ordinal.{w})) h
        simp only [Kappa.coe_mk] at this
        exact Subtype.ext (ht_injOn_of_isChain hb.1 x.2 y.2 this)
      · intro x y
        change Kappa.mk (ht (x : T)) (hlt x) < Kappa.mk (ht (y : T)) (hlt y) ↔ (x : T) < y
        rw [← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk,
          ← lt_iff_ht_lt_of_isChain hb.1 x.2 y.2]
    · rw [hT, Cardinal.ord_le, Ordinal.card_type, hcard]

end Tree

section TreeOfColoringAux

variable {κ : Cardinal.{w}} {D : Type w}

/-- AUX: not in paper. Equality of the graphs `C(·,δ) ↾ β`. -/
theorem fiberRestr_eq_fiberRestr {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ}
    (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) (hβ : β₁ = β₂)
    (hc : ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
      C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂)) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ :=
  ((fiberRestr_subset_iff h₁ h₂).2 ⟨hβ.le, hc⟩).antisymm
    ((fiberRestr_subset_iff h₂ h₁).2 ⟨hβ.ge, fun α hα₂ hα₁ => (hc α hα₁ hα₂).symm⟩)

/-- AUX: not in paper. Strict inclusion between the graphs `C(·,δ) ↾ β`. -/
theorem fiberRestr_ssubset_iff {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ}
    (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊂ fiberRestr C δ₂ β₂ h₂ ↔
      β₁ < β₂ ∧ ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
        C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂) := by
  constructor
  · rintro ⟨hs, hns⟩
    obtain ⟨hle, hc⟩ := (fiberRestr_subset_iff h₁ h₂).1 hs
    refine ⟨hle.lt_of_ne fun he => hns ?_, hc⟩
    exact (fiberRestr_eq_fiberRestr h₁ h₂ he hc).symm.le
  · rintro ⟨hlt, hc⟩
    refine ⟨(fiberRestr_subset_iff h₁ h₂).2 ⟨hlt.le, hc⟩, fun hs => ?_⟩
    exact hlt.not_ge ((fiberRestr_subset_iff h₂ h₁).1 hs).1

/-- AUX: not in paper. The height of `C(·,δ) ↾ β` in `T(C)` is `β`. -/
theorem ht_fiberRestr (C : Coloring (Kappa κ) D) {δ β : Kappa κ} (h : β ≤ δ) :
    ht (⟨fiberRestr C δ β h, δ, β, h, rfl⟩ : treeOfColoring C) = (β : Ordinal.{w}) := by
  let g : treeOfColoring C := ⟨fiberRestr C δ β h, δ, β, h, rfl⟩
  have hk : ∀ a : Set.Iio (β : Ordinal.{w}), (a : Ordinal.{w}) < κ.ord :=
    fun a => a.2.trans (Kappa.coe_lt_ord β)
  have hkl : ∀ a : Set.Iio (β : Ordinal.{w}), Kappa.mk a (hk a) < β := fun a =>
    Kappa.coe_lt_coe.1 (by rw [Kappa.coe_mk]; exact a.2)
  let f : (fun x y : Set.Iio (β : Ordinal.{w}) => x < y) ↪r
      (fun x y : Set.Iio g => (x : treeOfColoring C) < y) :=
    RelEmbedding.ofMonotone
      (fun a => ⟨⟨fiberRestr C δ (Kappa.mk a (hk a)) ((hkl a).le.trans h), δ, _, _, rfl⟩,
        show fiberRestr C δ _ _ ⊂ fiberRestr C δ β h from
          (fiberRestr_ssubset_iff ((hkl a).le.trans h) h).2 ⟨hkl a, fun _ _ _ => rfl⟩⟩)
      (fun a b hab => show fiberRestr C δ _ _ ⊂ fiberRestr C δ _ _ from
        (fiberRestr_ssubset_iff ((hkl a).le.trans h) ((hkl b).le.trans h)).2
          ⟨by rw [← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk]; exact hab,
            fun _ _ _ => rfl⟩)
  have e := RelIso.ofSurjective f (by
    rintro ⟨⟨_, δ', β', h', rfl⟩, hlt⟩
    have hss : fiberRestr C δ' β' h' ⊂ fiberRestr C δ β h := hlt
    obtain ⟨hββ, hag⟩ := (fiberRestr_ssubset_iff _ _).1 hss
    refine ⟨⟨β', Kappa.coe_lt_coe.2 hββ⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact fiberRestr_eq_fiberRestr ((hkl _).le.trans h) h' (Kappa.mk_coe β')
      fun α hα₁ hα₂ => (hag α hα₂ (hα₂.trans hββ)).symm)
  have := e.ordinal_lift_type_eq
  unfold ht
  rw [Ordinal.type_lt_Iio, Ordinal.lift_lift] at this
  exact (Ordinal.lift_inj.1 this).symm

/-- AUX: not in paper. The nodes of `Lev_α(T(C))` are the graphs `C(·,δ) ↾ β` with `β = α`. -/
theorem mem_lev_treeOfColoring {C : Coloring (Kappa κ) D} {g : treeOfColoring C}
    {α : Ordinal.{w}} :
    g ∈ Lev (treeOfColoring C) α ↔
      ∃ (δ β : Kappa κ) (h : β ≤ δ), g.1 = fiberRestr C δ β h ∧ (β : Ordinal.{w}) = α := by
  obtain ⟨_, δ, β, h, rfl⟩ := g
  constructor
  · intro hg
    exact ⟨δ, β, h, rfl, (ht_fiberRestr C h).symm.trans hg⟩
  · rintro ⟨δ', β', h', he, rfl⟩
    change ht _ = _
    have : (⟨fiberRestr C δ β h, δ, β, h, rfl⟩ : treeOfColoring C) =
        ⟨fiberRestr C δ' β' h', δ', β', h', rfl⟩ := Subtype.ext he
    rw [this, ht_fiberRestr]

/-- AUX: not in paper. The height of `T(C)` is `κ`. -/
theorem height_treeOfColoring (C : Coloring (Kappa κ) D) :
    height (treeOfColoring C) = κ.ord := by
  refine IsLeast.csInf_eq ⟨?_, fun α hα => ?_⟩
  · refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    obtain ⟨δ, β, h, -, hβ⟩ := mem_lev_treeOfColoring.1 hg
    exact (Kappa.coe_lt_ord β).ne hβ
  · by_contra hc
    have hlt := lt_of_not_ge hc
    let b : Kappa κ := Kappa.mk α hlt
    have hmem : (⟨fiberRestr C b b le_rfl, b, b, le_rfl, rfl⟩ : treeOfColoring C) ∈
        Lev (treeOfColoring C) α :=
      mem_lev_treeOfColoring.2 ⟨b, b, le_rfl, rfl, Kappa.coe_mk _ _⟩
    have hα' : Lev (treeOfColoring C) α = ∅ := hα
    rw [hα'] at hmem
    exact hmem

end TreeOfColoringAux

/-- AUX: not in paper. Claim 5.4 for every infinite `κ` (neither regularity nor uncountability
nor `μ < κ` is needed; the proof of Claim 5.4 uses only that there is a color). -/
theorem card_lev_treeOfColoring_le_of_aleph0_le (κ μ : Cardinal.{w}) (hκ0 : ℵ₀ ≤ κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := by
  classical
  intro β
  have hKμ : #(Kappa μ) = μ := Kappa.mk_eq μ
  -- `[κ]^2` is nonempty, hence there is at least one color
  have h1 : (1 : Ordinal.{w}) < κ.ord := by
    rw [Cardinal.lt_ord, Ordinal.card_one]
    exact Cardinal.one_lt_aleph0.trans_le hκ0
  have h0 : (0 : Ordinal.{w}) < κ.ord := zero_lt_one.trans h1
  have h01 : Kappa.mk 0 h0 < Kappa.mk 1 h1 := by
    rw [← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk]
    exact zero_lt_one
  have hμ0 : μ ≠ 0 := by
    rw [← hKμ]
    exact Cardinal.mk_ne_zero_iff.2 ⟨C.color _ _ h01⟩
  by_cases hβ : β < κ.ord
  swap
  · have : Lev (treeOfColoring C) β = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g hg => ?_
      obtain ⟨δ, β', h, -, hβ'⟩ := mem_lev_treeOfColoring.1 hg
      exact hβ (hβ' ▸ Kappa.coe_lt_ord β')
    rw [this]
    simp
  set b : Kappa κ := Kappa.mk β hβ with hb
  -- every node of level `β` is `C(·,δ) ↾ b` for some `δ ≥ b`
  have hnode : ∀ g ∈ Lev (treeOfColoring C) β,
      ∃ δ, b ≤ δ ∧ ∀ h : b ≤ δ, g.1 = fiberRestr C δ b h := by
    intro g hg
    obtain ⟨δ, β', h, hg, hβ'⟩ := mem_lev_treeOfColoring.1 hg
    have : β' = b := Kappa.coe_inj.1 (by rw [hβ', hb, Kappa.coe_mk])
    subst this
    exact ⟨δ, h, fun _ => hg⟩
  have : Nonempty (Kappa κ) := ⟨b⟩
  choose! dl hdl hgdl using hnode
  -- two nodes of level `β` whose colors agree below `b` are equal
  have heq : ∀ (g : treeOfColoring C) (hg : g ∈ Lev (treeOfColoring C) β)
      (g' : treeOfColoring C) (hg' : g' ∈ Lev (treeOfColoring C) β),
      (∀ (α : Kappa κ) (hα : α < b), C.color α (dl g) (hα.trans_le (hdl g hg)) =
        C.color α (dl g') (hα.trans_le (hdl g' hg'))) → g = g' := by
    intro g hg g' hg' hc
    refine Subtype.ext ?_
    rw [hgdl g hg (hdl g hg), hgdl g' hg' (hdl g' hg')]
    exact fiberRestr_eq_fiberRestr _ _ rfl fun α hα _ => hc α hα
  rcases le_or_gt ℵ₀ μ with hinf | hfin
  · -- `μ` infinite: inject the level into `μ + 1`
    let φ : Lev (treeOfColoring C) β → Option (Kappa μ) := fun g =>
      if h : b < dl g then some (C.color b (dl g) h) else none
    have hφ : Function.Injective φ := by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ e
      refine Subtype.ext (heq g hg g' hg' fun α hα => ?_)
      by_cases h : b < dl g <;> by_cases h' : b < dl g'
      · simp only [φ, dite_eq_left_of_eq_true (eq_true h),
          dite_eq_left_of_eq_true (eq_true h'), Option.some.injEq] at e
        exact hC.color_eq_of_le h h' e hα.le
      · simp [φ, h, h'] at e
      · simp [φ, h, h'] at e
      · have e1 : dl g = b := le_antisymm (not_lt.1 h) (hdl g hg)
        have e2 : dl g' = b := le_antisymm (not_lt.1 h') (hdl g' hg')
        exact C.color_congr rfl (e1.trans e2.symm) _ _
    calc #(Lev (treeOfColoring C) β) ≤ #(Option (Kappa μ)) := Cardinal.mk_le_of_injective hφ
      _ = μ + 1 := by rw [Cardinal.mk_option, hKμ]
      _ = μ := Cardinal.add_one_of_aleph0_le hinf
  · -- `μ = n` finite: `n + 1` distinct nodes give `n + 1` distinct colors `C(a,·)`
    obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.1 hfin
    by_contra hc
    have hn1 : ((n + 1 : ℕ) : Cardinal.{w}) ≤ #(Lev (treeOfColoring C) β) := by
      rw [Nat.cast_succ, ← Cardinal.succ_natCast]
      exact Order.succ_le_of_lt (lt_of_not_ge hc)
    obtain ⟨p, hpL, hpc⟩ := Cardinal.le_mk_iff_exists_subset.1 hn1
    have hpfin : p.Finite := Cardinal.lt_aleph0_iff_set_finite.1 (hpc ▸ Cardinal.natCast_lt_aleph0)
    have hw : ∀ (g : treeOfColoring C) (hg : g ∈ p) (g' : treeOfColoring C) (hg' : g' ∈ p),
        g ≠ g' → ∃ α, ∃ hα : α < b,
        C.color α (dl g) (hα.trans_le (hdl g (hpL hg))) ≠
          C.color α (dl g') (hα.trans_le (hdl g' (hpL hg'))) := by
      intro g hg g' hg' hne
      by_contra hc'
      push Not at hc'
      exact hne (heq g (hpL hg) g' (hpL hg') hc')
    choose! wf hwlt hwd using hw
    let W : Set (Kappa κ) := (fun q => wf q.1 q.2) '' ((p ×ˢ p) ∩ {q | q.1 ≠ q.2})
    have hWfin : W.Finite := ((hpfin.prod hpfin).inter_of_left _).image _
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hμ0 Nat.cast_zero
    have hpnt : Nontrivial p := by
      rw [← Cardinal.one_lt_iff_nontrivial, hpc]
      exact_mod_cast (by omega : 1 < n + 1)
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := exists_pair_ne p
    have hWne : W.Nonempty :=
      ⟨_, ⟨(x, y), ⟨⟨hx, hy⟩, fun e => hxy (Subtype.ext e)⟩, rfl⟩⟩
    obtain ⟨a, haW, hamax'⟩ := hWfin.exists_maximal hWne
    have hamax : ∀ y ∈ W, y ≤ a := fun y hy => (le_total y a).elim id (hamax' hy)
    have hab : a < b := by
      obtain ⟨q, ⟨⟨hq1, hq2⟩, hq⟩, rfl⟩ := haW
      exact hwlt q.1 hq1 q.2 hq2 hq
    let ψ : p → Kappa (n : Cardinal.{w}) := fun g =>
      C.color a (dl g) (hab.trans_le (hdl g (hpL g.2)))
    have hψ : Function.Injective ψ := by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ e
      by_contra hne
      have hne' : g ≠ g' := fun h => hne (Subtype.ext h)
      have hle : wf g g' ≤ a := hamax _ ⟨(g, g'), ⟨⟨hg, hg'⟩, hne'⟩, rfl⟩
      exact hwd g hg g' hg' hne' (hC.color_eq_of_le _ _ e hle)
    have := Cardinal.mk_le_of_injective hψ
    rw [hpc, hKμ, Nat.cast_le] at this
    omega

/-- **Claim 5.4** (Section 5, inside the proof of Lemma 5.3, direction (1) ⇒ (2)). For an
uncountable cardinal `κ` and a locally additive `C : [κ]^2 → μ`, all the levels of `T(C)` have
size `≤ μ`. (The paper works under the hypotheses of Lemma 5.3; of these, `κ` regular and
`μ < κ` are not needed and are not assumed here.) -/
theorem card_lev_treeOfColoring_le (κ μ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := by
  exact card_lev_treeOfColoring_le_of_aleph0_le κ μ hunc.le C hC

/-- AUX: not in paper. Every `κ`-tree (`κ ≠ 0`) has an enumeration (Definition 4.10). -/
theorem exists_enumeration {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
    (hκ : κ ≠ 0) (hT : IsKappaTree κ T) : Nonempty (Enumeration κ T) := by
  classical
  have hκ0 : (0 : Ordinal.{w}) < κ.ord := Cardinal.ord_pos.2 (pos_iff_ne_zero.2 hκ)
  obtain ⟨t₀, -⟩ := lev_nonempty (hT.1 ▸ hκ0 : (0 : Ordinal.{w}) < height T)
  have hf : ∀ α : Ordinal.{w}, ∃ f : Ordinal.{w} → T, ∀ _ : α < κ.ord,
      Set.BijOn f (Set.Iio (#(Lev T α)).ord) (Lev T α) := by
    intro α
    by_cases hα : α < κ.ord
    · obtain ⟨c, hc⟩ := lev_nonempty (hT.1 ▸ hα : α < height T)
      obtain ⟨f, hf, -⟩ := exists_bijOn_ord hc
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => t₀, fun h => absurd h hα⟩
  choose tf htf using hf
  exact ⟨⟨tf, htf⟩⟩

/-- AUX: not in paper. Direction (1) ⇒ (2) of Lemma 5.3 for every regular `κ` (also `κ = ℵ₀`;
the proof of Lemma 5.3 does not use that `κ` is uncountable). -/
theorem laArrowKappa_of_forall_branch (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (h1 : ∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) ≤ μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) :
    LaArrowKappa κ μ := by
  classical
  have hκ0 : ℵ₀ ≤ κ := hκ.aleph0_le
  intro C hC
  obtain ⟨B, hB, hBc⟩ := h1 (treeOfColoring C) (height_treeOfColoring C)
    (card_lev_treeOfColoring_le_of_aleph0_le κ μ hκ0 C hC)
  choose dg bg hbg hg using fun g : treeOfColoring C => g.2
  -- the levels of the nodes of `B` are unbounded in `κ`
  have hinj : Set.InjOn bg B := by
    intro g hgB g' hg'B he
    refine Subtype.ext ?_
    rw [hg g, hg g']
    rcases hB.1.total hgB hg'B with h | h
    · have hs : fiberRestr C (dg g) (bg g) (hbg g) ⊆ fiberRestr C (dg g') (bg g') (hbg g') := by
        rw [← hg g, ← hg g']
        exact h
      exact fiberRestr_eq_fiberRestr _ _ he ((fiberRestr_subset_iff _ _).1 hs).2
    · have hs : fiberRestr C (dg g') (bg g') (hbg g') ⊆ fiberRestr C (dg g) (bg g) (hbg g) := by
        rw [← hg g, ← hg g']
        exact h
      exact (fiberRestr_eq_fiberRestr _ _ he.symm ((fiberRestr_subset_iff _ _).1 hs).2).symm
  have hcard : #(bg '' B) = κ := by rw [Cardinal.mk_image_eq_of_injOn _ _ hinj, hBc]
  have hunb : ∀ γ : Kappa κ, ∃ g ∈ B, γ < bg g := by
    intro γ
    obtain ⟨_, ⟨g, hgB, rfl⟩, hγ⟩ := Kappa.exists_gt_of_card_eq hκ0 hcard γ
    exact ⟨g, hgB, hγ⟩
  choose G hGB hGb using hunb
  -- `F γ > γ` and `C(α, F γ) = C(α, F α)` for `α ≤ γ`
  let F : Kappa κ → Kappa κ := fun γ => dg (G γ)
  have hF : ∀ γ, γ < F γ := fun γ => (hGb γ).trans_le (hbg _)
  have hchain : ∀ α γ : Kappa κ, (hαγ : α ≤ γ) →
      C.color α (F γ) (hαγ.trans_lt (hF γ)) = C.color α (F α) (hF α) := by
    intro α γ hαγ
    have hα₁ : α < bg (G α) := hGb α
    have hα₂ : α < bg (G γ) := hαγ.trans_lt (hGb γ)
    rcases hB.1.total (hGB α) (hGB γ) with h | h
    · have hs : fiberRestr C (dg (G α)) (bg (G α)) (hbg _) ⊆
          fiberRestr C (dg (G γ)) (bg (G γ)) (hbg _) := by
        rw [← hg, ← hg]
        exact h
      exact (((fiberRestr_subset_iff _ _).1 hs).2 α hα₁ hα₂).symm
    · have hs : fiberRestr C (dg (G γ)) (bg (G γ)) (hbg _) ⊆
          fiberRestr C (dg (G α)) (bg (G α)) (hbg _) := by
        rw [← hg, ← hg]
        exact h
      exact ((fiberRestr_subset_iff _ _).1 hs).2 α hα₂ hα₁
  -- pigeonhole: `κ` many `γ` with the same color `C(F γ, F (F γ))`
  have hK : #(Kappa κ) = κ := Kappa.mk_eq κ
  obtain ⟨c, Γ, hΓs, hΓc, hΓ⟩ := Cardinal.infinite_pigeonhole_set
    (s := (Set.univ : Set (Kappa κ)))
    (fun γ => C.color (F γ) (F (F γ)) (hF (F γ))) κ
    (by rw [Cardinal.mk_univ, hK]) hκ0
    (by rw [Kappa.mk_eq, hκ.cof_ord]; exact hμ)
  have hΓκ : #Γ = κ := le_antisymm ((Cardinal.mk_set_le Γ).trans hK.le) hΓc
  -- thin out `Γ`
  obtain ⟨Γ', hΓ'Γ, hΓ'κ, hsp⟩ := Kappa.exists_sparse hκ hΓκ F
  refine ⟨F '' Γ', ?_, ?_⟩
  · have hinjF : Set.InjOn F Γ' := by
      intro x hx y hy hxy
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (hxy ▸ (hsp x hx y hy h)).not_gt (hF y) |>.elim
      · exact (hxy ▸ (hsp y hy x hx h)).not_gt (hF x) |>.elim
    rw [Cardinal.mk_image_eq_of_injOn _ _ hinjF, hΓ'κ]
  · -- every pair from `F '' Γ'` has color `c`
    have key : ∀ p : Pairs (Kappa κ), (∀ x ∈ p.1, x ∈ F '' Γ') → C p = c := by
      intro p hp
      obtain ⟨x, y, hxy, rfl⟩ := p.exists_eq_mk
      obtain ⟨γ₀, hγ₀, rfl⟩ := hp x (Sym2.mem_mk_left x y)
      obtain ⟨γ, hγ, rfl⟩ := hp y (Sym2.mem_mk_right _ y)
      have hlt : γ₀ < γ := by
        rcases lt_trichotomy γ₀ γ with h | rfl | h
        · exact h
        · exact absurd hxy (lt_irrefl _)
        · exact absurd hxy ((hsp γ hγ γ₀ hγ₀ h).trans (hF γ₀)).not_gt
      change C.color (F γ₀) (F γ) hxy = c
      rw [hchain (F γ₀) γ (hsp γ₀ hγ₀ γ hγ hlt).le]
      exact hΓ (hΓ'Γ hγ₀)
    intro p q hp hq
    rw [key p hp, key q hq]

/-- **Lemma 5.3** (Section 5, `\label{lemma 6}`, `\label{the main lemma}`). Suppose `κ` is a
regular uncountable cardinal and `μ < κ`. The following are equivalent: (1) every tree of height
`κ` whose levels have size `≤ μ` admits a `κ`-sized branch; (2) `κ → (κ)_{la_μ}`, namely every
locally additive coloring `C : [κ]^2 → μ` admits a homogeneous set of size `κ`. -/
theorem branch_iff_laArrowKappa (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ)
    (hμ : μ < κ) :
    (∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) ≤ μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) ↔
      LaArrowKappa κ μ := by
  classical
  have hκ0 : ℵ₀ ≤ κ := hunc.le
  constructor
  · -- (1) ⇒ (2)
    exact laArrowKappa_of_forall_branch κ μ hκ hμ
  · -- (2) ⇒ (1)
    intro h2 T _ _ hT hlev
    have hTk : IsKappaTree κ T := ⟨hT, fun α _ => (hlev α).trans_lt hμ⟩
    obtain ⟨e⟩ := exists_enumeration (Cardinal.aleph0_pos.trans_le hκ0).ne' hTk
    obtain ⟨C, hCe, -⟩ := existsUnique_isTreeColoring hTk e
    have hla := isLocallyAdditive_of_isTreeColoring e hCe
    -- the colors of `C(T,e)` are `< levelSup ≤ μ`
    have hsup : (levelSup κ T).ord ≤ μ.ord :=
      Cardinal.ord_le_ord.2 (ciSup_le' fun α => hlev _)
    let ι : Kappa (levelSup κ T) → Kappa μ := fun x =>
      Kappa.mk (x : Ordinal.{w}) ((Kappa.coe_lt_ord x).trans_le hsup)
    have hι : Function.Injective ι := by
      intro x y h
      have := congrArg (fun z : Kappa μ => (z : Ordinal.{w})) h
      simp only [ι, Kappa.coe_mk] at this
      exact Kappa.coe_inj.1 this
    obtain ⟨H, hH, hHom⟩ := h2 (ι ∘ C) (hla.comp_injective hι)
    have hHomC : IsHomogeneous C H := fun p q hp hq => hι (hHom p q hp hq)
    -- the common color `i`
    obtain ⟨x₀, hx₀⟩ : H.Nonempty := by
      rw [← Set.nonempty_coe_sort, ← Cardinal.mk_ne_zero_iff, hH]
      exact (Cardinal.aleph0_pos.trans_le hκ0).ne'
    obtain ⟨y₀, hy₀, hxy₀⟩ := Kappa.exists_gt_of_card_eq hκ0 hH x₀
    set i := C.color x₀ y₀ hxy₀ with hi
    have hcol : ∀ α ∈ H, ∀ δ ∈ H, ∀ h : α < δ, C.color α δ h = i := by
      intro α hα δ hδ h
      refine hHomC _ _ ?_ ?_
      · intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hα
        · exact hδ
      · intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hx₀
        · exact hy₀
    -- `{t^i_α : α ∈ H}` is a chain of size `κ`
    have hilt : ∀ α ∈ H, (i : Ordinal.{w}) < (#(Lev T (α : Ordinal.{w}))).ord := by
      intro α hα
      obtain ⟨δ, hδ, hαδ⟩ := Kappa.exists_gt_of_card_eq hκ0 hH α
      have := (hCe α δ hαδ).1
      rwa [hcol α hα δ hδ hαδ] at this
    have hht : ∀ α ∈ H, ht (e.t α i) = α := fun α hα =>
      e.ht_t (Kappa.coe_lt_ord α) (hilt α hα)
    have hlt : ∀ α ∈ H, ∀ β ∈ H, α < β → e.t α i < e.t β i := by
      intro α hα β hβ hαβ
      obtain ⟨γ, hγ, hβγ⟩ := Kappa.exists_gt_of_card_eq hκ0 hH β
      have h₁ := (hCe α γ (hαβ.trans hβγ)).2
      have h₂ := (hCe β γ hβγ).2
      rw [hcol α hα γ hγ] at h₁
      rw [hcol β hβ γ hγ] at h₂
      refine lt_of_le_of_le_of_ht_lt h₁ h₂ ?_
      rw [hht α hα, hht β hβ]
      exact Kappa.coe_lt_coe.2 hαβ
    let S : Set T := (fun α : Kappa κ => e.t α i) '' H
    have hSchain : IsChain (· ≤ ·) S := by
      rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ hne
      rcases lt_trichotomy α β with h | rfl | h
      · exact Or.inl (hlt α hα β hβ h).le
      · exact absurd rfl hne
      · exact Or.inr (hlt β hβ α hα h).le
    have hinjS : Set.InjOn (fun α : Kappa κ => e.t α i) H := by
      intro α hα β hβ h
      have := congrArg ht h
      simp only [hht α hα, hht β hβ] at this
      exact Kappa.coe_inj.1 this
    have hScard : #S = κ := by rw [Cardinal.mk_image_eq_of_injOn _ _ hinjS, hH]
    -- extend it to a branch
    obtain ⟨M, hM, hSM⟩ := hSchain.exists_maxChain
    refine ⟨M, hM, le_antisymm (mk_le_of_isChain hT hM.1) ?_⟩
    rw [← hScard]
    exact Cardinal.mk_le_mk_of_subset hSM

/-- **Theorem 5.2** (Section 5, `\label{theorem 4.2}`). For every infinite cardinal `μ` the
following are equivalent: (1) there exists no `μ⁺`-Aronszajn tree; (2) `μ⁺ → (μ⁺)_{la_μ}`, namely
every locally additive coloring `C : [μ⁺]^2 → μ` admits a homogeneous set of size `μ⁺`. -/
theorem noAronszajn_succ_iff_laArrowKappa (μ : Cardinal.{w}) (hμ : ℵ₀ ≤ μ) :
    NoAronszajn (Order.succ μ) ↔ LaArrowKappa (Order.succ μ) μ := by
  have hreg := Cardinal.isRegular_succ hμ
  have hlt : μ < Order.succ μ := Order.lt_succ μ
  rw [← branch_iff_laArrowKappa _ μ hreg (hμ.trans_lt hlt) hlt]
  constructor
  · intro h T _ _ hT hlev
    by_contra hc
    refine h T ⟨⟨hT, fun α _ => (hlev α).trans_lt hlt⟩, ?_⟩
    rintro ⟨b, hb⟩
    exact hc ⟨b, (isCofinalBranch_iff hT).1 hb⟩
  · intro h T _ _ ⟨hTk, hno⟩
    have hlev : ∀ α : Ordinal.{w}, #(Lev T α) ≤ μ := by
      intro α
      by_cases hα : α < (Order.succ μ).ord
      · exact Order.lt_succ_iff.1 (hTk.2 α hα)
      · have : Lev T α = ∅ := by
          refine Set.eq_empty_of_forall_notMem fun t ht' => hα ?_
          rw [← hTk.1, ← show ht t = α from ht']
          exact ht_lt_height t
        rw [this]
        simp
    obtain ⟨b, hb⟩ := h T hTk.1 hlev
    exact hno ⟨b, (isCofinalBranch_iff hTk.1).2 hb⟩

end JardenShami
