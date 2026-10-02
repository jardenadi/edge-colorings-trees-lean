import MyResearchesLLMLean.JardenShami.Section6

/-!
# Jarden–Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874), Section 7

Section 7 ("Ramsey Theorems for locally-additive colorings"): `κ → (κ)_{*-la_μ}` for
`μ⁺ < κ = cf(κ)` (after [Sh42, Theorem 1.1]), its failure for `μ⁺ = κ`, and `κ → (κ)_{la_μ}` for
regular `κ > μ⁺`.

Phase 1: all statements are proved, without changing any statement. Claim 7.8 is proved along a
route different from the paper's Cases A/B (no Fodor's lemma, no stationary sets): the level sizes
of a well-pruned subtree are eventually constant, and the diagonal argument of Claim 7.9
(`le_mk_lev_of_splitting`) gives a non-splitting node. Theorem 7.7 uses direction (1) ⇒ (2) of
Lemma 5.3 in the form `laArrowKappa_of_forall_branch` (Section 5, AUX), valid also for `κ = ℵ₀`.

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
which is a `κ`-tree") is the auxiliary lemma `exists_wellPruned_subtree` (AUX, proved);
Claim 7.8 and Theorem 7.7 take no extra hypothesis.
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

/-! ### Auxiliary lemmas for Subsection 7.1 (AUX: not in paper) -/

/-- AUX: not in paper. A pair read in the reverse order. -/
theorem Coloring.color_dual {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D)
    (a b : Aᵒᵈ) (h : a < b) :
    Coloring.color (A := Aᵒᵈ) C a b h =
      C.color (OrderDual.ofDual b) (OrderDual.ofDual a) h :=
  congrArg C (Subtype.ext Sym2.eq_swap)

/-- AUX: not in paper. *-local additivity spelled out in the original order: for
`x < y < z < w`, `C(y,z) = C(x,z)` implies `C(y,w) = C(x,w)`. -/
theorem isStarLocallyAdditive_iff {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) :
    IsStarLocallyAdditive C ↔
      ∀ (x y z w : A) (hxy : x < y) (hyz : y < z) (hzw : z < w),
        C.color y z hyz = C.color x z (hxy.trans hyz) →
          C.color y w (hyz.trans hzw) = C.color x w ((hxy.trans hyz).trans hzw) := by
  constructor
  · intro hC x y z w hxy hyz hzw h
    have := hC (OrderDual.toDual w) (OrderDual.toDual z) (OrderDual.toDual y)
      (OrderDual.toDual x) hzw hyz hxy
    have e := this ((Coloring.color_dual C (OrderDual.toDual z) (OrderDual.toDual y) hyz).trans
      (h.trans (Coloring.color_dual C (OrderDual.toDual z) (OrderDual.toDual x)
        (hxy.trans hyz)).symm))
    exact (Coloring.color_dual C (OrderDual.toDual w) (OrderDual.toDual y)
      (hyz.trans hzw)).symm.trans (e.trans (Coloring.color_dual C (OrderDual.toDual w)
        (OrderDual.toDual x) ((hxy.trans hyz).trans hzw)))
  · intro hC a b c d hab hbc hcd h
    simp only [Coloring.color_dual] at h ⊢
    exact hC (OrderDual.ofDual d) (OrderDual.ofDual c) (OrderDual.ofDual b) (OrderDual.ofDual a)
      hcd hbc hab h

/-- AUX: not in paper. For infinite `κ`, `κ` has no largest element. -/
theorem Kappa.exists_gt {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ) (x : Kappa κ) : ∃ y, x < y := by
  obtain ⟨y, -, h⟩ := Kappa.exists_gt_of_card_eq hκ
    (show #(Set.univ : Set (Kappa κ)) = κ by rw [Cardinal.mk_univ, Kappa.mk_eq]) x
  exact ⟨y, h⟩

/-- **Remark 7.2** (Section 7, `\label{remark 7.2}`). Under the standing assumption of Subsection
7.1: if `β ≠ γ`, `α₁` witnesses `β ∼ γ` and `α₁ < α₂`, then `α₂` witnesses `β ∼ γ` as well.
Hence `∼` is an equivalence relation. -/
theorem sim_witness_mono_and_equivalence (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C) :
    (∀ (β γ α₁ α₂ : Kappa κ) (hβ : β < α₁) (hγ : γ < α₁) (h₁₂ : α₁ < α₂), β ≠ γ →
        C.color β α₁ hβ = C.color γ α₁ hγ →
          C.color β α₂ (hβ.trans h₁₂) = C.color γ α₂ (hγ.trans h₁₂)) ∧
      Equivalence (Sim C) := by
  have hS := (isStarLocallyAdditive_iff C).1 hC
  have mono : ∀ (β γ α₁ α₂ : Kappa κ) (hβ : β < α₁) (hγ : γ < α₁) (h₁₂ : α₁ < α₂), β ≠ γ →
      C.color β α₁ hβ = C.color γ α₁ hγ →
        C.color β α₂ (hβ.trans h₁₂) = C.color γ α₂ (hγ.trans h₁₂) := by
    intro β γ α₁ α₂ hβ hγ h₁₂ hne h
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (hS β γ α₁ α₂ hlt hγ h₁₂ h.symm).symm
    · exact hS γ β α₁ α₂ hlt hβ h₁₂ h
  refine ⟨mono, ⟨fun β => ?_, fun {β γ} ⟨α, hβ, hγ, h⟩ => ⟨α, hγ, hβ, h.symm⟩, ?_⟩⟩
  · obtain ⟨α, hα⟩ := Kappa.exists_gt hκ.aleph0_le β
    exact ⟨α, hα, hα, rfl⟩
  · rintro β γ δ ⟨α, hβ, hγ, h⟩ ⟨α', hγ', hδ, h'⟩
    obtain ⟨α'', hα''⟩ := Kappa.exists_gt hκ.aleph0_le (max α α')
    have h1 : α < α'' := (le_max_left _ _).trans_lt hα''
    have h2 : α' < α'' := (le_max_right _ _).trans_lt hα''
    -- `α''` witnesses both `β ∼ γ` and `γ ∼ δ`
    have e1 : C.color β α'' (hβ.trans h1) = C.color γ α'' (hγ.trans h1) := by
      by_cases hne : β = γ
      · subst hne; rfl
      · exact mono β γ α α'' hβ hγ h1 hne h
    have e2 : C.color γ α'' (hγ'.trans h2) = C.color δ α'' (hδ.trans h2) := by
      by_cases hne : γ = δ
      · subst hne; rfl
      · exact mono γ δ α' α'' hγ' hδ h2 hne h'
    exact ⟨α'', hβ.trans h1, hδ.trans h2, e1.trans e2⟩

/-- **Lemma 7.3** (Section 7, `\label{lemma number of equivalence classes}`). Under the standing
assumption of Subsection 7.1: if `μ⁺ < κ` then the number of `∼`-equivalence classes is at most
`μ`. The classes are counted as the sets `{γ : β ∼ γ}`, `β < κ`. -/
theorem card_simClasses_le (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C)
    (h : Order.succ μ < κ) :
    #(Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ}) ≤ μ := by
  classical
  obtain ⟨-, heqv⟩ := sim_witness_mono_and_equivalence κ μ hκ hμ C hC
  set R := Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ} with hR
  by_contra hc
  obtain ⟨P, hPR, hPc⟩ := Cardinal.le_mk_iff_exists_subset.1 (Order.succ_le_of_lt (lt_of_not_ge hc))
  -- representatives
  have hrep : ∀ p : P, ∃ β : Kappa κ, {γ : Kappa κ | Sim C β γ} = p := fun p => hPR p.2
  choose r hr using hrep
  have hrinj : Function.Injective r := fun p p' h => Subtype.ext ((hr p).symm.trans (h ▸ hr p'))
  have hrc : #(Set.range r) < κ := by
    rw [Cardinal.mk_range_eq _ hrinj, hPc]
    exact h
  obtain ⟨αs, hαs⟩ := Kappa.exists_gt_of_card_lt hκ hrc
  -- the colors `C(r p, α*)` are pairwise distinct
  let φ : P → Kappa μ := fun p => C.color (r p) αs (hαs _ ⟨p, rfl⟩)
  have hφ : Function.Injective φ := by
    intro p p' e
    have hsim : Sim C (r p) (r p') := ⟨αs, _, _, e⟩
    refine Subtype.ext ?_
    rw [← hr p, ← hr p']
    ext γ
    exact ⟨fun h => heqv.trans (heqv.symm hsim) h, fun h => heqv.trans hsim h⟩
  have := Cardinal.mk_le_of_injective hφ
  rw [hPc, Kappa.mk_eq] at this
  exact (Order.lt_succ_of_not_isMax (not_isMax μ)).not_ge this

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
  classical
  intro C hC
  have hμ : μ < κ := (Order.lt_succ_of_not_isMax (not_isMax μ)).trans h
  have hκ0 := hκ.aleph0_le
  obtain ⟨mono, heqv⟩ := sim_witness_mono_and_equivalence κ μ hκ hμ C hC
  have hRle := card_simClasses_le κ μ hκ hμ C hC h
  -- some class `A` has size `κ`
  set R := Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ}
  let cl : Kappa κ → R := fun β => ⟨{γ | Sim C β γ}, β, rfl⟩
  obtain ⟨r, hr⟩ := Cardinal.infinite_pigeonhole_card cl κ (by rw [Kappa.mk_eq]) hκ0
    (by rw [hκ.cof_ord]; exact hRle.trans_lt hμ)
  set A : Set (Kappa κ) := cl ⁻¹' {r}
  have hAκ : #A = κ := le_antisymm ((Cardinal.mk_set_le A).trans (Kappa.mk_eq κ).le) hr
  have hAsim : ∀ y ∈ A, ∀ y' ∈ A, Sim C y y' := by
    intro y hy y' hy'
    have e : cl y = cl y' := hy.trans hy'.symm
    have e' : {γ | Sim C y γ} = {γ | Sim C y' γ} := congrArg Subtype.val e
    have : y' ∈ {γ | Sim C y' γ} := heqv.refl y'
    rw [← e'] at this
    exact this
  -- witnesses
  have hε : ∀ y y' : Kappa κ, ∃ e : Kappa κ, (y ∈ A → y' ∈ A → y < e ∧ y' < e) ∧
      ∀ (h1 : y < e) (h2 : y' < e), y ∈ A → y' ∈ A → C.color y e h1 = C.color y' e h2 := by
    intro y y'
    by_cases hy : y ∈ A ∧ y' ∈ A
    · obtain ⟨e, h1, h2, he⟩ := hAsim y hy.1 y' hy.2
      exact ⟨e, fun _ _ => ⟨h1, h2⟩, fun _ _ _ _ => he⟩
    · exact ⟨y, fun a b => absurd ⟨a, b⟩ hy, fun _ _ a b => absurd ⟨a, b⟩ hy⟩
  choose ε hεlt hεc using hε
  -- the greedy set `Y`
  obtain ⟨P, hP⟩ : ∃ P : Kappa κ → Prop, ∀ γ, P γ ↔ γ ∈ A ∧
      ∀ y y' (hyy' : y < y') (hy'γ : y' < γ), P y → P y' →
        C.color y γ (hyy'.trans hy'γ) = C.color y' γ hy'γ :=
    ⟨wellFounded_lt.fix fun γ ih => γ ∈ A ∧
      ∀ y y' (hyy' : y < y') (hy'γ : y' < γ), ih y (hyy'.trans hy'γ) → ih y' hy'γ →
        C.color y γ (hyy'.trans hy'γ) = C.color y' γ hy'γ,
      fun γ => by rw [WellFounded.fix_eq]⟩
  set Y : Set (Kappa κ) := {γ | P γ}
  have hYA : Y ⊆ A := fun γ hγ => ((hP γ).1 hγ).1
  have hYunb : ∀ x, ∃ y ∈ Y, x < y := by
    intro x
    by_contra hc
    push Not at hc
    have hYs : #Y < κ := (Cardinal.mk_le_mk_of_subset fun y hy => hc y hy).trans_lt
      (Kappa.mk_Iic_lt hκ0 x)
    let E : Set (Kappa κ) := Set.range fun q : Y × Y => ε q.1 q.2
    have hEs : #E < κ := by
      refine Cardinal.mk_range_le.trans_lt ?_
      rw [Cardinal.mk_prod, Cardinal.lift_id]
      exact Cardinal.mul_lt_of_lt hκ0 hYs hYs
    obtain ⟨z, hz⟩ := Kappa.exists_gt_of_card_lt hκ hEs
    obtain ⟨γ, hγA, hγ⟩ := Kappa.exists_gt_of_card_eq hκ0 hAκ (max x z)
    have hPγ : P γ := by
      refine (hP γ).2 ⟨hγA, fun y y' hyy' hy'γ hy hy' => ?_⟩
      obtain ⟨h1, h2⟩ := hεlt y y' (hYA hy) (hYA hy')
      have hεγ : ε y y' < γ :=
        (hz _ ⟨(⟨y, hy⟩, ⟨y', hy'⟩), rfl⟩).trans ((le_max_right _ _).trans_lt hγ)
      exact mono y y' (ε y y') γ h1 h2 hεγ hyy'.ne (hεc y y' h1 h2 (hYA hy) (hYA hy'))
    exact (hc γ hPγ).not_gt ((le_max_left _ _).trans_lt hγ)
  have : Nonempty (Kappa κ) :=
    ⟨Kappa.mk 0 (Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hκ0))⟩
  obtain ⟨y₁, hy₁, -⟩ := hYunb (Classical.arbitrary _)
  have hYne : Y.Nonempty := ⟨y₁, hy₁⟩
  set y₀ := WellFounded.min wellFounded_lt Y hYne
  have hy₀ : y₀ ∈ Y := WellFounded.min_mem _ _ _
  -- the elements of `Y` above `y₀`, and pigeonhole on `C(y₀, ·)`
  set s : Set (Kappa κ) := {y | y ∈ Y ∧ y₀ < y}
  have hsκ : #s = κ := Kappa.card_eq_of_forall_exists_gt hκ fun x => by
    obtain ⟨y, hy, hxy⟩ := hYunb (max x y₀)
    exact ⟨y, ⟨hy, (le_max_right _ _).trans_lt hxy⟩, (le_max_left _ _).trans_lt hxy⟩
  obtain ⟨t, B, hBs, hBκ, hBt⟩ := Cardinal.infinite_pigeonhole_set (s := s)
    (fun y : s => C.color y₀ y y.2.2) κ (by rw [hsκ]) hκ0
    (by rw [Kappa.mk_eq, hκ.cof_ord]; exact hμ)
  refine ⟨B, le_antisymm ((Cardinal.mk_set_le B).trans (Kappa.mk_eq κ).le) hBκ, ?_⟩
  have key : ∀ p : Pairs (Kappa κ), (∀ x ∈ p.1, x ∈ B) → C p = t := by
    intro p hp
    obtain ⟨x, y, hxy, rfl⟩ := p.exists_eq_mk
    have hx := hp x (Sym2.mem_mk_left x y)
    have hy := hp y (Sym2.mem_mk_right x y)
    have hPy := ((hP y).1 (hBs hy).1).2 y₀ x (hBs hx).2 hxy hy₀ (hBs hx).1
    change C.color x y hxy = t
    rw [← hPy]
    exact hBt hy
  exact fun p q hp hq => (key p hp).trans (key q hq).symm

/-- **Proposition 7.5** (Section 7, `\label{proposition mu^+<kappa can's be omitted}`).
`κ → (κ)_{*-la_μ}` does not hold if `μ⁺ = κ`. The standing assumption `κ = cf(κ)` of Subsection
7.1 is kept as `κ.IsRegular` (with Mathlib's definition this makes `κ`, hence `μ`, infinite; see
FIDELITY.md: for `μ ≤ 1` the statement without it is false). -/
theorem not_starLaArrowKappa_of_succ_eq (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ = κ) : ¬ StarLaArrowKappa κ μ := by
  classical
  have hκ0 := hκ.aleph0_le
  -- `μ` is infinite
  have hμ : ℵ₀ ≤ μ := by
    by_contra hc
    obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.1 (lt_of_not_ge hc)
    rw [← h, Cardinal.succ_natCast, ← Nat.cast_succ] at hκ0
    exact Cardinal.natCast_lt_aleph0.not_ge hκ0
  have : Nonempty (Kappa μ) := by
    rw [← Cardinal.mk_ne_zero_iff, Kappa.mk_eq]
    exact (Cardinal.aleph0_pos.trans_le hμ).ne'
  -- for each `α`, a map `g α : κ → μ`, injective on `{β : β < α}`
  have hg : ∀ α : Kappa κ, ∃ g : Kappa κ → Kappa μ, Set.InjOn g (Set.Iio α) := by
    intro α
    have hlt : #(Set.Iio α) < κ := by
      have := Cardinal.mk_Iio_lt α (by rw [Kappa.mk_eq, Ordinal.type_toType])
      rwa [Kappa.mk_eq] at this
    replace hlt : #(Set.Iio α) ≤ μ := Order.lt_succ_iff.1 (hlt.trans_eq h.symm)
    obtain ⟨e⟩ : Nonempty (Set.Iio α ↪ Kappa μ) := by
      rw [← Cardinal.le_def, Kappa.mk_eq]
      exact hlt
    refine ⟨fun β => if hβ : β < α then e ⟨β, hβ⟩ else Classical.arbitrary _, ?_⟩
    intro β hβ β' hβ' he
    simp only [dite_eq_left_of_eq_true (eq_true (show β < α from hβ)),
      dite_eq_left_of_eq_true (eq_true (show β' < α from hβ'))] at he
    exact congrArg Subtype.val (e.injective he)
  choose g hg using hg
  let C : Coloring (Kappa κ) (Kappa μ) := fun p => g p.1.sup p.1.inf
  have hCc : ∀ (a b : Kappa κ) (hab : a < b), C.color a b hab = g b a := by
    intro a b hab
    change g (Sym2.sup s(a, b)) (Sym2.inf s(a, b)) = g b a
    rw [Sym2.sup_mk, Sym2.inf_mk, sup_of_le_right hab.le, inf_of_le_left hab.le]
  -- `C(β,α) ≠ C(γ,α)` for `β < γ < α`
  have hne : ∀ (β γ α : Kappa κ) (hβγ : β < γ) (hγα : γ < α),
      C.color β α (hβγ.trans hγα) ≠ C.color γ α hγα := by
    intro β γ α hβγ hγα e
    rw [hCc, hCc] at e
    exact hβγ.ne (hg α (hβγ.trans hγα) hγα e)
  intro hArrow
  have hstar : IsStarLocallyAdditive C := by
    rw [isStarLocallyAdditive_iff]
    intro x y z w hxy hyz hzw e
    exact absurd e.symm (hne x y z hxy hyz)
  obtain ⟨H, hH, hHom⟩ := hArrow C hstar
  -- three elements `x < y < z` of `H`
  obtain ⟨x, hx⟩ : H.Nonempty := by
    rw [← Set.nonempty_coe_sort, ← Cardinal.mk_ne_zero_iff, hH]
    exact (Cardinal.aleph0_pos.trans_le hκ0).ne'
  obtain ⟨y, hy, hxy⟩ := Kappa.exists_gt_of_card_eq hκ0 hH x
  obtain ⟨z, hz, hyz⟩ := Kappa.exists_gt_of_card_eq hκ0 hH y
  refine hne x y z hxy hyz (hHom _ _ ?_ ?_)
  · intro u hu
    rcases Sym2.mem_iff.1 hu with rfl | rfl
    · exact hx
    · exact hz
  · intro u hu
    rcases Sym2.mem_iff.1 hu with rfl | rfl
    · exact hy
    · exact hz

/-! ## 7.2 locally-additive colorings -/

-- Question 7.6 (open problem: does `μ⁺ → (μ⁺)_{la_μ}` hold?) is not formalized.

section TreeAux

variable {T : Type w} [PartialOrder T] [IsTree T]

/-- AUX: not in paper. In a downward closed subset `S` of a tree, heights computed in `S` and
in `T` agree. -/
theorem ht_subtype_of_downward {S : Set T} (hS : ∀ s ∈ S, ∀ t < s, t ∈ S) (x : S) :
    ht x = ht (x : T) := by
  unfold ht
  refine RelIso.ordinalType_congr ?_
  exact
    { toFun := fun y => ⟨y.1.1, y.2⟩
      invFun := fun t => ⟨⟨t.1, hS x x.2 t.1 t.2⟩, t.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

/-- AUX: not in paper. Every node lies above a node of each smaller level. -/
theorem exists_le_ht_eq {t : T} {α : Ordinal.{w}} (h : α ≤ ht t) : ∃ s ≤ t, ht s = α := by
  rcases h.lt_or_eq with h | h
  · obtain ⟨s, hs, hsα⟩ := exists_lt_ht_eq h
    exact ⟨s, hs.le, hsα⟩
  · exact ⟨t, le_rfl, h.symm⟩

omit [IsTree T] in
/-- AUX: not in paper. For regular `κ`: if a set `U` of size `≥ κ` is covered by the cones
`{s : y ≤ s}` of fewer than `κ` nodes `y ∈ L`, then one of these cones has size `≥ κ`. -/
theorem exists_big_cone {κ : Cardinal.{w}} (hκ : κ.IsRegular) {U L : Set T} (hU : κ ≤ #U)
    (hL : #L < κ) (hcov : ∀ s ∈ U, ∃ y ∈ L, y ≤ s) : ∃ y ∈ L, κ ≤ #(Set.Ici y) := by
  by_contra hc
  push Not at hc
  have hsub : U ⊆ ⋃ y : L, Set.Ici (y : T) := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := hcov s hs
    exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, hys⟩
  have := (Cardinal.mk_le_mk_of_subset hsub).trans Cardinal.mk_iUnion_le_sum_mk
  exact (hU.trans this).not_gt (Cardinal.sum_lt_of_isRegular hκ hL fun y => hc y y.2)

/-- AUX: not in paper. In a `κ`-tree (`κ` regular), the nodes of height `< α` (`α < κ`) are
fewer than `κ`. -/
theorem mk_levLt_lt {κ : Cardinal.{w}} (hκ : κ.IsRegular) (hT : IsKappaTree κ T)
    {α : Ordinal.{w}} (hα : α < κ.ord) : #{s : T | ht s < α} < κ := by
  let ι := {β : Kappa κ // (β : Ordinal.{w}) < α}
  have hsub : {s : T | ht s < α} ⊆ ⋃ β : ι, Lev T (β.1 : Ordinal.{w}) := by
    intro s hs
    refine Set.mem_iUnion.2 ⟨⟨Kappa.mk (ht s) (hs.trans hα), by rw [Kappa.coe_mk]; exact hs⟩, ?_⟩
    exact (Kappa.coe_mk _ _).symm
  refine (Cardinal.mk_le_mk_of_subset hsub).trans_lt
    (Cardinal.mk_iUnion_le_sum_mk.trans_lt (Cardinal.sum_lt_of_isRegular hκ ?_ fun β =>
      hT.2 _ (Kappa.coe_lt_ord β.1)))
  refine (Cardinal.mk_le_of_injective (f := fun β : ι =>
    (⟨β.1, Kappa.coe_lt_coe.1 (by rw [Kappa.coe_mk]; exact β.2)⟩ :
      Set.Iio (Kappa.mk α hα))) ?_).trans_lt ?_
  · intro a b h
    exact Subtype.ext (congrArg (fun z : Set.Iio (Kappa.mk α hα) => (z : Kappa κ)) h)
  · have := Cardinal.mk_Iio_lt (Kappa.mk α hα) (by rw [Kappa.mk_eq, Ordinal.type_toType])
    rwa [Kappa.mk_eq] at this

/-- AUX: not in paper. In a `κ`-tree (`κ` regular): if `x` has `≥ κ` nodes above it and
`ht x < α < κ`, then some `y ∈ Lev_α(T)` with `x < y` has `≥ κ` nodes above it. -/
theorem exists_big_above {κ : Cardinal.{w}} (hκ : κ.IsRegular) (hT : IsKappaTree κ T) {x : T}
    (hx : κ ≤ #(Set.Ici x)) {α : Ordinal.{w}} (hxα : ht x < α) (hα : α < κ.ord) :
    ∃ y ∈ Lev T α, x < y ∧ κ ≤ #(Set.Ici y) := by
  have hκ0 := hκ.aleph0_le
  let U : Set T := {s | x ≤ s ∧ α ≤ ht s}
  have hU : κ ≤ #U := by
    by_contra hc
    have hsub : Set.Ici x ⊆ U ∪ {s : T | ht s < α} := by
      intro s hs
      by_cases h : α ≤ ht s
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr (lt_of_not_ge h)
    have := (Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_union_le _ _)
    exact hx.not_gt (this.trans_lt (Cardinal.add_lt_of_lt hκ0 (lt_of_not_ge hc)
      (mk_levLt_lt hκ hT hα)))
  obtain ⟨y, ⟨hyL, hxy⟩, hy⟩ := exists_big_cone hκ (L := {y | y ∈ Lev T α ∧ x < y}) hU
    ((Cardinal.mk_le_mk_of_subset fun y hy => hy.1).trans_lt (hT.2 α hα)) (by
      rintro s ⟨hxs, hαs⟩
      obtain ⟨y, hys, hyα⟩ := exists_le_ht_eq hαs
      exact ⟨y, ⟨hyα, lt_of_le_of_le_of_ht_lt hxs hys (by rw [hyα]; exact hxα)⟩, hys⟩)
  exact ⟨y, hyL, hxy, hy⟩

/-- AUX: not in paper. Strong form of `exists_wellPruned_subtree`: for regular `κ`, every
`κ`-tree has a downward closed subset (so heights are the same as in `T`) which is a well-pruned
`κ`-tree: the nodes above a fixed root `r` that have `κ` nodes above them. -/
theorem exists_wellPruned_subtree_downward (κ : Cardinal.{w}) (hκ : κ.IsRegular)
    (T : Type w) [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) :
    ∃ S : Set T, (∀ s ∈ S, ∀ t < s, t ∈ S) ∧ IsKappaTree κ S ∧ WellPruned S := by
  have hκ0 := hκ.aleph0_le
  have h0 : (0 : Ordinal.{w}) < κ.ord := Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hκ0)
  -- `T` has `≥ κ` nodes
  have hTκ : κ ≤ #(Set.univ : Set T) := by
    have hl : ∀ β : Kappa κ, (Lev T (β : Ordinal.{w})).Nonempty := fun β =>
      lev_nonempty (by rw [hT.1]; exact Kappa.coe_lt_ord β)
    choose c hc using hl
    rw [Cardinal.mk_univ, ← Kappa.mk_eq κ]
    refine Cardinal.mk_le_of_injective (f := c) fun a b h => ?_
    have := (hc a).symm.trans ((congrArg ht h).trans (hc b))
    exact Kappa.coe_inj.1 this
  -- a root with `κ` nodes above it
  obtain ⟨r, hr0, hr⟩ := exists_big_cone hκ hTκ (hT.2 0 h0) (by
    intro s _
    obtain ⟨y, hys, hy⟩ := exists_le_ht_eq (zero_le : (0 : Ordinal.{w}) ≤ ht s)
    exact ⟨y, hy, hys⟩)
  have hr0' : ht r = 0 := hr0
  let S : Set T := {t | r ≤ t ∧ κ ≤ #(Set.Ici t)}
  have hdown : ∀ s ∈ S, ∀ t < s, t ∈ S := by
    rintro s ⟨hrs, hs⟩ t hts
    refine ⟨?_, hs.trans (Cardinal.mk_le_mk_of_subset fun u hu => hts.le.trans hu)⟩
    rcases le_total_of_le hrs hts.le with h | h
    · exact h
    · rcases h.lt_or_eq with h | h
      · exact absurd (ht_lt_ht h) (by rw [hr0']; exact not_lt_zero)
      · exact h ▸ le_rfl
  have hht : ∀ x : S, ht x = ht (x : T) := ht_subtype_of_downward hdown
  -- extension inside `S`
  have hext : ∀ x : S, ∀ α : Ordinal.{w}, ht (x : T) < α → α < κ.ord →
      ∃ y : S, ht (y : T) = α ∧ x < y := by
    intro x α hxα hα
    obtain ⟨y, hyL, hxy, hy⟩ := exists_big_above hκ hT x.2.2 hxα hα
    exact ⟨⟨y, x.2.1.trans hxy.le, hy⟩, hyL, hxy⟩
  have rS : r ∈ S := ⟨le_rfl, hr⟩
  have hheight : height S = κ.ord := by
    refine IsLeast.csInf_eq ⟨?_, fun α hα => ?_⟩
    · refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      have : ht x = κ.ord := hx
      rw [hht] at this
      exact (hT.1 ▸ ht_lt_height (x : T)).ne this
    · by_contra hc
      have hlt := lt_of_not_ge hc
      have hne : (Lev S α).Nonempty := by
        rcases eq_or_ne α 0 with rfl | hα0
        · exact ⟨⟨r, rS⟩, (hht _).trans hr0'⟩
        · obtain ⟨y, hy, -⟩ := hext ⟨r, rS⟩ α (by rw [hr0']; exact pos_iff_ne_zero.2 hα0) hlt
          exact ⟨y, (hht y).trans hy⟩
      obtain ⟨y, hy⟩ := hne
      have hα' : Lev S α = ∅ := hα
      rw [hα'] at hy
      exact hy
  refine ⟨S, hdown, ⟨hheight, fun α hα => ?_⟩, ⟨⟨⟨r, rS⟩, (hht _).trans hr0', ?_⟩, ?_⟩⟩
  · refine (Cardinal.mk_le_of_injective (f := fun x : Lev S α =>
      (⟨x.1.1, (hht x.1).symm.trans x.2⟩ : Lev T α)) ?_).trans_lt (hT.2 α hα)
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Lev T α => (z : T)) h))
  · intro y hy
    have hy' : ht (y : T) = 0 := (hht y).symm.trans hy
    exact Subtype.ext (eq_of_le_of_le_of_ht_eq y.2.1 le_rfl (hr0'.trans hy'.symm)).symm
  · intro x α hxα hα
    rw [hheight] at hα
    rw [hht] at hxα
    obtain ⟨y, hy, hxy⟩ := hext x α hxα hα
    exact ⟨y, (hht y).trans hy, hxy⟩

end TreeAux

/-- AUX: not in paper. In the proof of Claim 7.8, Case A, the paper calls this a well-known fact
("it a well-known fact that every `κ`-tree has a well-pruned subtree which is a `κ`-tree") and
does not prove it. Stated for regular `κ`, the only case used (Claim 7.8 assumes `κ` regular); for
singular `κ` it can fail. A subtree is a subset with the induced order. -/
theorem exists_wellPruned_subtree (κ : Cardinal.{w}) (hκ : κ.IsRegular)
    (T : Type w) [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) :
    ∃ S : Set T, IsKappaTree κ S ∧ WellPruned S := by
  obtain ⟨S, -, hS, hwp⟩ := exists_wellPruned_subtree_downward κ hκ T hT
  exact ⟨S, hS, hwp⟩

/-- AUX: not in paper. Two nodes below a common node: the lower one is below the other. -/
theorem le_of_le_of_le_of_ht_le {T : Type w} [PartialOrder T] [IsTree T] {u v z : T}
    (hu : u ≤ z) (hv : v ≤ z) (h : ht u ≤ ht v) : u ≤ v := by
  rcases le_total_of_le hu hv with h' | h'
  · exact h'
  · exact (eq_of_le_of_le_of_ht_eq h' le_rfl (le_antisymm (ht_le_ht_of_le h') h)) ▸ le_rfl

/-- AUX: not in paper. The diagonal construction in the proof of Claim 7.9, in a general form.
Let `α` be a level such that every node of smaller height has an extension in `Lev_α(T)`, and
such that fewer than `ρ` ordinals below `α` are bounded below `α`. If for every `q ∈ [α₀, α)` some
`a ∈ Lev_q(T)` has two distinct extensions `b, c` of the same height `< α`, then
`|Lev_α(T)| ≥ ρ`. (The paper builds `d_i ∈ Lev_α(T)`, `i < λ`, by induction.) -/
theorem le_mk_lev_of_splitting {T : Type w} [PartialOrder T] [IsTree T] {ρ : Cardinal.{w}}
    {α α₀ : Ordinal.{w}} (hext : ∀ x : T, ht x < α → ∃ y ∈ Lev T α, x < y)
    (hbd : ∀ (ι : Type w) (f : ι → Ordinal.{w}), #ι < ρ → (∀ i, f i < α) →
      ∃ q < α, ∀ i, f i ≤ q)
    (hα₀ : α₀ < α)
    (hsplit : ∀ q : Ordinal.{w}, α₀ ≤ q → q < α → ∃ a b c : T, ht a = q ∧ q < ht b ∧
      ht b < α ∧ ht c = ht b ∧ a < b ∧ a < c ∧ b ≠ c) :
    ρ ≤ #(Lev T α) := by
  classical
  obtain ⟨t₀, -⟩ := hsplit α₀ le_rfl hα₀
  have : Nonempty T := ⟨t₀⟩
  -- the splitting data `a_q, b_q, c_q` and the extensions `E x ∈ Lev_α(T)`
  have hs : ∀ q : Ordinal.{w}, ∃ a b c : T, α₀ ≤ q → q < α → ht a = q ∧ q < ht b ∧
      ht b < α ∧ ht c = ht b ∧ a < b ∧ a < c ∧ b ≠ c := by
    intro q
    by_cases h : α₀ ≤ q ∧ q < α
    · obtain ⟨a, b, c, hh⟩ := hsplit q h.1 h.2
      exact ⟨a, b, c, fun _ _ => hh⟩
    · exact ⟨t₀, t₀, t₀, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose sa sb sc hsabc using hs
  have he : ∀ x : T, ∃ y : T, ht x < α → y ∈ Lev T α ∧ x < y := by
    intro x
    by_cases h : ht x < α
    · obtain ⟨y, hy, hxy⟩ := hext x h
      exact ⟨y, fun _ => ⟨hy, hxy⟩⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose E hE using he
  -- the recursion: `x i ∈ {b_q, c_q}` for `q = max α₀ (sup_{j<i} ht (x j))`
  obtain ⟨x, hx⟩ : ∃ x : Kappa ρ → T, ∀ i, x i =
      if ∃ j, ∃ _ : j < i, sb (max α₀ (⨆ j : Set.Iio i, ht (x j))) ≤ E (x j)
      then sc (max α₀ (⨆ j : Set.Iio i, ht (x j)))
      else sb (max α₀ (⨆ j : Set.Iio i, ht (x j))) :=
    ⟨wellFounded_lt.fix fun i ih =>
      if ∃ j, ∃ hj : j < i, sb (max α₀ (⨆ j : Set.Iio i, ht (ih j j.2))) ≤ E (ih j hj)
      then sc (max α₀ (⨆ j : Set.Iio i, ht (ih j j.2)))
      else sb (max α₀ (⨆ j : Set.Iio i, ht (ih j j.2))),
      fun i => by rw [WellFounded.fix_eq]⟩
  set Q : Kappa ρ → Ordinal.{w} := fun i => max α₀ (⨆ j : Set.Iio i, ht (x j)) with hQdef
  have hQle : ∀ i, ∀ j < i, ht (x j) ≤ Q i := fun i j hj =>
    (Ordinal.le_iSup (fun j : Set.Iio i => ht (x j)) ⟨j, hj⟩).trans (le_max_right _ _)
  -- heights stay below `α`
  have hmain : ∀ i, Q i < α ∧ ht (x i) < α := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i IH =>
    have hQ : Q i < α := by
      obtain ⟨q, hq, hqb⟩ := hbd (Set.Iio i) (fun j => ht (x j))
        (by
          have := Cardinal.mk_Iio_lt i (by rw [Kappa.mk_eq, Ordinal.type_toType])
          rwa [Kappa.mk_eq] at this)
        (fun j => (IH j j.2).2)
      exact max_lt hα₀ ((Ordinal.iSup_le hqb).trans_lt hq)
    refine ⟨hQ, ?_⟩
    obtain ⟨-, -, hb, hc, -⟩ := hsabc (Q i) (le_max_left _ _) hQ
    rw [hx i]
    split_ifs
    · rw [hc]; exact hb
    · exact hb
  have hdata : ∀ i, ht (sa (Q i)) = Q i ∧ Q i < ht (sb (Q i)) ∧ ht (sb (Q i)) < α ∧
      ht (sc (Q i)) = ht (sb (Q i)) ∧ sa (Q i) < sb (Q i) ∧ sa (Q i) < sc (Q i) ∧
        sb (Q i) ≠ sc (Q i) := fun i => hsabc (Q i) (le_max_left _ _) (hmain i).1
  let d : Kappa ρ → T := fun i => E (x i)
  have hd : ∀ i, d i ∈ Lev T α ∧ x i < d i := fun i => hE (x i) (hmain i).2
  -- the key property: `x i` is below no earlier `d j`
  have key : ∀ i, ∀ j < i, ¬ x i ≤ d j := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i IH =>
    intro j hj hle
    obtain ⟨ha, -, -, hcb, hab, hac, hbc⟩ := hdata i
    by_cases hcase : ∃ j, ∃ _ : j < i, sb (Q i) ≤ E (x j)
    · have hxi : x i = sc (Q i) := by
        rw [hx i]
        split_ifs with h
        · rfl
        · exact absurd hcase h
      obtain ⟨j₀, hj₀, hb₀⟩ := hcase
      rw [hxi] at hle
      by_cases hjj : j = j₀
      · subst hjj
        exact hbc (eq_of_le_of_le_of_ht_eq hb₀ hle hcb.symm)
      · -- `d j` and `d j₀` both lie above `a_q`
        have h1 : sa (Q i) ≤ d j := (hac.le.trans hle)
        have h2 : sa (Q i) ≤ d j₀ := hab.le.trans hb₀
        rcases lt_or_gt_of_ne hjj with hlt | hlt
        · -- `j < j₀`: `x j₀ ≤ a_q ≤ d j`
          have : x j₀ ≤ sa (Q i) := le_of_le_of_le_of_ht_le (hd j₀).2.le h2
            (by rw [ha]; exact hQle i j₀ hj₀)
          exact IH j₀ hj₀ j hlt (this.trans h1)
        · have : x j ≤ sa (Q i) := le_of_le_of_le_of_ht_le (hd j).2.le h1
            (by rw [ha]; exact hQle i j hj)
          exact IH j hj j₀ hlt (this.trans h2)
    · have hxi : x i = sb (Q i) := by
        rw [hx i]
        split_ifs with h
        · exact absurd h hcase
        · rfl
      rw [hxi] at hle
      exact hcase ⟨j, hj, hle⟩
  have hdinj : Function.Injective fun i : Kappa ρ => (⟨d i, (hd i).1⟩ : Lev T α) := by
    intro i j h
    have h' : d i = d j := congrArg (fun z : Lev T α => (z : T)) h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key j i hlt (h' ▸ (hd j).2.le)
    · exact key i j hlt (h' ▸ (hd i).2.le)
  have := Cardinal.mk_le_of_injective hdinj
  rwa [Kappa.mk_eq] at this

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
  intro α hα hcof
  by_contra hc
  push Not at hc
  have hα0 : (0 : Ordinal.{w}) < α := by
    rw [pos_iff_ne_zero]
    rintro rfl
    rw [Ordinal.cof_zero] at hcof
    exact hlamreg.pos.ne' hcof.symm
  have hle := le_mk_lev_of_splitting (ρ := lam) (α₀ := 0)
    (fun x hx => hwp.2 x α hx (by rw [hT.1]; exact hα))
    (fun ι f hι hf => ⟨⨆ i, f i, Ordinal.iSup_lt_of_lt_cof (by rwa [hcof]) hf,
      fun i => Ordinal.le_iSup f i⟩)
    hα0
    (fun q _ hq => by
      obtain ⟨β, hqβ, hβα, a, ha, b, hb, c, hc', hab, hac, hbc⟩ := hc q hq
      exact ⟨a, b, c, ha, by rw [hb]; exact hqβ, by rw [hb]; exact hβα, hc'.trans hb.symm,
        hab, hac, hbc⟩)
  exact (hle.trans_lt (hlev α)).false

/-- AUX: not in paper. In a well-pruned tree, the sizes of the levels are non-decreasing (the
restriction map `Lev_β(T) → Lev_α(T)` is onto). -/
theorem mk_lev_mono {T : Type w} [PartialOrder T] [IsTree T] (hwp : WellPruned T)
    {α β : Ordinal.{w}} (hαβ : α ≤ β) (hβ : β < height T) : #(Lev T α) ≤ #(Lev T β) := by
  classical
  rcases hαβ.lt_or_eq with hlt | rfl
  · have hr : ∀ y : Lev T β, ∃ x : Lev T α, (x : T) ≤ y := by
      intro y
      obtain ⟨x, hxy, hx⟩ := exists_le_ht_eq (show α ≤ ht (y : T) by rw [y.2]; exact hlt.le)
      exact ⟨⟨x, hx⟩, hxy⟩
    choose r hr using hr
    refine Cardinal.mk_le_of_surjective (f := r) fun x => ?_
    obtain ⟨y, hy, hxy⟩ := hwp.2 x β (by rw [x.2]; exact hlt) hβ
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    exact eq_of_le_of_le_of_ht_eq (hr ⟨y, hy⟩) hxy.le ((r ⟨y, hy⟩).2.trans x.2.symm)
  · exact le_rfl

/-- AUX: not in paper. In a well-pruned `κ`-tree (`κ` regular) whose levels have size `< λ`,
`λ < κ`, the sizes of the levels are eventually constant. -/
theorem exists_mk_lev_const {κ lam : Cardinal.{w}} (hκ : κ.IsRegular) (hlam : lam < κ)
    {T : Type w} [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) (hwp : WellPruned T)
    (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∃ α₀ < κ.ord, ∀ β : Ordinal.{w}, α₀ ≤ β → β < κ.ord → #(Lev T β) = #(Lev T α₀) := by
  classical
  let f : Kappa κ → Cardinal.{w} := fun α => #(Lev T (α : Ordinal.{w}))
  have hmono : Monotone f := fun a b hab =>
    mk_lev_mono hwp (Kappa.coe_le_coe.2 hab) (by rw [hT.1]; exact Kappa.coe_lt_ord b)
  have hfκ : ∀ α, (f α).ord < κ.ord := fun α =>
    Cardinal.ord_lt_ord.2 ((hlev _).trans hlam)
  suffices h : ∃ α₀ : Kappa κ, ∀ β, α₀ ≤ β → f β = f α₀ by
    obtain ⟨α₀, hα₀⟩ := h
    refine ⟨α₀, Kappa.coe_lt_ord α₀, fun β hβ hβκ => ?_⟩
    have := hα₀ (Kappa.mk β hβκ) (by rw [← Kappa.coe_le_coe, Kappa.coe_mk]; exact hβ)
    simpa [f] using this
  by_contra h
  push Not at h
  choose nxt hnxt hne using h
  have hgt : ∀ α, f α < f (nxt α) := fun α => lt_of_le_of_ne (hmono (hnxt α)) (hne α).symm
  -- code each size by an ordinal `< λ`
  let code : Kappa κ → Kappa κ := fun α => Kappa.mk (f α).ord (hfκ α)
  have hcode : ∀ a b, code a = code b → f a = f b := fun a b h => by
    have := congrArg (fun z : Kappa κ => (z : Ordinal.{w})) h
    simp only [code, Kappa.coe_mk] at this
    exact Cardinal.ord_injective this
  have hlamκ : lam.ord < κ.ord := Cardinal.ord_lt_ord.2 hlam
  have hV : #(Set.range code) < κ := by
    have hsub : Set.range code ⊆ Set.Iio (Kappa.mk lam.ord hlamκ) := by
      rintro _ ⟨α, rfl⟩
      rw [Set.mem_Iio, ← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk]
      exact Cardinal.ord_lt_ord.2 (hlev _)
    refine (Cardinal.mk_le_mk_of_subset hsub).trans_lt ?_
    have := Cardinal.mk_Iio_lt (Kappa.mk lam.ord hlamκ)
      (by rw [Kappa.mk_eq, Ordinal.type_toType])
    rwa [Kappa.mk_eq] at this
  have : Nonempty (Kappa κ) :=
    ⟨Kappa.mk 0 (Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hκ.aleph0_le))⟩
  let rep : Kappa κ → Kappa κ := Function.invFun code
  obtain ⟨z, hz⟩ := Kappa.exists_gt_of_card_lt hκ
    (Cardinal.mk_image_le.trans_lt hV : #((nxt ∘ rep) '' Set.range code) < κ)
  have hrep : code (rep (code z)) = code z := Function.invFun_eq ⟨z, rfl⟩
  have h1 : nxt (rep (code z)) < z := hz _ ⟨code z, ⟨z, rfl⟩, rfl⟩
  have h2 := hgt (rep (code z))
  rw [hcode _ _ hrep] at h2
  exact (hmono h1.le).not_gt h2

/-- AUX: not in paper. For regular `ρ < κ` (`κ` regular) and any `σ` mapping `κ` to `κ`, there
is a level `α ∈ (α₀, κ)` closed under `σ` such that any fewer than `ρ` ordinals below `α` are
bounded below `α` (`α` is the supremum of a `ρ`-sequence closing off under `σ`). -/
theorem exists_closed_level {κ ρ : Cardinal.{w}} (hκ : κ.IsRegular) (hρ : ρ.IsRegular)
    (hρκ : ρ < κ) {α₀ : Ordinal.{w}} (hα₀ : α₀ < κ.ord) (σ : Ordinal.{w} → Ordinal.{w})
    (hσ : ∀ q < κ.ord, σ q < κ.ord) :
    ∃ α, α₀ < α ∧ α < κ.ord ∧ (∀ q < α, σ q < α) ∧
      ∀ (ι : Type w) (f : ι → Ordinal.{w}), #ι < ρ → (∀ i, f i < α) → ∃ q < α, ∀ i, f i ≤ q := by
  classical
  have hκ0 := hκ.aleph0_le
  have hlim : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ0
  have hcof : κ.ord.cof = κ := hκ.cof_ord
  -- `σ' x = max x (sup_{q ≤ x} σ q)`
  let σ' : Ordinal.{w} → Ordinal.{w} := fun x =>
    max x (⨆ q : {q : Kappa κ // (q : Ordinal.{w}) ≤ x}, σ q.1)
  have hσ'lt : ∀ x < κ.ord, σ' x < κ.ord := by
    intro x hx
    refine max_lt hx (Ordinal.iSup_lt_of_lt_cof ?_ fun q => hσ _ (Kappa.coe_lt_ord _))
    rw [hcof]
    refine (Cardinal.mk_le_of_injective (f := fun q : {q : Kappa κ // (q : Ordinal.{w}) ≤ x} =>
      (⟨q.1, by rw [Set.mem_Iic, ← Kappa.coe_le_coe, Kappa.coe_mk]; exact q.2⟩ :
        Set.Iic (Kappa.mk x hx))) ?_).trans_lt (Kappa.mk_Iic_lt hκ0 _)
    intro a b h
    exact Subtype.ext (congrArg (fun z : Set.Iic (Kappa.mk x hx) => (z : Kappa κ)) h)
  have hσ'ge : ∀ x q, q ≤ x → q < κ.ord → σ q ≤ σ' x := fun x q hqx hq =>
    (Ordinal.le_iSup (fun q : {q : Kappa κ // (q : Ordinal.{w}) ≤ x} => σ q.1)
      ⟨Kappa.mk q hq, by rw [Kappa.coe_mk]; exact hqx⟩ |>.trans_eq' (by rw [Kappa.coe_mk])).trans
      (le_max_right _ _)
  -- the recursion `g i = max (α₀ + 1) (sup_{j<i} σ' (g j) + 1)`
  obtain ⟨g, hg⟩ : ∃ g : Kappa ρ → Ordinal.{w}, ∀ i,
      g i = max (α₀ + 1) (⨆ j : Set.Iio i, (σ' (g j) + 1)) :=
    ⟨wellFounded_lt.fix fun i ih => max (α₀ + 1) (⨆ j : Set.Iio i, (σ' (ih j j.2) + 1)),
      fun i => by rw [WellFounded.fix_eq]⟩
  have hgstep : ∀ i, ∀ j < i, σ' (g j) + 1 ≤ g i := fun i j hj => by
    rw [hg i]
    exact (Ordinal.le_iSup (fun j : Set.Iio i => σ' (g j) + 1) ⟨j, hj⟩).trans (le_max_right _ _)
  have hgmono : ∀ i j, j < i → g j < g i := fun i j hj =>
    (Order.lt_add_one_iff.2 (le_max_left _ _)).trans_le (hgstep i j hj)
  have hglt : ∀ i, g i < κ.ord := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i IH =>
    rw [hg i]
    refine max_lt (hlim.add_one_lt hα₀) (Ordinal.iSup_lt_of_lt_cof ?_ fun j =>
      hlim.add_one_lt (hσ'lt _ (IH j j.2)))
    rw [hcof]
    have := Cardinal.mk_Iio_lt i (by rw [Kappa.mk_eq, Ordinal.type_toType])
    rw [Kappa.mk_eq] at this
    exact this.trans hρκ
  have hρ0 := hρ.aleph0_le
  have : Nonempty (Kappa ρ) := ⟨Kappa.mk 0 (Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hρ0))⟩
  refine ⟨⨆ i, g i, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i⟩ := this
    have h1 : α₀ + 1 ≤ g i := by rw [hg i]; exact le_max_left _ _
    exact (Order.lt_add_one_iff.2 le_rfl).trans_le (h1.trans (Ordinal.le_iSup g i))
  · exact Ordinal.iSup_lt_of_lt_cof (by rw [hcof, Kappa.mk_eq]; exact hρκ) hglt
  · intro q hq
    obtain ⟨i, hi⟩ := Ordinal.lt_iSup_iff.1 hq
    obtain ⟨i', hi'⟩ := Kappa.exists_gt hρ0 i
    have hqκ : q < κ.ord := hi.trans (hglt i)
    calc σ q ≤ σ' (g i) := hσ'ge _ _ hi.le hqκ
      _ < σ' (g i) + 1 := Order.lt_add_one_iff.2 le_rfl
      _ ≤ g i' := hgstep i' i hi'
      _ ≤ ⨆ i, g i := Ordinal.le_iSup g i'
  · intro ι f hι hf
    have hex : ∀ k, ∃ i, f k < g i := fun k => Ordinal.lt_iSup_iff.1 (hf k)
    choose ik hik using hex
    obtain ⟨is, his⟩ := Kappa.exists_gt_of_card_lt hρ
      (Cardinal.mk_range_le.trans_lt hι : #(Set.range ik) < ρ)
    obtain ⟨is', his'⟩ := Kappa.exists_gt hρ0 is
    exact ⟨g is, (hgmono is' is his').trans_le (Ordinal.le_iSup g is'),
      fun k => ((hik k).trans (hgmono is (ik k) (his _ ⟨k, rfl⟩))).le⟩

/-- AUX: not in paper. In a well-pruned `κ`-tree (`κ` regular) whose levels have size `< λ`,
`λ < κ`, some node `a` does not split: any two nodes above `a` of the same height are equal.
(Replaces Cases A and B of the paper's proof of Claim 7.8: the level sizes are eventually a constant
`n < λ`; for finite `n` the restriction maps are bijective, and for infinite `n` the diagonal
argument of Claim 7.9 (`le_mk_lev_of_splitting`) at a level closed under splitting and of
cofinality `≥ n⁺` (`exists_closed_level`) gives a level of size `≥ n⁺`.) -/
theorem exists_nonsplitting {κ lam : Cardinal.{w}} (hκ : κ.IsRegular) (hlam : lam < κ)
    {T : Type w} [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) (hwp : WellPruned T)
    (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∃ a : T, ∀ b c : T, a < b → a < c → ht b = ht c → b = c := by
  classical
  obtain ⟨α₀, hα₀, hconst⟩ := exists_mk_lev_const hκ hlam hT hwp hlev
  by_contra hns
  push Not at hns
  have hα₀h : α₀ < height T := by rw [hT.1]; exact hα₀
  obtain ⟨a₀, ha₀⟩ := lev_nonempty hα₀h
  rcases lt_or_ge (#(Lev T α₀)) ℵ₀ with hfin | hinf
  · -- finite constant size: the restriction map is a bijection, so `a₀` cannot split
    obtain ⟨b, c, hab, hac, hbc, hne⟩ := hns a₀
    set β := ht b with hβdef
    have hβ : β < κ.ord := hT.1 ▸ ht_lt_height b
    have hα₀β : α₀ < β := by rw [← show ht a₀ = α₀ from ha₀]; exact ht_lt_ht hab
    have hr : ∀ y : Lev T β, ∃ x : Lev T α₀, (x : T) ≤ y := by
      intro y
      obtain ⟨x, hxy, hx⟩ := exists_le_ht_eq (show α₀ ≤ ht (y : T) by rw [y.2]; exact hα₀β.le)
      exact ⟨⟨x, hx⟩, hxy⟩
    choose r hr using hr
    have hsurj : Function.Surjective r := by
      intro x
      obtain ⟨y, hy, hxy⟩ := hwp.2 x β (by rw [x.2]; exact hα₀β) (by rw [hT.1]; exact hβ)
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      exact eq_of_le_of_le_of_ht_eq (hr ⟨y, hy⟩) hxy.le ((r ⟨y, hy⟩).2.trans x.2.symm)
    have hfinβ : Finite (Lev T β) := Cardinal.lt_aleph0_iff_finite.1
      ((hconst β hα₀β.le hβ).trans_lt hfin)
    obtain ⟨e⟩ : Nonempty (Lev T β ≃ Lev T α₀) := Cardinal.eq.1 (hconst β hα₀β.le hβ)
    have hinj := (Finite.injective_iff_surjective_of_equiv e).2 hsurj
    have hrb : r ⟨b, rfl⟩ = ⟨a₀, ha₀⟩ := Subtype.ext (eq_of_le_of_le_of_ht_eq (hr ⟨b, rfl⟩)
      hab.le ((r ⟨b, rfl⟩).2.trans ha₀.symm))
    have hrc : r ⟨c, hbc.symm⟩ = ⟨a₀, ha₀⟩ := Subtype.ext (eq_of_le_of_le_of_ht_eq
      (hr ⟨c, hbc.symm⟩) hac.le ((r ⟨c, hbc.symm⟩).2.trans ha₀.symm))
    exact hne (congrArg Subtype.val (hinj (hrb.trans hrc.symm)))
  · -- infinite constant size `n`: a level of size `≥ n⁺` contradicts `|Lev| = n`
    set n := #(Lev T α₀)
    have hρ : (Order.succ n).IsRegular := Cardinal.isRegular_succ hinf
    have hρκ : Order.succ n < κ := (Order.succ_le_of_lt (hlev α₀)).trans_lt hlam
    -- for each level `q`, the height `σ q` of a splitting above a node of `Lev_q`
    have hsp : ∀ q : Ordinal.{w}, ∃ s : Ordinal.{w}, q < κ.ord → s < κ.ord ∧
        ∃ a b c : T, ht a = q ∧ q < ht b ∧ ht b = s ∧ ht c = ht b ∧ a < b ∧ a < c ∧ b ≠ c := by
      intro q
      by_cases hq : q < κ.ord
      · obtain ⟨a, ha⟩ := lev_nonempty (show q < height T by rw [hT.1]; exact hq)
        obtain ⟨b, c, hab, hac, hbc, hne⟩ := hns a
        refine ⟨ht b, fun _ => ⟨hT.1 ▸ ht_lt_height b, a, b, c, ha, ?_, rfl, hbc.symm, hab,
          hac, hne⟩⟩
        rw [← show ht a = q from ha]
        exact ht_lt_ht hab
      · exact ⟨0, fun h => absurd h hq⟩
    choose σ hσ using hsp
    obtain ⟨α, hα₀α, hακ, hclosed, hbd⟩ := exists_closed_level hκ hρ hρκ hα₀ σ
      (fun q hq => (hσ q hq).1)
    have hle := le_mk_lev_of_splitting (T := T) (ρ := Order.succ n) (α := α) (α₀ := α₀)
      (fun x hx => hwp.2 x α hx (by rw [hT.1]; exact hακ)) hbd hα₀α
      (fun q _ hq => by
        obtain ⟨-, a, b, c, ha, hqb, hb, hcb, hab, hac, hne⟩ := hσ q (hq.trans hακ)
        exact ⟨a, b, c, ha, hqb, hb ▸ hclosed q hq, hcb, hab, hac, hne⟩)
    rw [hconst α hα₀α.le hακ] at hle
    exact (Order.lt_succ_of_not_isMax (not_isMax n)).not_ge hle

/-- AUX: not in paper. In a `κ`-tree, a chain of size `≥ κ` yields a cofinal branch. -/
theorem exists_isCofinalBranch_of_isChain {κ : Cardinal.{w}} {T : Type w} [PartialOrder T]
    [IsTree T] (hT : IsKappaTree κ T) {c : Set T} (hc : IsChain (· ≤ ·) c) (hcκ : κ ≤ #c) :
    ∃ b : Set T, IsCofinalBranch b := by
  obtain ⟨M, hM, hcM⟩ := hc.exists_maxChain
  refine ⟨M, (isCofinalBranch_iff hT.1).2 ⟨hM, le_antisymm (mk_le_of_isChain hT.1 hM.1) ?_⟩⟩
  exact hcκ.trans (Cardinal.mk_le_mk_of_subset hcM)

/-- **Claim 7.8** (Section 7, `\label{the exercise of kunen}`; recalled from
[Large, Proposition 7.9] and proved in the paper "for completeness"). Let `κ` and `λ` be cardinals
such that `κ` is regular and `λ < κ`. If `T` is a `κ`-tree whose levels have size `< λ`, then
`T` is not `κ`-Aronszajn. -/
theorem not_isAronszajn_of_card_lev_lt (κ lam : Cardinal.{w})
    (hκ : κ.IsRegular) (hlam : lam < κ) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ¬ IsAronszajn κ T := by
  rintro ⟨-, hno⟩
  obtain ⟨S, hdown, hS, hwp⟩ := exists_wellPruned_subtree_downward κ hκ T hT
  have hht : ∀ x : S, ht x = ht (x : T) := ht_subtype_of_downward hdown
  have hlevS : ∀ α : Ordinal.{w}, #(Lev S α) < lam := fun α =>
    (Cardinal.mk_le_of_injective (f := fun x : Lev S α => (⟨x.1.1, (hht x.1).symm.trans x.2⟩ :
      Lev T α)) (fun a b h => Subtype.ext (Subtype.ext
        (congrArg (fun z : Lev T α => (z : T)) h)))).trans_lt (hlev α)
  obtain ⟨a, ha⟩ := exists_nonsplitting hκ hlam hS hwp hlevS
  -- the nodes of `S` above `a` form a chain
  have ha' : ∀ b c : S, a ≤ b → a ≤ c → ht b = ht c → b = c := by
    intro b c hb hc hbc
    rcases hb.lt_or_eq with hb | rfl
    · rcases hc.lt_or_eq with hc | rfl
      · exact ha b c hb hc hbc
      · exact (eq_of_le_of_le_of_ht_eq hb.le le_rfl hbc.symm).symm
    · exact eq_of_le_of_le_of_ht_eq hc le_rfl hbc
  let C : Set T := (fun x : S => (x : T)) '' {x : S | a ≤ x}
  have hchain : IsChain (· ≤ ·) C := by
    have key : ∀ x y : S, a ≤ x → a ≤ y → ht x ≤ ht y → x ≤ y := by
      intro x y hx hy hxy
      obtain ⟨y', hy'y, hy'⟩ := exists_le_ht_eq hxy
      have hay' : a ≤ y' :=
        le_of_le_of_le_of_ht_le hy hy'y (by rw [hy']; exact ht_le_ht_of_le hx)
      exact (ha' x y' hx hay' hy'.symm) ▸ hy'y
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ -
    rcases le_total (ht x) (ht y) with h | h
    · exact Or.inl (key x y hx hy h)
    · exact Or.inr (key y x hy hx h)
  -- it has size `κ`: its heights are unbounded in `κ`
  have hCκ : κ ≤ #C := by
    have hunb : ∀ β : Kappa κ, ∃ y ∈ Set.range (fun x : C => Kappa.mk (ht (x : T))
        (hT.1 ▸ ht_lt_height (x : T))), β < y := by
      intro β
      have hγ : max (ht a + 1) ((β : Ordinal.{w}) + 1) < κ.ord := by
        have hlim := Cardinal.isSuccLimit_ord hκ.aleph0_le
        refine max_lt (hlim.add_one_lt ?_) (hlim.add_one_lt (Kappa.coe_lt_ord β))
        rw [← hS.1]
        exact ht_lt_height a
      obtain ⟨y, hy, hay⟩ := hwp.2 a _ (lt_of_lt_of_le (Order.lt_add_one_iff.2 le_rfl)
        (le_max_left _ _)) (by rw [hS.1]; exact hγ)
      refine ⟨_, ⟨⟨y, y, hay.le, rfl⟩, rfl⟩, ?_⟩
      rw [← Kappa.coe_lt_coe, Kappa.coe_mk, ← hht, show ht y = _ from hy]
      exact lt_of_lt_of_le (Order.lt_add_one_iff.2 le_rfl) (le_max_right _ _)
    have := Kappa.card_eq_of_forall_exists_gt hκ hunb
    rw [← this]
    exact Cardinal.mk_range_le
  exact hno (exists_isCofinalBranch_of_isChain hT hchain hCκ)

/-- **Theorem 7.7** (Section 7, `\label{the only theorem}`). Let `κ` be a regular cardinal and
`μ` a cardinal with `μ⁺ < κ`. Then `κ → (κ)_{la_μ}` (in the sense of Section 5,
`LaArrowKappa`). -/
theorem laArrowKappa_of_succ_lt (κ μ : Cardinal.{w})
    (hκ : κ.IsRegular) (h : Order.succ μ < κ) : LaArrowKappa κ μ := by
  have hlt : μ < Order.succ μ := Order.lt_succ_of_not_isMax (not_isMax μ)
  have hμ : μ < κ := hlt.trans h
  refine laArrowKappa_of_forall_branch κ μ hκ hμ fun T _ _ hT hlev => ?_
  have hTk : IsKappaTree κ T := ⟨hT, fun α _ => (hlev α).trans_lt hμ⟩
  have hna := not_isAronszajn_of_card_lev_lt κ (Order.succ μ) hκ h T hTk
    (fun α => (hlev α).trans_lt hlt)
  by_contra hc
  refine hna ⟨hTk, ?_⟩
  rintro ⟨b, hb⟩
  exact hc ⟨b, (isCofinalBranch_iff hT).1 hb⟩

end JardenShami
