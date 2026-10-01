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

/-! ## Auxiliary lemmas on `[A]^2` (AUX: not in paper) -/

section AuxPairs

/-- AUX: not in paper. Every element of `[A]^2` is `{a, b}` for some `a < b`. -/
theorem Pairs.exists_eq_mk {A : Type*} [LinearOrder A] (p : Pairs A) :
    ∃ (a b : A) (h : a < b), p = Pairs.mk a b h.ne := by
  obtain ⟨z, hz⟩ := p
  induction z using Sym2.ind with
  | h x y =>
    have hxy : x ≠ y := by simpa [Sym2.mk_isDiag_iff] using hz
    rcases hxy.lt_or_gt with h | h
    · exact ⟨x, y, h, rfl⟩
    · exact ⟨y, x, h, Subtype.ext Sym2.eq_swap⟩

/-- AUX: not in paper. `{a, b} = {c, d}` with `a < b` and `c < d` forces `a = c` and `b = d`. -/
theorem Pairs.mk_inj {A : Type*} [LinearOrder A] {a b c d : A} (hab : a < b) (hcd : c < d)
    (h : Pairs.mk a b hab.ne = Pairs.mk c d hcd.ne) : a = c ∧ b = d := by
  have h' : s(a, b) = s(c, d) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · subst h1; subst h2
    exact absurd (hab.trans hcd) (lt_irrefl _)

/-- AUX: not in paper. Homogeneity (Definition 2.2) in terms of `C(a,b)`, `a < b`. -/
theorem isHomogeneous_iff_color {A : Type*} [LinearOrder A] {D : Type*} (C : Coloring A D)
    (B : Set A) :
    IsHomogeneous C B ↔ ∀ (a b c d : A) (hab : a < b) (hcd : c < d),
      a ∈ B → b ∈ B → c ∈ B → d ∈ B → C.color a b hab = C.color c d hcd := by
  constructor
  · intro h a b c d hab hcd ha hb hc hd
    apply h
    · intro x hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl <;> assumption
    · intro x hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl <;> assumption
  · intro h p q hp hq
    obtain ⟨a, b, hab, rfl⟩ := p.exists_eq_mk
    obtain ⟨c, d, hcd, rfl⟩ := q.exists_eq_mk
    exact h a b c d hab hcd (hp a (Sym2.mem_mk_left a b)) (hp b (Sym2.mem_mk_right a b))
      (hq c (Sym2.mem_mk_left c d)) (hq d (Sym2.mem_mk_right c d))

/-- AUX: not in paper. The image of a pair under an injective map. -/
def Pairs.map {A B : Type*} (f : A → B) (hf : Function.Injective f) (p : Pairs A) : Pairs B :=
  ⟨p.1.map f, by rw [Sym2.isDiag_map hf]; exact p.2⟩

/-- AUX: not in paper. `f {a, b} = {f a, f b}`. -/
theorem Pairs.map_mk {A B : Type*} (f : A → B) (hf : Function.Injective f) (a b : A)
    (h : a ≠ b) : Pairs.map f hf (Pairs.mk a b h) = Pairs.mk (f a) (f b) (hf.ne h) :=
  Subtype.ext (Sym2.map_mk f a b)

end AuxPairs

section Sec3

variable {X : Type w} [LinearOrder X]

/-- **Theorem 3.1** (Section 3, `\label{generalizing add to loc less than mu colors}`,
`\label{theorem generalizing add to la}`). Let `κ, μ` be cardinals with `2^μ + ℵ₀ ≤ κ` and `F` a
family of subsets of a linearly ordered set. If `F → (F)_{add_κ}` then `F → (F)_{la_μ}`. -/
theorem arrow_la_of_arrow_add (κ μ : Cardinal.{v}) (hκ : 2 ^ μ + ℵ₀ ≤ κ) (F : Set (Set X))
    (h : Arrow F F (addEq κ)) : Arrow F F (laEq μ) := by
  sorry

/-! ## The argument of the proof of Theorem 3.1, for `< μ` colors (AUX: not in paper) -/

/-- AUX: not in paper. The argument of the paper's proof of Theorem 3.1, for the classes
`add_{<μ}` and `la_{<μ}`: if the set of colors `D* = D → Option D` (the partial functions
`u_{a,b} : D_b → D`) has fewer than `μ` elements whenever `D` does, then
`F → (F)_{add_{<μ}}` implies `F → (F)_{la_{<μ}}`. Used for Corollaries 3.2 and 3.3; it does not
use Theorem 3.1 itself. -/
theorem arrow_laLt_of_arrow_addLt_of_card (μ : Cardinal.{v})
    (hpow : ∀ D : Type v, #D < μ → #(D → Option D) < μ) (F : Set (Set X))
    (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) := by
  classical
  rintro S hS D C ⟨hla, hD⟩
  have hwd := (uMap_wellDefined_iff C).2 hla
  -- `R p t v`: `p = {a, b}` with `a < b`, and `v = u_{a,b}(t)` with witness `c`.
  let R : Pairs S → D → D → Prop := fun p t v => ∃ (a b c : S) (hab : a < b) (hbc : b < c),
    p = Pairs.mk a b hab.ne ∧ C.color b c hbc = t ∧ C.color a c (hab.trans hbc) = v
  -- `C*(a,b) = u_{a,b}`, as a partial function `D → Option D` with domain `D_b`.
  let Cs : Coloring S (D → Option D) := fun p t =>
    if hv : ∃ v, R p t v then some hv.choose else none
  have key1 : ∀ (a b c : S) (hab : a < b) (hbc : b < c),
      Cs.color a b hab (C.color b c hbc) = some (C.color a c (hab.trans hbc)) := by
    intro a b c hab hbc
    have hex : ∃ v, R (Pairs.mk a b hab.ne) (C.color b c hbc) v :=
      ⟨_, a, b, c, hab, hbc, rfl, rfl, rfl⟩
    change (if hv : ∃ v, R (Pairs.mk a b hab.ne) (C.color b c hbc) v then some hv.choose
      else none) = _
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨a', b', c', hab', hbc', hp, ht, hv⟩ := hex.choose_spec
    obtain ⟨rfl, rfl⟩ := Pairs.mk_inj hab hab' hp
    rw [← hv]
    exact congrArg some (hwd a b c' c hab hbc' hbc ht)
  have key2 : ∀ (a b : S) (hab : a < b) (t : D),
      (¬ ∃ (c : S) (hbc : b < c), C.color b c hbc = t) → Cs.color a b hab t = none := by
    intro a b hab t hn
    change (if hv : ∃ v, R (Pairs.mk a b hab.ne) t v then some hv.choose else none) = _
    have hn' : ¬ ∃ v, R (Pairs.mk a b hab.ne) t v := by
      rintro ⟨v, a', b', c', hab', hbc', hp, ht, -⟩
      obtain ⟨rfl, rfl⟩ := Pairs.mk_inj hab hab' hp
      exact hn ⟨c', hbc', ht⟩
    rw [dite_eq_right_of_eq_false (eq_false hn')]
  -- Claim 2.8: `C*` is additive, with `s(f, g) = f ∘ g` (composition of partial functions).
  have hadd : IsAdditive Cs := by
    refine ⟨fun fg t => (fg.2 t).bind fg.1, ?_⟩
    intro a b c hab hbc
    funext t
    change Cs.color a c (hab.trans hbc) t = (Cs.color b c hbc t).bind (Cs.color a b hab)
    by_cases ht : ∃ (d : S) (hcd : c < d), C.color c d hcd = t
    · obtain ⟨d, hcd, rfl⟩ := ht
      rw [key1 b c d hbc hcd, Option.bind_some, key1 a b d hab (hbc.trans hcd),
        key1 a c d (hab.trans hbc) hcd]
    · rw [key2 b c hbc t ht, Option.bind_none, key2 a c (hab.trans hbc) t ht]
  obtain ⟨B, hBF, hBhom⟩ := h S hS (D → Option D) Cs ⟨hadd, hpow D hD⟩
  -- The coloring `C ↾ [B]^2`, as a coloring of `B` viewed as a subset of `X`.
  have hsub : ∀ x ∈ Subtype.val '' B, x ∈ S := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  let ι : (Subtype.val '' B : Set X) → S := fun x => ⟨x.1, hsub x.1 x.2⟩
  have hιB : ∀ x, ι x ∈ B := by
    rintro ⟨x, y, hy, rfl⟩
    exact hy
  have hι : StrictMono ι := fun _ _ h => h
  let Cb : Coloring (Subtype.val '' B : Set X) D := fun p => C (Pairs.map ι hι.injective p)
  have hCb : ∀ a b (hab : a < b), Cb.color a b hab = C.color (ι a) (ι b) (hι hab) := by
    intro a b hab
    exact congrArg C (Pairs.map_mk ι hι.injective a b hab.ne)
  -- `C ↾ [B]^2` is additive, with `s(x, y) = f(y)` where `f` is the constant value of `C*`.
  have hCbadd : IsAdditive Cb := by
    by_cases hp : ∃ (a b : S) (_ : a < b), a ∈ B ∧ b ∈ B
    · obtain ⟨a₀, b₀, h₀, ha₀, hb₀⟩ := hp
      refine ⟨fun xy => (Cs.color a₀ b₀ h₀ xy.2).getD xy.1, ?_⟩
      intro a b c hab hbc
      rw [hCb, hCb, hCb]
      have hc : Cs.color (ι a) (ι b) (hι hab) = Cs.color a₀ b₀ h₀ :=
        (isHomogeneous_iff_color Cs B).1 hBhom _ _ _ _ _ _ (hιB a) (hιB b) ha₀ hb₀
      change _ = (Cs.color a₀ b₀ h₀ (C.color (ι b) (ι c) (hι hbc))).getD _
      rw [← hc, key1]
      rfl
    · refine ⟨Prod.fst, ?_⟩
      intro a b c hab hbc
      exact absurd ⟨ι a, ι b, hι hab, hιB a, hιB b⟩ hp
  obtain ⟨E, hEF, hEhom⟩ := h _ hBF D Cb ⟨hCbadd, hD⟩
  refine ⟨ι '' E, ?_, ?_⟩
  · rw [Set.image_image]
    exact hEF
  · rw [isHomogeneous_iff_color]
    rintro _ _ _ _ hab hcd ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact (hCb a b hab).symm.trans
      (((isHomogeneous_iff_color Cb E).1 hEhom a b c d hab hcd ha hb hc hd).trans (hCb c d hcd))

/-- **Corollary 3.2** (Section 3, `\label{generalizing add to loc for strong limit cardinal}`).
Let `μ` be a strong limit cardinal and `F` a family of subsets of a linearly ordered set.
If `F → (F)_{add_{<μ}}` then `F → (F)_{la_{<μ}}`. (Mathlib's `IsStrongLimit` includes `ℵ₀`.) -/
theorem arrow_laLt_of_arrow_addLt_strongLimit (μ : Cardinal.{v}) (hμ : μ.IsStrongLimit)
    (F : Set (Set X)) (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) := by
  refine arrow_laLt_of_arrow_addLt_of_card μ (fun D hD => ?_) F h
  rw [← Cardinal.power_def, Cardinal.mk_option]
  rcases lt_or_ge #D ℵ₀ with hfin | hinf
  · exact (Cardinal.power_lt_aleph0 (Cardinal.add_lt_aleph0 hfin Cardinal.one_lt_aleph0)
      hfin).trans_le hμ.aleph0_le
  · rw [Cardinal.add_one_of_aleph0_le hinf, Cardinal.power_self_eq hinf]
    exact hμ.isStrongPrelimit hD

/-- **Corollary 3.3** (Section 3, `\label{generalizing add to loc for finite}`).
If `F → (F)_{add_{<ℵ₀}}` then `F → (F)_{la_{<ℵ₀}}`. -/
theorem arrow_laLt_aleph0_of_arrow_addLt_aleph0 (F : Set (Set X))
    (h : Arrow F F (addLt (ℵ₀ : Cardinal.{v}))) : Arrow F F (laLt (ℵ₀ : Cardinal.{v})) := by
  refine arrow_laLt_of_arrow_addLt_of_card ℵ₀ (fun D hD => ?_) F h
  have : Finite D := Cardinal.lt_aleph0_iff_finite.1 hD
  exact Cardinal.lt_aleph0_iff_finite.2 inferInstance

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
  exact arrow_laLt_aleph0_of_arrow_addLt_aleph0 _ hfact

end JardenShami
