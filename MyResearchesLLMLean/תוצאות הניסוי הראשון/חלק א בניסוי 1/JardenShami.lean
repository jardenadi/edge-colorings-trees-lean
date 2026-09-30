import Mathlib

/-!
# A note on edge colorings and trees (Jarden–Shami, arXiv:2204.06874v1)

Lean 4 / Mathlib formalization of the definitions and statements of the paper,
each followed by a bounded proof attempt.  **This file has not been compiled.**
`sorry` marks a proof that was not completed within the per-statement budget.

## Encoding conventions

* A coloring of a linearly ordered `A` is a total function `C : A → A → D`;
  only the values `C a b` with `a < b` are ever inspected (Definition 2.1).
* `κ` (as an ordered set with the `∈`-order) is `Kappa κ := κ.ord.toType`.
* "Coloring with `μ` colors" means `#D = μ` (Definition 2.1).
* A "class of colorings" is a predicate on colorings of subsets `S ⊆ X`
  (`ColoringClass`); `Arrow F₁ F₂ 𝒞` is Definition 2.10.
* Partial functions `I ⇀ V` are `I → Option V`, ordered by inclusion of graphs (`PSeq`).
  They are used for `u_{a,b}` (Notation 2.5), for history trees and for `T(C)`.
* Trees: `IsTree` (well-ordered predecessor sets); `ht` via `Ordinal.type`.
* Colors of `C(T,e)` are ordinals, so `treeColoringRaw` is `Ordinal`-valued.
-/

open Cardinal Ordinal Set

universe u v w

namespace JardenShami

/-! ## 2. Basic definitions -/







section Basic
variable {A : Type u} {D : Type v}

/-- Definition 2.2 -/
def IsHomogeneous [LT A] (C : A → A → D) (B : Set A) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ a' ∈ B, ∀ b' ∈ B, a < b → a' < b' → C a b = C a' b'

/-- Definition 2.3 (additive coloring) -/
def IsAdditive [LT A] (C : A → A → D) : Prop :=
  ∃ s : D → D → D, ∀ a b c : A, a < b → b < c → C a c = s (C a b) (C b c)



/-- Definition 2.4 (locally additive coloring) -/
def IsLocallyAdditive [LT A] (C : A → A → D) : Prop :=
  ∀ a b c d : A, a < b → b < c → c < d → C b c = C b d → C a c = C a d

/-- Definition 2.6, `*`-locally additive: local additivity w.r.t. the reverse order.
In the reverse order `a ≺ b ≺ c ≺ d` means `d < c < b < a`, and the value of the pair
`{x,y}` is `C (min) (max)`. -/
def IsStarLocallyAdditive [LT A] (C : A → A → D) : Prop :=
  ∀ a b c d : A, d < c → c < b → b < a → C c b = C d b → C c a = C d a








/-
2
/-- Definition 2.6: a coloring of the cardinal `κ` with its `∈`-order. -/
 abbrev Kappa (κ : Cardinal.{u}) : Type u := κ.ord.toType
--
-- ביטלתי זמנית את הפקודה אברב כלומר קצר. השלם...
2
-/


/-- Notation 2.5: `D_b`. -/
def Db [LT A] (C : A → A → D) (b : A) : Set D := {t | ∃ c, b < c ∧ C b c = t}

open Classical in
/-- Notation 2.5: `u_{a,b} : D_b → D`, `u_{a,b}(C(b,c)) = C(a,c)`,
encoded as a partial function on `D` with domain `D_b`. -/
noncomputable def u [LT A] (C : A → A → D) (a b : A) : D → Option D :=
  fun t => if h : ∃ c, b < c ∧ C b c = t then some (C a h.choose) else none





/-- Composition of partial functions. -/
def pcomp (f g : D → Option D) : D → Option D := fun t => (g t).bind f

/-- Well-definedness of `u_{a,b}` (Notation 2.5): `u_{a,b}(C(b,c)) = C(a,c)`. -/
theorem u_spec [LinearOrder A] {C : A → A → D} (hC : IsLocallyAdditive C)
    {a b c : A} (hab : a < b) (hbc : b < c) : u C a b (C b c) = some (C a c) := by
  classical
  have h : ∃ c', b < c' ∧ C b c' = C b c := ⟨c, hbc, rfl⟩
  simp only [u, dif_pos h]
  obtain ⟨hlt, heq⟩ := h.choose_spec
  congr 1
  rcases lt_trichotomy h.choose c with h1 | h1 | h1
  · exact hC a b _ c hab hlt h1 heq
  · rw [h1]
  · exact (hC a b c _ hab hbc h1 heq.symm).symm

/-- Remark 2.7 -/
theorem remark_2_7 [LinearOrder A] {C : A → A → D} (h : IsAdditive C) :
    IsLocallyAdditive C := by
  obtain ⟨s, hs⟩ := h
  intro a b c d hab hbc hcd he
  rw [hs a b c hab hbc, hs a b d hab (hbc.trans hcd), he]

/-- Claim 2.8: `u_{a,b} ∘ u_{b,c} = u_{a,c}` (as partial functions; both are
undefined outside `D_c`). -/
theorem claim_2_8 [LinearOrder A] {C : A → A → D} (hC : IsLocallyAdditive C)
    {a b c : A} (hab : a < b) (hbc : b < c) :
    pcomp (u C a b) (u C b c) = u C a c := by
  classical
  funext t
  by_cases ht : ∃ d, c < d ∧ C c d = t
  · obtain ⟨d, hcd, rfl⟩ := ht
    simp only [pcomp, u_spec hC hbc hcd, Option.bind_some,
      u_spec hC hab (hbc.trans hcd), u_spec hC (hab.trans hbc) hcd]
  · simp only [pcomp, u, dif_neg ht, Option.bind_none]

end Basic

/-! ### Notation 2.9 and Definition 2.10 (generalized arrow notation) -/

/-- A class of colorings of subsets of the linearly ordered set `X`. -/
def ColoringClass (X : Type u) [LT X] : Type (u + 1) :=
  ∀ (S : Set X) (D : Type u), (S → S → D) → Prop

/-- Definition 2.10: `F₁ → (F₂)_𝒞`. -/
def Arrow {X : Type u} [LT X] (F₁ F₂ : Set (Set X)) (𝒞 : ColoringClass X) : Prop :=
  ∀ S ∈ F₁, ∀ (D : Type u) (C : S → S → D), 𝒞 S D C →
    ∃ E : Set S, (Subtype.val '' E) ∈ F₂ ∧ IsHomogeneous C E

section Classes
variable {X : Type u} [LT X]

/-- all colorings with `μ` colors -/
def colEq (μ : Cardinal.{u}) : ColoringClass X := fun _ D _ => #D = μ
/-- `add_μ` -/
def addEq (μ : Cardinal.{u}) : ColoringClass X := fun _ D C => IsAdditive C ∧ #D = μ
/-- `add_{<μ}` -/
def addLt (μ : Cardinal.{u}) : ColoringClass X := fun _ D C => IsAdditive C ∧ #D < μ
/-- `la_μ` -/
def laEq (μ : Cardinal.{u}) : ColoringClass X := fun _ D C => IsLocallyAdditive C ∧ #D = μ
/-- `la_{<μ}` -/
def laLt (μ : Cardinal.{u}) : ColoringClass X := fun _ D C => IsLocallyAdditive C ∧ #D < μ
/-- `*-la_μ` -/
def starLaEq (μ : Cardinal.{u}) : ColoringClass X :=
  fun _ D C => IsStarLocallyAdditive C ∧ #D = μ
/-- `*-la_{<μ}` -/
def starLaLt (μ : Cardinal.{u}) : ColoringClass X :=
  fun _ D C => IsStarLocallyAdditive C ∧ #D < μ

end Classes


/-
1
אני חותך כאן כדי לטפל בקמפול הקובץ


/-- The family of subsets of `κ` of cardinality `κ`. -/
def BigSubsets (κ : Cardinal.{u}) : Set (Set (Kappa κ)) := {S | #S = κ}

/-- `κ → (κ)^{la}_μ` -/
def RamseyLA (κ μ : Cardinal.{u}) : Prop := Arrow (BigSubsets κ) (BigSubsets κ) (laEq μ)
/-- `κ →^{*-la} (κ)_μ` -/
def RamseyStarLA (κ μ : Cardinal.{u}) : Prop :=
  Arrow (BigSubsets κ) (BigSubsets κ) (starLaEq μ)

/-! ## 3. Replacing additivity by local additivity -/

/-- Theorem 3.1.
Proof idea (paper): `D* =` partial functions `μ ⇀ μ` (here `D → Option D`), `|D*| ≤ κ`;
`C*(a,b) = u_{a,b}` is additive by Claim 2.8 (with `s = pcomp`); pad `D*` to exactly `κ`
colors; get `B ∈ F` homogeneous for `C*` with value `f`; then
`C(a,c) = f(C(b,c))`, so `C↾B` is additive (`s x y = (f y).getD x`); apply the hypothesis
again.  Not completed: the cardinality bound `|D → Option D| ≤ κ` and the transport of the
coloring along subtypes `↥S ⊇ B` are missing. -/
theorem theorem_3_1 {X : Type u} [LinearOrder X] (κ μ : Cardinal.{u})
    (h : 2 ^ μ + ℵ₀ ≤ κ) (F : Set (Set X)) (hF : Arrow F F (addEq κ)) :
    Arrow F F (laEq μ) := by
  sorry

/-- Corollary 3.2.  (Note: obtained from the *proof* of 3.1 with "at most `κ` colors";
literally from the statement of 3.1 one needs `2^ν + ℵ₀ < μ`, which fails for `μ = ℵ₀`.) -/
theorem corollary_3_2 {X : Type u} [LinearOrder X] (μ : Cardinal.{u}) (hμ : μ.IsStrongLimit)
    (F : Set (Set X)) (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) := by
  sorry

/-- Corollary 3.3 -/
theorem corollary_3_3 {X : Type u} [LinearOrder X] (F : Set (Set X))
    (h : Arrow F F (addLt ℵ₀)) : Arrow F F (laLt ℵ₀) :=
  corollary_3_2 ℵ₀ Cardinal.isStrongLimit_aleph0 F h

/-- Subsets of `I` that are dense in some interval of `I`. -/
def DenseInSomeInterval (I : Type u) [LinearOrder I] : Set (Set I) :=
  {S | ∃ J : Set I, J.OrdConnected ∧ (∃ a ∈ J, ∃ b ∈ J, a < b) ∧
    ∀ x ∈ J, ∀ y ∈ J, x < y → ∃ s ∈ S, x < s ∧ s < y}

/-- Fact 3.4 (Shelah, [3, Theorem 1.3]); cited, not proved in the paper. -/
theorem fact_3_4 (I : Type u) [LinearOrder I] [DenselyOrdered I] :
    Arrow (DenseInSomeInterval I) (DenseInSomeInterval I) (addLt ℵ₀) := by
  sorry

/-- Corollary 3.5 -/
theorem corollary_3_5 (I : Type u) [LinearOrder I] [DenselyOrdered I] :
    Arrow (DenseInSomeInterval I) (DenseInSomeInterval I) (laLt ℵ₀) :=
  corollary_3_3 _ (fact_3_4 I)

/-! ## 4. Trees and colorings -/

/-- A tree: a partial order in which the predecessors of every element are well-ordered. -/
class IsTree (T : Type w) [PartialOrder T] : Prop where
  wo : ∀ t : T, IsWellOrder (Set.Iio t) (fun a b => (a : T) < b)

section Trees
variable {T : Type w} [PartialOrder T] [IsTree T]

/-- `ht(t, T)` -/
noncomputable def ht (t : T) : Ordinal.{w} :=
  @Ordinal.type (Set.Iio t) (fun a b => (a : T) < b) (IsTree.wo t)

variable (T)
/-- `Lev_α(T)` -/
def Lev (α : Ordinal.{w}) : Set T := {t | ht t = α}
/-- `Lev_{<α}(T)` -/
def LevLt (α : Ordinal.{w}) : Set T := {t | ht t < α}
/-- `ht(T)`: the first `α` with `Lev_α(T) = ∅`. -/
noncomputable def treeHeight : Ordinal.{w} := sInf {α | Lev T α = ∅}

/-- well-pruned tree -/
def IsWellPruned : Prop :=
  (∃! t : T, ht t = 0) ∧
  ∀ x : T, ∀ α : Ordinal.{w}, ht x < α → α < treeHeight T → ∃ y ∈ Lev T α, x < y

/-- a `κ`-tree: height `κ` and levels of size `< κ` -/
def IsKappaTree (κ : Cardinal.{w}) : Prop :=
  treeHeight T = κ.ord ∧ ∀ α, #(Lev T α) < κ

variable {T}
/-- cofinal branch: a maximal chain whose order type is the height of the tree -/
def CofinalBranch (b : Set T) : Prop :=
  IsMaxChain (· ≤ ·) b ∧
  ∃ h : IsWellOrder b (fun x y => (x : T) < y),
    @Ordinal.type b (fun x y => (x : T) < y) h = treeHeight T

variable (T)
/-- `κ`-Aronszajn tree -/
def IsAronszajn (κ : Cardinal.{w}) : Prop := IsKappaTree T κ ∧ ¬ ∃ b : Set T, CofinalBranch b

/-- "`T` admits a `κ`-sized branch" -/
def HasBranchOfSize (κ : Cardinal.{w}) : Prop := ∃ b : Set T, IsMaxChain (· ≤ ·) b ∧ #b = κ

/-- Remark after the definition of well-pruned: a well-pruned tree of limit height has no
leaves ("clearly"). -/
theorem wellPruned_limit_noLeaves (hT : IsWellPruned T) (hlim : (treeHeight T).IsLimit) :
    ∀ t : T, ¬ IsMax t := by
  sorry

end Trees

/-- The tree property at `κ`. -/
def TreeProperty (κ : Cardinal.{u}) : Prop :=
  ¬ ∃ (T : Type u) (_ : PartialOrder T) (_ : IsTree T), IsAronszajn T κ

/-! ### 4.1 Reconstructing a tree from its history -/

/-- Partial functions `I ⇀ V`, ordered by inclusion of graphs. -/
def PSeq (I : Type v) (V : Type w) : Type (max v w) := I → Option V

instance {I : Type v} {V : Type w} : PartialOrder (PSeq I V) where
  le f g := ∀ i v, f i = some v → g i = some v
  le_refl f i v h := h
  le_trans f g h hfg hgh i v hf := hgh i v (hfg i v hf)
  le_antisymm f g hfg hgf := by
    funext i
    rcases hf : f i with _ | v
    · rcases hg : g i with _ | w
      · rfl
      · have := hgf i w hg
        rw [hf] at this
        cases this
    · exact (hfg i v hf).symm

section History
variable {T : Type u} [PartialOrder T] [IsTree T]

open Classical in
/-- Definition 4.1: `f_t : ht(t) → T`, `f_t(α)` = the unique `t' < t` on level `α`
(partial function on ordinals with domain `ht(t)`). -/
noncomputable def historyFun (t : T) : PSeq Ordinal.{u} T :=
  fun α => if h : ∃ t', t' < t ∧ ht t' = α then some h.choose else none

variable (T)
/-- Definition 4.1: the history tree `F_T = ({f_t : t ∈ T}, ⊆)`. -/
def HistoryTree : Type (u + 1) := {f : PSeq Ordinal.{u} T // ∃ t : T, f = historyFun t}

instance : PartialOrder (HistoryTree T) :=
  inferInstanceAs (PartialOrder {f : PSeq Ordinal.{u} T // ∃ t : T, f = historyFun t})

/-- successor ordinals -/
def IsSuccOrd (α : Ordinal.{u}) : Prop := ∃ β, α = Order.succ β

/-- Definition 4.2: `T^succ`. -/
def SuccPart : Type u := {t : T // IsSuccOrd (ht t)}

instance : PartialOrder (SuccPart T) := inferInstanceAs (PartialOrder {t : T // IsSuccOrd (ht t)})

/-- Definition 4.2: `(F_T)^succ = ({f_t : t ∈ T^succ}, ⊆)`. -/
def HistoryTreeSucc : Type (u + 1) :=
  {x : HistoryTree T // ∃ t : T, IsSuccOrd (ht t) ∧ x.1 = historyFun t}

instance : PartialOrder (HistoryTreeSucc T) :=
  inferInstanceAs (PartialOrder {x : HistoryTree T // ∃ t : T, IsSuccOrd (ht t) ∧ x.1 = historyFun t})

end History

/-- Remark 4.3.  Idea: `ht(f_t, F_T) = ht(t, T)`, and order isomorphisms preserve heights. -/
theorem remark_4_3 {T S : Type u} [PartialOrder T] [IsTree T] [PartialOrder S] [IsTree S]
    (g : HistoryTree T ≃o HistoryTree S) :
    ∃ g' : HistoryTreeSucc T ≃o HistoryTreeSucc S, ∀ x, (g' x).1 = g x.1 := by
  sorry

/-- Proposition 4.4.  Idea (paper): `h(t) = f_{t*}` where `t* > t` has height `ht(t)+1`. -/
theorem proposition_4_4 {T : Type u} [PartialOrder T] [IsTree T] (hT : ∀ t : T, ¬ IsMax t) :
    Nonempty (T ≃o HistoryTreeSucc T) := by
  sorry

/-- Corollary 4.5 -/
theorem corollary_4_5 {T S : Type u} [PartialOrder T] [IsTree T] [PartialOrder S] [IsTree S]
    (hT : ∀ t : T, ¬ IsMax t) (hS : ∀ s : S, ¬ IsMax s) :
    Nonempty (T ≃o S) ↔ Nonempty (HistoryTree T ≃o HistoryTree S) := by
  constructor
  · sorry -- the "trivial" direction (not proved in the paper)
  · rintro ⟨g⟩
    obtain ⟨g', -⟩ := remark_4_3 g
    obtain ⟨a⟩ := proposition_4_4 hT
    obtain ⟨b⟩ := proposition_4_4 hS
    exact ⟨a.trans (g'.trans b.symm)⟩

/-! ### 4.2 The tree of a coloring -/

section TreeOfColoring
variable {A : Type u} {D : Type v}

/-- `C(·,δ) ↾ β` as a partial function `A ⇀ D` with domain `{α | α < β}`. -/
def truncFiber [LT A] (C : A → A → D) (β δ : A) : PSeq A D :=
  fun α => if α < β then some (C α δ) else none

/-- Definition 4.6: `T(C) = {C(·,δ) ↾ β | β ≤ δ < κ}`, ordered by `⊆`. -/
def TC [LinearOrder A] (C : A → A → D) : Type (max u v) :=
  {f : PSeq A D // ∃ β δ : A, β ≤ δ ∧ f = truncFiber C β δ}

instance [LinearOrder A] (C : A → A → D) : PartialOrder (TC C) :=
  inferInstanceAs (PartialOrder {f : PSeq A D // ∃ β δ : A, β ≤ δ ∧ f = truncFiber C β δ})

/-- `T(C)` is a tree (implicit in Definition 4.6).  Idea: the predecessors of
`C(·,δ)↾β` are the `C(·,δ)↾β'` with `β' < β`, indexed order-isomorphically by `β' ∈ A`. -/
instance [LinearOrder A] [WellFoundedLT A] (C : A → A → D) : IsTree (TC C) :=
  ⟨fun t => sorry⟩

/-- Remark 4.7 -/
theorem remark_4_7 (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (f : Kappa κ → Fin 2) :
    IsLocallyAdditive (fun (α : Kappa κ) (_ : Kappa κ) => f α) ∧
    IsStarLocallyAdditive (fun (α : Kappa κ) (_ : Kappa κ) => f α) ∧
    Nonempty (TC (fun (α : Kappa κ) (_ : Kappa κ) => f α) ≃o Kappa κ) := by
  refine ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ h => h, ?_⟩
  sorry -- `f↾β ↦ β`; uses that `Kappa κ` has no maximum

/-- Remark 4.8 -/
theorem remark_4_8 (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (f : Kappa κ → Fin 2)
    (hf : ∀ β : Kappa κ, ∃ δ₀ δ₁, β ≤ δ₀ ∧ β ≤ δ₁ ∧ f δ₀ = 0 ∧ f δ₁ = 1) :
    IsLocallyAdditive (fun (_ : Kappa κ) (β : Kappa κ) => f β) ∧
    IsStarLocallyAdditive (fun (_ : Kappa κ) (β : Kappa κ) => f β) ∧
    ∀ g : PSeq (Kappa κ) (Fin 2),
      (∃ x : TC (fun (_ : Kappa κ) (β : Kappa κ) => f β), x.1 = g) ↔
        ∃ (i : Fin 2) (β : Kappa κ), g = fun α => if α < β then some i else none := by
  refine ⟨fun _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ _ _ _ => rfl, ?_⟩
  sorry

/-- Question 4.9 (open, no statement): find a characterization of the equivalence classes of
locally additive colorings induced by `C ↦ T(C)`. -/

end TreeOfColoring

/-! ### 4.3 The locally additive coloring of an enumerated tree -/

/-- Definition 4.10: an enumeration `e = ⟨⟨t^i_α : i < μ_α⟩ : α < κ⟩` of the levels of `T`.
`toFun α i = some t` means `t = t^i_α`; each level is enumerated bijectively by
the ordinals `i < μ_α = |Lev_α(T)|`. -/
structure Enumeration (T : Type u) [PartialOrder T] [IsTree T] where
  toFun : Ordinal.{u} → Ordinal.{u} → Option T
  mem_lt : ∀ α i t, toFun α i = some t → ht t = α ∧ i < (#(Lev T α)).ord
  total : ∀ α i, i < (#(Lev T α)).ord → ∃ t, toFun α i = some t
  surj : ∀ t : T, ∃ i, toFun (ht t) i = some t
  inj : ∀ α i j t, toFun α i = some t → toFun α j = some t → i = j

/-- the ordinal `α` corresponding to an element of `Kappa κ` -/
noncomputable def ordOf {κ : Cardinal.{u}} (α : Kappa κ) : Ordinal.{u} :=
  Ordinal.typein (· < ·) α

section Enum
variable {T : Type u} [PartialOrder T] [IsTree T]

/-- `μ = sup {μ_α : α < κ}` -/
noncomputable def levelSup (κ : Cardinal.{u}) (T : Type u) [PartialOrder T] [IsTree T] :
    Cardinal.{u} :=
  sSup {c | ∃ α < κ.ord, c = #(Lev T α)}

open Classical in
/-- Definition 4.11: `C(T,e)(α,δ) = i` iff `α < δ` and `i` is the unique ordinal with
`t^i_α ≤ t^0_δ` (ordinal-valued; see `treeColoringRaw_lt` for `i < μ`). -/
noncomputable def treeColoringRaw (κ : Cardinal.{u}) (e : Enumeration T)
    (α δ : Kappa κ) : Ordinal.{u} :=
  if h : α < δ ∧ ∃ i t s, e.toFun (ordOf α) i = some t ∧ e.toFun (ordOf δ) 0 = some s ∧ t ≤ s
  then h.2.choose else 0

/-- the colors of `C(T,e)` are `< μ` (Definition 4.11: `C(T,e) : [κ]² → μ`) -/
theorem treeColoringRaw_lt (κ : Cardinal.{u}) (hT : IsKappaTree T κ) (e : Enumeration T)
    (α δ : Kappa κ) : treeColoringRaw κ e α δ < (levelSup κ T).ord := by
  sorry

/-- Claim 4.12.  Paper's proof: for `α<β<γ₁,γ₂` with `C(β,γ₁)=C(β,γ₂)=i`, both
`t^{C(α,γⱼ)}_α` lie below `t^i_β`, hence are comparable and on level `α`, hence equal;
conclude by injectivity of the enumeration.  Not completed (needs: predecessor of `t^0_γ` on
each lower level exists and is unique). -/
theorem claim_4_12 (κ : Cardinal.{u}) (hT : IsKappaTree T κ) (e : Enumeration T) :
    IsLocallyAdditive (treeColoringRaw κ e) := by
  sorry

/-- Definition 4.13: `e` covers `T` -/
def Enumeration.Covers (e : Enumeration T) (κ : Cardinal.{u}) : Prop :=
  ∀ t : T, ∃ δ : Kappa κ, ∃ s, e.toFun (ordOf δ) 0 = some s ∧ t < s

/-- Remark 4.14 (the proof uses regularity of `κ`).  Idea: fix a bijection `f : κ → T`,
choose `δ_γ` increasing with `f(γ) < t^0_{δ_γ}`. -/
theorem remark_4_14 (κ : Cardinal.{u}) (hκ : κ.IsRegular) (hT : IsKappaTree T κ)
    (hwp : IsWellPruned T) : ∃ e : Enumeration T, e.Covers κ := by
  sorry

/-- Theorem 4.15.  Proof in the paper: `h(C(·,δ)↾β) = f_{t^{C(β,δ)}_β}` and Claims
4.16–4.19 (well-defined + injective, order-homomorphism, surjective).  Not completed. -/
theorem theorem_4_15 (κ : Cardinal.{u}) (hT : IsKappaTree T κ) (e : Enumeration T)
    (hcov : e.Covers κ) :
    Nonempty (TC (treeColoringRaw κ e) ≃o HistoryTree T) := by
  sorry

/-- Corollary 4.20 -/
theorem corollary_4_20 (κ : Cardinal.{u})
    {T₁ T₂ : Type u} [PartialOrder T₁] [IsTree T₁] [PartialOrder T₂] [IsTree T₂]
    (h₁ : IsKappaTree T₁ κ) (h₂ : IsKappaTree T₂ κ)
    (hl₁ : ∀ t : T₁, ¬ IsMax t) (hl₂ : ∀ t : T₂, ¬ IsMax t)
    (e₁ : Enumeration T₁) (e₂ : Enumeration T₂) (c₁ : e₁.Covers κ) (c₂ : e₂.Covers κ) :
    Nonempty (T₁ ≃o T₂) ↔
      Nonempty (TC (treeColoringRaw κ e₁) ≃o TC (treeColoringRaw κ e₂)) := by
  obtain ⟨a⟩ := theorem_4_15 κ h₁ e₁ c₁
  obtain ⟨b⟩ := theorem_4_15 κ h₂ e₂ c₂
  rw [corollary_4_5 hl₁ hl₂]
  constructor
  · rintro ⟨g⟩
    exact ⟨a.trans (g.trans b.symm)⟩
  · rintro ⟨g⟩
    exact ⟨a.symm.trans (g.trans b)⟩

end Enum

/-! ## 5. The tree property at successor cardinals -/

/-- strongly inaccessible cardinal -/
def StronglyInaccessible (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ κ.IsRegular ∧ κ.IsStrongLimit

/-- weakly compact = strongly inaccessible with the tree property (as in the paper) -/
def WeaklyCompact (κ : Cardinal.{u}) : Prop := StronglyInaccessible κ ∧ TreeProperty κ

/-- Fact 5.1 (cited) -/
theorem fact_5_1 (κ : Cardinal.{u}) (hκ : StronglyInaccessible κ) :
    TreeProperty κ ↔
      ∀ lam < κ, Arrow (BigSubsets κ) (BigSubsets κ) (colEq lam) := by
  sorry

/-- Claim 5.4 (inside the proof of Lemma 5.3): all levels of `T(C)` have size `≤ μ`.
Proof (paper): otherwise take `μ⁺` many `δ_i` with distinct `C(·,δ_i)↾β`, find `i<j` with
`C(β,δ_i)=C(β,δ_j)`, and `α<β` with `C(α,δ_i)≠C(α,δ_j)`; this contradicts
`C(α,δ)=u_{α,β}(C(β,δ))`. -/
theorem claim_5_4 (κ μ : Cardinal.{u}) (hκ : κ.IsRegular) (hμκ : μ < κ)
    {D : Type u} (hD : #D = μ) (C : Kappa κ → Kappa κ → D) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{u}, #(Lev (TC C) β) ≤ μ := by
  sorry

/-- (1) of Lemma 5.3: every tree of height `κ` whose levels have size `≤ μ` has a
`κ`-sized branch. -/
def AllBranches (κ μ : Cardinal.{u}) : Prop :=
  ∀ (T : Type u) [PartialOrder T] [IsTree T],
    treeHeight T = κ.ord → (∀ α, #(Lev T α) ≤ μ) → HasBranchOfSize T κ

/-- Lemma 5.3.
(1)⇒(2): by Claim 5.4 and (1), `T(C)` has a cofinal branch `b`; take a club-like
continuous `f` with `b↾f(i) ⊆ C(·,f(i+1))`, and a `κ`-sized subset of `{f(i+1)}` on which `b`
is constant.
(¬1)⇒(¬2): from a tree without `κ`-branch build `C(T,e)` (Claim 4.12); a homogeneous
`H` of color `i` would give the chain `{t^i_α | α ∈ H}`.  Not completed. -/
theorem lemma_5_3 (κ μ : Cardinal.{u}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ) (hμ : μ < κ) :
    AllBranches κ μ ↔ RamseyLA κ μ := by
  sorry

/-- Theorem 5.2 (the case `κ = μ⁺` of Lemma 5.3).  Needs the routine equivalence:
a tree of height `μ⁺` with levels `≤ μ` is a `μ⁺`-tree, and a `μ⁺`-sized branch is cofinal. -/
theorem theorem_5_2 (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    TreeProperty (Order.succ μ) ↔ RamseyLA (Order.succ μ) μ := by
  have h := lemma_5_3 (Order.succ μ) μ (Cardinal.isRegular_succ hμ)
    (hμ.trans_lt (Order.lt_succ μ)) (Order.lt_succ μ)
  rw [← h]
  sorry

/-! ## 6. Strongly inaccessibles in the tree sense -/

/-- Definition 6.1: the tree exponent `λ^{μ,tr}`. -/
noncomputable def treeExp (lam μ : Cardinal.{u}) : Cardinal.{u} :=
  sSup {c | ∃ (T : Type u) (_ : PartialOrder T) (_ : IsTree T),
    #T ≤ lam ∧ treeHeight T = μ.ord ∧ c = #{b : Set T // CofinalBranch b}}

/-- Remark 6.2.  Idea: a cofinal branch is determined by the function `α ↦` its element of
level `α`, i.e. an element of `μ → T`. -/
theorem remark_6_2 (lam μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (hle : μ ≤ lam) :
    treeExp lam μ ≤ lam ^ μ := by
  sorry

/-- Fact 6.3 (cited): `κ → (κ)²` iff `κ` is weakly compact. -/
theorem fact_6_3 (κ : Cardinal.{u}) (hκ : ℵ₀ < κ) :
    Arrow (BigSubsets κ) (BigSubsets κ) (colEq 2) ↔ WeaklyCompact κ := by
  sorry

/-- Auxiliary standard fact: in a strongly inaccessible `κ`, `λ^μ < κ` for `λ, μ < κ`. -/
theorem power_lt_of_stronglyInaccessible {κ : Cardinal.{u}} (hκ : StronglyInaccessible κ)
    {lam μ : Cardinal.{u}} (hl : lam < κ) (hμ : μ < κ) : lam ^ μ < κ := by
  sorry

/-- Theorem 6.4 (`λ^{μ,tr}` is only defined for infinite `μ ≤ λ`).
(2)⇒(1): Remark 6.2.  (1)⇒(2): by Fact 6.3 prove `κ → (κ)²`: for `F : [κ]² → 2` build the
tree `t_α` of functions (`t_α(ξ) = F(β,α)`), show its levels are `< κ` using (1), take a
`κ`-branch `B` and split it according to the value of `F`.  Not completed. -/
theorem theorem_6_4 (κ : Cardinal.{u}) (hunc : ℵ₀ < κ) (hreg : κ.IsRegular)
    (htp : TreeProperty κ) :
    (∀ lam μ : Cardinal.{u}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      StronglyInaccessible κ := by
  sorry

/-- Corollary 6.5 -/
theorem corollary_6_5 (κ : Cardinal.{u}) (hunc : ℵ₀ < κ) :
    WeaklyCompact κ ↔
      κ.IsRegular ∧ TreeProperty κ ∧
        ∀ lam μ : Cardinal.{u}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ := by
  constructor
  · rintro ⟨hi, htp⟩
    refine ⟨hi.2.1, htp, ?_⟩
    intro lam μ hμ hle hlam
    exact (remark_6_2 lam μ hμ hle).trans_lt
      (power_lt_of_stronglyInaccessible hi hlam (hle.trans_lt hlam))
  · rintro ⟨hreg, htp, h3⟩
    exact ⟨(theorem_6_4 κ hunc hreg htp).1 h3, htp⟩

/-! ## 7. Ramsey theorems for locally additive colorings -/

section Star
variable {A : Type u} {D : Type v}

/-- Definition 7.1: `β ∼ γ` (with witness `α`). -/
def Sim [LT A] (C : A → A → D) (β γ : A) : Prop := ∃ α, β < α ∧ γ < α ∧ C β α = C γ α

/-- Remark 7.2 (first part): witnesses can be increased. -/
theorem remark_7_2_witness [LinearOrder A] {C : A → A → D} (hC : IsStarLocallyAdditive C)
    {β γ α₁ α₂ : A} (hβ : β < α₁) (hγ : γ < α₁) (hw : C β α₁ = C γ α₁) (h12 : α₁ < α₂) :
    C β α₂ = C γ α₂ := by
  rcases lt_trichotomy β γ with h | h | h
  · exact (hC α₂ α₁ γ β h hγ h12 hw.symm).symm
  · rw [h]
  · exact hC α₂ α₁ β γ h hβ h12 hw

/-- Remark 7.2: `∼` is an equivalence relation. -/
theorem remark_7_2_equiv [LinearOrder A] [NoMaxOrder A] {C : A → A → D}
    (hC : IsStarLocallyAdditive C) : Equivalence (Sim C) := by
  refine ⟨fun β => ?_, fun {β γ} h => ?_, fun {β γ η} h1 h2 => ?_⟩
  · obtain ⟨α, hα⟩ := exists_gt β
    exact ⟨α, hα, hα, rfl⟩
  · obtain ⟨α, h1, h2, h3⟩ := h
    exact ⟨α, h2, h1, h3.symm⟩
  · obtain ⟨α₁, hβ1, hγ1, h1⟩ := h1
    obtain ⟨α₂, hγ2, hη2, h2⟩ := h2
    rcases le_total α₁ α₂ with h | h
    · have : C β α₂ = C γ α₂ := by
        rcases h.eq_or_lt with rfl | hlt
        · exact h1
        · exact remark_7_2_witness hC hβ1 hγ1 h1 hlt
      exact ⟨α₂, hβ1.trans_le h, hη2, this.trans h2⟩
    · have : C γ α₁ = C η α₁ := by
        rcases h.eq_or_lt with rfl | hlt
        · exact h2
        · exact remark_7_2_witness hC hγ2 hη2 h2 hlt
      exact ⟨α₁, hβ1, hη2.trans_le h, h1.trans this⟩

/-- the setoid of `∼` -/
def simSetoid [LinearOrder A] [NoMaxOrder A] {C : A → A → D}
    (hC : IsStarLocallyAdditive C) : Setoid A := ⟨Sim C, remark_7_2_equiv hC⟩

end Star

/-- auxiliary: fewer than `κ` elements of `Kappa κ` are bounded (`κ` regular) -/
theorem exists_upper_bound (κ : Cardinal.{u}) (hκ : κ.IsRegular) (s : Set (Kappa κ))
    (hs : #s < κ) : ∃ α : Kappa κ, ∀ x ∈ s, x < α := by
  sorry

/-- Lemma 7.3: if `μ⁺ < κ` (`κ` regular) then there are at most `μ` classes of `∼`. -/
theorem lemma_7_3 (κ μ : Cardinal.{u}) (hκ : κ.IsRegular) (hμ : Order.succ μ < κ)
    [NoMaxOrder (Kappa κ)] {D : Type u} (hD : #D = μ) (C : Kappa κ → Kappa κ → D)
    (hC : IsStarLocallyAdditive C) : #(Quotient (simSetoid hC)) ≤ μ := by
  by_contra hlt
  push_neg at hlt
  have hle : Order.succ μ ≤ #(Quotient (simSetoid hC)) := Order.succ_le_of_lt hlt
  set P : Type u := (Order.succ μ).ord.toType with hPdef
  have hP : #P = Order.succ μ := by simp [hPdef]
  obtain ⟨g⟩ : Nonempty (P ↪ Quotient (simSetoid hC)) :=
    (Cardinal.le_def _ _).1 (hP.trans_le hle)
  let r : P → Kappa κ := fun i => Quotient.out (g i)
  obtain ⟨α, hα⟩ := exists_upper_bound κ hκ (Set.range r)
    ((Cardinal.mk_range_le).trans_lt (hP ▸ hμ))
  have hni : ¬ Function.Injective (fun i => C (r i) α) := by
    intro hinj
    have := Cardinal.mk_le_of_injective hinj
    rw [hP, hD] at this
    exact absurd this (not_le_of_gt (Order.lt_succ μ))
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨i, j, hij, hne⟩ := hni
  apply hne
  apply g.injective
  have hs : Sim C (r i) (r j) := ⟨α, hα _ ⟨i, rfl⟩, hα _ ⟨j, rfl⟩, hij⟩
  have := Quotient.sound (s := simSetoid hC) hs
  simpa [r] using this

/-- Theorem 7.4.
Proof (paper): by Lemma 7.3 some `∼`-class `A` is unbounded; build by induction an
increasing sequence `y_α ∈ A` with `C(y_β,y_α) = C(y_γ,y_α)` for `β<γ<α` (Remark 7.2);
pigeonhole `f(α) = C(y₀,y_α)` on an unbounded set `B` (as `μ < κ = cf κ`).
Not completed. -/
theorem theorem_7_4 (κ μ : Cardinal.{u}) (hκ : κ.IsRegular) (hμ : Order.succ μ < κ) :
    RamseyStarLA κ μ := by
  sorry

/-- Proposition 7.5 (`μ` infinite).  Coloring: `C(β,α) = f_α(β)` for injections
`f_α : α → μ`; it is `*`-locally additive vacuously and has no homogeneous set of size 3. -/
theorem proposition_7_5 (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    ¬ RamseyStarLA (Order.succ μ) μ := by
  sorry

/-- Question 7.6 (open in the paper). -/
def Question_7_6 : Prop := ∀ μ : Cardinal.{u}, ℵ₀ ≤ μ → RamseyLA (Order.succ μ) μ

/-- Claim 7.9 (inside the proof of Claim 7.8): `T` well-pruned `κ`-tree, `λ` regular with all
levels of size `< λ`.  For every `α < κ` with `cf(α) = λ` there is `q(α) < α` such that no node
of level `q(α)` has two distinct extensions on a level `β ∈ (q(α), α)`.
Proof: otherwise build `λ` many pairwise distinct nodes of `Lev_α(T)`. -/
theorem claim_7_9 (κ lam : Cardinal.{u}) (hκ : κ.IsRegular) (hlam : lam.IsRegular)
    (hlk : lam < κ) (T : Type u) [PartialOrder T] [IsTree T] (hT : IsKappaTree T κ)
    (hwp : IsWellPruned T) (hlev : ∀ γ, #(Lev T γ) < lam) :
    ∀ α : Ordinal.{u}, α < κ.ord → α.cof = lam →
      ∃ q < α, ∀ β, q < β → β < α → ∀ a b c : T,
        ht a = q → ht b = β → ht c = β → a < b → a < c → b = c := by
  sorry

/-- Claim 7.8 ([1, Prop. 7.9]).  Case A (`λ` regular): Claim 7.9 + Fodor's lemma;
Case B (`λ` singular): reduce to Case A. -/
theorem claim_7_8 (κ lam : Cardinal.{u}) (hκ : κ.IsRegular) (hlk : lam < κ)
    (T : Type u) [PartialOrder T] [IsTree T] (hT : IsKappaTree T κ)
    (hlev : ∀ γ, #(Lev T γ) < lam) : ¬ IsAronszajn T κ := by
  sorry

/-- Theorem 7.7 (from Lemma 5.3 and Claim 7.8 with `λ = μ⁺`). -/
theorem theorem_7_7 (κ μ : Cardinal.{u}) (hκ : κ.IsRegular) (hμ : Order.succ μ < κ) :
    RamseyLA κ μ := by
  sorry

end JardenShami

אני חותך עד לכאן כדי לטפל בקמפול הקובץ
1
-/
