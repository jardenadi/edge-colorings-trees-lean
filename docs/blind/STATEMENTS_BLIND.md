Lean 4 + Mathlib statements, proofs omitted.

```lean
open Cardinal

universe v w

noncomputable section

namespace Formal

def Pairs (A : Type w) : Type w := {z : Sym2 A // ¬ z.IsDiag}

def Pairs.mk {A : Type w} (a b : A) (h : a ≠ b) : Pairs A :=
  ⟨s(a, b), by simpa [Sym2.mk_isDiag_iff] using h⟩

abbrev Coloring (A : Type w) (D : Type v) : Type (max w v) := Pairs A → D

def Coloring.color {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) (a b : A)
    (h : a < b) : D :=
  C (Pairs.mk a b h.ne)

def IsHomogeneous {A : Type w} {D : Type v} (C : Coloring A D) (B : Set A) : Prop :=
  ∀ p q : Pairs A, (∀ x ∈ p.1, x ∈ B) → (∀ x ∈ q.1, x ∈ B) → C p = C q

section LinearOrder

variable {A : Type w} [LinearOrder A] {D : Type v}

def IsAdditive (C : Coloring A D) : Prop :=
  ∃ s : D × D → D, ∀ (a b c : A) (hab : a < b) (hbc : b < c),
    C.color a c (hab.trans hbc) = s (C.color a b hab, C.color b c hbc)

def IsLocallyAdditive (C : Coloring A D) : Prop :=
  ∀ (a b c d : A) (hab : a < b) (hbc : b < c) (hcd : c < d),
    C.color b c hbc = C.color b d (hbc.trans hcd) →
      C.color a c (hab.trans hbc) = C.color a d ((hab.trans hbc).trans hcd)

def IsStarLocallyAdditive (C : Coloring A D) : Prop :=
  IsLocallyAdditive (A := Aᵒᵈ) C

def Dset (C : Coloring A D) (b : A) : Set D :=
  {t | ∃ (c : A) (h : b < c), C.color b c h = t}

def uMap (C : Coloring A D) (a b : A) (hab : a < b) : Dset C b → D :=
  fun t => C.color a (Classical.choose t.2) (hab.trans (Classical.choose_spec t.2).fst)

theorem thm_01 {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    uMap C a b hab ⟨C.color b c hbc, c, hbc, rfl⟩ = C.color a c (hab.trans hbc) := sorry

theorem thm_02 (C : Coloring A D) :
    (∀ (a b c c' : A) (hab : a < b) (hbc : b < c) (hbc' : b < c'),
        C.color b c hbc = C.color b c' hbc' →
          C.color a c (hab.trans hbc) = C.color a c' (hab.trans hbc')) ↔
      IsLocallyAdditive C := sorry

theorem thm_03 {C : Coloring A D} (hC : IsLocallyAdditive C) :
    IsAdditive C := sorry

theorem thm_04 {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    ∀ t : Dset C c, ∃ h : uMap C b c hbc t ∈ Dset C b,
      uMap C a b hab ⟨uMap C b c hbc t, h⟩ = uMap C a c (hab.trans hbc) t := sorry

end LinearOrder

abbrev Kappa (κ : Cardinal.{w}) : Type w := κ.ord.ToType

def ColoringClass (X : Type w) [LinearOrder X] : Type (max w (v + 1)) :=
  ∀ (S : Set X) (D : Type v), Coloring S D → Prop

section Classes

variable {X : Type w} [LinearOrder X]

def allColorings (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D _ => #D = μ

def add : ColoringClass.{v, w} X := fun _ _ C => IsAdditive C

def addEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsAdditive C ∧ #D = μ

def addLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsAdditive C ∧ #D < μ

def la : ColoringClass.{v, w} X := fun _ _ C => IsLocallyAdditive C

def laEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsLocallyAdditive C ∧ #D = μ

def laLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsLocallyAdditive C ∧ #D < μ

def IsRegularCardinalOrder (S : Set X) : Prop :=
  ∃ κ : Cardinal.{w}, κ.IsRegular ∧ Nonempty (S ≃o Kappa κ)

def starLa : ColoringClass.{v, w} X :=
  fun S _ C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C

def starLaEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X :=
  fun S D C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C ∧ #D = μ

def starLaLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X :=
  fun S D C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C ∧ #D < μ

def Arrow (F₁ F₂ : Set (Set X)) (𝔆 : ColoringClass.{v, w} X) : Prop :=
  ∀ S ∈ F₁, ∀ (D : Type v) (C : Coloring S D), 𝔆 S D C →
    ∃ E : Set S, Subtype.val '' E ∈ F₂ ∧ IsHomogeneous C E

end Classes

def bigSubsets (κ : Cardinal.{w}) : Set (Set (Kappa κ)) := {S | #S = κ}

end Formal
```

```lean
open Cardinal

universe v w

noncomputable section

namespace Formal

section AuxPairs

end AuxPairs

section Sec3

variable {X : Type w} [LinearOrder X]

theorem thm_05 (κ μ : Cardinal.{v}) (hκ : μ + ℵ₀ ≤ κ) (F : Set (Set X))
    (h : Arrow F F (addEq κ)) : Arrow F F (laEq μ) := sorry

theorem thm_06 (μ : Cardinal.{v}) (hμ : μ.IsStrongLimit)
    (F : Set (Set X)) (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) := sorry

theorem thm_07 (F : Set (Set X))
    (h : Arrow F F (addLt (ℵ₀ : Cardinal.{v}))) : Arrow F F (laLt (ℵ₀ : Cardinal.{v})) := sorry

end Sec3

def denseInSomeInterval (I : Type w) [LinearOrder I] : Set (Set I) :=
  {S | ∃ a b : I, a < b ∧ ∀ x y : I, a < x → x < y → y < b → ∃ s ∈ S, x < s ∧ s < y}

def Hyp1 (I : Type w) [LinearOrder I] [DenselyOrdered I] : Prop :=
  Arrow (denseInSomeInterval I) (denseInSomeInterval I) (addLt (ℵ₀ : Cardinal.{v}))

theorem thm_08 (I : Type w) [LinearOrder I] [DenselyOrdered I]
    (hfact : Hyp1.{v, w} I) :
    Arrow (denseInSomeInterval I) (denseInSomeInterval I) (laLt (ℵ₀ : Cardinal.{v})) := sorry

end Formal
```

```lean
open Cardinal

universe u v w

noncomputable section

namespace Formal

class IsTree (T : Type w) [PartialOrder T] : Prop where
  wellOrder_Iio : ∀ t : T, IsWellOrder (Set.Iio t) (fun x y => (x : T) < y)

namespace Tree

variable {T : Type w} [PartialOrder T] [IsTree T]

def ht (t : T) : Ordinal.{w} :=
  @Ordinal.type (Set.Iio t) (fun x y => (x : T) < y) (IsTree.wellOrder_Iio t)

variable (T) in

def Lev (α : Ordinal.{w}) : Set T := {t | ht t = α}

variable (T) in

def LevLt (α : Ordinal.{w}) : Set T := {t | ht t < α}

variable (T) in

def height : Ordinal.{w} := sInf {α | Lev T α = ∅}

def IsBranch (b : Set T) : Prop := IsMaxChain (· ≤ ·) b

def IsCofinalBranch (b : Set T) : Prop :=
  IsBranch b ∧ ∃ h : IsWellOrder b (fun x y => (x : T) < y),
    @Ordinal.type b (fun x y => (x : T) < y) h = height T

def IsLeaf (t : T) : Prop := IsMax t

variable (T) in

def WellPruned : Prop :=
  (∃! x : T, ht x = 0) ∧
    ∀ (x : T) (α : Ordinal.{w}), ht x < α → α < height T → ∃ y ∈ Lev T α, x < y

instance (t : T) : IsWellOrder (Set.Iio t) (fun x y => (x : T) < y) := IsTree.wellOrder_Iio t

theorem thm_09 (hT : WellPruned T)
    (hlim : Order.IsSuccLimit (height T)) : ∀ t : T, ¬ IsLeaf t := sorry

end Tree

open Tree

def IsKappaTree (κ : Cardinal.{w}) (T : Type w) [PartialOrder T] [IsTree T] : Prop :=
  height T = κ.ord ∧ ∀ α : Ordinal.{w}, α < κ.ord → #(Lev T α) < κ

section History

variable {T : Type w} [PartialOrder T] [IsTree T]

def histFun (t : T) : Set (Ordinal.{w} × T) := {p | p.2 < t ∧ ht p.2 = p.1}

variable (T) in

def HistoryTree : Set (Set (Ordinal.{w} × T)) := Set.range histFun

variable (T) in

theorem thm_10 : IsTree (HistoryTree T) := sorry

instance : IsTree (HistoryTree T) := thm_10 T

variable (T) in

def succPart : Set T := {t | ∃ β : Ordinal.{w}, ht t = Order.succ β}

theorem thm_11 (t : T) :
    ht (⟨histFun t, t, rfl⟩ : HistoryTree T) = Ordinal.lift.{w + 1} (ht t) := sorry

theorem thm_12 (g : HistoryTree T) :
    g ∈ succPart (HistoryTree T) ↔ ∃ t ∈ succPart T, g.1 = histFun t := sorry

theorem thm_13 {S : Type w} [PartialOrder S] [IsTree S]
    (g : HistoryTree T ≃o HistoryTree S) :
    ∃ g' : succPart (HistoryTree T) ≃o succPart (HistoryTree S),
      ∀ x : succPart (HistoryTree T), (g' x : HistoryTree S) = g x := sorry

theorem thm_14 (hT : ∀ t : T, ¬ IsLeaf t) :
    Nonempty (T ≃o succPart (HistoryTree T)) := sorry

theorem thm_15 {S : Type w} [PartialOrder S] [IsTree S]
    (hT : ∀ t : T, ¬ IsLeaf t) :
    Nonempty (T ≃o S) ↔ Nonempty (HistoryTree T ≃o HistoryTree S) := sorry

end History

section TreeOfColoring

variable {κ : Cardinal.{w}} {D : Type v}

def fiberRestr (C : Coloring (Kappa κ) D) (δ β : Kappa κ) (hβ : β ≤ δ) :
    Set (Kappa κ × D) :=
  {p | ∃ h : p.1 < β, p.2 = C.color p.1 δ (h.trans_le hβ)}

def treeOfColoring (C : Coloring (Kappa κ) D) : Set (Set (Kappa κ × D)) :=
  {g | ∃ (δ β : Kappa κ) (hβ : β ≤ δ), g = fiberRestr C δ β hβ}

theorem thm_16 (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := sorry

instance (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := thm_16 C

theorem thm_17 (C : Coloring (Kappa κ) D) :
    ∀ g ∈ treeOfColoring C, ∀ γ : Kappa κ, {p ∈ g | p.1 < γ} ∈ treeOfColoring C := sorry

def colorMinOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.inf

theorem thm_18 (f : Kappa κ → Fin 2) :
    IsLocallyAdditive (colorMinOf f) ∧ IsStarLocallyAdditive (colorMinOf f) ∧
      Nonempty (treeOfColoring (colorMinOf f) ≃o Kappa κ) := sorry

def colorMaxOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.sup

theorem thm_19 (f : Kappa κ → Fin 2)
    (hf : ¬ ∃ (α₀ : Kappa κ) (i : Fin 2), ∀ β, α₀ ≤ β → f β = i) :
    IsLocallyAdditive (colorMaxOf f) ∧ IsStarLocallyAdditive (colorMaxOf f) ∧
      treeOfColoring (colorMaxOf f) =
        {g | ∃ (β : Kappa κ) (i : Fin 2), g = {p | p.1 < β ∧ p.2 = i}} := sorry

end TreeOfColoring

section Enumeration

variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]

variable (κ T) in

structure Enumeration where
  
  t : Ordinal.{w} → Ordinal.{w} → T
  bijOn : ∀ α < κ.ord, Set.BijOn (t α) (Set.Iio (#(Lev T α)).ord) (Lev T α)

variable (κ T) in

def levelSup : Cardinal.{w} := ⨆ α : Kappa κ, #(Lev T (α : Ordinal.{w}))

def IsTreeColoring (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T))) :
    Prop :=
  ∀ (α δ : Kappa κ) (h : α < δ),
    ((C.color α δ h : Ordinal.{w}) < (#(Lev T (α : Ordinal.{w}))).ord) ∧
      e.t α (C.color α δ h) ≤ e.t δ 0

theorem thm_20 (hT : IsKappaTree κ T) (e : Enumeration κ T) :
    ∃! C, IsTreeColoring e C := sorry

theorem thm_21 (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    IsLocallyAdditive C := sorry

def Enumeration.Covers (e : Enumeration κ T) : Prop :=
  ∀ t : T, ∃ δ < κ.ord, t < e.t δ 0

theorem thm_22 (hκ : ℵ₀ ≤ κ) (hT : IsKappaTree κ T) (hwp : WellPruned T) :
    ∀ e : Enumeration κ T, e.Covers := sorry

def Enumeration.node (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T)))
    (β δ : Kappa κ) (_h : β ≤ δ) : T :=
  if hβ : β < δ then e.t β (C.color β δ hβ) else e.t δ 0

theorem thm_23 (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {α β δ : Kappa κ} (hαβ : α < β) (hβδ : β ≤ δ) {i : Ordinal.{w}}
    (hi : i < (#(Lev T (α : Ordinal.{w}))).ord) :
    ((C.color α δ (hαβ.trans_le hβδ) : Ordinal.{w}) = i) ↔
      ((α : Ordinal.{w}), e.t α i) ∈ histFun (e.node C β δ hβδ) := sorry

theorem thm_24 (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) ⊆ histFun (e.node C β₂ δ₂ h₂) := sorry

theorem thm_25 (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) = histFun (e.node C β₂ δ₂ h₂) := sorry

theorem thm_26 (hT : IsKappaTree κ T) (e : Enumeration κ T) (he : e.Covers)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) (t : T) :
    ∃ (β δ : Kappa κ) (h : β ≤ δ), histFun (e.node C β δ h) = histFun t := sorry

theorem thm_27 (hT : IsKappaTree κ T) (e : Enumeration κ T)
    (he : e.Covers) {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    Nonempty (treeOfColoring C ≃o HistoryTree T) := sorry

end Enumeration

theorem thm_28 {κ : Cardinal.{w}}
    {T₁ T₂ : Type w} [PartialOrder T₁] [IsTree T₁] [PartialOrder T₂] [IsTree T₂]
    (h₁ : IsKappaTree κ T₁) (h₂ : IsKappaTree κ T₂)
    (hl₁ : ∀ t : T₁, ¬ IsLeaf t) (hl₂ : ∀ t : T₂, ¬ IsLeaf t)
    (e₁ : Enumeration κ T₁) (e₂ : Enumeration κ T₂) (c₁ : e₁.Covers) (c₂ : e₂.Covers)
    {C₁ : Coloring (Kappa κ) (Kappa (levelSup κ T₁))} (hC₁ : IsTreeColoring e₁ C₁)
    {C₂ : Coloring (Kappa κ) (Kappa (levelSup κ T₂))} (hC₂ : IsTreeColoring e₂ C₂) :
    Nonempty (T₁ ≃o T₂) ↔ Nonempty (treeOfColoring C₁ ≃o treeOfColoring C₂) := sorry

end Formal
```

```lean
open Cardinal

universe w

noncomputable section

namespace Formal

open Tree

def IsAronszajn (κ : Cardinal.{w}) (T : Type w) [PartialOrder T] [IsTree T] : Prop :=
  IsKappaTree κ T ∧ ¬ ∃ b : Set T, IsCofinalBranch b

def NoAronszajn (κ : Cardinal.{w}) : Prop :=
  ∀ (T : Type w) [PartialOrder T] [IsTree T], ¬ IsAronszajn κ T

def LaArrowKappa (κ μ : Cardinal.{w}) : Prop :=
  ∀ C : Coloring (Kappa κ) (Kappa μ), IsLocallyAdditive C →
    ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H

def Hyp2 : Prop :=
  ∀ κ : Cardinal.{w}, κ.IsInaccessible →
    (NoAronszajn κ ↔
      ∀ lam : Cardinal.{w}, lam < κ → ∀ C : Coloring (Kappa κ) (Kappa lam),
        ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H)

section Aux

variable {κ : Cardinal.{w}}

end Aux

namespace Tree

variable {T : Type w} [PartialOrder T] [IsTree T]

end Tree

section TreeOfColoringAux

variable {κ : Cardinal.{w}} {D : Type w}

end TreeOfColoringAux

theorem thm_29 (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ)
    (hμ : μ < κ) (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := sorry

theorem thm_30 (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ)
    (hμ : μ < κ) :
    (∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) < μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) ↔
      LaArrowKappa κ μ := sorry

theorem thm_31 (μ : Cardinal.{w}) (hμ : ℵ₀ ≤ μ) :
    NoAronszajn (Order.succ μ) ↔ LaArrowKappa (Order.succ μ) μ := sorry

end Formal
```

```lean
open Cardinal

universe w

noncomputable section

namespace Formal

open Tree

theorem thm_32 {T : Type w} [PartialOrder T] [IsTree T] (S : Set T) : IsTree S := sorry

instance {T : Type w} [PartialOrder T] [IsTree T] (S : Set T) : IsTree S := thm_32 S

def Lim (T : Type w) [PartialOrder T] [IsTree T] : Set (Set T) := {b | IsCofinalBranch b}

def treeExp (lam μ : Cardinal.{w}) : Cardinal.{w} :=
  sSup {c | ∃ (T : Type w) (_ : PartialOrder T) (_ : IsTree T),
    height T = μ.ord ∧ #T ≤ lam ∧ c = #(Lim T)}

theorem thm_33 (lam μ : Cardinal.{w}) (hlam : ℵ₀ ≤ lam) (hμ : ℵ₀ ≤ μ) :
    treeExp lam μ ≤ lam ^ μ := sorry

def IsWeaklyCompact (κ : Cardinal.{w}) : Prop := κ.IsInaccessible ∧ NoAronszajn κ

def Hyp3 : Prop :=
  ∀ κ : Cardinal.{w}, ℵ₀ < κ →
    (Arrow (bigSubsets κ) (bigSubsets κ) (allColorings.{w, w} (2 : Cardinal.{w})) ↔
      IsWeaklyCompact κ)

section BinTree

variable {ν : Cardinal.{w}}

end BinTree

theorem thm_34 (hF : Hyp3.{w}) (κ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (hreg : κ.IsRegular) (htp : NoAronszajn κ) :
    (∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      κ.IsInaccessible := sorry

theorem thm_35 (hF : Hyp3.{w}) (κ : Cardinal.{w}) (hunc : ℵ₀ < κ) :
    IsWeaklyCompact κ ↔
      κ.IsStrongLimit ∧ NoAronszajn κ ∧
        ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ := sorry

end Formal
```

```lean
open Cardinal

universe v w

noncomputable section

namespace Formal

open Tree

def Sim {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) (β γ : A) : Prop :=
  ∃ (α : A) (hβ : β < α) (hγ : γ < α), C.color β α hβ = C.color γ α hγ

theorem thm_36 (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C) :
    (∀ (β γ α₁ α₂ : Kappa κ) (hβ : β < α₁) (hγ : γ < α₁) (h₁₂ : α₁ < α₂), β ≠ γ →
        C.color β α₁ hβ = C.color γ α₁ hγ →
          C.color β α₂ (hβ.trans h₁₂) = C.color γ α₂ (hγ.trans h₁₂)) ∧
      Equivalence (Sim C) := sorry

theorem thm_37 (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C)
    (h : Order.succ μ < κ) :
    #(Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ}) ≤ μ := sorry

def StarLaArrowKappa (κ μ : Cardinal.{w}) : Prop :=
  ∀ C : Coloring (Kappa κ) (Kappa μ), IsStarLocallyAdditive C →
    ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H

theorem thm_38 (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : μ < κ) : StarLaArrowKappa κ μ := sorry

theorem thm_39 (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ = κ) : ¬ StarLaArrowKappa κ μ := sorry

section TreeAux

variable {T : Type w} [PartialOrder T] [IsTree T]

end TreeAux

theorem thm_40 (κ lam : Cardinal.{w}) (hκ : κ.IsRegular)
    (hlamreg : lam.IsRegular) (hlam : lam < κ) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hwp : WellPruned T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∀ α : Ordinal.{w}, α < κ.ord → α.cof = lam →
      ∃ q < α, ∀ β : Ordinal.{w}, q < β → β < α →
        ∃ a ∈ Lev T q, ∀ b ∈ Lev T β, ∀ c ∈ Lev T β, a < b → a < c → b = c := sorry

theorem thm_41 (κ lam : Cardinal.{w})
    (hκ : κ.IsRegular) (hlam : lam < κ) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ¬ IsAronszajn κ T := sorry

theorem thm_42 (κ μ : Cardinal.{w})
    (hκ : κ.IsRegular) (h : Order.succ μ < κ) : LaArrowKappa κ μ := sorry

end Formal
```
