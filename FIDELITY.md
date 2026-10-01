# FIDELITY — Jarden & Shami, "A Note on Edge Colorings and Trees" (arXiv:2204.06874)

Scope of this pass: **Phase 0, Sections 2 and 3 only** (first experiment).
Lean files: `MyResearchesLLMLean/JardenShami/Section2.lean`, `MyResearchesLLMLean/JardenShami/Section3.lean`
(both imported from `MyResearchesLLMLean.lean`). All proofs are `sorry`. No axioms, no AUX lemmas.

Numbering (active text only; one shared counter per section):
Section 2: 2.1 Def (coloring), 2.2 Def (homogeneous), 2.3 Def (additive, `definition additive`),
2.4 Def (locally-additive, `definition locally-additive`), 2.5 Notation (`notation local additivity`),
2.6 Def (la / *-la on a cardinal), 2.7 Remark, 2.8 Claim (`C^* is additive`), 2.9 Notation (classes),
2.10 Def (arrow). Section 3: 3.1 Theorem, 3.2 Corollary, 3.3 Corollary, 3.4 Fact (`fact dense`),
3.5 Corollary (unlabelled).

## General encoding choices (apply to all rows)

* **E1. `[A]^2`.** `Pairs A := {z : Sym2 A // ¬ z.IsDiag}` (exactly the 2-element subsets).
  A coloring is `Coloring A D := Pairs A → D`. `C(a,b)` for `a < b` is `C.color a b h`.
  Because the coloring lives on unordered pairs, the same `C` is a coloring of the reverse order `Aᵒᵈ`;
  this gives a literal encoding of "*-locally additive = locally additive w.r.t. the reverse order".
* **E2. "with μ colors"** means `#D = μ` for the codomain `D` (as in Def 2.1), not the size of the range.
* **E3. Universes.** Colors live in one fixed universe `v` (`D : Type v`, `μ κ : Cardinal.{v}`);
  the ambient linear order `X` lives in universe `w`. The paper's "class of colorings" ranges over all sets;
  here it ranges over color sets in `Type v`. Since all properties are invariant under bijections of `D`,
  this only matters through which cardinals are available.
* **E4. A cardinal `κ` with its ∈-order** is `Kappa κ := κ.ord.ToType` (same universe as `κ`).
* **E5. A class of colorings** (Notation 2.9, Def 2.10) is `ColoringClass X`: a predicate on
  `(S, D, C)` with `S : Set X`, `D : Type v`, `C : Coloring S D`; `S` carries the order induced from `X`.

## Main table

| # | Paper statement (paraphrase) | Lean name | Back-translation of the Lean statement | Reference basis and changes | Doubts / choices | Approved by user |
|---|---|---|---|---|---|---|
| 2.1 | A coloring of `A` with `μ` colors is `C : [A]^2 → D`, `#D = μ`; for linearly ordered `A`, `C(a,b) := C({a,b})` for `a<b`. | `Pairs`, `Pairs.mk`, `Coloring`, `Coloring.color` | `Pairs A` = unordered pairs of distinct elements of `A`; a coloring is any function from it to `D`; `C.color a b h` (h : a<b) is the color of `{a,b}`. | ref1 (`Sym2 A → D`). Change: restricted to non-diagonal pairs, so it is literally `[A]^2` (ref1 also colors the diagonal, which forces `D ≠ ∅` when `A ≠ ∅`). ref2 uses `A → A → D` (only `a<b` used). | E1, E2. "μ colors" is not a separate def; it is `#D = μ` inside the classes. | approved |
| 2.2 | `B ⊆ A` is homogeneous for `C` if `C ↾ [B]^2` is constant. | `IsHomogeneous` | Any two pairs whose elements are all in `B` get the same color. | ref2's formulation (all pairs equal), adapted to `Pairs`. ref1 uses `∃ d, ∀ pairs, C = d`. | ref1 vs ref2 differ when `[B]^2 = ∅` and `D = ∅` (ref1 makes it false). Chose "all values equal", which is the usual meaning of "constant" on an empty domain. | approved |
| 2.3 | `C` additive: `∃ s : D×D → D`, `∀ a<b<c`, `C(a,c) = s(C(a,b), C(b,c))`. | `IsAdditive` | Exists `s : D × D → D` with `C.color a c = s (C.color a b, C.color b c)` for `a<b<c`. | ref1 (uncurried `s`, as in paper). ref2 curried — equivalent. | none | approved |
| 2.4 | `C` locally-additive: `∀ a<b<c<d`, `C(b,c)=C(b,d) → C(a,c)=C(a,d)`. | `IsLocallyAdditive` | Same, with `C.color`. | ref1/ref2 (identical content). | none | approved |
| 2.5 | For la `C`: `D_b` = colors `C(b,c)`, `c>b`; for `a<b`, `u_{a,b} : D_b → D`, `u_{a,b}(C(b,c)) = C(a,c)`. | `Dset`, `uMap`, `uMap_color` | `Dset C b` = `{t \| ∃ c > b, C(b,c) = t}`. `uMap C a b hab t` = `C(a,c)` for a chosen witness `c>b` of `t ∈ D_b`. `uMap_color`: if `C` is la and `a<b<c` then `uMap C a b (C(b,c)) = C(a,c)`. | ref1 (subtype domain `D_b`), plus an explicit hypothesis `a<b` in `uMap` (needed to form `C(a,c)` on `[A]^2`). ref2 encodes `u` as a partial function `D → Option D`. | The paper *defines* `u` by its equation; with a choice-based def the equation becomes the statement `uMap_color` (true only for la `C`, which the Notation assumes). It is listed as part of 2.5, not as AUX. | approved |
| 2.5 Note | (unnumbered) `u_{a,b}` is well-defined for each `a<b` iff `C` is locally additive. | `uMap_wellDefined_iff` | (`∀ a<b, ∀ c,c' > b, C(b,c)=C(b,c') → C(a,c)=C(a,c')`) ↔ `IsLocallyAdditive C`. | ref1, adapted to `C.color`. ref2 does not state it. | "Well-defined" formalized as independence of the witness `c`. | approved |
| 2.6 | For a cardinal `κ`: `C` on `κ` is la if la w.r.t. ∈-order; *-la if la w.r.t. the reverse order. | `Kappa`, `IsStarLocallyAdditive` | `Kappa κ = κ.ord.ToType`. `IsStarLocallyAdditive C := IsLocallyAdditive` of `C` viewed on `Aᵒᵈ`. | ref1 / ref2 write the reversed condition by hand (both equivalent to ours); `Kappa` follows ref2 (`ToType`, universe `u`), not ref1 (`Set.Iio κ.ord`, universe `u+1`). | Paper defines *-la only for colorings of cardinals; Lean defines it for every linear order (for `κ` take `A = Kappa κ`). | approved |
| 2.7 | Every additive coloring is locally-additive. | `additive_isLocallyAdditive` | `IsAdditive C → IsLocallyAdditive C`. | ref1/ref2. | none (no proof in paper; easy). | approved |
| 2.8 | For la `C` and `a<b<c`: `u_{a,b} ∘ u_{b,c} = u_{a,c}`. | `uMap_comp` | For every `t ∈ D_c`: `u_{b,c}(t) ∈ D_b`, and `u_{a,b}(u_{b,c}(t)) = u_{a,c}(t)`. | ref1. ref2 states it as equality of partial functions. | The range condition `u_{b,c}(D_c) ⊆ D_b` is implicit in the paper; included in the statement. The paper's proof says the functions go "into μ"; for a general `D` it should be "into `D`" (harmless slip, the context of Thm 3.1 has `D = μ`). The label `C^* is additive` names the use in Thm 3.1, not this statement. | approved |
| 2.9 | `add`, `add_μ`, `add_{<μ}`, `la`, `*-la` (on a regular cardinal), `la_μ`, `la_{<μ}`, `*-la_μ`, `*-la_{<μ}`. | `ColoringClass`, `add`, `addEq`, `addLt`, `la`, `laEq`, `laLt`, `IsRegularCardinalOrder`, `starLa`, `starLaEq`, `starLaLt` | Predicates on `(S, D, C)`: e.g. `addEq μ` = `C` additive ∧ `#D = μ`; `starLaEq μ` = `S` order-isomorphic to some regular cardinal ∧ `C` *-la ∧ `#D = μ`. | ref1 (has all classes, separate universes). ref2 lacks `add`, `la`, `*-la` and uses one universe for `X` and `D`. Change: the `*-la` classes now include "on a regular cardinal" (ignored in both refs). | "*-la on a regular cardinal" interpreted as: the domain `S`, with the induced order, is order-isomorphic to a regular cardinal. Choice to approve. E3, E5. | approved |
| 2.10 | `F₁ → (F₂)_𝔆`: for every `S ∈ F₁` and coloring `C ∈ 𝔆` of `S` there is `E ⊆ S`, `E ∈ F₂`, `C↾[E]^2` constant. "`κ`" for `F` = subsets of `κ` of size `κ`; "`μ`" for `𝔆` = all colorings with `μ` colors. | `Arrow`, `bigSubsets`, `allColorings` | `Arrow F₁ F₂ 𝔆`: ∀ `S ∈ F₁`, ∀ `D : Type v`, ∀ `C : Coloring S D` in `𝔆`, ∃ `E ⊆ S` with `E ∈ F₂` (as a subset of `X`) and `E` homogeneous. `bigSubsets κ = {S ⊆ Kappa κ \| #S = κ}`. `allColorings μ` = `#D = μ`. | ref1/ref2 (same shape). | The paper reuses the letter `D` for the set in `F₁`; Lean uses `S`. Colors restricted to universe `v` (E3). | approved |
| 3.1 | If `2^μ + ℵ₀ ≤ κ` and `F → (F)_{add_κ}` then `F → (F)_{la_μ}` (`F` any family of subsets of a linear order). | `arrow_la_of_arrow_add` | For `κ μ : Cardinal.{v}` with `2^μ + ℵ₀ ≤ κ` and `F : Set (Set X)`: `Arrow F F (addEq κ) → Arrow F F (laEq μ)`. | ref1/ref2 (identical content). ref3 is NOT the same statement: there `F` is all subsets, the hypothesis is over all linear orders with `#D ≤ κ`, the coloring carries an extra map `u` and a fresh color `d0`, and since `∅` is homogeneous the conclusion `∃ E, IsHomogeneous C E` is trivially true. The general (paper) version is stated here. | Proof gap (not a statement error): the proof applies `add_κ` to `C*` with `#D* ≤ κ` colors and to `C↾B` with `μ` colors, while `add_κ` means exactly `κ` colors. Fixable by enlarging the codomain to size `κ` (Def 2.1 counts the codomain). To keep in mind for Phase 1. | approved |
| 3.2 | `μ` strong limit, `F → (F)_{add_{<μ}}` ⟹ `F → (F)_{la_{<μ}}`. | `arrow_laLt_of_arrow_addLt_strongLimit` | Same, with Mathlib's `Cardinal.IsStrongLimit` (which includes `ℵ₀`). | ref1/ref2. | (a) No proof in the paper. For uncountable `μ` it follows from the statement of 3.1 (take `κ = 2^ν + ℵ₀ < μ`). For `μ = ℵ₀` it does not (`2^n + ℵ₀ = ℵ₀ ≮ ℵ₀`); it needs the *proof* of 3.1 (then `D*` is finite). ref2 notes the same. (b) Unclear whether the paper counts `ℵ₀` as a strong limit (Cor 3.3 being separate suggests maybe not). With Mathlib's definition, 3.2 includes 3.3. Choice to approve. | approved |
| 3.3 | `F → (F)_{add_{<ℵ₀}}` ⟹ `F → (F)_{la_{<ℵ₀}}`. | `arrow_laLt_aleph0_of_arrow_addLt_aleph0` | Same. | ref1 (sorry); ref2 derives it from 3.2 with `μ = ℵ₀`. | No proof in the paper; does NOT follow from the statement of 3.1 (which needs `κ ≥ ℵ₀` colors while the hypothesis gives only finitely many). Follows from the proof of 3.1 or from 3.2 with `ℵ₀` strong limit. Reported as an incomplete derivation, statement itself is fine. | approved |
| 3.4 | (Shelah) `I` dense linear order, `F` = subsets of `I` dense in some interval: `F → (F)_{add_{<ℵ₀}}`. | `denseInSomeInterval`, `Fact_3_4` (FACT) | `denseInSomeInterval I` = `{S \| ∃ a<b, ∀ x<y in (a,b), ∃ s ∈ S, x<s<y}`. `Fact_3_4 I : Prop` = `Arrow F F (addLt ℵ₀)` for that `F`. | ref1/ref2 state it as a `theorem ... sorry`; changed to a FACT hypothesis (`def ... : Prop`) per CLAUDE.md. Interval: refs use "order-convex set with two points"; here an open interval `(a,b)`, `a<b`. | "Dense in an interval" interpreted without requiring `S ⊆ (a,b)`; for the arrow principles the two versions (and the refs' convex-set version) are equivalent when `I` is dense. "Dense linear ordering" = `[DenselyOrdered I]`; Mathlib allows `I` empty or a singleton, then `F = ∅` and everything is trivial. | approved |
| 3.5 | Same `I`, `F`: `F → (F)_{la_{<ℵ₀}}`. | `arrow_laLt_aleph0_denseInSomeInterval` | Assuming `Fact_3_4 I`: `Arrow F F (laLt ℵ₀)`. | ref1/ref2 (ref2 proves it from 3.3 and the fact). Change: the fact is an explicit hypothesis. | The paper's sentence before 3.5 cites Theorem 3.1, but the proof uses Cor 3.3 (correct: 3.1 alone does not suffice, see 3.3). | approved |

## Cited facts table (FACT hypotheses)

| Location in the paper | Statement | Lean name | Results that depend on it |
|---|---|---|---|
| Fact 3.4 (`\label{fact dense}`), cited from [Sh42, Theorem 1.3] | For a dense linear ordering `I` and `F` = subsets of `I` dense in some interval of `I`: `F → (F)_{add_{<ℵ₀}}`. | `Fact_3_4` | Corollary 3.5 (`arrow_laLt_aleph0_denseInSomeInterval`) |

No well-known unproved facts are used in the proofs of Sections 2–3 beyond elementary cardinal
arithmetic (`|D*| ≤ 2^μ` for infinite `μ`, finite for finite `μ`), which can be proved in Phase 1.

## Notes on the reference files (Sections 2–3)

* ref2: everything from Section 2 to the end of the file is inside a block comment
  (opened at line 34 with a Hebrew note), so ref2 compiles to almost nothing as is.
* ref1 vs ref2 disagreements: encoding of colorings (`Sym2` vs `A → A → D`); `IsHomogeneous`
  (`∃ d` vs all equal); `Kappa` (`Set.Iio κ.ord`, `Type (u+1)` vs `κ.ord.toType`); `u_{a,b}`
  (subtype domain vs `D → Option D`) and hence the form of Claim 2.8; ref2 lacks classes
  `add`, `la`, `*-la` and the "Note" after 2.5; ref2 derives 3.3 from 3.2 while ref1 leaves it `sorry`.
  Mathematical content otherwise agrees.
* ref3 (Theorem 3.1, restricted): see row 3.1; its statement is degenerate (trivial) as noted.

## Summary of sorries (Phase 0)

* Paper statements: 8 (`uMap_color`, `uMap_wellDefined_iff`, `additive_isLocallyAdditive`, `uMap_comp`,
  3.1, 3.2, 3.3, 3.5). AUX: 0. STUCK: 0.

## Build status

`lake build` succeeds. Warnings: 8 × `declaration uses sorry` (the 8 statements above) and
2 × Mathlib header-linter style warnings ("Copyright too short") on Section2.lean and Section3.lean
(no copyright header; harmless). Loading Mathlib in this environment takes several minutes per file (I/O).
