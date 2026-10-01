# Experiment log

Run log of the LLM-agent formalization runs (paper: Jarden & Shami, arXiv:2204.06874).

## Run: Phase 1, Section 2 (approved rows 2.1–2.10)

* Date: 2026-10-01. Agent: Claude Code (model Claude Opus 5.5).
* Scope: proofs of the 4 approved statements in `MyResearchesLLMLean/JardenShami/Section2.lean`:
  `uMap_color`, `uMap_wellDefined_iff`, `additive_isLocallyAdditive`, `uMap_comp`.
  Sections 3–5 and `reference/` were not touched.
* Start: 2026-10-01T16:59:55Z. End (last check done): 2026-10-01T17:00:53Z.
  **Duration: about 1 minute** (58 s of wall-clock time from start to the final build and axiom check;
  this does not include the time to write this log or update FIDELITY.md).
* Result: 4/4 proved, each on the first attempt (no failed attempts, no STUCK, no AUX lemmas).
  Section 2 has no sorries left.
  * `uMap_color`: a local `have` shows that any two witnesses `c, c' > b` with `C(b,c) = C(b,c')` give
    `C(a,c) = C(a,c')` (by trichotomy on `c, c'` and local additivity). This is then applied to the
    witness chosen by `uMap`.
  * `uMap_wellDefined_iff`: (→) instantiate with `c < d`; (←) trichotomy on `c, c'`.
  * `additive_isLocallyAdditive`: rewrite both `C(a,c)` and `C(a,d)` with `s`, then use the
    hypothesis `C(b,c) = C(b,d)`.
  * `uMap_comp`: `u_{b,c}(t)` is by definition `C(b,d)` for the witness `d` chosen for `t`, so it is in
    `D_b` (witness `d`), and `uMap_color` gives `u_{a,b}(C(b,d)) = C(a,d) = u_{a,c}(t)`.
* Checks: `lake build` succeeds (27 sorries left, all in Sections 3–5).
  `#print axioms` for the 4 theorems shows only `propext`, `Quot.sound`, and `Classical.choice`.
* Changes: only the proof bodies in `Section2.lean` (4 `sorry` lines replaced). No statements or
  definitions were changed, and no imports were added.
