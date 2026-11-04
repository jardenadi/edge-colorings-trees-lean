# Lean 4 formalization of "A Note on Edge Colorings and Trees"

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23964479.svg)](https://doi.org/10.5281/zenodo.23964479)

A formalization in Lean 4 and Mathlib of

> Adi Jarden and Ziv Shami, *A Note on Edge Colorings and Trees*, arXiv:[2204.06874](https://arxiv.org/abs/2204.06874).

The formalization covers Sections 2–7 of the paper. It was produced with an AI coding agent (Claude Code) under a workflow in which a mathematician reviews every formal statement for fidelity before any proof is written (see [Method](#method)).

An earlier, hand-written formalization of a single theorem of Jarden and Shami is available at https://github.com/jardenadi/Jarden-Shami-Colorings.

## Highlights

Besides verifying the paper, the formalization produced the following (details in [Findings about the paper](#findings-about-the-paper)):

- **A stronger form of Theorem 6.4.** For every uncountable regular cardinal κ, the condition "λ^{μ,tr} < κ for all λ, μ < κ" is equivalent to κ being strongly inaccessible, *without assuming the tree property*. The tree property is needed only in 6.5 (weak compactness).
- **Gaps in the printed proofs.** In 4.14, 4.16, 6.4, 7.2, 7.5, 7.7 and 7.8 the printed proof omits cases (mostly finite ones) or relies on unstated assumptions. The formal proofs handle all of them.
- **Hypotheses that turned out to be unnecessary.** Besides the tree property and Fact 6.3 in Theorem 6.4 (and Fact 6.3 in Corollary 6.5), the following hypotheses are not needed, and the Lean statements are stated without them, so they are stronger than the paper's: that `T` is a `κ`-tree (Claim 4.12); that `κ` is regular and `μ < κ` (Claim 5.4, under the hypotheses of Lemma 5.3); that `μ` is infinite (Remark 6.2); `μ < κ` (Remark 7.2, and redundant in Lemma 7.3, where it follows from `μ⁺ < κ`); that `κ` is regular and `λ < κ` (Claim 7.9).

## Status

- Every theorem of Sections 2–7 is stated and proved in Lean. The project contains no `sorry` and declares no `axiom` of its own.
- The proofs rely only on the three axioms that are built into Lean and used throughout Mathlib: `propext`, `Classical.choice`, and `Quot.sound`. The `#print axioms` output for the theorems is recorded in the section files.
- Three results that the paper cites from the literature are **not reproved**. Each is stated in Lean as a proposition (`def Fact_3_4`, `def Fact_5_1`, `def Fact_6_3 : Prop`), and a theorem that needs one takes it as an explicit hypothesis. In practice only `Fact_3_4` is used: Corollary 3.5 assumes it as `hfact`. `Fact_5_1` and `Fact_6_3` are recorded as definitions only, for documentation: no theorem takes them as a hypothesis. In the paper, 5.1 only motivates Theorem 5.2, and the proofs of Theorem 6.4 and Corollary 6.5 given here do not need 6.3 (see Highlights).
- The file also contains a few auxiliary statements (marked `AUX`) that are not in the paper.

## Building

Requirements: [elan](https://github.com/leanprover/elan), the Lean version manager. The Lean toolchain is pinned in `lean-toolchain` and the Mathlib revision in `lake-manifest.json`, so the build is reproducible.

Download the pinned Mathlib build cache, so that Mathlib is not compiled from source:

```bash
lake exe cache get
```

Build the project:

```bash
lake build
```

To check which axioms a theorem uses, add `#print axioms theorem_name` to a Lean file and run it in the project environment:

```bash
lake env lean path/to/file.lean
```

The files import only the Mathlib modules they need. A blanket `import Mathlib` is much heavier on memory and build time.

## Repository structure

| Path | Contents |
|---|---|
| `MyResearchesLLMLean/Basic.lean` | Shared definitions |
| `MyResearchesLLMLean/JardenShami/Section2.lean` … `Section7.lean` | The formalization, one file per section of the paper (Section 1 has no file) |
| `MyResearchesLLMLean.lean` | Root file importing everything |
| `FIDELITY.md` | Table matching each paper statement to its Lean statement, with the fidelity review |
| `docs/STATEMENTS.md` | The Lean statements in readable form |
| `docs/blind/STATEMENTS_BLIND.md` | The de-identified statements used in the blind fidelity check (see below) |
| `docs/FORMALIZATION_PLAYBOOK.md` | The workflow used |
| `EXPERIMENT_LOG.md` | Log of the process |
| `CLAUDE.md` | The standing instructions given to the agent |
| `paper/` | LaTeX source of the paper |

## Fidelity of the statements

A formalization is only as trustworthy as its statements, and checking only the conclusion of a statement is a sanity check, not a fidelity check. Therefore:

1. All statements were written first, with `sorry`, and each was approved by a mathematician against the paper, line by line, before any proof was started. `FIDELITY.md` records the paper statement, the Lean statement and the decision for each. Where the paper leaves an assumption implicit (for example that a cardinal is infinite), the formal statement makes it explicit, and the change is recorded there.
2. Git tags mark the approved statements (`statements-v1`, `statements-v1.1`), and the proof stage was checked against them by comparing the opening lines of every declaration.
3. A **blind fidelity check** was run at the end of the statement stage. The 42 formal statements were stripped of comments and of the paper's names, and 8 were deliberately altered (for example a reversed implication, a dropped hypothesis, `∃` changed to `∀`, `≤` changed to `<`). Two independent language models (Gemini and ChatGPT) translated the stripped statements into natural language without any context. Both identified exactly the 8 altered statements. The other 34 were found faithful, with no false alarms. The check did not include the `AUX` statements. The de-identified statements are in `docs/blind/STATEMENTS_BLIND.md`, so the check can be repeated; the key listing the altered statements is available from the authors on request.

## Findings about the paper

Formalization exposed places where the printed proofs are incomplete, mostly finite special cases and unstated assumptions: 4.14, 4.16, 6.4, 7.2, 7.5, 7.7 and 7.8.
For 6.4, two gaps in the printed proof were found: the hypothesis (1) is applied to the level tree `Lev_{<α}(T)`, whose height is an ordinal rather than a cardinal, and a map used on successor levels is not injective.

Formalization also showed that a hypothesis is unnecessary. For every uncountable regular cardinal κ, the condition "λ^{μ,tr} < κ for all λ, μ < κ" is equivalent to κ being strongly inaccessible, **without assuming the tree property**. The proof goes by induction on ν < κ, showing 2^ν < κ using the binary tree 2^{<ν}, which has height ν, fewer than κ nodes, and 2^ν cofinal branches. The tree property is needed only in 6.5 (weak compactness). Both the direct implication (1) ⇒ (2) of 6.4 without Fact 6.3 and without the tree property, and the strengthening itself, are formalized in `Section6.lean` as auxiliary statements marked `AUX: not in paper`, together with the lemmas about the binary tree 2^{<ν} that they use. We did not search the literature, and we make no claim of novelty.

## Method

1. **Stage 0, statements.** All statements with `sorry`, then line-by-line fidelity approval by the mathematician, then the blind check.
2. **Stage 1, proofs.** Section by section, with a budget of about five proof attempts per statement, after which the statement is left with `sorry` and marked `STUCK`. The agent could add explicit assumptions where needed, provided it reported them.
3. **Checks before every commit.** `git diff --stat`, comparison of declaration headers with the statements tag, a count of declarations using `sorry`, and `#print axioms`.
4. **Division of labor.** The agent writes proofs. The human mathematician reviews statement fidelity and verifies the agent's claims against the paper and the code. The agent was configured not to push. Commits, tags and pushes were reviewed and done by the human.

Experiment 2, the one documented here, ran with `claude-opus-5-5` between 1 and 2 October 2026. The whole paper was formalized in about 27 hours of elapsed (wall-clock) time, measured from the first instruction given to the agent until the formalization was complete. Details are in `docs/FORMALIZATION_PLAYBOOK.md` and `EXPERIMENT_LOG.md`.

## Citing

If you use this work, please cite the paper above and this repository:

```bibtex
@misc{jarden2026lean,
  author = {Jarden, Adi},
  title  = {Lean 4 formalization of "A Note on Edge Colorings and Trees"},
  year   = {2026},
  doi    = {10.5281/zenodo.23964479},
  url    = {https://github.com/jardenadi/edge-colorings-trees-lean}
}
```

The DOI above is the Zenodo concept DOI, which always resolves to the latest version. Version-specific DOIs are listed on the [Zenodo record](https://doi.org/10.5281/zenodo.23964479).

## License

The Lean code and the documentation of this repository are released under the Apache License 2.0. See [LICENSE](LICENSE). The paper itself (`paper/`) is the authors' work and is not covered by this license.
