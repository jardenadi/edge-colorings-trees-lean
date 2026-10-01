# MyResearches_LLM_Lean

Research project: formalizing mathematics papers in Lean 4 + Mathlib, and comparing LLM-agent methods for doing so.

## Language
- Talk to the user in Hebrew. Keep code, identifiers and code comments in English.

## Environment
- Lean toolchain: leanprover/lean4:v4.34.1; Mathlib is pinned to v4.34.1 (see lakefile.toml).
- Never run `lake update`, and never edit lean-toolchain, lakefile.toml or lake-manifest.json, without asking.
- Library code lives in MyResearchesLLMLean/ (the default build target). Files at the repo root, such as CardinalMulSelf.lean, are outside that target, so `lake build` does not check them.

## Current target
- Paper: "A Note on Edge Colorings and Trees" (Jarden & Shami), arXiv:2204.06874. LaTeX source: paper/edge_colorings_trees.tex.
- Goal: formalize the whole paper as it is stated in the paper.
- Read only the active text of the .tex file. Ignore everything inside \begin{comment} ... \end{comment} and everything after a % sign: these are discarded drafts and private notes (some in Hebrew), not part of the paper.
- Cite results by their number in the compiled paper and by their \label. All theorem-like environments (theorem, corollary, lemma, definition, remark, claim, ...) share one counter within each section; for example, Section 3 begins with Theorem 3.1, Corollary 3.2, Corollary 3.3.
- The paper may contain typos or small errors (for example, a displayed equivalence with a missing right-hand side). If a statement as written is false or incomplete, do not silently fix it: report it, and record it in FIDELITY.md.
- Results that the paper cites from the literature and does not prove (the `fact` environments, and statements introduced by "Recall" that have no proof in the paper): do not prove them and do not add axioms. State each one as an explicit hypothesis (a `def ... : Prop`) of the results that depend on it, with a docstring starting `FACT: cited, not proved in the paper`, and list them in FIDELITY.md.
- If a proof in the paper uses a well-known fact without proving it (for example, that every kappa-tree has a well-pruned subtree that is a kappa-tree), either prove it as an AUX lemma or state it as a FACT hypothesis, and list it in FIDELITY.md.
- Questions and open problems in the paper are not formalized.
- Reference files in reference/. Never edit them. They are not part of the build, were written in other settings, and may need adaptation to compile here:
  - ref1_statements_sorry.lean: definitions and statements with `sorry`, no proofs. Written by an LLM in an earlier experiment. Its fidelity to the paper has NOT been verified.
  - ref2_statements_partial_proofs.lean: like ref1, with some of the proofs filled in. Same caveat.
  - ref3_theorem_full_proof_restricted_F.lean: one theorem formalized by the user with LLM help, with a complete proof, but only for a restricted version in which F is always the set of all subsets of the linearly ordered set A. The paper does not assume this.
- New code goes under MyResearchesLLMLean/JardenShami/. Import every new module from MyResearchesLLMLean.lean, otherwise `lake build` will not check it.

## Workflow

### Phase 0: statements
- Do this phase only when the user asks for it.
- Read the paper. Use ref1 and ref2 as a starting point for definitions and statements, but check each one against the paper and fix whatever does not match. If ref1 and ref2 disagree on a statement, say so in FIDELITY.md. For the theorem of ref3, state the general version as in the paper (F not restricted).
- Leave every proof as `sorry`. Do not start proving in this phase.
- Put a docstring on every definition and statement citing its place in the paper (section, definition or theorem number).
- Create FIDELITY.md with two tables.
- Create FIDELITY.md with two tables.
  - Main table, one row per definition/theorem: paper statement (short paraphrase) | Lean name | plain-language back-translation of the Lean statement | based on which reference file, and changes relative to it (none, or what and why) | role | used by | doubts or choices you made | approved by user (leave empty).
  - role is your proposal and the user decides: "core" (definitions; main results that no other result depends on; statements the paper applies outside the formalized text; when in doubt, core) or "stepping stone" (a lemma, claim or corollary used only to prove other statements). used by lists the statements whose proofs in the paper use this one.
  - Cited facts table, one row per FACT hypothesis: location in the paper | statement | which results depend on it.

### Phase 1: proofs
- Start only when the user asks. Work only on statements whose row in FIDELITY.md is marked approved by the user. Do not prove statements that are not approved yet.
- Proofs in the reference files (the partial proofs in ref2, the full proof in ref3 for the restricted theorem) may be used as starting material. Adapt them and re-check them against the approved statement. Do not assume they transfer; in particular, the proof in ref3 may rely on the restriction on F.
- Work autonomously: iterate without asking the user for confirmation between attempts.
- Budget per lemma: about 5 failed attempts with genuinely different approaches. Then leave `sorry` with a comment `-- STUCK: <why>` and move on to the next lemma. Return to STUCK lemmas in a second pass.
- When stuck, before another attempt, step back and look at the paper as a whole:
  (a) Is this really a statement from the paper, or an auxiliary lemma you introduced, possibly by mistake?
  (b) Is the formalized statement actually correct (missing hypotheses, edge cases, empty or infinite cases, universe or cardinality issues)?
  (c) Does the paper's proof suggest a different route or a different decomposition?
- If a paper statement seems false or mis-formalized, do not change it. Report it to the user.
- Auxiliary lemmas are allowed and need not match the paper. Give each a docstring starting with `AUX: not in paper`, and keep them separate from the paper's statements. An auxiliary lemma may never be used to change a definition or an approved statement.

## Faithfulness rules
- Definitions and statements whose row in FIDELITY.md is marked approved by the user must not be changed, weakened or strengthened without the user's approval. The user marks approval in that file.
- Do not add axioms. Do not use `native_decide`.

## Checking your work
- Use the lean-lsp MCP tools for diagnostics and goal states while working.
- Before finishing, confirm with the compiler: `lake build` for library files; for root-level files run `lake env lean -Dweak.linter.mathlibStandardSet=true <file>.lean`.

## Final report (in Hebrew)
- Remaining `sorry`s, counted separately: paper statements, AUX lemmas, STUCK.
- The list of FACT hypotheses and of AUX lemmas added.
- Warnings.

## Git
- Do not commit or push unless asked.