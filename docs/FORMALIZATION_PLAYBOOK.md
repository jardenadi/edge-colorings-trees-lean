
# Playbook: formalizing a mathematics paper in Lean 4 with an LLM agent

Status: working draft, based on one project (one paper, Sections 2-5 so far). Everything below is an
observation from that project, not a validated result.

## 1. What Lean can and cannot verify

- Lean verifies that a proof proves the statement as written. It cannot verify that the statement
  is the paper's statement. Fidelity of definitions and statements is verified only by a human.
- Therefore: separate the work into a statements phase and a proofs phase, with a human approval
  gate between them, and keep a frozen record of the statements (section 4).
- Run sanity checks on statements, because a faithful-looking statement can be vacuous.
  Example from our project: a restricted version of a theorem whose conclusion was
  trivially true (the empty set is homogeneous), so its complete proof proved nothing.
  Check: is the conclusion trivially satisfiable, are hypotheses contradictory, what happens for
  empty or finite cases?

## 2. Repository layout

- paper/: the LaTeX source, the single source of truth. Tell the agent to ignore commented-out
  blocks and % notes, and to cite results by the compiled numbering (shared counters per section).
- reference/: earlier attempts (other models, older versions). Read-only, not part of the build,
  treated as unverified.
- Library/<PaperName>/SectionN.lean: one file per section of the paper.
- FIDELITY.md: one row per definition and theorem (see section 3).
- CLAUDE.md: instructions to the agent (template in section 7).
- EXPERIMENT_LOG.md: one entry per run (section 6).

## 3. FIDELITY.md

Main table columns: number in paper | paper statement (short) | Lean name |
back-translation of the Lean statement into plain mathematics | basis and changes relative to
reference files | doubts and choices | approved by user.

- Include encoding choices in a separate list (for example how unordered pairs, universes and
  cardinals are encoded), and refer to them from rows.
- The back-translation written by the same agent that wrote the Lean is not an independent check.
  Have a different reader (a human, or a different model without access to the agent's table)
  translate the Lean back to mathematics, and compare with the paper.
- The agent must report errors and typos in the paper (we found a missing right-hand side in
  a displayed equivalence, and a remark that is false for finite cardinals). It must not silently
  fix them, and it must record them in a row.
- Results the paper cites without proof are stated as explicit hypotheses
  (a def ... : Prop whose docstring begins with FACT), never as axioms. List them in a separate
  table with the results that depend on them.
- Facts "well known" but used without proof inside a paper's proofs: either prove them as auxiliary
  lemmas (docstring AUX: not in paper) or treat them as FACT hypotheses.


## 3a. What the human must check: the fidelity core

Not every statement needs human fidelity review. Split the statements into two kinds.

- Core: (a) the definitions, (b) the main results of the paper that no other result depends on,
  (c) any statement the paper applies outside the formalized text.
- Stepping stone: a lemma, claim or corollary that serves only to prove other statements.

Why stepping stones need no fidelity review: if one is mis-formalized, either it becomes unprovable
(a visible failure), or it is provable but the statements that use it do not follow from it
(again visible). The error is caught by the pipeline, provided the chain ends in core statements
that were reviewed.

Caveats.
- The protection works only if each stepping stone is actually used in the proof of a core
  statement. Check this from the proofs, not only from the paper: inspect the proof term, or
  collect the constants a proof uses with a small meta-program (Expr.getUsedConstants; untested
  here). A stepping stone that is not used downstream is unprotected and must be reviewed.
- A stepping stone that differs from the paper's lemma but is sufficient for its use is harmless
  for the paper's results, but it is not the paper's lemma. Record this in FIDELITY.md.
- A false or vacuous stepping stone is dangerous only together with a trivial core statement.
  Hence: review the core, including a vacuity check of every core statement.
- Borderline cases (for example corollaries stated without proof in the paper) should be treated
  as core.

Workflow consequences.
- Each row of FIDELITY.md carries a role (core or stepping stone) and the list of statements that
  use it. The agent proposes the role; the human decides.
- The human review record (the "approved" column) covers the core. The frozen tag
  (statements-vN) still contains the statements of the whole paper.

## 4. Freeze the statements

- When statements of a section are approved, record the approval in FIDELITY.md and create a git tag
  (for example statements-sec2-3), and push the tag.
- When all statements are approved, tag statements-v1: the whole paper with sorry in place of
  every proof.
- Later, check mechanically that proofs did not change statements:
  git diff <tag> HEAD -- <file> | grep "^-" | grep -v "^---" | grep -v "sorry"
  should print nothing. (The check shows removed lines other than sorry.)
- Do this from the start of the project, not after the first proofs have replaced the sorries.

## 5. Phases

Phase 0 (statements). The agent writes definitions and statements with sorry, a docstring citing the
paper for each, and FIDELITY.md. It does not prove anything. The human reviews and marks approved.
Run it on a few sections at a time, review, then continue, because a wrong encoding found late is
expensive.

Phase 1 (proofs). Only on approved statements. Budget about 5 genuinely different attempts per
lemma, then leave sorry with a STUCK comment and move on, and return in a second pass. When stuck,
step back to the paper: is this really a statement of the paper, is the formalized statement
correct, does the paper's proof suggest another route? Auxiliary lemmas are allowed and marked
AUX. A statement marked approved is never changed without the human.

## 6. Checks that do not rely on the agent's report

- Build with lake build, and count sorries from the compiler output (declaration uses sorry),
  not from the agent's summary.
- #print axioms for each proved statement: only propext, Classical.choice, Quot.sound are acceptable;
  sorryAx means a hidden sorry.
- No new axioms and no native_decide.
- Use minimal Mathlib imports. In our project replacing a full import of Mathlib with two modules
  reduced the build from 8928 to 974 jobs.
- Log every run in EXPERIMENT_LOG.md: model, Claude Code version, repository commit at the start,
  instructions version (commit), duration, human interventions, usage. Note: the session counter
  in the agent resets on clearing or restarting the session, and the account-level percentages
  include other usage on the same account.

## 7. Permissions and isolation

- Run the agent inside a dev container. Check what is mounted (/proc/mounts) and that the host
  drives are not visible.
- Allow rules: the Lean MCP server, lake build, lake env lean, edits of .lean files. Deny git push.
  Permission rules are a convenience, not a security boundary; git history is the real protection.
- Do not edit files the agent is editing (especially FIDELITY.md) while it runs.
- Reading is always safe.

## 8. Template: CLAUDE.md for a new paper

(Copy the CLAUDE.md of the current project, replace the section "Current target", and keep the
sections Language, Environment, Workflow, Faithfulness rules, Checking your work, Final report, Git.)

## 9. Open questions

- How much of the review can be delegated to an independent model reader?
- Whether the observed times and costs scale to proofs that are not routine.
- A principled treatment of vacuity checks.


## 3a. What the human must check: the fidelity core

Not every statement needs human fidelity review. Split the statements of the paper into two kinds.

- Fidelity-critical statements (the fidelity core): statements whose correctness in Lean is NOT
  checked by anything else. These are (a) the definitions, (b) the main results of the paper that
  other results do not depend on, and (c) any statement used in an application outside the formalized
  text (for example a claim the paper makes about an external notion).
- Intermediate statements (stepping stones): lemmas, claims and corollaries that serve only to prove
  other statements. If such a statement is mis-formalized, one of two things happens: it becomes
  unprovable (the proof fails, which is visible), or it is provable but a downstream result that
  uses it does not follow (the downstream proof fails, or, if the downstream statement is itself
  checked, the error is exposed there). Either way, the error is caught by the pipeline and the human
  need not review the statement.

Caveat (vacuity). The protection works only if the downstream statement is faithful and
non-vacuous. A stepping stone that is false or trivially true, combined with a downstream result
that is also trivial, passes everything. Hence the chain must end in checked statements:
the definitions and the main results. Also a stepping stone that is too weak but still sufficient for its use is harmless for the paper's results, but it is not
the paper's lemma. Record this in FIDELITY.md if it matters.

Consequences for the workflow.
- Mark each row of FIDELITY.md as core or stepping stone, and list under each stepping stone the
  results that use it.
- The human reviews and approves the core. Stepping stones are approved automatically if the chain
  closes, that is, if each is used in the proof of a core statement.
- The frozen tag (statements-vN) contains the files of the whole paper, but the human
  review record covers only the core. Store the core list in FIDELITY.md under a section "Core".





 