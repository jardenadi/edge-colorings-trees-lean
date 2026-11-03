
# Playbook: formalizing a mathematics paper in Lean 4 with an LLM agent
> Note: commit hashes in this document refer to the history of the private development repository and differ from the hashes in this repository. The tags are preserved.
> Note: commit hashes in this document refer to the history of the private development repository and differ from the hashes in this repository. The tags are preserved.

Status: working draft, based on one project: Jarden & Shami, "A Note on Edge Colorings and Trees"
(arXiv:2204.06874), formalized completely (Sections 2-7, statements and proofs; tag proofs-v1).
Everything below is an observation from that project, not a validated result. The document is for
the mathematician who directs the work; CLAUDE.md remains the agent's instructions.

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

Columns in the final version of the table (one row per definition or statement): number in paper |
paper statement (short paraphrase) | Lean name | back-translation | basis in the reference files and
changes | role (core or stepping stone, section 3a) | used by | doubts and choices | approved by user.
In Phase 1 the agent appends a note "Phase 1: ..." to the doubts cell of every row it proves (how it
was proved, which hypotheses turned out unused, which gaps in the paper's proof it met). Groups of
auxiliary lemmas get one row per section ("AUX (Section N, Phase 1)") listing their names; AUX rows are
not approved, since they are not statements of the paper.

FACT versus AUX.
- FACT: a result the paper cites and does not prove. It becomes a def ... : Prop and an explicit
  hypothesis of every result that uses it; it is never proved and never an axiom. In this project:
  Fact_3_4, Fact_5_1, Fact_6_3.
- AUX: anything the agent proves that is not a statement of the paper (helper lemmas, a well-known
  fact used inside a proof, a stronger form of a paper statement). AUX lemmas may not be used to change
  a definition or an approved statement. In this project the "well-known" fact in the proof of Claim
  7.8 (every κ-tree has a well-pruned subtree that is a κ-tree) started as a FACT hypothesis and was
  turned into an AUX lemma by the user's decision; it was then proved.

Sanity check versus fidelity check. Checking only the conclusion of a Lean statement (is it the
conclusion the paper states?) is a sanity check, not a fidelity check. Fidelity also requires the
hypotheses, the quantifiers and the encodings (how pairs, colorings, trees, heights, cardinals are
represented) to match the paper. Example: Proposition 7.5 has the paper's conclusion in every reading,
but without the standing assumption of its subsection it is false (section 9).


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
- Moving a theorem block within a file (needed when a proof uses a later claim; in this project
  4.15, 4.17, 5.2 and 5.4 were moved) also produces removed lines. Inspect such hits by hand; they are
  not changes of statements.
- Tags of this project: statements-sec2-3, statements-sec2-5, statements-v1, statements-v1.1 (the
  whole paper with sorry) and proofs-v1 (all proofs, no sorry). See section 11 for why there are two
  statements-v1 tags.

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

In this project Phase 1 ran section by section (2, 3, 4, 5, 6, 7); each run ended with an
uncommitted working tree that the human reviewed and committed (Section 3 took two commits). No STUCK lemma
occurred. When a section contained rows not yet approved (4.3, 4.16-4.19, 5.4, 6.2, 7.2, 7.3, 7.9), the
human asked explicitly to prove them too and approved them after reading; the agent recorded this in
the row.

Commit discipline.
- Approval commits and proof commits are separate. An approval commit changes only the approval
  column of FIDELITY.md (and summary sentences that mention approval); a proof commit changes .lean
  files and the Phase 1 notes. This keeps "what the human approved" and "what the agent proved"
  separable in the history. (In the history of this project one approval change, 6.2, was committed
  under a copy of the preceding Phase 1 commit message, 80a716c; the content was right, the message was
  not. Check the message as well as the diff.)
- The human, not the agent, runs git commit, git tag and git push. The agent's permissions deny
  git push, and its instructions forbid commits and tags unless asked.

Checks before each commit (run by the human or requested from the agent, never taken from the
agent's summary alone):
- git diff --stat: only the expected files changed (for a proof commit: SectionN.lean and
  FIDELITY.md; for an approval commit: FIDELITY.md only).
- Compare the statement lines with the statements tag (the grep command of section 4).
- Count `declaration uses sorry` in the output of lake build, and compare with the summary in
  FIDELITY.md.

Final check (before tagging proofs-v1):
- #print axioms on every declaration of every section file: only propext, Classical.choice,
  Quot.sound (some declarations use fewer or none). In this project: 210 declarations, no sorryAx and
  no other axiom.
- git diff statements-v1.1 HEAD on the .lean files: no statement changed (only proofs, moved blocks,
  and added AUX lemmas).
- lake build with no `declaration uses sorry`; then tag proofs-v1.

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

## 6a. Memory and imports

Status: observed, not measured.

- On a machine with 16 GB of RAM, replacing `import Mathlib` with focused imports of only the modules
  needed is what made it possible to finish the work in the last days, when builds and servers got
  stuck for lack of memory.
- A possible explanation: every Lean process (lake build, the LSP server of the editor, the
  lean-lsp-mcp server used by the agent) loads all of Mathlib when a file imports it, and several such
  processes run at the same time.
- Under WSL2 the Linux virtual machine gets by default about 50% of the host's memory. The limit can be
  raised in `.wslconfig` (in the Windows user's home folder) and takes effect after `wsl --shutdown`.
- In this project (from git log):
  - f75dde2 (2026-09-30, initial commit): the template files import Mathlib.
  - 2b8084e (2026-10-01 09:10, Phase 0 of Sections 2-3): Section2.lean imports Mathlib;
    Section3.lean imports Section2.
  - a139a9b (2026-10-01 11:16, "Replace import Mathlib with minimal imports in Section2"):
    `import Mathlib` replaced by `import Mathlib.Data.Sym.Sym2` and
    `import Mathlib.SetTheory.Cardinal.Regular` (the 8928 to 974 jobs of section 6).
  - fb310ef (Phase 0 of Sections 4-5): Section4.lean adds `import Mathlib.Data.Sym.Sym2.Order`.
  - f271958 (Phase 1 of Section 5): Section5.lean adds `import Mathlib.SetTheory.Cardinal.Pigeonhole`.
  - No later file of the library imports all of Mathlib. The agent's scratch files imported a project
    section instead of Mathlib; FIDELITY.md records that loading full `import Mathlib` took about
    15 minutes in this environment.
- Rule: start every new file with focused imports, and let the agent add a Mathlib module only when a
  lemma it needs is missing (and say so in its report).

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

## 9. Mathematical findings: what the formalization exposed in the paper

Each item: the gap, and how it was handled. Numbers are those of the compiled paper. All are recorded
in the corresponding rows of FIDELITY.md.

- Remark 4.14 (an enumeration covering a well-pruned κ-tree exists "for every cardinal κ"). False for
  finite κ ≥ 1: covering is defined with the strict order (t <_T t^0_δ), so a node on the top level
  of a finite tree is below no t^0_δ (e.g. κ = 1, the one-point tree). The paper's proof assumes κ
  regular. Handled: the hypothesis ℵ₀ ≤ κ was added (approved change of the statement); the proof
  showed that regularity is not needed (a bijection κ ≃ κ × κ suffices).
- Claim 4.16 (inside the proof of 4.15). The displayed equivalence lacks its right-hand side
  "= i"; also i must range over i < μ_α (otherwise t^i_α is undefined), not i < μ. Handled: stated
  with "= i" and i < μ_α (approved reading), proved as clause (1) of the paper's proof.
- Theorem 6.4, direction (1) ⇒ (2). Two gaps in the proof (not in the statement): (a) hypothesis (1)
  is applied to Lev_{<α}(T), a tree of height α where α is an ordinal that need not be a cardinal (and
  the tree may be finite), while Definition 6.1 defines λ^{μ,tr} only for infinite cardinals μ ≤ λ;
  (b) the map t_β ↦ {t_γ : t_γ <_T t_β} is not injective on successor levels (two nodes with the same
  predecessors, differing in the last value 0/1). Handled: not repaired; 6.4 was proved by a
  different and stronger argument (section 10).
- Proposition 7.5. Read without the standing assumption of Subsection 7.1 (κ = cf(κ)), it is false for
  μ ≤ 1: for μ = 0, κ = 1 and μ = 1, κ = 2 every coloring is *-locally additive and κ itself is
  homogeneous. Handled: the standing assumption is an explicit hypothesis κ.IsRegular; Mathlib's
  notion of regular includes ℵ₀ ≤ κ, so μ is infinite and the paper's proof works.
- Theorem 7.7 (κ regular, μ⁺ < κ: κ → (κ)_{la_μ}). The proof goes through Lemma 5.3, which assumes κ
  uncountable, so the case κ = ℵ₀ (μ finite) is not covered. Handled without a separate Ramsey
  argument and without a new hypothesis: the proof of (1) ⇒ (2) of Lemma 5.3 does not use
  uncountability, so it was stated as an AUX lemma for every regular κ (laArrowKappa_of_forall_branch),
  and Claim 7.8 was proved also for κ = ℵ₀.
- Claim 7.8 (a κ-tree with levels of size < λ < κ, κ regular, is not κ-Aronszajn). The proof splits
  into Case A (λ regular, uses cf(α) = λ and Fodor's lemma, hence needs λ infinite and κ uncountable)
  and Case B (λ singular), and omits finite λ and κ = ℵ₀; Case B uses that the level sizes do not
  decrease, which holds in a well-pruned tree, while "without loss of generality well-pruned" is said
  only in Case A. Handled: the statement was kept and proved in all cases along a different route
  (pass to a well-pruned subtree; level sizes are then non-decreasing, hence eventually constant n;
  for finite n the restriction maps are bijections; for infinite n the diagonal argument of Claim 7.9
  at a suitable level gives a contradiction; so some node does not split, and the nodes above it form
  a cofinal branch). No Fodor's lemma, no stationary sets.
- Remark 7.2. The paper says "By local additivity"; the argument uses *-local additivity, the standing
  assumption of the subsection. A slip of wording; the proof confirmed the intended reading.

## 10. Central case: Theorem 6.4 in a stronger form

Theorem 6.4 of the paper: for κ uncountable, regular and with the tree property, (1) λ^{μ,tr} < κ for
all λ, μ < κ is equivalent to (2) κ strongly inaccessible. The paper's proof of (1) ⇒ (2) builds a tree
from a coloring F : [κ]^2 → 2, uses (1) to show it is a κ-tree, the tree property to get a κ-branch,
and Fact 6.3 to conclude.

What was formalized instead (by the user's decision, after the agent proposed it): the AUX theorem
treeExp_lt_iff_isInaccessible_of_isRegular proves the same equivalence for every uncountable regular
κ, without the tree property and without Fact 6.3. Theorem 6.4 follows at once; its statement is
unchanged, and its hypotheses "tree property" and Fact 6.3 remain as unused hypotheses (unused-variable
warnings).

The argument. (2) ⇒ (1): λ^{μ,tr} ≤ λ^μ (Remark 6.2) and λ^μ < κ for strongly inaccessible κ.
(1) ⇒ (2): show 2^ν < κ for every ν < κ, by induction on ν. For finite ν this is clear. For infinite
ν, consider the full binary tree 2^{<ν} (functions from an ordinal β < ν to 2, ordered by extension).
Its height is ν; it has at most Σ_{β<ν} 2^{|β|} nodes, which is < κ by the induction hypothesis and the
regularity of κ; and every f : ν → 2 gives its own cofinal branch, so it has at least 2^ν cofinal
branches. Applying (1) with μ = ν and λ = max(ν, number of nodes) gives 2^ν ≤ λ^{ν,tr} < κ. Hence κ is
a strong limit, and being uncountable and regular, strongly inaccessible.

The lesson: formalizing exposes unnecessary hypotheses. Here the proof needed neither the tree
property nor the cited Fact 6.3, and it avoided both gaps of the paper's proof (section 9). We expect
the stronger statement to be elementary folklore. TODO: find a reference in the literature.

## 11. Process incidents and lessons

- A statements tag created before the approval commit. statements-v1 was created on commit 26860f8
  (Approve core statements of Sections 6-7) before the approval marks of Sections 6-7 were committed
  in 1b44718; statements-v1.1 was then created on 1b44718 (the difference between the two tags is
  FIDELITY.md only). TODO: details of how the remote tag was corrected. Rule: commit the approvals
  first, check git status is clean, then tag; never move a pushed tag silently: create a new tag
  (as v1.1 here) or document the move.
- An unclosed quote in git tag -m. The shell waited for the closing quote, which looked like a
  stuck terminal. TODO: which tag and how it was resolved. Rule: write the tag message on one line, or
  put it in a file and use git tag -F file; if the prompt changes to "> ", press Ctrl-C and retype.
- git add -p was confusing (interactive hunk selection; the agent cannot run interactive git
  commands at all). TODO: what exactly went wrong. Rule: stage whole files by name
  (git add FIDELITY.md ...) and check git diff --cached --stat before committing.
- Instructions left in the input line without pressing Enter. The agent never received them.
  TODO: which instruction and when. Rule: after giving an instruction, check that it appears in the
  conversation; when the agent's report does not address it, it was not sent.
- A Phase 1 note in FIDELITY.md that became stale after approval. The note in row 6.2 still said "Not
  yet approved; proved at the user's explicit request" after the row was approved; the user noticed
  and asked to fix it (fixed in 5a38584). While writing this playbook, the same stale note was found
  in rows 4.3 and 4.16-4.19 ("Row not yet approved ..."), which are approved; they are not fixed yet.
  Rule: an approval is not only a change of the approval column; search the row and the summary
  section for "not yet approved" and update them in the same approval commit.

## 12. Data

Sources: FIDELITY.md at each commit, EXPERIMENT_LOG.md, git log (commit times are UTC).

AUX declarations (marked "AUX: not in paper"), all proved:

| Section | AUX |
|---|---|
| 2 | 0 |
| 3 | 8 |
| 4 | 52 |
| 5 | 22 (20 in Phase 1 of Section 5, 2 added in Phase 1 of Section 7) |
| 6 | 16 |
| 7 | 17 (including exists_wellPruned_subtree) |
| Total | 115 |

Number of `declaration uses sorry` (as recorded in FIDELITY.md at each commit):

| Stage | Commit | sorry |
|---|---|---|
| Phase 0, Sections 2-3 | 2b8084e | 8 |
| Phase 0, Sections 2-5 | fb310ef | 31 |
| Phase 1, Section 2 done | 4406118 | 27 |
| Phase 0, Sections 2-7 | ba62f8d | 38 |
| Well-pruned subtree as AUX (tag statements-v1) | 26860f8 | 39 |
| Section 3 partly proved (tag statements-v1.1) | 1b44718 | 36 |
| Phase 1, Section 3 done | a6b9d2e | 35 |
| Phase 1, Section 4 done | d6d38c9 | 15 |
| Phase 1, Section 5 done | f271958 | 12 |
| Phase 1, Section 6 done | 79dc772 | 8 |
| Phase 1, Section 7 done (tag proofs-v1 on 9af7ce8) | 5a38584 | 0 |

Time. Agent working time is recorded only for Phase 1 of Section 2: about 1 minute (EXPERIMENT_LOG.md,
58 s from start to the final build and axiom check). For the other runs only commit times are known.
The intervals below run from the previous commit to the commit of the section; they include the
human's review and are not agent working time.

| Run | From (commit, UTC) | To (commit, UTC) | Interval |
|---|---|---|---|
| Phase 0, Sections 2-3 | 12a32ac 06:23 (2026-10-01) | 2b8084e 09:10 | 2 h 47 min |
| Phase 0, Sections 4-5 | 0f96a11 12:42 | fb310ef 13:10 | 28 min |
| Phase 0, Sections 6-7 | 529b108 20:39 | ba62f8d 20:56 | 17 min |
| Phase 1, Section 3 | 1b44718 23:06 (2026-10-01) | a6b9d2e 05:27 (2026-10-02) | 6 h 21 min (overnight; partial commit c25b2f8 at 23:12) |
| Phase 1, Section 4 | a6b9d2e 05:27 | d6d38c9 06:12 | 45 min |
| Phase 1, Section 5 | a0b4467 07:44 | f271958 08:04 | 20 min |
| Phase 1, Section 6 | 02099f4 08:12 | 79dc772 08:51 | 39 min |
| Phase 1, Section 7 | 80a716c 09:47 | 5a38584 10:23 | 36 min |

TODO: agent working time, number of human interventions and token or cost usage for every run except
Phase 1 of Section 2 (EXPERIMENT_LOG.md has only that run).

## 13. Limitations and notes for reuse

- The cited facts Fact_3_4, Fact_5_1 and Fact_6_3 remain explicit hypotheses; they are not proved.
  Fact_5_1 is used by no proof; Fact_6_3 is a hypothesis of 6.4 and 6.5 but no proof uses it
  (section 10).
- Question 7.6 (does μ⁺ → (μ⁺)_{la_μ} hold?) is an open problem and is not formalized. Question 4.9 is
  not formalized either.
- Claim 7.8 is proved along a route different from the paper's (section 9); Theorem 6.4 is proved from
  a stronger AUX theorem (section 10). Claim 7.9 is proved as in the paper, but 7.8 does not use it
  directly (both use the AUX lemma le_mk_lev_of_splitting).
- Several hypotheses of unchanged statements turned out unused (unused-variable warnings): hT in 4.12,
  hκ and hμ in 5.4, hμ in 6.2, hF and htp in 6.4, hμ in 7.2, hκ and hlam in 7.9. They were kept because
  the statements are the paper's.
- Statements changed with the user's approval: 4.14 (hypothesis ℵ₀ ≤ κ), 4.16 (reading "= i",
  i < μ_α), and the encoding choices recorded in FIDELITY.md. No statement was changed in Phase 1.

## 14. Open questions

- How much of the review can be delegated to an independent model reader?
- Whether the observed times and costs scale to proofs that are not routine.
- A principled treatment of vacuity checks.