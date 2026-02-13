---
name: code-review
description: Review code using parallel specialist agents
user-invocable: true
---

# Code Review

Review code specified by `$ARGUMENTS`, using the project's code review policies.

## Step 1: Figure Out What to Review

The user's `$ARGUMENTS` could be anything. Interpret them:

| Arguments | What to do |
|-----------|-----------|
| *(empty)* | Run `git diff -- '*.rs'` and `git diff --cached -- '*.rs'`. Review the uncommitted changes to `.rs` files. If no changes, say so and stop. |
| A file path | Read that file. Review it. |
| A file path with lines (`foo.rs:50-80`) | Read that file. Focus the review on those lines (but read the full file for context). |
| Multiple file paths | Read all of them. Review each, and also look for consistency across them. |
| A PR number or URL (`#123`, URL) | Fetch the PR diff with `gh pr diff`. Review the diff. |
| A module or concept name | Use Grep/Glob to find where that code lives. Read those files. Review them. |
| A mix of the above | Handle each part, then review the union. |

If you're unsure what the user means, ask before launching reviewers.

## Step 2: Discover and Launch Reviewers

1. Use Glob to find all `.claude/code-review/*.md` files.
2. Read `.claude/code-review/standards.md` (master standards shared by all
   reviewers).
3. For EACH policy file **except `standards.md`**, launch a `general-purpose`
   Task agent (use model `sonnet`). Give each agent a prompt constructed from
   this template — adapt it based on what you're reviewing:

   > You are reviewing Rust code in the ragu project (a recursive proof system /
   > proof-carrying data framework).
   >
   > Read these files:
   > - `.claude/code-review/standards.md` (master standards that always apply)
   > - `.claude/code-review/{focus}.md` (your specific review policy)
   {if focus is "documentation", also include:}
   > - `.claude/review/writing.md` (shared writing rules)
   > - `.claude/review/math.md` (shared math rules)
   >
   > **What to review:** {describe the specific content — file paths, line
   > ranges, the diff, whatever the user specified. If reviewing a diff, include
   > the diff text and list the full file paths for context.}
   >
   > {If the scope is a diff or a narrow range, add: "Focus on the specified
   > content. Flag issues in surrounding text ONLY if the specified content
   > introduced an inconsistency with it."}
   >
   > {If the scope spans multiple files or a concept, add: "Pay attention to
   > consistency across the files. Flag contradictions, redundancies, or
   > inconsistencies as they span these locations."}
   >
   > For each finding:
   > - **Location**: file path and line number (or quoted text)
   > - **Issue**: what's wrong, specifically
   > - **Suggestion**: a concrete fix, not just "improve this"
   > - **Severity**: `must-fix` (correctness bug, safety issue, clear violation)
   >   or `suggestion` (improvement, not wrong as-is)
   >
   > Stay within your policy's scope. Be specific. If you find no real issues,
   > say so — don't manufacture problems.

   Launch ALL agents in parallel (multiple Task calls in one message).

## Step 3: Run Automated Checks

In parallel with the reviewer agents (launched in Step 2), run automated checks:

1. `cargo clippy --workspace --all-features -- -D warnings`
2. `cargo fmt --all -- --check`
3. `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all --document-private-items`

If any check fails, include the relevant diagnostics alongside reviewer results
in the synthesis step.

## Step 4: Synthesize

Once all agents return, organize findings by location (file path, then line
number). If multiple reviewers flagged overlapping concerns, merge them. Present:

- **Must-fix** issues first
- **Suggestions** second
- For each finding, note which reviewer(s) identified it

If the review scope was cross-file or conceptual, add a short section about
cross-cutting observations (consistency, naming conventions, etc.).

## Step 5: Validate Proposed Changes

After synthesizing findings, but before presenting them to the user:

1. Collect all proposed changes (the "suggestion" field from each finding) into
   a single numbered list — the **proposed plan**.
2. For EACH policy file (same set as Step 2 — every `.claude/code-review/*.md`
   except `standards.md`), launch a `general-purpose` Task agent (model
   `sonnet`) with this prompt:

   > You are validating a set of proposed code changes against review policies.
   >
   > Read these files:
   > - `.claude/code-review/standards.md` (master standards)
   > - `.claude/code-review/{focus}.md` (your policy)
   {if focus is "documentation":}
   > - `.claude/review/writing.md` (shared writing rules)
   > - `.claude/review/math.md` (shared math rules)
   >
   > Here is the proposed plan of changes:
   > {numbered list of proposed changes with locations and suggested rewrites}
   >
   > For each proposed change, check whether applying it would **introduce** a
   > violation of any rule in your policy or the master standards. Only flag
   > real conflicts — do not restate rules that are already satisfied.
   >
   > For each conflict found:
   > - **Change #**: which proposed change
   > - **Rule violated**: quote the relevant policy text
   > - **Conflict**: explain specifically how the suggestion violates the rule
   > - **Resolution**: suggest how to fix the suggestion to comply
   >
   > If no proposed changes conflict with your policy, say so.

   Launch ALL agents in parallel.

3. Merge validation feedback into the findings. For each conflict:
   - If the validator provides a compliant alternative, replace the original
     suggestion with the corrected version.
   - If the conflict has no clear resolution, annotate the finding with the
     conflict so the user can decide during triage.

4. If any suggestions were corrected, briefly note it in the synthesis output.

## Step 6: Triage

Two modes based on how the review was invoked:

### Local Mode (file paths, diff, concept)

Use AskUserQuestion to let the user decide the disposition of each finding (or
group of closely related findings). For each, offer:

- **Fix** — apply the suggested fix now
- **Skip** — drop this finding

If there are many findings, batch them into logical groups and ask about each
group rather than each individual finding.

For each finding the user chose to **fix**:

1. Read the target file to get the current content.
2. Apply the suggested change using the Edit tool.
3. After applying all fixes, run `just ci_local` to verify.
4. Briefly report what was changed and any CI results.

### PR Mode (`#123` or PR URL)

Use AskUserQuestion to let the user decide whether to post a synthesis comment
on the PR via `gh pr comment`. Format findings as a numbered list with code links
using the full commit SHA and line ranges (`L[start]-L[end]`).
