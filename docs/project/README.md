# Project management

Status: current · Updated: 2026-10-07

This folder is how work on starked-bitcoin is planned, tracked and handed
over. It applies equally to people and to AI agents. **The repository is
the only source of truth for project state.** Chat history, agent memory and
personal notes are not; if something matters, it goes here.

## The files

| File | Answers | How it changes |
|---|---|---|
| [status.md](status.md) | *Where are we right now, and what do I do next?* | **Rewritten** at the end of every session. Always current, never historical. |
| [roadmap.md](roadmap.md) | *What is done, what remains, and in what order?* | Items change status in place. New items are added with an ID. |
| [log.md](log.md) | *What happened, when, and what did we learn?* | **Append-only.** Newest entry at the top. Never edit old entries; correct them in a new one. |
| [decisions.md](decisions.md) | *Why is it built this way?* | **Append-only.** Reversing a decision means adding a new entry that supersedes the old one. |

## Starting a session (pick up work)

Do these steps in order, without skipping any.

1. **Read [status.md](status.md) fully.** It names the current item, the exact
   next step, anything in flight and any blockers.
2. **Verify the state.** Run every command in
   [status.md § Verify](status.md#verify-the-current-state). If a check fails,
   *stop*: fixing it is the first task. Log the failure.
3. **Check for uncommitted work** (`git status`). status.md must explain
   every uncommitted file. If it doesn't, find out before touching it.
4. **Read the roadmap entry** for the current item and the docs it links to.
5. If status.md is missing, stale (its HEAD doesn't match `git log -1`) or
   unclear, reconstruct the state from `git log`, roadmap.md and the latest
   log entry. Rewrite status.md *before* starting new work.

## During a session

- **One roadmap item in progress at a time.** If you have to switch, set the
  first item back to `todo` or `blocked`, with a note.
- **Commit at every green checkpoint:** tests pass and Lean builds. Never
  commit a `sorry`, a failing test or stale `airs/*.json`.
- **Commit messages:** `<area>: <what changed>`, where area is `Lean`,
  `Header chain vN`, `IR`, `Docs`, `Zig` and so on. The body says why, and
  names the theorem for proof commits.
- **Git:** commit locally. **Never push, open PRs, or touch remotes without
  explicit approval from the project owner.**
- **Long operations** (builds over 5 minutes, benchmarks): write the command
  and its expected duration into status.md *before* starting, so an
  interrupted session can be resumed.
- **A new design choice** gets a decisions.md entry when you make it.
- **Discovering work:** add it to roadmap.md (backlog) right away, with an ID.
  Don't keep a private to-do list.

## Ending a session (log progress)

Do this before stopping, even if the work is unfinished.

1. Bring the tree to a clean state: commit, or document every uncommitted
   file in status.md.
2. Add a **log entry** at the top of [log.md](log.md), using its template.
3. Update the item statuses in [roadmap.md](roadmap.md).
4. **Rewrite [status.md](status.md)** using its template. The "Next step" must
   be concrete enough that someone with no context can start in 5 minutes:
   file, function or theorem, and what to do.
5. Commit with `Docs: session log <date>`. It can be combined with the last
   work commit.

## Definition of done

**An AIR version is done** when every item in
[guides/adding-an-air.md](../guides/adding-an-air.md) is checked:

- spec plus `#guard`s;
- layout doc;
- Lean definition;
- regenerated JSON;
- Zig witness;
- satisfy, tamper and refuse tests;
- soundness theorem with standard axioms only;
- [verification.md](../reference/verification.md) updated;
- roadmap, log and status updated.

**Any other item is done** when:

- the roadmap entry's "Done when" is met;
- the tests and the Lean build are green;
- the docs are updated per the [documentation rules](../../README.md#documentation-rules).

## Statuses

`todo` · `in-progress` · `blocked (<reason / who unblocks>)` · `done (<commit>)` · `dropped (<decision ID>)`

## Escalation: when to stop and ask the owner

Stop, record the question under status.md "Needs owner", and ask, when:

- a decision changes the scope, trust model or public statement of a proof;
- an action is outward-facing: pushing, filing issues or PRs upstream, or
  publishing benchmarks;
- the work would modify code outside this repo, including the stwo-zig
  submodule or the owner's other checkouts;
- the same failure persists after two genuinely different approaches;
- legal, licensing or security-disclosure questions come up.

Everything else: decide, record the decision, continue.
