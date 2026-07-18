# RaftFix

**From Ambiguous Prose to a Verified Invariant: A Leader-Completeness Bug in the CCF TLA+ Specification and Its Commit-Certificate Fix**

Ovidiu Marcu · Claude

## Summary

This repository documents a formalization bug in the publicly available TLA+
specification of Microsoft's Confidential Consortium Framework (CCF). The spec's
`LeaderCompletenessInv` — a faithful-looking rendering of Raft's Leader
Completeness property — is **not** an invariant of the specification. We exhibit
a concrete, reachable 37-step execution that violates it while every other safety
invariant (including the core log-agreement property) holds.

The defect is a *formalization ambiguity*, not a protocol bug: Leader
Completeness is keyed on each entry's **authoring term** (read from current
state) instead of the term in which the entry was **committed**. The fix adds a
committed commit-certificate history variable that records the commit term, and
re-keys Leader Completeness on it.

## Contents

### Write-up (PDF)

| File | Description |
|------|-------------|
| `paper.pdf` | The full write-up of the bug, its root cause, and the commit-certificate fix. |
| `ccffix.pdf` | `ccffix` module — a FIX layer (wrapper) over `ccfraft.tla` adding the committed commit-certificate history variable and restating Leader Completeness in commit-term-keyed form. |
| `MCtrace.pdf` | `MCtrace` module — a scripted reachability witness driving the real `ccfraft` actions to a state that violates `LeaderCompletenessInv` (the bug). |
| `MCtrace_fix.pdf` | `MCtrace_fix` module — the same scripted trace checked against the fixed, commit-term-keyed invariant. |

### TLA⁺ specs

The runnable specs backing every claim in the paper are included so the results can be
reproduced from source (see [Reproducing](#reproducing)). They are grouped by the role
they play.

**Tier 1 — the reproducible artifact (minimal dependency closure).** The smallest set
that runs the paper's headline before/after: the old invariant fails, the fixed one passes.

| File | Role |
|------|------|
| `ccfraft.tla` | Upstream CCF consensus spec — **unmodified**; the subject of the bug. |
| `Network.tla` | Dependency of `ccfraft` (`INSTANCE Network`). |
| `abs.tla` | Dependency of `ccfraft` (refinement abstraction). |
| `ccffix.tla` | **The fix** — adds the `committed` commit-certificate ghost and restates Leader Completeness keyed on the commit term. |
| `MCtrace.tla` / `MCtrace.cfg` | Scripted 38-step bug witness driving the real `ccfraft` actions — old `LeaderCompletenessInv` **FAILS**. |
| `MCtrace_fix.tla` / `MCtrace_fix.cfg` | The same trace over the fix layer — new commit-term `LeaderCompleteness` **PASSES**. |

**Tier 2 — supporting evidence (safety + legality).** Backs the "the fix holds under
search" and "the pre-violation state is legal" claims.

| File | Role |
|------|------|
| `MCfix.tla` / `MCfix.cfg` | Real-`Init` safety driver for bounded BFS and deep random simulation of the fixed invariant. |
| `MCseed.tla` / `MCseed.cfg` | One-step legality seed: the pre-violation state passes the full 16-invariant suite (only `LeaderCompletenessInv` breaks on the next step). |
| `MCccfraft.tla` / `MCccfraft.cfg` | Standard CCF harness (real `Init`). |
| `MCAliases.tla` | Trace-pretty-printing aliases required by `MCccfraft`. |

**Tier 3 — negative controls (blind search does *not* find the bug).** Evidence for the
paper's "why it was missed" argument; see the [Reproducibility appendix](#reproducibility-appendix--blind-model-checking-misses-the-bug)
and the full exploration procedure in [`METHODOLOGY.md`](METHODOLOGY.md).

| File | Role |
|------|------|
| `MC3.tla` / `MC3.cfg` | 3-node blind exhaustive-BFS model — reaches only depth ~19 / ~45M states, no violation. |
| `MC5.tla` / `MC5.cfg` | 5-node blind random-simulation model — ~7.4M states, no violation. |
| `MCprobe.cfg`, `MCwindow.cfg` | **Precondition "window" probes** (checked against the `MC*` modules): trap invariants (`NoStaleLeaderProbe`, `NoIndirectWindowProbe`) that fire on the *structural precondition* of the bug. BFS never even surfaced the precondition (depth 14 / ~3.3M states) — an **unsuccessful** attempt whose failure is what motivated the scripted trace. |

> **The 38-step witness was not found by search.** All Tier 3 approaches (including the
> window probe) failed; the witness was produced by the hand-authored scripted trace
> `MCtrace.tla`. See [`METHODOLOGY.md`](METHODOLOGY.md) for the complete step-by-step
> account of how it was derived and validated.

## The trace (3 nodes, quorum = 2, StartTerm = 2)

- n1@2 appends a client entry e2 and signs it (s2), but does NOT replicate it.
- n2 times out, wins term 3 (n3 still only has the start log, so the up-to-date
  check lets n2 win), appends/signs its own e3/s3 → n2 diverges at index 5.
- n1 (stepped down to Follower@3) times out, wins term 4 with n3; `BecomeLeader`
  truncates n1 to its committable prefix, which keeps e2/s2.
- n1 appends e4/s4, replicates idx 5..8 to n3.
- `AdvanceCommitIndex` (n1) commits the term-4 signature (idx 8), **indirectly**
  committing the term-2 entry e2 (idx 5). n2 is still Leader@3 with a term-3
  entry at idx 5 ⇒ `LeaderCompletenessInv` breaks.

## Reproducing

### Prerequisites

The specs are checked with **TLC** from the standard TLA⁺ tools plus the **Community
Modules** (`ccfraft.tla` uses `FiniteSetsExt`, `SequencesExt`, `Functions`, and
`IOUtils`, which are not in the standard library). Both jars are **vendored** in `lib/`
so the artifact is self-contained — no downloads required:

- `lib/tla2tools.jar` — standard TLA⁺ tools (TLC).
- `lib/CommunityModules-deps.jar` — Community Modules.

Set a classpath pointing at both (run from this directory):

```sh
CP="lib/tla2tools.jar:lib/CommunityModules-deps.jar"
```

> The pinned jars are those used to produce the paper's results
> ([TLA⁺ tools](https://github.com/tlaplus/tlaplus/releases) and
> [Community Modules](https://github.com/tlaplus/CommunityModules/releases)); swap in
> newer releases at the same paths if you prefer.

> **The `-Dtlc2.tool.impl.Tool.cdot=true` flag is required on every run below.**
> `ccfraft.tla` uses `\cdot` (action composition), and TLC only evaluates it with
> this system property set.

All commands are run from this directory (the one containing this `README.md`).

### 1. The headline: before / after on the exact bug trace

```sh
# BEFORE — old entry-term invariant still fails (bug reproduced):
java -Dtlc2.tool.impl.Tool.cdot=true -cp "$CP" tlc2.TLC -config MCtrace.cfg     MCtrace.tla
#   => Error: Invariant LeaderCompletenessInv is violated.  (38-state trace, ~3 s)

# AFTER — fixed commit-term cert invariant holds on the SAME 38-step trace:
java -Dtlc2.tool.impl.Tool.cdot=true -cp "$CP" tlc2.TLC -config MCtrace_fix.cfg MCtrace_fix.tla
#   => Model checking completed. No error has been found.
```

At the final state: `commitIndex[n1]=8` (the term-4 signature is committed, so the
term-2 entry at index 5 is committed **indirectly**) while `n2` is `Leader@3` with a
term-3 entry at index 5. The index-5 certificate has `cterm = 4`, so for `n2` the
fixed antecedent `4 < 3` is false and `n2` is correctly exempt.

### 2. Legality of the pre-violation state (seed)

```sh
java -Dtlc2.tool.impl.Tool.cdot=true -cp "$CP" tlc2.TLC -config MCseed.cfg MCseed.tla
```

Expected: `LeaderCompletenessInv` is violated only *after* `AdvanceCommitIndex(n1)`; the
seed state itself passes all of `TypeInv, SignatureInv, MonoLogInv, LogMatchingInv,
LogConfigurationConsistentInv, MembershipStateConsistentInv, CommitCommittableIndices,
MoreThanOneLeaderInv, ElectionSafetyInv, NoLeaderBeforeInitialTerm,
MatchIndexBoundedByLogInv, QuorumLogInv, ReplicationInv, LogInv`. Only the entry-term
`LeaderCompletenessInv` fails — the keying, not CCF's safety, is the culprit. `LogInv`
(the real log-agreement property) holds throughout.

### 3. Safety of the fix — bounded BFS from the real `Init` (3 nodes, terms ≤ 4)

```sh
java -Dtlc2.tool.impl.Tool.cdot=true -cp "$CP" tlc2.TLC -config MCfix.cfg -workers auto MCfix.tla
```

Checks `LeaderCompleteness` (fixed) + `LogInv` + `CommittedTypeOK`. The `committed` ghost
grows monotonically, so the state space is unbounded for exhaustive BFS — this is a deep
partial sweep. It explores millions of states with no violation; stop it with Ctrl-C
(or wrap in `timeout 600 java ...`).

### 4. Safety of the fix — deep random simulation (primary fix evidence)

```sh
java -Dtlc2.tool.impl.Tool.cdot=true -cp "$CP" tlc2.TLC -config MCfix.cfg -simulate -depth 120 -workers auto MCfix.tla
```

Random traces up to depth 120 (well past the ~37-step indirect-commit witness), checking
the fixed invariant on every state. Expected: millions of states, no violation.

## Reproducibility appendix — blind model-checking misses the bug

The witness is ~37 steps deep and only appears under multi-term exploration, so
undirected search does **not** surface it. This is why the defect survived in the
published spec, and it is reproducible here with the Tier 3 models.

```sh
# 3-node exhaustive BFS — reaches only ~depth 19 / tens of millions of states before
# exhausting resources; no LeaderCompletenessInv violation is reported.
java -Dtlc2.tool.impl.Tool.cdot=true -cp "$CP" tlc2.TLC -config MC3.cfg -workers auto MC3.tla

# 5-node random simulation — churns millions of states without hitting the witness.
java -Dtlc2.tool.impl.Tool.cdot=true -cp "$CP" tlc2.TLC -config MC5.cfg -simulate -workers auto MC5.tla
```

The root cause of the miss is exploration budget, not luck: CCF's harness defaults
`TERM_COUNT = 0` (no multi-term exploration), so the term ladder (term 2 → 3 → 4) that
the witness needs is never built. Exhaustive 3-node BFS reached only ~depth 19 across
~45M states, and 5-node random simulation churned ~7.4M states — neither found it.

A third, sharper attempt also failed: the **precondition "window" probes**
(`MCprobe.cfg` / `MCwindow.cfg`) add trap invariants that fire not on the full violation
but on its much weaker *structural precondition* — a current leader coexisting with an
indirect commit that still holds an entry inside the entry-term window
(`NoIndirectWindowProbe`). The hope was that BFS could at least reach the precondition and
seed a forward search. It could not: at depth 14 / ~3.3M states the precondition had
**still not appeared**. Blind BFS cannot even build the window, let alone the violation —
which is precisely the evidence that undirected checking is the wrong tool here.

The bug was located only with the **directed** approach: the one-step seed (`MCseed`)
proves the target state is legal and the invariant non-inductive, and the scripted trace
(`MCtrace`) drives the real `ccfraft` actions in a fixed, hand-derived order to reach the
violation from `Init`. For the complete, step-by-step exploration procedure — every
attempt that failed, and exactly how the scripted path was derived and certified by TLC —
see [`METHODOLOGY.md`](METHODOLOGY.md).
