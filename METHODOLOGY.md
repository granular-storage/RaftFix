# How the bug was found — exploration procedure

This document records the full search procedure that led to the 38-step witness
violating CCF's entry-term `LeaderCompletenessInv`, **including the approaches that did
not work**. The headline result is short:

> **The 38-step witness was *not* found by model-checking search.** Blind exhaustive
> BFS, blind random simulation, and a targeted *precondition probe* all failed to reach
> it. The witness was produced by a **hand-authored scripted trace** (`MCtrace.tla`) that
> drives the real `ccfraft` actions along one fixed path to the violation.

Recording the failed attempts is deliberate: they are the evidence for *why* the defect
survived in the published spec, and they define the boundary between what undirected
checking can and cannot reach here.

--------------------------------------------------------------------------------

## Why undirected search cannot reach it

The witness has two properties that put it outside the reach of blind checking under any
practical budget:

1. **It is deep.** The violating state is at **step 37** — an entry authored in term 2,
   left un-replicated, surviving two leader changes (term 3, then term 4), and finally
   *indirectly* committed by a term-4 signature. Exhaustive breadth-first search does not
   get close to that depth before exhausting memory.

2. **It needs a term ladder that the default harness never builds.** The execution
   requires terms to climb 2 → 3 → 4. CCF's model-checking harness defaults
   `TERM_COUNT = 0` (no multi-term exploration), so the very state shape the bug needs is
   pruned away before search begins. Even with `TERM_COUNT` raised, the combined depth +
   branching makes exhaustive coverage of the relevant region infeasible.

The consequence: the bug is *reachable* (it is a genuine behavior of CCF's `Spec`), but
it is not *discoverable* by throwing states at TLC. It has to be **directed**.

--------------------------------------------------------------------------------

## The procedure, in order

The attempts below are listed in the order they were tried. The first three are
**negative results** (search); the last two are the **directed** approach that worked.

### 1. Blind exhaustive BFS — `MC3.tla` / `MC3.cfg` *(did not find it)*

3-node model, checking the real `LeaderCompletenessInv`. Breadth-first search from the
real `Init`.

- **Outcome:** reached only **depth ~19** after **~45M states**, never approaching the
  required depth ~37. No violation. Stopped on resource exhaustion.

### 2. Blind random simulation — `MC5.tla` / `MC5.cfg` *(did not find it)*

5-node model, random deep traces, checking `LeaderCompletenessInv`, `LogInv`, and
`QuorumLogInv`.

- **Outcome:** churned **~7.4M states** along random paths without hitting the witness.
  Random walks are extremely unlikely to stumble onto the exact 37-action sequence.

### 3. Precondition probe — `MCprobe.cfg` / `MCwindow.cfg` *(did not find it — this is the "window probe")*

Rather than wait for the full violation, this attempt asked TLC to surface the much
weaker **structural precondition** that must exist *before* `LeaderCompletenessInv` can
break. The idea: if BFS could reach even the precondition, that reachable near-violation
state could seed a forward search to the real violation.

Two trap invariants were added ahead of `LeaderCompletenessInv` (defined in
`MC3.tla`/`MC5.tla`):

- `NoStaleLeaderProbe` — asserts no state has two leaders `i`, `j` with
  `currentTerm[i] < currentTerm[j]` (a lower-term leader coexisting with a higher one).
- `NoIndirectWindowProbe` — the decisive one: asserts no state has a current leader `i`
  and another node `j` whose committed prefix was **sealed at a term above `i`'s term**
  (an indirect commit) yet still contains a committed entry whose **own term is `<= i`'s
  term** — i.e. the entry-term "window" in which the buggy invariant would fire.

`MCprobe.cfg` checks both probes; `MCwindow.cfg` is the focused variant checking
`NoIndirectWindowProbe` alone (it was derived from `MCprobe.cfg` by dropping
`NoStaleLeaderProbe`). Both were run as BFS so the *shortest* path to any probe violation
would surface fast.

- **Outcome — UNSUCCESSFUL:** at **depth 14 / ~3.3M states** the probe had **still not
  surfaced the precondition** (`NoIndirectWindowProbe` was never violated), and
  `LeaderCompletenessInv` remained clean. Blind BFS cannot even build the
  indirect-commit-with-stale-leader *window* within budget, let alone the full violation.

This is the informational value of the window probe: it is a **negative result** that
localises *why* search fails — the failure is upstream of the violation, at the
precondition. It is what motivated abandoning search entirely and driving the trace by
hand.

### 4. Directed one-step seed — `MCseed.tla` / `MCseed.cfg` *(proves legality)*

A hand-built pre-violation state, checked in a single step against CCF's **full
16-invariant suite**.

- **Outcome:** the seed state passes `TypeInv, SignatureInv, MonoLogInv, LogMatchingInv,
  LogConfigurationConsistentInv, MembershipStateConsistentInv, CommitCommittableIndices,
  MoreThanOneLeaderInv, ElectionSafetyInv, NoLeaderBeforeInitialTerm,
  MatchIndexBoundedByLogInv, QuorumLogInv, ReplicationInv, LogInv` — and only
  `LeaderCompletenessInv` breaks on the next step (`AdvanceCommitIndex(n1)`). This proves
  the state is **legal**, so the invariant is genuinely non-inductive rather than the
  state being an artifact. (`LogInv`, the real log-agreement safety property, holds
  throughout.)

### 5. The scripted trace — `MCtrace.tla` / `MCtrace.cfg` *(the witness)*

The decisive artifact. `MCtrace.tla` reaches the violation from CCF's real `Init` by
driving the real `ccfraft` actions in a **fixed, hand-authored order** — a directed path,
not a search.

--------------------------------------------------------------------------------

## How the scripted path itself was derived

The 38-move sequence was not guessed and was not extracted from a search hit (there was
none — see #1–#3). It was constructed in four steps:

1. **Start from the known counterexample shape.** The target is the classic Raft
   **Figure-8 indirect commit**, from Raft's own **Figure 8** (Ongaro & Ousterhout,
   *In Search of an Understandable Consensus Algorithm*, USENIX ATC 2014; and Ongaro's
   Ph.D. dissertation, §5.4). Figure 8 is Raft's illustration of *why a leader may not
   commit an earlier-term entry merely because it is stored on a majority*: an entry
   authored in a low term `Te` can be replicated, survive a leader change, and only be
   committed later — **indirectly** — when a higher-term leader commits a current-term
   entry on top of it, at which point its commit term `Tc > Te`. Panel 8(e) is the unsafe
   overwrite case; the witness here uses the indirect-commit variant **plus one surviving
   stale leader** at a term between `Te` and `Tc`, so that an intervening leader is wrongly
   required (by entry-term keying) to hold the entry. This is the exact shape under which
   entry-term keying is known to be unsound (the same defect exhibited in the
   granular-storage `raft.tla` work), so it defined *what* end-state to aim for.

2. **Pin down and legality-check the end-state (the seed, #4).** The desired
   near-violation state was hand-built as `MCseed` and checked against CCF's full
   16-invariant suite. A single `AdvanceCommitIndex(n1)` broke **only**
   `LeaderCompletenessInv`, with every other invariant holding — confirming the target is
   a *legal* CCF state and the invariant is non-inductive. This established the state was
   worth reaching, but "legal ≠ reachable from `Init`".

3. **Hand-derive the exact action sequence that lands in it.** To upgrade "legal" to
   "reachable", the precise path from CCF's real `Init` to that state was worked out by
   reasoning about `ccfraft`'s own action semantics — e.g. that `BecomeLeader` truncates a
   new leader to its committable prefix (which is what *keeps* the signed term-2 entry
   when `n1` reclaims term 4), and that `AppendEntries` backs its sent index off by one on
   a `NACK` before filling the follower's log. The result was the ~37-action script:
   create the term-2 entry on `n1` (unreplicated) → elect `n2`@3 → `n1` steps down and
   reclaims term 4 → replicate to `n3` (one NACK backup, then fill) → `AdvanceCommitIndex`
   indirectly commits the term-2 entry while `n2` stays a divergent `Leader`@3.

4. **Encode it and let TLC validate every step.** The path was written into `MCtrace.tla`
   as a `step`-guarded disjunction of real `ccfraft` actions and run. TLC acts as the
   checker of the construction: if any `Move`'s pinned action were not actually enabled in
   the state produced by the previous move, the trace would deadlock at that step instead
   of advancing — so a clean run to `step = 38` is itself proof that the hand-authored path
   is executable by the unmodified spec. TLC confirmed the run and reported
   `LeaderCompletenessInv` violated at the final step, with all other safety invariants
   holding throughout.

In short: **domain knowledge chose the target, the seed proved it legal, action-semantics
reasoning produced the path, and TLC certified that the path is a genuine reachable
execution.** Search was never able to supply the path — that is exactly why the scripted
trace was necessary.

--------------------------------------------------------------------------------

## What "scripted trace" means

`MCtrace.tla` is not a new protocol and it does not fabricate messages. It is a thin
driver over the unmodified `ccfraft` spec:

```tla
VARIABLE step
Move(k, A) == step = k /\ A /\ step' = k + 1   \* enable exactly ONE real action at step k
```

`TNext` is then a hand-written disjunction of 38 `Move` clauses (steps 0..37), each a
**genuine `ccfraft` action with pinned parameters**:

```tla
TNext ==
    \/ Move(0,  ClientRequest(NodeOne))            \* e2 @ idx5 (term 2)
    \/ Move(1,  SignCommittableMessages(NodeOne))  \* s2 @ idx6 (term 2)
    \/ Move(2,  Timeout(NodeTwo))                  \* n2 -> Candidate@3
    ...
    \/ Move(11, BecomeLeader(NodeTwo))             \* n2 Leader@3 (truncates to idx4)
    \/ Move(12, ClientRequest(NodeTwo))            \* e3 @ idx5 (term 3) -- DIVERGENCE
    ...
    \/ Move(19, BecomeLeader(NodeOne))             \* n1 Leader@4 (truncate KEEPS e2/s2)
    ...
    \/ Move(37, AdvanceCommitIndex(NodeOne))       \* commit idx8 -> indirectly idx5 => VIOLATION
```

Because the `step` counter admits exactly one real action per step and every action is a
real `ccfraft` transition (the peer messages are produced by the spec itself, e.g. via
`RequestVote` / `AppendEntries` / `Receive`), the resulting 38-state behavior is a
**genuine reachable execution of CCF's `Spec`**. Finding one such execution that violates
`LeaderCompletenessInv` proves the property is not an invariant.

"Scripted" refers only to the *order* being authored by hand (a directed path to the
target), in contrast to BFS/simulation which explore the whole reachable set. This is the
standard TLA⁺ technique for exhibiting a deep, hard-to-reach witness (it mirrors the
granular-storage `MCTraceLC` driver).

The trace story (3 nodes, quorum = 2, `StartTerm = 2`):

- `n1@2` appends a client entry `e2` and signs it (`s2`), but does **not** replicate it.
- `n2` times out and wins term 3 (`n3` still holds only the start log, so the up-to-date
  check lets `n2` win); `n2` appends/signs its own `e3`/`s3` — `n2` **diverges** at idx 5.
- `n1` (stepped down to Follower@3) times out and wins term 4 with `n3`; `BecomeLeader`
  truncates `n1` to its committable prefix, which **keeps** `e2`/`s2`.
- `n1` appends `e4`/`s4` and replicates idx 5..8 to `n3` (one NACK backup, then fills).
- `AdvanceCommitIndex(n1)` commits the term-4 signature (idx 8), **indirectly** committing
  the term-2 entry `e2` (idx 5). `n2` is still Leader@3 with a term-3 entry at idx 5 ⇒
  `LeaderCompletenessInv` breaks.

--------------------------------------------------------------------------------

## Outcome summary

| # | Method | Files | Result |
|---|--------|-------|--------|
| 1 | Blind exhaustive BFS (3-node) | `MC3.*` | ❌ depth ~19 / ~45M states — no violation |
| 2 | Blind random simulation (5-node) | `MC5.*` | ❌ ~7.4M states — no violation |
| 3 | **Precondition "window" probe** (BFS) | `MCprobe.cfg`, `MCwindow.cfg` | ❌ depth 14 / ~3.3M states — precondition never even surfaced |
| 4 | Directed one-step legality seed | `MCseed.*` | ✅ proves the violating state is legal (16 invariants) — non-inductiveness |
| 5 | **Directed scripted trace** | `MCtrace.*` | ✅ **the 38-step witness** — `LeaderCompletenessInv` violated |

Net: undirected checking (#1–#3, including the window probe) does not find the bug; the
directed seed (#4) proves the target state is legal, and the **scripted trace (#5) is the
witness**. The fix is then validated on that same trace by `MCtrace_fix.tla` and swept
more broadly by `MCfix.tla` — see [`README.md`](README.md).
