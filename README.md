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

| File | Description |
|------|-------------|
| `paper.pdf` | The full write-up of the bug, its root cause, and the commit-certificate fix. |
| `ccffix.pdf` | `ccffix` module — a FIX layer (wrapper) over `ccfraft.tla` adding the committed commit-certificate history variable and restating Leader Completeness in commit-term-keyed form. |
| `MCtrace.pdf` | `MCtrace` module — a scripted reachability witness driving the real `ccfraft` actions to a state that violates `LeaderCompletenessInv` (the bug). |
| `MCtrace_fix.pdf` | `MCtrace_fix` module — the same scripted trace checked against the fixed, commit-term-keyed invariant. |

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
