---------- MODULE MCtrace ----------
\* SCRIPTED reachability witness: drive the REAL ccfraft actions, in a fixed order,
\* from the real Init to a state that violates LeaderCompletenessInv. A `step` counter
\* enables exactly one action per step, so every state is reached by genuine ccfraft
\* transitions (messages are produced by the spec, not fabricated).
\*
\* Story (3 nodes, quorum=2, StartTerm=2; start leader assumed n1):
\*   - n1@2 appends a client entry e2 and signs it (s2), but does NOT replicate it.
\*   - n2 times out, wins term 3 (n3 still only has the start log, so the up-to-date
\*     check lets n2 win), then appends/sign its own e3/s3  -> n2 DIVERGES at index 5.
\*   - n1 (stepped down to Follower@3 by n2's vote request) times out, wins term 4 with n3;
\*     BecomeLeader truncates n1 to its committable prefix, which KEEPS e2/s2.
\*   - n1 appends e4/s4, replicates idx 5..8 to n3 (one NACK backup, then fills).
\*   - AdvanceCommitIndex(n1) commits the term-4 signature (idx 8), INDIRECTLY committing
\*     the term-2 entry e2 (idx 5). n2 is still Leader@3 with a term-3 entry at idx 5.
\*     => LeaderCompletenessInv breaks.
EXTENDS ccfraft, TLC

CONSTANTS NodeOne, NodeTwo, NodeThree

ToServers == {NodeOne, NodeTwo, NodeThree}
Configurations == << ToServers >>

VARIABLE step
varsS == << vars, step >>

TInit ==
    /\ step = 0
    /\ InitMessagesVars
    /\ InitCandidateVars
    /\ InitLeaderVars
    /\ preVoteStatus = [i \in Servers |-> {PreVoteDisabled}]
    /\ InitLogConfigServerVars(Configurations[1], JoinedLog)   \* multi-node start (JoinedLog)

\* Each entry: <stepGuard, Action>. Action is a REAL ccfraft action with pinned params.
Move(k, A) == step = k /\ A /\ step' = k + 1

TNext ==
    \/ Move(0,  ClientRequest(NodeOne))                      \* e2 @ idx5 (term2)
    \/ Move(1,  SignCommittableMessages(NodeOne))            \* s2 @ idx6 (term2)
    \/ Move(2,  Timeout(NodeTwo))                            \* n2 -> Candidate@3
    \/ Move(3,  RequestVote(NodeTwo, NodeThree))
    \/ Move(4,  RequestVote(NodeTwo, NodeOne))
    \/ Move(5,  Receive(NodeThree, NodeTwo))                 \* n3 UpdateTerm->3
    \/ Move(6,  Receive(NodeThree, NodeTwo))                 \* n3 grants vote
    \/ Move(7,  Receive(NodeOne, NodeTwo))                   \* n1 UpdateTerm->3 (steps down)
    \/ Move(8,  Receive(NodeOne, NodeTwo))                   \* n1 rejects (more up-to-date)
    \/ Move(9,  Receive(NodeTwo, NodeThree))                 \* n2 tallies n3's grant
    \/ Move(10, Receive(NodeTwo, NodeOne))                   \* n2 drains n1's reject
    \/ Move(11, BecomeLeader(NodeTwo))                       \* n2 Leader@3 (truncates to idx4)
    \/ Move(12, ClientRequest(NodeTwo))                      \* e3 @ idx5 (term3) -- DIVERGENCE
    \/ Move(13, SignCommittableMessages(NodeTwo))            \* s3 @ idx6 (term3)
    \/ Move(14, Timeout(NodeOne))                            \* n1 -> Candidate@4
    \/ Move(15, RequestVote(NodeOne, NodeThree))
    \/ Move(16, Receive(NodeThree, NodeOne))                 \* n3 UpdateTerm->4
    \/ Move(17, Receive(NodeThree, NodeOne))                 \* n3 grants n1
    \/ Move(18, Receive(NodeOne, NodeThree))                 \* n1 tallies grant
    \/ Move(19, BecomeLeader(NodeOne))                       \* n1 Leader@4 (truncate KEEPS e2/s2)
    \/ Move(20, ClientRequest(NodeOne))                      \* e4 @ idx7 (term4)
    \/ Move(21, SignCommittableMessages(NodeOne))            \* s4 @ idx8 (term4)
    \/ Move(22, AppendEntries(NodeOne, NodeThree))           \* AE idx7 -> n3 rejects (gap)
    \/ Move(23, Receive(NodeThree, NodeOne))                 \* n3 NACK (lastLogIndex=4)
    \/ Move(24, Receive(NodeOne, NodeThree))                 \* n1 backs sentIndex to 4
    \/ Move(25, AppendEntries(NodeOne, NodeThree))           \* AE idx5 (e2)
    \/ Move(26, Receive(NodeThree, NodeOne))                 \* n3 appends e2
    \/ Move(27, Receive(NodeOne, NodeThree))                 \* matchIndex=5
    \/ Move(28, AppendEntries(NodeOne, NodeThree))           \* AE idx6 (s2)
    \/ Move(29, Receive(NodeThree, NodeOne))                 \* n3 appends s2
    \/ Move(30, Receive(NodeOne, NodeThree))                 \* matchIndex=6
    \/ Move(31, AppendEntries(NodeOne, NodeThree))           \* AE idx7 (e4)
    \/ Move(32, Receive(NodeThree, NodeOne))                 \* n3 appends e4
    \/ Move(33, Receive(NodeOne, NodeThree))                 \* matchIndex=7
    \/ Move(34, AppendEntries(NodeOne, NodeThree))           \* AE idx8 (s4)
    \/ Move(35, Receive(NodeThree, NodeOne))                 \* n3 appends s4
    \/ Move(36, Receive(NodeOne, NodeThree))                 \* matchIndex=8
    \/ Move(37, AdvanceCommitIndex(NodeOne))                 \* commit idx8 -> indirectly idx5  => VIOLATION

TraceSpec == TInit /\ [][TNext]_varsS
===================================
