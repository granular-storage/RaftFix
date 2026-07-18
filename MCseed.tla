---------- MODULE MCseed ----------
\* DIRECTED probe: start from a hand-built state that is ONE AdvanceCommitIndex
\* step before the predicted entry-term-keying violation, and let TLC explore
\* forward while checking the FULL CCF invariant suite.
\*
\* Scenario (3 nodes, quorum=2; StartTerm=2):
\*   - n1 = Leader@4. log = [r2,s2,r2,s2, e2(5), s2(6), e4(7), s4(8)], commitIndex=4.
\*       matchIndex[n1][n3]=8 => AdvanceCommitIndex(n1) will jump commitIndex 4 -> 8,
\*       INDIRECTLY committing the term-2 entry e2 at index 5 (sealed by the term-4 sig).
\*   - n3 = Follower@4 with the identical log (the committing quorum {n1,n3}).
\*   - n2 = STALE Leader@3. log = [r2,s2,r2,s2, e3(5), s3(6)] -- DIVERGES at index 5.
\*
\* After AdvanceCommitIndex(n1): CommittedTermPrefix(n1, currentTerm[n2]=3) includes
\* index 5 (entry-term 2 <= 3) but log[n2][5] is the term-3 entry => LeaderCompletenessInv
\* should break, IF this state is legal/reachable. The full invariant suite tells us
\* whether the seed is a legal CCF state.
EXTENDS ccfraft, TLC

CONSTANTS NodeOne, NodeTwo, NodeThree

ToServers == {NodeOne, NodeTwo, NodeThree}
Configurations == << ToServers >>          \* single static config (reconfig never fires)
TermCount == 1                              \* freeze elections (cap = StartTerm+1 = 3)
RequestCount == 2

CCF == INSTANCE ccfraft

\* ---- log-entry helpers ----
re(t, cfg) == [term |-> t, contentType |-> TypeReconfiguration, configuration |-> cfg]
sg(t)      == [term |-> t, contentType |-> TypeSignature]
en(t)      == [term |-> t, contentType |-> TypeEntry]

SL    == << re(2, {NodeOne}), sg(2), re(2, ToServers), sg(2) >>   \* the joined start log (idx 1-4)
N1log == SL \o << en(2), sg(2), en(4), sg(4) >>                   \* idx 5-8
N3log == N1log
N2log == SL \o << en(3), sg(3) >>                                 \* idx 5-6 (divergent at idx 5)

Cfgs == (3 :> ToServers)

InitNear ==
    /\ messages          = [s \in ToServers |-> <<>>]
    /\ currentTerm       = (NodeOne :> 4 @@ NodeTwo :> 3 @@ NodeThree :> 4)
    /\ leadershipState   = (NodeOne :> Leader @@ NodeTwo :> Leader @@ NodeThree :> Follower)
    /\ membershipState   = [s \in ToServers |-> Active]
    /\ votedFor          = (NodeOne :> NodeOne @@ NodeTwo :> NodeTwo @@ NodeThree :> NodeOne)
    /\ isNewFollower     = [s \in ToServers |-> TRUE]
    /\ log               = (NodeOne :> N1log @@ NodeTwo :> N2log @@ NodeThree :> N3log)
    /\ commitIndex       = [s \in ToServers |-> 4]
    /\ configurations    = [s \in ToServers |-> Cfgs]
    /\ hasJoined         = [s \in ToServers |-> TRUE]
    /\ retirementCompleted = [s \in ToServers |-> {}]
    /\ votesGranted      = (NodeOne :> {NodeOne, NodeThree} @@ NodeTwo :> {NodeTwo, NodeThree} @@ NodeThree :> {})
    /\ sentIndex         = ( NodeOne   :> (NodeOne :> 8 @@ NodeTwo :> 4 @@ NodeThree :> 8) @@
                             NodeTwo   :> [s \in ToServers |-> 6] @@
                             NodeThree :> [s \in ToServers |-> 0] )
    /\ matchIndex        = ( NodeOne   :> (NodeOne :> 0 @@ NodeTwo :> 0 @@ NodeThree :> 8) @@
                             NodeTwo   :> [s \in ToServers |-> 0] @@
                             NodeThree :> [s \in ToServers |-> 0] )
    /\ preVoteStatus     = [s \in ToServers |-> {PreVoteDisabled}]

\* ---- bounded action overrides (keep Next finite; elections frozen) ----
MCCheckQuorum(i) == FALSE

MCChangeConfigurationInt(i, newConfiguration) ==
    /\ Len(Configurations) > 1
    /\ configurations[i] # <<>>
    /\ \E configCount \in 1..Len(Configurations)-1:
        /\ Configurations[configCount] = CCF!MaxConfiguration(i)
        /\ CCF!ChangeConfigurationInt(i, Configurations[configCount+1])

MCTimeout(i) ==
    /\ currentTerm[i] < StartTerm + TermCount
    /\ Cardinality({ s \in GetServerSetForIndex(i, commitIndex[i]) : leadershipState[s] = Candidate}) < 1
    /\ CCF!Timeout(i)

MCRcvProposeVoteRequest(i, j) ==
    /\ currentTerm[i] < StartTerm + TermCount
    /\ CCF!RcvProposeVoteRequest(i, j)

MCClientRequest(i) ==
    /\ FoldSeq(LAMBDA e, count: IF e.contentType = TypeEntry THEN count + 1 ELSE count, 0, log[i]) <= RequestCount
    /\ CCF!ClientRequest(i)

MCSignCommittableMessages(i) ==
    /\ log[i] # <<>> => \lnot (Last(log[i]).contentType = TypeSignature /\ Last(log[i]).term = currentTerm[i])
    /\ CCF!SignCommittableMessages(i)

MCSend(msg) ==
    /\ ~ \E n \in Network!Messages:
        /\ n.dest = msg.dest /\ n.source = msg.source /\ n.term = msg.term /\ n.type = AppendEntriesRequest
    /\ ~ \E n \in Network!Messages:
        /\ n.dest = msg.source /\ n.source = msg.dest /\ n.term = msg.term /\ n.type = AppendEntriesResponse
    /\ CCF!Send(msg)

MCseedSpec == InitNear /\ [][Next]_vars
===================================
