---------- MODULE MC5 ----------
\* 5-node driver for ccfraft.tla, built to probe whether the entry-term-keyed
\* LeaderCompletenessInv can break at >=5 servers / >=3 terms.
\* Single static 5-node configuration (no reconfiguration), pre-vote disabled,
\* CheckQuorum disabled (so a stale leader can persist), bounded terms/requests.
EXTENDS ccfraft, TLC

CONSTANTS NodeOne, NodeTwo, NodeThree, NodeFour, NodeFive

Configurations == << {NodeOne, NodeTwo, NodeThree, NodeFour, NodeFive} >>
ASSUME Configurations \in Seq(SUBSET Servers)

\* StartTerm = 2 (defined in ccfraft). TermCount=3 => terms reach up to 5.
TermCount == 3
RequestCount == 2

ToServers == UNION Range(Configurations)

CCF == INSTANCE ccfraft

\* Disable CheckQuorum so leaders never voluntarily step down -> stale leaders persist.
MCCheckQuorum(i) == FALSE

\* Reconfiguration disabled (single config -> Len(Configurations)=1 -> never enabled).
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

\* Pre-vote fully disabled on every node (plain-Raft election path).
MCInit ==
    /\ InitMessagesVars
    /\ InitCandidateVars
    /\ InitLeaderVars
    /\ preVoteStatus = [i \in Servers |-> {PreVoteDisabled}]
    /\ IF Cardinality(Configurations[1]) = 1
       THEN InitLogConfigServerVars(Configurations[1], StartLog)
       ELSE InitLogConfigServerVars(Configurations[1], JoinedLog)

MCSpec == MCInit /\ [][Next]_vars

Symmetry == Permutations(Servers)
View == << reconfigurationVars, messageVars, serverVars, candidateVars, leaderVars, logVars >>

----
\* ---- Directed probes (checked as invariants; a TLC "violation" = a reachable witness) ----

\* P1: a stale lower-term leader coexists with a strictly-higher-term leader.
\* This is the breeding ground for the entry-term-keying counterexample.
NoStaleLeaderProbe ==
    ~ \E i, j \in Servers :
        /\ leadershipState[i] = Leader
        /\ leadershipState[j] = Leader
        /\ currentTerm[i] < currentTerm[j]

\* P2: the full precondition -- a current leader i, and a node j whose committed
\* prefix was sealed at a term ABOVE i's term (indirect commit) yet contains a
\* committed entry whose own term is <= i's term (the entry-term-keyed window).
\* If LeaderCompletenessInv is to break, a state matching P2 must exist first.
NoIndirectWindowProbe ==
    ~ \E i, j \in Servers :
        /\ i # j
        /\ leadershipState[i] = Leader
        /\ commitIndex[j] > 0
        /\ log[j][commitIndex[j]].term > currentTerm[i]
        /\ \E k \in 1..commitIndex[j] : log[j][k].term <= currentTerm[i]
================================
