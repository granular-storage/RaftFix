---------- MODULE MCfix ----------
\* Safety driver for the FIX: real CCF MCInit + the `committed` cert history
\* variable + the commit-term-keyed LeaderCompleteness, checked by BFS and by
\* simulation. 3-node static config (where the bug was found), terms up to 4.
EXTENDS ccffix, TLC

CONSTANTS NodeOne, NodeTwo, NodeThree

ToServers == {NodeOne, NodeTwo, NodeThree}
Configurations == << ToServers >>
TermCount == 2          \* StartTerm(2) + 2 => terms reach 4 (enough for indirect commit)
RequestCount == 2

CCF == INSTANCE ccfraft

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

MCInit ==
    /\ InitMessagesVars
    /\ InitCandidateVars
    /\ InitLeaderVars
    /\ preVoteStatus = [i \in Servers |-> {PreVoteDisabled}]
    /\ IF Cardinality(Configurations[1]) = 1
       THEN InitLogConfigServerVars(Configurations[1], StartLog)
       ELSE InitLogConfigServerVars(Configurations[1], JoinedLog)

\* Spec = real (bounded) CCF behaviour, with the committed cert ghost tracked by FixNext.
MCFixInit == MCInit /\ committed = {}
MCFixSpec == MCFixInit /\ [][FixNext]_fixVars

\* committed is in the view so invariant checking distinguishes states by it (sound).
Symmetry == Permutations(Servers)
View == << reconfigurationVars, messageVars, serverVars, candidateVars, leaderVars, logVars, committed >>
================================
