---- MODULE skeenAlgorithm ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS NPROCESS, MESSAGES

VARIABLES pc, sent, pending, received, lc, messages

ASSUME (NPROCESS \in Nat) /\ (MESSAGES # {})
ASSUME (NPROCESS >= 2)

vars == << pc, sent, pending, received, lc, messages >>

Processes == 1 .. NPROCESS

Init ==
    /\ messages = [i \in Processes |-> MESSAGES]
    /\ pending = [i \in Processes |-> {}]
    /\ received = [i \in Processes |-> {}]
    /\ sent = [i \in Processes |-> [bc |-> {}, ts |-> {}, sn |-> {}]]
    /\ pc \in [Processes -> {"BCAST", ""}]
    /\ lc = [i \in Processes |-> 0]

Broadcast(message) == 
    [i \in Processes |-> [sent[i] EXCEPT !.bc = sent[i].bc \cup {message}]]

UpponBCAST(self) ==
    /\ (pc[self] = "BCAST") /\ (messages[self] # {})
    /\ LET  currentMessage == CHOOSE x \in messages[self]: TRUE
        IN  /\ sent' = Broadcast(<<self, currentMessage>>)
            /\ messages' = [messages EXCEPT ![self] = messages[self] \ {currentMessage}]
            /\ UNCHANGED <<lc, pending, pc, received>>

(* <<TYPE, SOURCE, DESTINATION, MESSAGE_BODY, TIMESTAMP>> *)
ReceivedMessage(self) ==
    /\ \E msg \in sent[self].bc:
        /\ msg \notin pending[self]
        /\ pending' = [pending EXCEPT ![self] = pending[self] \cup { msg }]
        /\ sent' = [sent EXCEPT ![msg[1]].ts = sent[msg[1]].ts \cup {<<self, msg[2], lc[self]>>}]
        /\ UNCHANGED <<received, pc, messages, lc>>

MaxTSAllProcess(S) == (CHOOSE t \in S : \A s \in S : s[3] <= t[3])[3]

SN(message) ==
    [i \in Processes |-> [sent[i] EXCEPT !.sn = sent[i].sn \cup {message}]]

ReceivedTSFromAll(self) ==
    /\ LET  msgs == {m1 \in sent[self].ts: \A m2 \in sent[self].ts: m1[2] = m2[2]}
        IN  /\ Cardinality(msgs) = NPROCESS
            /\ LET m == CHOOSE x \in msgs: TRUE
                IN  /\ sent' = SN(<<self, m[2], MaxTSAllProcess(msgs)>>)
                    /\ UNCHANGED <<received, pending, lc, messages, pc>>

ReceivedSN(self) ==
    /\ \E msg \in sent[self].sn:
        /\ <<msg[1], msg[2]>> \notin received[self]
        /\ received' = [received EXCEPT ![self] = received[self] \cup {<<msg[1], msg[2]>>}]
        /\ UNCHANGED <<sent, pending, lc, messages, pc>>

\* FIX RECEIVED
Accept(self) ==
    /\ Cardinality(Processes \times MESSAGES) = Cardinality(received[self])
    /\ pc' = [pc EXCEPT ![self] = "AC"]
    /\ UNCHANGED  <<sent, pending, lc, messages, received>>

Steps(self) ==
    \/ UpponBCAST(self)
    \/ ReceivedMessage(self)
    \/ ReceivedTSFromAll(self)
    \/ ReceivedSN(self)
    \/ Accept(self)
    \/ UNCHANGED vars

Next == (\E self \in Processes: Steps(self))

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

TypeOK ==
    /\ pc \in [ Processes -> {"BCAST", "SN", "AC", ""} ]

\* Properties

Agreement == []((\E self \in Processes: pc[self] = "AC") => <>[](\A self \in Processes: pc[self] = "AC"))

SelectedMessage == CHOOSE m \in (Processes \times MESSAGES): TRUE

Validity == []((\E self \in Processes: SelectedMessage \in sent[self].bc) => <>[](\A p \in Processes: SelectedMessage \in received[p]))

Integrity == []((\E self \in Processes: SelectedMessage \in received[self]) => <>[](\A self \in Processes: Cardinality({m \in received[self]: m = SelectedMessage}) = 1))

\* TotalOrder == 


====