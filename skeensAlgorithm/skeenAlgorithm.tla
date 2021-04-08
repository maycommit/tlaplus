---- MODULE SkeenAlgorithm ----
EXTENDS TLC, Naturals, FiniteSets, Sequences
CONSTANTS NPROCESS, MESSAGES
VARIABLES pc, sent, pending, received, messages, lclock
ASSUME (NPROCESS \in Nat) /\ (MESSAGES # {})
ASSUME (NPROCESS >= 2)

vars == << pc, sent, pending, received, messages, lclock>>

Processes == 1 .. NPROCESS

Init ==
    /\ messages = [i \in Processes |-> MESSAGES]
    /\ pending = [i \in Processes |-> {}]
    /\ received = [i \in Processes |-> {}]
    /\ sent = {}
    /\ pc \in [Processes -> {"BCAST", ""}]
    /\ lclock = [i \in Processes |-> 0]

UpponBCAST(self) ==
    /\ (pc[self] = "BCAST") /\ (messages[self] # {})
    /\ LET  currentMessage == CHOOSE x \in messages[self]: TRUE
        IN  /\ sent' = sent \cup {<<"BC", self, currentMessage>>}
            /\ messages' = [messages EXCEPT ![self] = messages[self] \ {currentMessage}]
            /\ UNCHANGED <<pending, pc, received, lclock>>
    
ReceivedMessage(self) ==
    /\ LET msgs == {m \in sent: m[1] = "BC"}
        IN  /\ \E msg \in msgs:
                /\ msg \notin pending[self]
                /\ pending' = [pending EXCEPT ![self] = pending[self] \cup { msg }]
                /\ sent' = sent \cup {<<"TS", self, msg[2], msg[3], lclock[self]>>}
                /\ lclock' = [lclock EXCEPT ![self] = lclock[self] + 1]
                /\ UNCHANGED <<received, pc, messages>>

MaxTS(a, b) == IF a > b THEN a ELSE b

ReceivedTS(self) ==
    /\ \E msg \in {m \in sent: m[1] = "TS" /\ m[3] = self}:
        /\ msg \notin received[self]
        /\ received' = [received EXCEPT ![self] = received[self] \cup {msg}]
        /\ lclock' = [lclock EXCEPT ![self] = MaxTS(msg[5], lclock[self] + 1)]
        /\ UNCHANGED <<sent, pc, messages, pending>>

MaxTSAllProcess(S) == (CHOOSE t \in S : \A s \in S : s[5] <= t[5])[5]

FilterStamppedMessages(self) ==
    {m1 \in received[self]:
        /\ m1[1] = "TS"
        /\ Cardinality({m2 \in received[self]: m2[1] = "TS" /\ m1[3] = m2[3] /\ m1[4] = m2[4]}) = NPROCESS}

\* 107 808	14 408  
ReceivedTSFromAll(self) ==
    /\ LET  msgs == FilterStamppedMessages(self)
        IN  /\ \E m \in msgs:
                    /\ sent' = sent \cup {<<"SN", self, m[4], MaxTSAllProcess(msgs)>>}
                    /\ UNCHANGED <<lclock, messages, pc, pending, received>>

ReceivedSN(self) ==
    /\ pc[self] # "AC"
    /\ \E msg \in {m \in sent: m[1] = "SN"}:
        /\ received' = [received EXCEPT ![self] = received[self] \cup {<<"SN", msg[2], msg[3]>>}]
        /\ UNCHANGED <<sent, pending, messages, lclock, pc>>

\* FIX RECEIVED
Accept(self) ==
    /\ LET msgs == {m \in received[self]: m[1] = "SN"}
        IN  /\ Cardinality(Processes \times MESSAGES) = Cardinality(msgs)
            /\ pc' = [pc EXCEPT ![self] = "AC"]
            /\ UNCHANGED  <<sent, pending, messages, received, lclock>>

Steps(self) ==
    \/ UpponBCAST(self)
    \/ ReceivedMessage(self)
    \/ ReceivedTS(self)
    \/ ReceivedTSFromAll(self)
    \/ ReceivedSN(self)
    \/ Accept(self)
    \/ UNCHANGED vars

Next == (\E self \in Processes: Steps(self))

Spec == /\ Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ pc \in [ Processes -> {"BCAST", "AC", ""} ]


\* Properties
M == CHOOSE m \in MESSAGES: TRUE

Agreement == []((\E self \in Processes: pc[self] = "AC") => <>(\A self \in Processes: pc[self] = "AC"))

Validity == [](\E self \in Processes: (<<"BC", self, M>> \in sent => <>[](\A p \in Processes: <<"SN", self, M>> \in received[p])))

Integrity == [](\E self \in Processes: (<<"SN", self, M>> \in received[self] => <>[](\A p \in Processes: Cardinality({m \in received[p]: m = <<"SN", self, M>>}) = 1)))

\* TotalOrder == 


====