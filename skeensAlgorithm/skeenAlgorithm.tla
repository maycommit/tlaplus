---- MODULE skeenAlgorithm ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS NPROCESS, MESSAGES

VARIABLES pc, sent, pending, received, lc, messages

ASSUME (NPROCESS \in Nat) /\ (MESSAGES # {})
ASSUME (NPROCESS > 1)

vars == << pc, sent, pending, received, lc, messages >>

Processes == 1 .. NPROCESS

Init ==
    /\ messages = [i \in Processes |-> MESSAGES]
    /\ pending = [i \in Processes |-> {}]
    /\ received = [i \in Processes |-> {}]
    /\ sent = [i \in Processes |-> [bcast |-> {}, ts |-> {}, sn |-> {}]]
    /\ pc \in [Processes -> {"BCAST", ""}]
    /\ lc = [i \in Processes |-> 0]

UpponBCAST(self) ==
    /\ (pc[self] = "BCAST") /\ (messages[self] # {})
    /\ LET currentMessage == CHOOSE x \in messages[self]: TRUE
        IN  /\ sent' = [i \in Processes |-> [sent[self] EXCEPT !.bcast = sent[self].bcast \cup {[source |-> self, message |-> currentMessage]}]]
            /\ messages' = [messages EXCEPT ![self] = messages[self] \ {currentMessage}]
            /\ UNCHANGED <<lc, pending, pc, received>>


ReceivedBCAST(self) ==
  /\ pc[self] # "SN"
  /\ \E m \in sent[self].bcast:
        /\ m \notin pending[self]
        /\ pending' = [pending  EXCEPT ![self] = pending[self] \cup {m}]
        /\ sent' = [sent EXCEPT ![m.source].ts = sent[m.source].ts \cup {[source |-> self, message |-> m.message, ts |-> lc[self]]}] 
        /\ lc' = [lc EXCEPT ![self] = lc[self] + 1]
        /\ UNCHANGED <<received, pc, messages>>

MaxTSAllProcess(S) == CHOOSE t \in S : \A s \in S : s.ts <= t.ts

ReceivedTS(self) ==
    /\ pc[self] # "SN"
    /\ LET msgs == sent[self].ts
        IN  /\ Cardinality(msgs) = NPROCESS
            /\ LET maxTS == MaxTSAllProcess(msgs).ts
                IN  /\ \E m \in msgs:
                        /\ [source |-> self, message |-> m.message, ts |-> maxTS] \notin sent[self].sn
                        /\ sent' = [i \in Processes |-> [sent[self] EXCEPT !.sn = sent[self].sn \cup {[source |-> self, message |-> m.message, ts |-> maxTS]}]]
                        /\ pc' = [pc EXCEPT ![self] = "SN"]
                        /\ UNCHANGED <<pending, received, lc, messages>>

\* FIX RECEIVED
Accept(self) ==
    /\ (Cardinality(MESSAGES) = Cardinality(sent[self].sn))
    /\ pc' = [pc EXCEPT ![self] = "AC"]
    /\ received' = [received EXCEPT ![self] = sent[self].sn]
    /\ UNCHANGED <<sent, pending, lc, messages>>

Steps(self) ==
    \/ UpponBCAST(self)
    \/ ReceivedBCAST(self)
    \/ ReceivedTS(self)
    \/ Accept(self)
    \/ UNCHANGED vars

Next == (\E self \in Processes: Steps(self))

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars


TypeOK ==
    /\ pc \in [ Processes -> {"BCAST", "SN", "AC", ""} ]

\* Properties

Agreement == []((\A self \in Processes: pc[self] = "AC") => <>(\E self \in Processes: pc[self] = "AC"))

\* GetMessage == CHOOSE m \in MESSAGES: TRUE

\* Validity == WF_<<>>(\A p \in Processes: <<p, GetMessage>> \in deliveryBuffer[p])

\* Integrity == ()

\* TotalOrder == ()

====