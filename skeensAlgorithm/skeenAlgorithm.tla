---- MODULE skeenAlgorithm ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS NPROCESS, MESSAGES

VARIABLES pc, sentTS, sentSN, sentM, pendingBuffer, deliveryBuffer, LC

ASSUME (NPROCESS \in Nat) /\ (MESSAGES # {})

vars == << pendingBuffer, deliveryBuffer, pc, sentM, sentTS, sentSN, LC >>

Processes == 1 .. NPROCESS

Init ==
    /\ pendingBuffer = [i \in Processes |-> {}]
    /\ deliveryBuffer = [i \in Processes |-> {}]
    /\ pc \in [Processes -> {"BCAST", ""}]
    /\ LC = [i \in  Processes |-> 0]
    /\ sentM = {}
    /\ sentTS = {}
    /\ sentSN = {}

UpponBCAST(self, msg) ==
    /\ (pc[self] = "BCAST") /\ (<<self, msg>> \notin sentM)
    /\ sentM' = sentM \cup {<<self, msg>>}
    /\ UNCHANGED << LC, sentTS, sentSN, deliveryBuffer, pendingBuffer,  pc >>

UpponSentM(self) ==
    /\ pc[self] = "BCAST"
    /\ Cardinality({ m \in sentM: m[1] = self }) = Cardinality(MESSAGES)
    /\ pc' = [pc EXCEPT ![self] = "PENDING"]
    /\ UNCHANGED << LC, sentTS, sentSN, deliveryBuffer, pendingBuffer, sentM>>

ReceivedM(self) ==
    /\ \E msg \in sentM:
        /\ msg \notin pendingBuffer[self]
        /\ pendingBuffer' = [pendingBuffer EXCEPT ![self] = pendingBuffer[self] \cup { msg }]
        /\ LC' = [LC EXCEPT ![self] = LC[self] + 1]
        \* <<source, destination, message, timestamp>>
        /\ sentTS' = sentTS \cup {<<self, msg[1], msg[2], LC[self]>>}
        /\ UNCHANGED <<pc, sentSN,  deliveryBuffer, sentM>>

Max(S) == CHOOSE t \in S : \A s \in S : s[4] <= t[4]

ReceivedTS(self) ==
    /\ pc[self] = "PENDING"
    /\ LET msgs == { m \in sentTS: m[2] = self }
        IN  /\ NPROCESS = Cardinality(msgs)
            /\ LET m == CHOOSE m \in msgs: TRUE
                IN  /\ sentSN' = sentSN \cup {<<self, m[3], Max(msgs)[4]>>}
            /\ sentM' = sentM \ { <<m[2], m[3]>> : m \in sentTS }
            /\ pc' = [pc EXCEPT ![self] = "SN"]
    /\ UNCHANGED <<LC, deliveryBuffer, pendingBuffer, sentTS>>

ReceivedSNMessage(self) ==
    /\ \E msg \in sentSN:
        /\ <<msg[1], msg[2]>> \notin deliveryBuffer[self]
        /\ pendingBuffer' = [pendingBuffer EXCEPT ![self] = pendingBuffer[self] \ {<<msg[1], msg[2]>>}]
        /\ deliveryBuffer' = [deliveryBuffer EXCEPT ![self] = deliveryBuffer[self] \cup {<<msg[1], msg[2]>>}]
        /\ UNCHANGED <<LC, pc, sentM, sentTS, sentSN >>

Received(self) ==
    /\ (deliveryBuffer[self] # {}) /\ (Cardinality(deliveryBuffer[self]) = Cardinality(MESSAGES))
    /\ pc' = [pc EXCEPT ![self] = "AC"]
    /\ UNCHANGED <<LC, pendingBuffer, sentM, sentSN, sentTS, deliveryBuffer>>

Step(self, msg) ==
    \/ UpponBCAST(self, msg)
    \/ UpponSentM(self)
    \/ ReceivedM(self)
    \/ ReceivedTS(self)
    \/ ReceivedSNMessage(self)
    \/ Received(self)
    \/ UNCHANGED vars


Next == (\E self \in Processes: \E msg \in MESSAGES: Step(self, msg))

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

TypeOK ==
    /\ pc \in [ Processes -> {"BCAST", "PENDING", "SN", "AC", ""} ]

Agreement == []((\E self \in Processes: pc[self] = "AC") => <>[](\A self \in Processes: pc[self] = "AC"))

GetMessage == CHOOSE m \in MESSAGES: TRUE

Validity == WF_<<>>(\A p \in Processes: <<p, GetMessage>> \in deliveryBuffer[p])

\* Integrity == ()

\* TotalOrder == ()

====