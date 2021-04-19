---- MODULE GMCast0 ----
EXTENDS TLC, FiniteSets, Naturals

CONSTANT NPROCESS

VARIABLES K, pending, delivering, delivered, previousSet, pc, sent

vars == <<K, pending, delivering, delivered, previousSet, pc, sent>>

Processess == 1 .. NPROCESS

Init ==
    /\ pc \in [Processess -> {"GMCAST", "NONE"}]
    /\ delivered = [i \in Processess |-> {}]
    /\ delivering = [i \in Processess |-> {}]
    /\ pending = [i \in Processess |-> {}]
    /\ previousSet = [i \in Processess |-> {}]
    /\ sent = [i \in Processess |-> {}]
    /\ K = [i \in Processess |-> 0]
    

GMCast(self) ==
    /\ pc[self] = "GMCAST"
    /\ LET msg == [stage |-> 0, source |-> self, message |-> "M1"]
        IN  /\ sent' = [i \in Processess |-> sent[i] \cup {msg}]
            /\ UNCHANGED <<K, pending, delivering, delivered, previousSet, pc>>

AssignTimestamp(self) ==
    /\ \E msg \in { m \in sent[self]: m.stage = 0}:
        /\ LET pendingMsg == [sender |-> msg.source, message |-> msg.message, k |-> K[self]]
               sentMsg == [stage |-> 1, source |-> self, dest |-> msg.source, message |-> msg.message, k |-> K[self]]
            IN  /\ sentMsg \notin sent[self]
                /\ IF msg \notin previousSet[self]
                    THEN /\ K' = [K EXCEPT ![self] = @ + 1]
                         /\ previousSet' = [previousSet EXCEPT ![self] = {msg}]
                    ELSE UNCHANGED <<K, previousSet>>
                /\ previousSet' = [previousSet EXCEPT ![self] = @ \cup {msg}]
                /\ pending' = [pending EXCEPT ![self] = @ \cup {pendingMsg}]
                /\ sent' = [sent EXCEPT ![msg.source] = @ \cup {sentMsg}]
                /\ UNCHANGED <<pc, delivered, delivering>>

CountStamppedMessage(self, msg) == 
    Cardinality({m \in sent[self]: m.stage = 1 /\ msg.message = m.message})

FilterStamppedMessages(self) ==
    {m \in sent[self]: /\ m.stage = 1 /\ CountStamppedMessage(self, m) = NPROCESS}

MaxK(S) == (CHOOSE t \in S : \A s \in S : s.k <= t.k).k

ComputeSeqNumber(self) ==
    /\ LET msgs == FilterStamppedMessages(self)
        IN /\ \E m \in msgs:
            /\ LET sentMsg == [stage |-> 2, source |-> self, message |-> m.message, sn |-> MaxK(msgs)]
                IN  /\ sent' = [i \in Processess |-> sent[i] \cup {sentMsg}]
                    /\ UNCHANGED <<K, pc, pending, delivered, delivering, previousSet>>

AssignSeqNumber(self)  ==
    /\ \E msg \in { m \in sent[self]: m.stage = 2 }:
        /\ msg \in pending[self]
        /\ IF msg[4] > K[self] 
            THEN /\ K' = [K EXCEPT ![self] = msg[4]]
                 /\ previousSet' = [previousSet EXCEPT ![self] = {}]
            ELSE UNCHANGED <<K, previousSet>>
        /\ pending = [pending EXCEPT ![self] = @ \ {CHOOSE m \in pending[self]: m.message = msg.message}]
        /\ delivering = [delivering EXCEPT ![self] = @ \cup {[sender |-> msg.source, message |-> msg.message, k |-> K[self]]}]
        /\ UNCHANGED <<delivered, pc>>

Steps(self) ==
    \/ GMCast(self)
    \/ AssignTimestamp(self)
    \/ ComputeSeqNumber(self)
    \/ AssignSeqNumber(self)
    \/ UNCHANGED vars
    
Next == \E p \in Processess: Steps(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====