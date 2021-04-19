---- MODULE SkeenAlgorithm ----

EXTENDS TLC, Naturals, FiniteSets, Sequences
CONSTANTS NPROCESS, MESSAGES
VARIABLES pc, sent, pending, received, messages, lclock, delivering, delivered

ASSUME (NPROCESS \in Nat) /\ (MESSAGES # {})
ASSUME (NPROCESS >= 2)

  (*************************************************************************)
  (* It is convenient to define some identifier to be the tuple of all     *)
  (* variables.  I like to use the identifier `vars'.                      *)
  (*************************************************************************)
vars == << pc, sent, pending, received, messages, lclock, delivering, delivered>>

Processes == 1 .. NPROCESS

Init ==
    /\ messages = [i \in Processes |-> MESSAGES]
    /\ pending = [i \in Processes |-> {}]
    /\ received = [i \in Processes |-> {}]
    /\ delivered = [i \in Processes |-> {}]
    /\ delivering = [i \in Processes |-> {}]
    /\ pc \in [Processes -> {"TOCAST", "NONE"}]
    /\ sent = [i \in Processes |-> {}]
    /\ lclock = [i \in Processes |-> 0]

\* If the process starts with TOCast, all messages will be transmitted to everyone.
TOCast(self) ==
    /\ pc[self] = "TOCAST"
    /\ \E message \in messages[self]:
        /\ LET sentMsg == [stage |-> 0, source |-> self, message |-> message]
            IN  /\ sent' = [i \in Processes |-> sent[i] \cup {sentMsg}]
                /\ messages' = [messages EXCEPT ![self] = @ \ {message}]
                /\ UNCHANGED <<pending, received, pc, lclock, delivered, delivering>>

\* A process receives a new message, stamps the message with a local timestamp and sends it to the sender
AssignTimestamp(self) ==
    /\ \E msg \in { m \in sent[self]: m.stage = 0 }:
        /\ lclock' = [lclock EXCEPT ![self] = @ + 1]
        /\ pending' = [pending EXCEPT ![self] = @ \cup {[
            sender |-> msg.source,
            message |-> msg.message,
            timestamp |-> lclock[self]]}]
        /\ sent' = [sent EXCEPT ![msg.source] = @ \cup {[
            stage |-> 1,
            source |-> self,
            message |-> msg.message,
            timestamp |-> lclock[self]]}]
        /\ UNCHANGED <<messages, received, pc, delivered, delivering>>


MaxTimestamp(a, b) == IF a > b THEN a ELSE b

\* A process receives a stamped message and updates logical clock
ReceivedStage1Message(self) ==
    /\ \E msg \in {m \in sent[self]: m.stage = 1}:
        /\ received' = [received EXCEPT ![self] = @ \cup {[
            stage |-> 1,
            source |-> msg.source,
            messages |-> msg.message,
            timestamp |->  msg.timestamp]}]
        /\ lclock' = [lclock EXCEPT ![self] = MaxTimestamp(msg.timestamp, lclock[self]) + 1]
        /\ UNCHANGED <<sent, pc, messages, pending, delivered, delivering>>
        
CountReceivedStage1Message(self, msg) ==
    Cardinality({m \in received[self]: m.stage = 1 /\ msg.message = m.message})
   
FilterReceivedStage1Message(self) ==
    {msg \in received[self]: msg.stage = 1 /\ CountReceivedStage1Message(self, msg) = NPROCESS}

SeqNumber(S) == (CHOOSE t \in S : \A s \in S : s.timestamp <= t.timestamp).timestamp

ComputeSeqNumber(self) == 
    /\ LET receivedMessages == FilterReceivedStage1Message(self)
        IN  /\ \E msg \in receivedMessages:
                /\ sent' = [i \in Processes |-> sent[i] \cup {[
                    stage |-> 2,
                    source |-> self,
                    message |-> msg.message,
                    sn |-> SeqNumber(receivedMessages)]}]
                /\ UNCHANGED <<lclock, messages, pc, pending, received, delivered, delivering>>

AssignSeqNumber(self) ==
    /\ \E msg \in {m \in sent[self]: m.stage = 2}:
        /\ pending' = pending \ {}
        /\ delivering' = [delivering EXCEPT ![self] = {[
            sender |-> msg.source,
            message |-> msg.message,
            timestamp |-> msg.sn]}]
        /\ UNCHANGED <<sent, received, pc, delivered>>


DoDeliver(self) ==
    /\ \E msg \in {m \in delivering: \A m1 \in pending \union delivering: m.timestamp <= m1.timestamp}:
        /\ delivering' = [delivering EXCEPT ![self] = @ \ msg]
        /\ delivered = [delivered EXCEPT ![self] = @ \cup {msg.message}]
        /\ UNCHANGED <<sent, pc, pending, received>>


Steps(self) ==
    \/ TOCast(self)
    \/ AssignTimestamp(self)
    \/ ReceivedStage1Message(self)
    \/ ComputeSeqNumber(self)
    \/ AssignSeqNumber(self)
    \/ DoDeliver(self)
    \/ UNCHANGED vars



Next == (\E p \in Processes: Steps(p))

Spec == /\ Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ pc \in [Processes -> {"TOCAST", "NONE"}]

\* Properties
M == CHOOSE m \in MESSAGES: TRUE

(***********************************************************************)
(*                  *)
(***********************************************************************)

\* FIX
\* Agreement == <>[](\A self \in Processes: Cardinality(Processes \times MESSAGES) = Cardinality({received[self]})))

(***********************************************************************)
(* Agreement: If a correct process TO-delivers a message m, then every *)
(* correct process in Dst(m) eventually TO-delivers m.                 *)
(***********************************************************************)

(******************************************************************)
(* Validity: If a correct process TO-multicasts a message m, then *)
(* every correct process in Dst(m) eventually TO-delivers m.      *)
(******************************************************************)

Validity == [](\A self \in Processes: (<<"BC", self, M>> \in sent => <>[](\A p \in Processes: <<"SN", self, M>> \in received[p])))
\* EXPERIMENT

(*************************************************************************************)
(* Integrity: For any message m, every correct process p TO-delivers m at most once, *)
(* and only if p ∈ Dst(m) and m was TO-multicast by some process Orig(m).            *)
(*************************************************************************************)
Integrity == [](\E self \in Processes: (<<"SN", self, M>> \in received[self] => <>[](\A p \in Processes: Cardinality({m \in received[p]: m = <<"SN", self, M>>}) = 1)))

\* Pairwise total order: If two correct processes p and q TO-deliver messages m and m1, then p TO-delivers m before m1 if and only if q TO-delivers m before m1.
\* TotalOrder == [](\E self \in )

\* TotalOrder == 


====