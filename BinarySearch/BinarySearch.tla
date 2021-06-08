---- MODULE BinarySearch ----
EXTENDS TLC, Sequences, FiniteSets, Naturals, Integers

CONSTANTS OrderedList, SearchItem
VARIABLES searchIndex

ASSUME /\ (Len(OrderedList) # 0)
ASSUME /\ (SearchItem \in Nat)

vars == << searchIndex >>

InitialStart == 1
InitialEnd == Len(OrderedList)

Init ==
    /\ searchIndex = 0

RECURSIVE Search(_, _, _)
Search(start, end, item) ==
    /\ LET Index == (start + end) \div 2
        IN  \/  /\ start <= end
                /\ IF OrderedList[Index] = item
                    THEN searchIndex' = Index
                    ELSE IF OrderedList[Index] < item
                        THEN Search(Index+1, end, item)
                        ELSE Search(start, Index-1, item)
            \/ UNCHANGED vars

Next == Search(InitialStart, InitialEnd, SearchItem)

Spec == 
    /\ Init
    /\ [][Next]_vars
====