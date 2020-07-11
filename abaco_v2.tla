------------------------------ MODULE abaco_v2 ------------------------------

\* The formal specification for Abaco's execution and autoscaler engine.


EXTENDS Integers, FiniteSets

CONSTANT MaxActors, Actors
VARIABLES actorIds, actorState,actorsData



\* Possible statuses for actors, executions and workers
actorStatus == { "SUBMITTED", "READY", "ERROR", "DELETED", "INIT" }

\* Record types
\* ------------
\* An actor includes its id and its statuts
Actor == [ actorId: Actors, status: actorStatus ]
noActor == [actorId |-> "", status|->"INIT"]


Init == /\ actorIds = {}
        /\ actorState = [a \in Actors |-> noActor]
        /\ actorsData = {}




\*actorsData == [a \in actorIds |-> Actor]


\* actual stores variables (functions) map ids to records



\* Actions
\* -------
\* create a new actor with the next actor id.


vars == <<actorIds, actorState,actorsData>>


createActor(a) ==  /\ Cardinality(actorIds) < MaxActors
                   /\ actorState[a].status="INIT" 
                   /\ actorState'= [ actorState EXCEPT ![a] = [actorId |-> a, status|->"SUBMITTED"]]
                   /\ actorIds' = actorIds \cup {a}  
                   /\ actorsData' = actorsData \cup {[actorId |-> a, status |-> "SUBMITTED"]}                        
                  

Next == \E a \in Actors: createActor(a)
   

Spec == Init /\ [][Next]_vars      





=============================================================================
\* Modification History
\* Last modified Fri Jul 10 17:49:55 CDT 2020 by spadhy
\* Created Thu Jul 09 16:22:58 CDT 2020 by spadhy
