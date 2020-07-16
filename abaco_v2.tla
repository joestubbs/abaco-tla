------------------------------ MODULE abaco_v2 ------------------------------

\* The formal specification for Abaco's execution and autoscaler engine.


EXTENDS Integers, FiniteSets

CONSTANTS MaxActors, Actors \* Max number of Actors,  Actors Id
VARIABLES actorIds, actorState,actorsData

\* ADD TypeInvariant
\* ActorIdTypeInvariants == actorsIds \in Actors


\* Possible statuses for actors
actorStatus == { "SUBMITTED", "READY", "ERROR", "DELETED", "INIT" }


\* Record types
\* ------------
\* An actor includes its id and its statuts
Actor == [ actorId: Actors, status: actorStatus ]
noActor == [actorId |-> "", status|->"INIT"] \* initial state record


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
                   /\ actorsData' = actorsData \cup {[a|->[actorId |-> a, status |-> "SUBMITTED"]]}                        
                  

Next == \E a \in Actors: createActor(a)
   

Spec == Init /\ [][Next]_vars      





=============================================================================
\* Modification History
\* Last modified Thu Jul 16 12:35:37 CDT 2020 by spadhy
\* Created Thu Jul 09 16:22:58 CDT 2020 by spadhy
