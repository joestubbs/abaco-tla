---------------------------- MODULE actor_delete ----------------------------

(********************************************************************

This is is the specification for a messaging queue model in Abaco.
Each actor in the actor set is associated with a message queue. 
A message for the actor for execution is appended to the queue.
A worker from the set of workers working for the actor picks the message
is its status is IDLE. If number of messages in the queue exceeds the
 ScaleUpThreshold, a new worker is created.

*******************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Actors,           \* Set of Actors
          Workers,          \* Set of Workers
         \* Message,          \* Set of messages that can be sent
          MaxQueueSize,     \* Maximum queue size of the message queue.
          MaxMessage,       \* Maximum number of message that are sent
          MaxWorkers,       \* Maximum number of Workers that are allowed to be created 
          ScaleUpThreshold  \* ScaleUpThreshold 

VARIABLES msg_queues,         \* message_queues. One queue corresponds to an actor
          actorStatus,        \* set of actors
          workerStatus,       \* workers status 
          m,                  \* a counter to be increment to represent work 
          tmsg,               \* a counter to keep track for total number of mesages sent
          totalNumWorkers,    \* a counter for total number of workers created so far
          workersCreated,     \* a set of workers created so far
          cmd_queues,         \* command queues for workers
          actorWorkers,        \* subset of workers for each actor
          saveWork
vars == <<msg_queues,actorStatus,workerStatus,m, tmsg, totalNumWorkers, workersCreated, cmd_queues,actorWorkers,saveWork>>        

WorkerState == {"-","IDLE", "BUSY","FINISHED","STOPPING","DELETED"} \* Worker state
AllActors == Actors \cup {"a0"}      \* actors in the Actors constant and a non-existent actor

(**************************************************************************************
 ****** Set of all possible message types in the queue                             ****
 **************************************************************************************)
 Messages == [type : {"DELETE","EXECUTE"},  actor: Actors]


TypeInvariant == 
  /\ actorStatus \in [Actors -> { "SUBMITTED", "READY", "ERROR", "SHUTTING_DOWN","DELETED"}] 
  /\ msg_queues \in [Actors -> Seq(Messages)] \* multiple queues
  /\ workerStatus \in [Workers -> [actor:AllActors, status:WorkerState]] \* Note actor belongs to AllActors which incudes the non-existent actor
  /\ workersCreated \subseteq Workers
  /\ cmd_queues \in [Workers -> Seq(Messages)]    \* one command queue for worker
  /\ actorWorkers \in [Actors -> SUBSET Workers] \*  each actor mapped to subset of workers
 
  
  

Init == 
    /\ actorStatus = [a \in Actors |-> "READY"] 
    /\ workerStatus = [w \in Workers|-> [actor|->"a0",status|->"-"]] \* a0 is in AllActors but not in Actors
    /\ msg_queues = [a \in Actors |-> <<>>]
    /\ m = 0
    /\ tmsg = 0
    /\ totalNumWorkers = 0
    /\ workersCreated = {}
    /\ cmd_queues = [w \in Workers |-> <<>>]  \* all command queues are empty
    /\ actorWorkers = [a \in Actors |-> {}]   \* actorWorkers are also empty
    /\ saveWork = 0
    
    
ActorRecv(msg, a) ==    
    /\  actorStatus[a] = "READY"
    /\  msg.type = "EXECUTE"
    /\  tmsg < MaxMessage
    /\  Len(msg_queues[a]) <  MaxQueueSize
    /\  msg_queues'= [msg_queues EXCEPT ![a] = Append(msg_queues[a],msg)]
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<actorStatus,workerStatus,m,totalNumWorkers, workersCreated,cmd_queues,actorWorkers,saveWork>>   

 
 ActorDeleteMsg(msg,a) ==
    /\ msg.type = "DELETE"
    /\ msg.actor = a
    /\  msg_queues'= [msg_queues EXCEPT ![a] = Append(msg_queues[a],msg)]
    /\ actorStatus' = [actorStatus EXCEPT ![a] = "SHUTTING_DOWN"]
    \*/\ workerStatus' = \A w \in actorWorkers: workerStatus[w]=[actor|->a, status|->"STOPPING"]
    /\ workerStatus' = [ w \in Workers |-> IF workerStatus[w].actor=a  THEN  [actor|->a, status|->"STOPPING"]
                                                                           ELSE workerStatus[w]]
    
    /\ UNCHANGED<<msg_queues,m, tmsg,totalNumWorkers, workersCreated, cmd_queues,actorWorkers,saveWork>>                                                                        
 
  
 DeleteWorker(w,a) ==
 /\ workerStatus[w].status = "STOPPING"
 /\ saveWork' = saveWork + 1
 /\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}] \*<-- may need to change to IF then else
 /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"DELETED"]]                                                   
 /\ UNCHANGED<<msg_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated, cmd_queues>>                                                  
 
 
 DeleteActor(a) ==
     /\ actorStatus[a] = "SHUTTING_DOWN"
     /\ actorWorkers[a] = {}
     /\ actorStatus' = [actorStatus EXCEPT ![a]="DELETED"] 
     /\ UNCHANGED<<msg_queues,workerStatus,m, tmsg, totalNumWorkers, workersCreated, cmd_queues,actorWorkers,saveWork>> 
 
 


CreateWorker(w,a) ==
    /\ Len(msg_queues[a]) > ScaleUpThreshold
    /\ totalNumWorkers < MaxWorkers
    /\ actorStatus[a]="READY"
    /\ workerStatus[w]=[actor|->"a0", status|->"-"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] 
    /\ workersCreated' = workersCreated \cup {w}
   \* /\ actorWorkers' = [ a1 \in Actors |-> IF a=a1 THEN actorWorkers[a] \cup {w}  \* Note the way an element of sequence is updated
   \* ELSE actorWorkers[a]]
   \*  
    /\ actorWorkers' = [actorWorkers EXCEPT ![a]= actorWorkers[a] \cup {w}]                                              
    /\ totalNumWorkers' = totalNumWorkers + 1      
    /\ UNCHANGED<<msg_queues,actorStatus,m,tmsg,cmd_queues,saveWork>>
   

WorkerRecv(w,a) ==
    /\ Len(msg_queues[a]) > 0  
    /\ workerStatus[w] = [actor|->a, status|->"IDLE"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"BUSY"]]  
    /\ msg_queues'= [msg_queues EXCEPT ![a] = Tail(msg_queues[a])]
    /\ UNCHANGED<<actorStatus,m, tmsg, totalNumWorkers, workersCreated,cmd_queues,actorWorkers,saveWork>>    

WorkerBusy(w,a) == 
    /\ workerStatus[w] = [actor|->a, status|->"BUSY"]  
    /\ m' = m + 1  
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"FINISHED"]]    
    /\ UNCHANGED<<msg_queues,actorStatus,tmsg, totalNumWorkers, workersCreated,cmd_queues,actorWorkers,saveWork>>   

FreeWorker(w,a) ==
 /\ workerStatus[w] = [actor|->a, status|->"FINISHED"]
 /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] 
 /\ UNCHANGED<<msg_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated,cmd_queues,actorWorkers,saveWork>>         

Next == 
            \/ \E msg \in Messages, a \in Actors: ActorRecv(msg,a) 
            \/ \E msg \in Messages, a \in Actors:  ActorDeleteMsg(msg,a)
            \/ \E w \in Workers,  a1 \in Actors: CreateWorker(w,a1)  
            \/ \E w1 \in Workers, a2 \in Actors: WorkerRecv(w1, a2)
             \/ \E w2 \in Workers, a3\in Actors: WorkerBusy(w2,a3)
            \/ \E w3 \in Workers, a4\in Actors: FreeWorker(w3,a4)
            \/ \E w4 \in Workers, a6 \in Actors: DeleteWorker(w4,a6)
            \/ \E a7 \in Actors: DeleteActor(a7)

Spec == Init /\ [][Next]_vars  



=============================================================================
\* Modification History
\* Last modified Thu Aug 13 17:28:42 CDT 2020 by spadhy
\* Created Thu Aug 13 00:58:32 CDT 2020 by spadhy
