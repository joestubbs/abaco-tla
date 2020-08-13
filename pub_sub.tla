------------------------------ MODULE pub_sub ------------------------------
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
          Message,          \* Set of messages that can be sent
          
          \*Data,
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
          workersCreated      \* a set of workers created so far
          
vars == <<msg_queues,actorStatus,workerStatus,m, tmsg, totalNumWorkers, workersCreated>>        

WorkerState == {"-","IDLE", "BUSY","FINISHED"} \* Worker state
AllActors == Actors \cup {"a0"}  \* actors in the Actors constant and a non-existent actor

(**************************************************************************************
 ****** Set of all possible message types in the queue with the Actor that sent it ****
 ************************************************************************************** *)
\* Messages == [type : {"UPDATE","DELETE","STOP","EXECUTE"}, actor : Actors, value:Data]


TypeInvariant == 
  /\ actorStatus \in [Actors -> { "SUBMITTED", "READY", "ERROR", "DELETED"}] 
  /\ msg_queues \in [Actors -> Seq(Message)] \* multiple queues
  /\ workerStatus \in [Workers -> [actor:AllActors, status:WorkerState]] \* Note actor belongs to AllActors which incudes the non-existent actor
  /\ workersCreated \subseteq Workers
 
  
  

Init == 
    /\ actorStatus = [a \in Actors |-> "READY"] 
    /\ workerStatus = [w \in Workers|-> [actor|->"a0",status|->"-"]] \* a0 is in AllActors but not in Actors
    /\ msg_queues = [a \in Actors |-> <<>>]
    /\ m = 0
    /\ tmsg = 0
    /\ totalNumWorkers = 0
    /\ workersCreated = {}
  
    
    
ActorRecv(msg, a) ==    
    /\  actorStatus[a] = "READY"
    /\  tmsg < MaxMessage
    /\  Len(msg_queues[a]) <  MaxQueueSize
    /\  msg_queues' = [ a1 \in Actors |-> IF a=a1 THEN Append(msg_queues[a],msg)  \* Note the way an element of sequence is updated
                                                 ELSE msg_queues[a]]
    \*/\  msg_queues'= [msg_queues EXCEPT ![msg_queues[a]] = Append(msg_queues[a],msg)] <-- this is not working
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<actorStatus,workerStatus,m,totalNumWorkers, workersCreated>>   

 
      
CreateWorker(w,a) ==
    /\ Len(msg_queues[a]) > ScaleUpThreshold
    /\ totalNumWorkers < MaxWorkers
    /\ workerStatus[w]=[actor|->"a0", status|->"-"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] 
    /\ workersCreated' = workersCreated \cup {w}
    /\ totalNumWorkers' = totalNumWorkers + 1
    /\ UNCHANGED<<msg_queues,actorStatus,m,tmsg>>
   

WorkerRecv(w,a) ==
    /\ Len(msg_queues[a]) > 0  
    /\ workerStatus[w] = [actor|->a, status|->"IDLE"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"BUSY"]]  
    /\ msg_queues' = [ a1 \in Actors |-> IF a=a1 THEN Tail(msg_queues[a])
                                                 ELSE msg_queues[a]]
    /\ UNCHANGED<<actorStatus,m, tmsg, totalNumWorkers, workersCreated>>    

WorkerBusy(w,a) == 
    /\ workerStatus[w] = [actor|->a, status|->"BUSY"]  
    /\ m' = m + 1  
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"FINISHED"]]    
    /\ UNCHANGED<<msg_queues,actorStatus,tmsg, totalNumWorkers, workersCreated>>   

FreeWorker(w,a) ==
 /\ workerStatus[w] = [actor|->a, status|->"FINISHED"]
 /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] 
 /\ UNCHANGED<<msg_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated>>         

Next ==     \/ \E msg \in Message, a \in Actors: ActorRecv(msg,a)  
            \/ \E w \in Workers,  a1 \in Actors: CreateWorker(w,a1)
            \/ \E w1 \in Workers, a2 \in Actors: WorkerRecv(w1, a2)
            \/ \E w2 \in Workers, a3\in Actors: WorkerBusy(w2,a3)
            \/ \E w3 \in Workers, a4\in Actors: FreeWorker(w3,a4)

Spec == Init /\ [][Next]_vars  

=============================================================================
\* Modification History
\* Last modified Tue Aug 11 08:34:21 CDT 2020 by spadhy
\* Created Mon Aug 10 10:23:50 CDT 2020 by spadhy