----------------------------- MODULE austoscale -----------------------------
(***************************************************************************
Algorithm Steps:
1. The Actor recieves the message: ActorRecv(msg)
    a) Actor's status is ready
    b) Total number of messages < MaxMessage
    b) append the message into the queue tail
           
2. If message queue size > threshold & all workers are busy & total number of workers< the Max number of workers
   a) Create a worker 
   b) change the state of the worker to idle

3.  Worker recieves the message: WorkerRecv(msg)
    If queue length > 1 and a worker's state is idle
    a) dequeue the execution message from thw head of queue
    b) change the status to busy
    b) Does the execution
    


*************************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Actors,           \* Set of Actors
          Workers,          \* Set of Workers
          Message,          \* Set of all messages that can be sent
          MaxQueueSize,     \* Maximum queue size of the message queue.  This we can make in unbounded as well 
          MaxMessage,       \* Maximum number of message sent
          MaxWorkers,       \* Maximum number of Workers to be created
          ScaleUpThreshold  \* ScaleUpThreshold 

VARIABLES msg_queue,         \* message_queue for messages
          actorStatus,       \* set of actors
          workerStatus,      \* workers status 
          m,                 \* a counter to be increment to represent work 
          tmsg,              \* acounter for total number of mesages sent
          totalNumWorkers,   \*
          workersCreated     \* workers created
          
vars == <<msg_queue,actorStatus,workerStatus,m, tmsg, totalNumWorkers, workersCreated>>        


TypeInvariant == 
  /\ actorStatus \in [Actors -> { "SUBMITTED", "READY", "ERROR", "DELETED"}]
  /\ workerStatus \in [Workers -> {"-","IDLE", "BUSY","FINISHED"}] 
  /\ msg_queue \in Seq(Message)
  /\ workersCreated \subseteq Workers
  
  

Init == 
    /\ actorStatus = [a \in Actors |-> "READY"] 
    /\ workerStatus = [w \in Workers|-> "-"]
    /\ msg_queue = <<>>
    /\ m=0
    /\ tmsg = 0
    /\ totalNumWorkers = 0
    /\ workersCreated = {}
    
ActorRecv(msg, a) ==    
    /\  actorStatus[a]="READY"
    /\  tmsg < MaxMessage
    /\  Len(msg_queue) <  MaxQueueSize
    /\  msg_queue'= Append(msg_queue,msg)
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<actorStatus,workerStatus,m,totalNumWorkers, workersCreated>>   

CreateWorker(w) ==
    /\ Len(msg_queue) > ScaleUpThreshold
    /\ \A w1 \in Workers: workerStatus[w1] \in {"BUSY","-"}
    /\ totalNumWorkers < MaxWorkers
    /\ workerStatus[w] = "-"
    /\ workerStatus' = [workerStatus EXCEPT ![w] = "IDLE"] 
    /\ workersCreated' = workersCreated \cup {w}
    /\ totalNumWorkers' = totalNumWorkers + 1
    /\ UNCHANGED<<msg_queue,actorStatus,m,tmsg>>
   

WorkerRecv(w) ==
    /\ Len(msg_queue) > 0  
    /\ workerStatus[w] = "IDLE"
    /\ workerStatus' = [workerStatus EXCEPT ![w] = "BUSY"]  
    /\ msg_queue'=Tail(msg_queue) 
    /\ UNCHANGED<<actorStatus,m, tmsg, totalNumWorkers, workersCreated>>    

WorkerBusy(w) == 
    /\ workerStatus[w] = "BUSY"  
    /\ m' = m + 1  
    /\ workerStatus' = [workerStatus EXCEPT ![w] = "FINISHED"]    
    /\ UNCHANGED<<msg_queue,actorStatus,tmsg, totalNumWorkers, workersCreated>>   

FreeWorker(w) ==
 /\ workerStatus[w] = "FINISHED"
 /\ workerStatus' = [workerStatus EXCEPT ![w] = "IDLE"]
 /\ UNCHANGED<<msg_queue,actorStatus,m, tmsg, totalNumWorkers, workersCreated>>   

 Next == /\ \/ \E msg \in Message, a \in Actors: ActorRecv(msg,a)
            \/ \E w \in Workers: CreateWorker(w)
            \/ \E w1 \in Workers: WorkerRecv(w1)
            \/ \E w2 \in Workers: WorkerBusy(w2)
            \/ \E w3 \in Workers: FreeWorker(w3)
       
   

Spec == Init /\ [][Next]_vars  
=============================================================================
\* Modification History
\* Last modified Wed Aug 05 14:54:17 CDT 2020 by spadhy
\* Created Wed Aug 05 12:45:12 CDT 2020 by spadhy
