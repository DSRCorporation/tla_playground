------------------------------- MODULE net -------------------------------
EXTENDS Naturals, Bags

CONSTANTS
  Messages,
  MaxSamePackets,
  MessagesToSend
  
ASSUME
  MessagesToSend \subseteq Messages

VARIABLES 
  network,
  outbox,
  processed
  
vars == <<network, outbox, processed>>

IdReq == "req"
IdRep == "rep"
ReqPackets == [type: {IdReq}, msg: Messages]
RepPackets == [type: {IdRep}, msg: Messages]
Packets == ReqPackets \union RepPackets
  
Init == /\ network = EmptyBag
        /\ outbox = MessagesToSend
        /\ processed = {}
        
TypeInvariants == /\ IsABag(network)
                  /\ BagToSet(network) \subseteq Packets
                  /\ outbox \subseteq Messages
                  /\ processed \subseteq Messages
          
Req(m) == [type |-> IdReq, msg |-> m]
Rep(m) == [type |-> IdRep, msg |-> m]
          
Comm(in, out) == LET LimitPackets(net) == 
                       [p \in BagToSet(net) |-> IF CopiesIn(p, net) > MaxSamePackets 
                                                THEN MaxSamePackets 
                                                ELSE CopiesIn(p, net)]
                 IN network' = LimitPackets(network (-) SetToBag(in) (+) SetToBag(out))
                 
Sent(type) == {p \in BagToSet(network): p \in type}          
                  
SendRequest(m) == /\ m \in outbox 
                  /\ Comm({}, {Req(m)})
                  /\ UNCHANGED <<outbox, processed>>
                  
RecvRequest(p) == /\ p \in Sent(ReqPackets)
                  /\ Comm({p}, {Rep(p.msg)})
                  /\ processed' = processed \union {p.msg}
                  /\ UNCHANGED <<outbox>>
                  
RecvReply(p) == /\ p \in Sent(RepPackets)
                /\ Comm({p}, {})
                /\ outbox' = outbox \ {p.msg}
                /\ UNCHANGED <<processed>>                  

LosePacket == \E p \in Sent(Packets):
                /\ Comm({p}, {})
                /\ UNCHANGED <<outbox, processed>>

Next == \/ \E m \in Messages: SendRequest(m)
        \/ \E p \in ReqPackets: RecvRequest(p)
        \/ \E p \in RepPackets: RecvReply(p)
        \/ LosePacket

Spec == /\ Init 
        /\ [][Next]_vars 
        /\ \A m \in Messages: WF_vars(SendRequest(m))
        /\ \A p \in ReqPackets: SF_vars(RecvRequest(p))
        /\ \A p \in RepPackets: SF_vars(RecvReply(p))

Completed == /\ processed = MessagesToSend
             /\ outbox = {}
             
EventuallyCompleted == <>[]Completed

=============================================================================
