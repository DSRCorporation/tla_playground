------------------------------ MODULE net_pcal ------------------------------
EXTENDS Naturals, TLC, Bags

CONSTANTS
  Messages,
  MaxSamePackets,
  MessagesToSend
  
ASSUME
  MessagesToSend \subseteq Messages

(* --algorithm net_pcal
variables
  network = EmptyBag,
  outbox = MessagesToSend,
  processed = {}

define
  \* Type definitions
  IdReq == "req"
  IdRep == "rep"
  ReqPackets == [type: {IdReq}, msg: Messages]
  RepPackets == [type: {IdRep}, msg: Messages]
  Packets == ReqPackets \union RepPackets
          
  TypeInvariants == /\ IsABag(network)
                    /\ BagToSet(network) \subseteq Packets
                    /\ outbox \subseteq Messages
                    /\ processed \subseteq Messages
  
  \* Utility
  Req(m) == [type |-> IdReq, msg |-> m]
  Rep(m) == [type |-> IdRep, msg |-> m]
  Sent(type) == {p \in BagToSet(network): p \in type}
  
  \* Completion
  Completed == /\ processed = MessagesToSend
               /\ outbox = {}
             
  EventuallyCompleted == <>[]Completed
end define

\* Network communication
macro Comm(in, out)
begin
  network := LET LimitPackets(net) == 
                   [p \in BagToSet(net) |-> IF CopiesIn(p, net) > MaxSamePackets 
                                            THEN MaxSamePackets 
                                            ELSE CopiesIn(p, net)]
             IN LimitPackets(network (-) SetToBag(in) (+) SetToBag(out))
end macro

fair process send_request \in Messages
begin
  send_request:
  while TRUE do
    await self \in outbox;
    Comm({}, {Req(self)})
  end while
end process

fair+ process recv_request \in ReqPackets
begin
  recv_request:
  while TRUE do
    await self \in Sent(ReqPackets);
    Comm({self}, {Rep(self.msg)});
    processed := processed \union {self.msg}
  end while
end process

fair+ process recv_reply \in RepPackets
begin
  recv_reply:
  while TRUE do
    await self \in Sent(RepPackets);
    Comm({self}, {});
    outbox := outbox \ {self.msg}
  end while
end process 
                 
process lose_packet = "lose_packet"
begin
  lose_packet:
  while TRUE do
    with lost_p \in Sent(Packets) do
      Comm({lost_p}, {})
    end with
  end while
end process                 

end algorithm *)
\* BEGIN TRANSLATION
\* Label send_request of process send_request at line 56 col 3 changed to send_request_
\* Label recv_request of process recv_request at line 65 col 3 changed to recv_request_
\* Label recv_reply of process recv_reply at line 75 col 3 changed to recv_reply_
\* Label lose_packet of process lose_packet at line 85 col 3 changed to lose_packet_
VARIABLES network, outbox, processed

(* define statement *)
IdReq == "req"
IdRep == "rep"
ReqPackets == [type: {IdReq}, msg: Messages]
RepPackets == [type: {IdRep}, msg: Messages]
Packets == ReqPackets \union RepPackets

TypeInvariants == /\ IsABag(network)
                  /\ BagToSet(network) \subseteq Packets
                  /\ outbox \subseteq Messages
                  /\ processed \subseteq Messages


Req(m) == [type |-> IdReq, msg |-> m]
Rep(m) == [type |-> IdRep, msg |-> m]
Sent(type) == {p \in BagToSet(network): p \in type}


Completed == /\ processed = MessagesToSend
             /\ outbox = {}

EventuallyCompleted == <>[]Completed


vars == << network, outbox, processed >>

ProcSet == (Messages) \cup (ReqPackets) \cup (RepPackets) \cup {"lose_packet"}

Init == (* Global variables *)
        /\ network = EmptyBag
        /\ outbox = MessagesToSend
        /\ processed = {}

send_request(self) == /\ self \in outbox
                      /\ network' = (LET LimitPackets(net) ==
                                           [p \in BagToSet(net) |-> IF CopiesIn(p, net) > MaxSamePackets
                                                                    THEN MaxSamePackets
                                                                    ELSE CopiesIn(p, net)]
                                     IN LimitPackets(network (-) SetToBag(({})) (+) SetToBag(({Req(self)}))))
                      /\ UNCHANGED << outbox, processed >>

recv_request(self) == /\ self \in Sent(ReqPackets)
                      /\ network' = (LET LimitPackets(net) ==
                                           [p \in BagToSet(net) |-> IF CopiesIn(p, net) > MaxSamePackets
                                                                    THEN MaxSamePackets
                                                                    ELSE CopiesIn(p, net)]
                                     IN LimitPackets(network (-) SetToBag(({self})) (+) SetToBag(({Rep(self.msg)}))))
                      /\ processed' = (processed \union {self.msg})
                      /\ UNCHANGED outbox

recv_reply(self) == /\ self \in Sent(RepPackets)
                    /\ network' = (LET LimitPackets(net) ==
                                         [p \in BagToSet(net) |-> IF CopiesIn(p, net) > MaxSamePackets
                                                                  THEN MaxSamePackets
                                                                  ELSE CopiesIn(p, net)]
                                   IN LimitPackets(network (-) SetToBag(({self})) (+) SetToBag(({}))))
                    /\ outbox' = outbox \ {self.msg}
                    /\ UNCHANGED processed

lose_packet == /\ \E lost_p \in Sent(Packets):
                    network' = (LET LimitPackets(net) ==
                                      [p \in BagToSet(net) |-> IF CopiesIn(p, net) > MaxSamePackets
                                                               THEN MaxSamePackets
                                                               ELSE CopiesIn(p, net)]
                                IN LimitPackets(network (-) SetToBag(({lost_p})) (+) SetToBag(({}))))
               /\ UNCHANGED << outbox, processed >>

Next == lose_packet
           \/ (\E self \in Messages: send_request(self))
           \/ (\E self \in ReqPackets: recv_request(self))
           \/ (\E self \in RepPackets: recv_reply(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Messages : WF_vars(send_request(self))
        /\ \A self \in ReqPackets : SF_vars(recv_request(self))
        /\ \A self \in RepPackets : SF_vars(recv_reply(self))

\* END TRANSLATION

=============================================================================
