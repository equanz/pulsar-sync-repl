---- MODULE main ----
EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS NULL, Clusters, LocalProducers, NumMsgs\*, Msgs

ASSUME Cardinality(Clusters) >= 2
ASSUME Cardinality(LocalProducers) >= 1
ASSUME NumMsgs >= 1
\*ASSUME Len(Msgs) >= 1

IsMsg(msg) ==
    /\ DOMAIN msg = {"src", "send_ack"}
    /\ msg.src \in Clusters
    /\ msg.send_ack \in BOOLEAN 
IsAckedMsg(msg) ==
    /\ IsMsg(msg)
    /\ msg.send_ack = TRUE
IsNotAckedMsg(msg) ==
    /\ IsMsg(msg)
    /\ msg.send_ack = FALSE
(* TODO: remove
IndexOfEarliestNotAckedMsg(msgs) ==
    IF \A i \in 1..Len(msgs): IsMsg(msgs[i]) /\
        \E j \in 1..Len(msgs): IsNotAckedMsg(msgs[j]) THEN
        LET k == CHOOSE k \in 1..Len(msgs): \A l \in 1..Len(msgs): k <= l
        IN k
    ELSE
        0
*)

(*--algorithm sync_replication
variables
    topics = [c \in Clusters |-> <<>>], \* each clusters has their own topic   replication backlog
    replicators = {r \in [{1, 2} -> Clusters]: r[1] /= r[2]}, \* {<<src, dst>>, ...}   {r \in {<<s, d>>: s, d \in Clusters}: r[1] /= r[2]}
    producers = {<<c, p>>: c \in Clusters, p \in LocalProducers}; \* {<<cluster1, producer1>>, <<cluster1, producer2>>, ... <<cluster2, producer1>>, ...}

define
    TypeInvariant ==
        /\ \A c \in DOMAIN topics: 
            \A i \in 1..Len(topics[c]): IsMsg(topics[c][i])
        /\ \A r \in replicators: r[1] /= r[2]

    \* TODO move it to the property or remove it
    \* all of the replication cluster topics are equivalent
    TopicInvariant ==
        /\ \A c1, c2 \in Clusters: topics[c1] = topics[c2]

    TopicsAreEquivalentWhenAcked ==
        /\ \A c1, c2 \in DOMAIN topics:
            \/ c1 = c2
            \/ SelectSeq(topics[c1], IsAckedMsg) = SelectSeq(topics[c2], IsAckedMsg)
end define;

process replicator \in replicators
variables
    src = self[1],
    dst = self[2],
    msg = NULL;
begin
    Receive:
        await Len(topics[src]) >= 1;
        msg := Head(topics[src]);
        topics[src] := Tail(topics[src]);
    Replicate:
        if msg.src = src then
            topics[dst] := Append(topics[dst], msg);
        end if;
    goto Receive;
end process;

process broker \in Clusters
begin
    Await:
        await Len(topics[self]) >= 1;
    SendAck:
        \* ack earliest not acked message
        if \E i \in 1..Len(topics[self]): IsNotAckedMsg(topics[self][i]) then
            with index = CHOOSE j \in 1..Len(topics[self]): \A k \in 1..Len(topics[self]): j <= k do
                topics[self][index].send_ack := TRUE;
            end with;
        end if;
    goto Await;
end process;

process producer \in producers
variables
    \*msgs = Msgs, TODO
    count = 0,
    cluster = self[1];
begin
    Producer:
    while count < NumMsgs do
        Send:
            topics[cluster] := Append(topics[cluster], [src |-> cluster, send_ack |-> FALSE]);
            count := count + 1;
    end while;
end process;

end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "a81f4ade" /\ chksum(tla) = "d7619906")
VARIABLES topics, replicators, producers, pc

(* define statement *)
TypeInvariant ==
    /\ \A c \in DOMAIN topics:
        \A i \in 1..Len(topics[c]): IsMsg(topics[c][i])
    /\ \A r \in replicators: r[1] /= r[2]



TopicInvariant ==
    /\ \A c1, c2 \in Clusters: topics[c1] = topics[c2]

TopicsAreEquivalentWhenAcked ==
    /\ \A c1, c2 \in DOMAIN topics:
        \/ c1 = c2
        \/ SelectSeq(topics[c1], IsAckedMsg) = SelectSeq(topics[c2], IsAckedMsg)

VARIABLES src, dst, msg, count, cluster

vars == << topics, replicators, producers, pc, src, dst, msg, count, cluster
        >>

ProcSet == (replicators) \cup (Clusters) \cup (producers)

Init == (* Global variables *)
        /\ topics = [c \in Clusters |-> <<>>]
        /\ replicators = {r \in [{1, 2} -> Clusters]: r[1] /= r[2]}
        /\ producers = {<<c, p>>: c \in Clusters, p \in LocalProducers}
        (* Process replicator *)
        /\ src = [self \in replicators |-> self[1]]
        /\ dst = [self \in replicators |-> self[2]]
        /\ msg = [self \in replicators |-> NULL]
        (* Process producer *)
        /\ count = [self \in producers |-> 0]
        /\ cluster = [self \in producers |-> self[1]]
        /\ pc = [self \in ProcSet |-> CASE self \in replicators -> "Receive"
                                        [] self \in Clusters -> "Await"
                                        [] self \in producers -> "Producer"]

Receive(self) == /\ pc[self] = "Receive"
                 /\ Len(topics[src[self]]) >= 1
                 /\ msg' = [msg EXCEPT ![self] = Head(topics[src[self]])]
                 /\ topics' = [topics EXCEPT ![src[self]] = Tail(topics[src[self]])]
                 /\ pc' = [pc EXCEPT ![self] = "Replicate"]
                 /\ UNCHANGED << replicators, producers, src, dst, count, 
                                 cluster >>

Replicate(self) == /\ pc[self] = "Replicate"
                   /\ IF msg[self].src = src[self]
                         THEN /\ topics' = [topics EXCEPT ![dst[self]] = Append(topics[dst[self]], msg[self])]
                         ELSE /\ TRUE
                              /\ UNCHANGED topics
                   /\ pc' = [pc EXCEPT ![self] = "Receive"]
                   /\ UNCHANGED << replicators, producers, src, dst, msg, 
                                   count, cluster >>

replicator(self) == Receive(self) \/ Replicate(self)

Await(self) == /\ pc[self] = "Await"
               /\ Len(topics[self]) >= 1
               /\ pc' = [pc EXCEPT ![self] = "SendAck"]
               /\ UNCHANGED << topics, replicators, producers, src, dst, msg, 
                               count, cluster >>

SendAck(self) == /\ pc[self] = "SendAck"
                 /\ IF \E i \in 1..Len(topics[self]): IsNotAckedMsg(topics[self][i])
                       THEN /\ LET index == CHOOSE j \in 1..Len(topics[self]): \A k \in 1..Len(topics[self]): j <= k IN
                                 topics' = [topics EXCEPT ![self][index].send_ack = TRUE]
                       ELSE /\ TRUE
                            /\ UNCHANGED topics
                 /\ pc' = [pc EXCEPT ![self] = "Await"]
                 /\ UNCHANGED << replicators, producers, src, dst, msg, count, 
                                 cluster >>

broker(self) == Await(self) \/ SendAck(self)

Producer(self) == /\ pc[self] = "Producer"
                  /\ IF count[self] < NumMsgs
                        THEN /\ pc' = [pc EXCEPT ![self] = "Send"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << topics, replicators, producers, src, dst, 
                                  msg, count, cluster >>

Send(self) == /\ pc[self] = "Send"
              /\ topics' = [topics EXCEPT ![cluster[self]] = Append(topics[cluster[self]], [src |-> cluster[self], send_ack |-> FALSE])]
              /\ count' = [count EXCEPT ![self] = count[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "Producer"]
              /\ UNCHANGED << replicators, producers, src, dst, msg, cluster >>

producer(self) == Producer(self) \/ Send(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in replicators: replicator(self))
           \/ (\E self \in Clusters: broker(self))
           \/ (\E self \in producers: producer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
