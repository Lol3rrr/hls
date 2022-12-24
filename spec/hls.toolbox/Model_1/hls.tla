-------------------------------- MODULE hls --------------------------------


EXTENDS Integers, Sequences, TLC, FiniteSets
CrdtSet == INSTANCE crdt
 
CONSTANT REQS
ASSUME REQS \in 0..10

CONSTANT Clients
CONSTANT Servers
ASSUME Clients \intersect Servers = {}
ASSUME Cardinality(Servers) > 1

CONSTANT Replicas
ASSUME Replicas \in 1..Cardinality(Servers)


(*--algorithm hls
variables
  ServerQueues = [t \in Servers |-> [write |-> <<>>, read |-> <<>>, crdt |-> <<>>]];
  ServerData = [t \in Servers |-> {}];
  
  ClientCrdts = [t \in Clients |-> CrdtSet!EmptySet];
  ServerCrdts = [t \in Servers |-> CrdtSet!EmptySet];
  
  WrittenFiles = {};
  ConfirmedFiles = {};
  
  OnlineServers = Servers;

define
    ServerHasWork(serv) == ServerQueues[serv].write /= <<>> \/ ServerQueues[serv].read /= <<>> \/ ServerQueues[serv].crdt /= <<>>

    ContainsFile(file) == \E x \in OnlineServers: file \in ServerData[x]
    AllFilesOnline == \A f \in ConfirmedFiles: ContainsFile(f)
    AllClientsDone == \A t \in Clients: pc[t] = "Done"
    AllDone == AllClientsDone /\ (\A serv \in Servers: pc[serv] = "Done")

    IsCorrect ==
        /\ Cardinality(Servers \ OnlineServers) = 0 => AllFilesOnline
        /\ AllDone => (Cardinality(Servers \ OnlineServers) < Replicas => AllFilesOnline)
        /\ AllDone => (\A serv \in OnlineServers: \A cli \in Clients: ClientCrdts[cli] = ServerCrdts[serv])
end define;

macro send_write(written_to, value) begin
    if Cardinality(OnlineServers \ written_to) > 0 then
        with target \in OnlineServers \ written_to do
          written_to := written_to \union {target};
          ServerQueues[target].write := Append(ServerQueues[target].write, value);
          WrittenFiles := WrittenFiles \union {value};
        end with;
    end if;
end macro

macro send_read(written_to, value) begin
    if Cardinality(OnlineServers \ written_to) > 0 then
        with target \in OnlineServers \ written_to do
            written_to := written_to \union {target};
            ServerQueues[target].read := Append(ServerQueues[target].read, value);
        end with;
    end if;
end macro

procedure GossipBroadcast(server, ops, neighbours)
variables
    targets = {};
    tmp_targets = {};
    op = {};
begin
    SetupTargets:
        if Cardinality(targets) < neighbours /\ Cardinality(OnlineServers \ (targets \union {server})) > 0 then
             with serv \in (OnlineServers \ (targets \union {server})) do
                targets := targets \union {serv};
            end with;
            goto SetupTargets;
        else
            goto Send;
        end if;
    Send:
        if ops = <<>> then
            return;
        else
            op := Head(ops);
            ops := Tail(ops);
            tmp_targets := targets;
            
            goto SendOp;
        end if;
    SendOp:
        if Cardinality(tmp_targets) > 0 then
            with serv \in tmp_targets do
                ServerQueues[serv].crdt := Append(ServerQueues[serv].crdt, op);
                tmp_targets := tmp_targets \ {serv};
            end with;
            goto SendOp;
        else
            goto Send;
        end if;
end procedure;

process client \in Clients
variables
    iteration = 0;
    send_iteration = 0;
    send_written_to = {};
    last_op = {};
begin
    Run:
        while iteration <= REQS do
            either
                send_iteration := 0;
                send_written_to := {};
                WriteToReplicas:
                    while send_iteration < Replicas do
                        send_write(send_written_to, self);
                        send_iteration := send_iteration + 1;
                    end while;
                StoreInLocalVolume:
                    last_op := CrdtSet!AddOp(self, send_written_to);
                    ClientCrdts[self] := CrdtSet!SetApplyOp(ClientCrdts[self], last_op);
                StoreInServerVolume:
                    while Cardinality(send_written_to) > 0 do
                        with serv \in send_written_to do
                            ServerQueues[serv].crdt := Append(ServerQueues[serv].crdt, last_op);
                            send_written_to := send_written_to \ {serv};
                        end with;
                    end while;
            or
                send_iteration := 0;
                send_written_to := {};
                ReadFromReplicas:
                    while send_iteration < Replicas do
                        send_read(send_written_to, self);
                        send_iteration := send_iteration + 1;
                    end while;
            end either;
            IncRun:
                iteration := iteration + 1;
        end while;
end process

process server \in Servers
variables
    write_request = 0;
    read_request = 0;
    ops = <<>>;
begin
    RunServer:
        either
            if self \in OnlineServers then
                OnlineServers := OnlineServers \ {self};
            else
                OnlineServers := OnlineServers \union {self};
            end if;
            goto RunServer;
        or
            if self \in OnlineServers then
                goto ServiceRequest;
            end if;
        or
            goto GossipState;
        end either;
        
    \* Check and (potentially) handle a Read or Write Request
    ServiceRequest:
        if ServerQueues[self].write # <<>> then
            write_request := Head(ServerQueues[self].write);
            ServerQueues[self].write := Tail(ServerQueues[self].write);
            
            ServerData[self] := ServerData[self] \union {write_request};
            ConfirmedFiles := ConfirmedFiles \union {write_request};
            
        elsif ServerQueues[self].read # <<>> then
            read_request := Head(ServerQueues[self].read);
            ServerQueues[self].read := Tail(ServerQueues[self].read);
            
            skip;
        elsif ServerQueues[self].crdt # <<>> then
            op := Head(ServerQueues[self].crdt);
            ServerQueues[self].crdt := Tail(ServerQueues[self].crdt);
            
            ServerCrdts[self] := CrdtSet!SetApplyOp(ServerCrdts[self], op);
            ops := Append(ops, op);
        end if; 
        
        goto RunServer;
    
    \* Try to send the current CRDT State to other Volumes
    GossipState:
        call GossipBroadcast(self, ops, 1);
        goto RunServer;
end process

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d4d24a9f" /\ chksum(tla) = "926524a4")
\* Process server at line 143 col 1 changed to server_
\* Process variable ops of process server at line 147 col 5 changed to ops_
CONSTANT defaultInitValue
VARIABLES ServerQueues, ServerData, ClientCrdts, ServerCrdts, WrittenFiles, 
          ConfirmedFiles, OnlineServers, pc, stack

(* define statement *)
ServerHasWork(serv) == ServerQueues[serv].write /= <<>> \/ ServerQueues[serv].read /= <<>> \/ ServerQueues[serv].crdt /= <<>>

ContainsFile(file) == \E x \in OnlineServers: file \in ServerData[x]
AllFilesOnline == \A f \in ConfirmedFiles: ContainsFile(f)
AllClientsDone == \A t \in Clients: pc[t] = "Done"
AllDone == AllClientsDone /\ (\A serv \in Servers: pc[serv] = "Done")

IsCorrect ==
    /\ Cardinality(Servers \ OnlineServers) = 0 => AllFilesOnline
    /\ AllDone => (Cardinality(Servers \ OnlineServers) < Replicas => AllFilesOnline)
    /\ AllDone => (\A serv \in OnlineServers: \A cli \in Clients: ClientCrdts[cli] = ServerCrdts[serv])

VARIABLES server, ops, neighbours, targets, tmp_targets, op, iteration, 
          send_iteration, send_written_to, last_op, write_request, 
          read_request, ops_

vars == << ServerQueues, ServerData, ClientCrdts, ServerCrdts, WrittenFiles, 
           ConfirmedFiles, OnlineServers, pc, stack, server, ops, neighbours, 
           targets, tmp_targets, op, iteration, send_iteration, 
           send_written_to, last_op, write_request, read_request, ops_ >>

ProcSet == (Clients) \cup (Servers)

Init == (* Global variables *)
        /\ ServerQueues = [t \in Servers |-> [write |-> <<>>, read |-> <<>>, crdt |-> <<>>]]
        /\ ServerData = [t \in Servers |-> {}]
        /\ ClientCrdts = [t \in Clients |-> CrdtSet!EmptySet]
        /\ ServerCrdts = [t \in Servers |-> CrdtSet!EmptySet]
        /\ WrittenFiles = {}
        /\ ConfirmedFiles = {}
        /\ OnlineServers = Servers
        (* Procedure GossipBroadcast *)
        /\ server = [ self \in ProcSet |-> defaultInitValue]
        /\ ops = [ self \in ProcSet |-> defaultInitValue]
        /\ neighbours = [ self \in ProcSet |-> defaultInitValue]
        /\ targets = [ self \in ProcSet |-> {}]
        /\ tmp_targets = [ self \in ProcSet |-> {}]
        /\ op = [ self \in ProcSet |-> {}]
        (* Process client *)
        /\ iteration = [self \in Clients |-> 0]
        /\ send_iteration = [self \in Clients |-> 0]
        /\ send_written_to = [self \in Clients |-> {}]
        /\ last_op = [self \in Clients |-> {}]
        (* Process server_ *)
        /\ write_request = [self \in Servers |-> 0]
        /\ read_request = [self \in Servers |-> 0]
        /\ ops_ = [self \in Servers |-> <<>>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Run"
                                        [] self \in Servers -> "RunServer"]

SetupTargets(self) == /\ pc[self] = "SetupTargets"
                      /\ IF Cardinality(targets[self]) < neighbours[self] /\ Cardinality(OnlineServers \ (targets[self] \union {server[self]})) > 0
                            THEN /\ \E serv \in (OnlineServers \ (targets[self] \union {server[self]})):
                                      targets' = [targets EXCEPT ![self] = targets[self] \union {serv}]
                                 /\ pc' = [pc EXCEPT ![self] = "SetupTargets"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Send"]
                                 /\ UNCHANGED targets
                      /\ UNCHANGED << ServerQueues, ServerData, ClientCrdts, 
                                      ServerCrdts, WrittenFiles, 
                                      ConfirmedFiles, OnlineServers, stack, 
                                      server, ops, neighbours, tmp_targets, op, 
                                      iteration, send_iteration, 
                                      send_written_to, last_op, write_request, 
                                      read_request, ops_ >>

Send(self) == /\ pc[self] = "Send"
              /\ IF ops[self] = <<>>
                    THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ targets' = [targets EXCEPT ![self] = Head(stack[self]).targets]
                         /\ tmp_targets' = [tmp_targets EXCEPT ![self] = Head(stack[self]).tmp_targets]
                         /\ op' = [op EXCEPT ![self] = Head(stack[self]).op]
                         /\ server' = [server EXCEPT ![self] = Head(stack[self]).server]
                         /\ ops' = [ops EXCEPT ![self] = Head(stack[self]).ops]
                         /\ neighbours' = [neighbours EXCEPT ![self] = Head(stack[self]).neighbours]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ op' = [op EXCEPT ![self] = Head(ops[self])]
                         /\ ops' = [ops EXCEPT ![self] = Tail(ops[self])]
                         /\ tmp_targets' = [tmp_targets EXCEPT ![self] = targets[self]]
                         /\ pc' = [pc EXCEPT ![self] = "SendOp"]
                         /\ UNCHANGED << stack, server, neighbours, targets >>
              /\ UNCHANGED << ServerQueues, ServerData, ClientCrdts, 
                              ServerCrdts, WrittenFiles, ConfirmedFiles, 
                              OnlineServers, iteration, send_iteration, 
                              send_written_to, last_op, write_request, 
                              read_request, ops_ >>

SendOp(self) == /\ pc[self] = "SendOp"
                /\ IF Cardinality(tmp_targets[self]) > 0
                      THEN /\ \E serv \in tmp_targets[self]:
                                /\ ServerQueues' = [ServerQueues EXCEPT ![serv].crdt = Append(ServerQueues[serv].crdt, op[self])]
                                /\ tmp_targets' = [tmp_targets EXCEPT ![self] = tmp_targets[self] \ {serv}]
                           /\ pc' = [pc EXCEPT ![self] = "SendOp"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Send"]
                           /\ UNCHANGED << ServerQueues, tmp_targets >>
                /\ UNCHANGED << ServerData, ClientCrdts, ServerCrdts, 
                                WrittenFiles, ConfirmedFiles, OnlineServers, 
                                stack, server, ops, neighbours, targets, op, 
                                iteration, send_iteration, send_written_to, 
                                last_op, write_request, read_request, ops_ >>

GossipBroadcast(self) == SetupTargets(self) \/ Send(self) \/ SendOp(self)

Run(self) == /\ pc[self] = "Run"
             /\ IF iteration[self] <= REQS
                   THEN /\ \/ /\ send_iteration' = [send_iteration EXCEPT ![self] = 0]
                              /\ send_written_to' = [send_written_to EXCEPT ![self] = {}]
                              /\ pc' = [pc EXCEPT ![self] = "WriteToReplicas"]
                           \/ /\ send_iteration' = [send_iteration EXCEPT ![self] = 0]
                              /\ send_written_to' = [send_written_to EXCEPT ![self] = {}]
                              /\ pc' = [pc EXCEPT ![self] = "ReadFromReplicas"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << send_iteration, send_written_to >>
             /\ UNCHANGED << ServerQueues, ServerData, ClientCrdts, 
                             ServerCrdts, WrittenFiles, ConfirmedFiles, 
                             OnlineServers, stack, server, ops, neighbours, 
                             targets, tmp_targets, op, iteration, last_op, 
                             write_request, read_request, ops_ >>

IncRun(self) == /\ pc[self] = "IncRun"
                /\ iteration' = [iteration EXCEPT ![self] = iteration[self] + 1]
                /\ pc' = [pc EXCEPT ![self] = "Run"]
                /\ UNCHANGED << ServerQueues, ServerData, ClientCrdts, 
                                ServerCrdts, WrittenFiles, ConfirmedFiles, 
                                OnlineServers, stack, server, ops, neighbours, 
                                targets, tmp_targets, op, send_iteration, 
                                send_written_to, last_op, write_request, 
                                read_request, ops_ >>

WriteToReplicas(self) == /\ pc[self] = "WriteToReplicas"
                         /\ IF send_iteration[self] < Replicas
                               THEN /\ IF Cardinality(OnlineServers \ send_written_to[self]) > 0
                                          THEN /\ \E target \in OnlineServers \ send_written_to[self]:
                                                    /\ send_written_to' = [send_written_to EXCEPT ![self] = send_written_to[self] \union {target}]
                                                    /\ ServerQueues' = [ServerQueues EXCEPT ![target].write = Append(ServerQueues[target].write, self)]
                                                    /\ WrittenFiles' = (WrittenFiles \union {self})
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << ServerQueues, 
                                                               WrittenFiles, 
                                                               send_written_to >>
                                    /\ send_iteration' = [send_iteration EXCEPT ![self] = send_iteration[self] + 1]
                                    /\ pc' = [pc EXCEPT ![self] = "WriteToReplicas"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "StoreInLocalVolume"]
                                    /\ UNCHANGED << ServerQueues, WrittenFiles, 
                                                    send_iteration, 
                                                    send_written_to >>
                         /\ UNCHANGED << ServerData, ClientCrdts, ServerCrdts, 
                                         ConfirmedFiles, OnlineServers, stack, 
                                         server, ops, neighbours, targets, 
                                         tmp_targets, op, iteration, last_op, 
                                         write_request, read_request, ops_ >>

StoreInLocalVolume(self) == /\ pc[self] = "StoreInLocalVolume"
                            /\ last_op' = [last_op EXCEPT ![self] = CrdtSet!AddOp(self, send_written_to[self])]
                            /\ ClientCrdts' = [ClientCrdts EXCEPT ![self] = CrdtSet!SetApplyOp(ClientCrdts[self], last_op'[self])]
                            /\ pc' = [pc EXCEPT ![self] = "StoreInServerVolume"]
                            /\ UNCHANGED << ServerQueues, ServerData, 
                                            ServerCrdts, WrittenFiles, 
                                            ConfirmedFiles, OnlineServers, 
                                            stack, server, ops, neighbours, 
                                            targets, tmp_targets, op, 
                                            iteration, send_iteration, 
                                            send_written_to, write_request, 
                                            read_request, ops_ >>

StoreInServerVolume(self) == /\ pc[self] = "StoreInServerVolume"
                             /\ IF Cardinality(send_written_to[self]) > 0
                                   THEN /\ \E serv \in send_written_to[self]:
                                             /\ ServerQueues' = [ServerQueues EXCEPT ![serv].crdt = Append(ServerQueues[serv].crdt, last_op[self])]
                                             /\ send_written_to' = [send_written_to EXCEPT ![self] = send_written_to[self] \ {serv}]
                                        /\ pc' = [pc EXCEPT ![self] = "StoreInServerVolume"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "IncRun"]
                                        /\ UNCHANGED << ServerQueues, 
                                                        send_written_to >>
                             /\ UNCHANGED << ServerData, ClientCrdts, 
                                             ServerCrdts, WrittenFiles, 
                                             ConfirmedFiles, OnlineServers, 
                                             stack, server, ops, neighbours, 
                                             targets, tmp_targets, op, 
                                             iteration, send_iteration, 
                                             last_op, write_request, 
                                             read_request, ops_ >>

ReadFromReplicas(self) == /\ pc[self] = "ReadFromReplicas"
                          /\ IF send_iteration[self] < Replicas
                                THEN /\ IF Cardinality(OnlineServers \ send_written_to[self]) > 0
                                           THEN /\ \E target \in OnlineServers \ send_written_to[self]:
                                                     /\ send_written_to' = [send_written_to EXCEPT ![self] = send_written_to[self] \union {target}]
                                                     /\ ServerQueues' = [ServerQueues EXCEPT ![target].read = Append(ServerQueues[target].read, self)]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED << ServerQueues, 
                                                                send_written_to >>
                                     /\ send_iteration' = [send_iteration EXCEPT ![self] = send_iteration[self] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "ReadFromReplicas"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "IncRun"]
                                     /\ UNCHANGED << ServerQueues, 
                                                     send_iteration, 
                                                     send_written_to >>
                          /\ UNCHANGED << ServerData, ClientCrdts, ServerCrdts, 
                                          WrittenFiles, ConfirmedFiles, 
                                          OnlineServers, stack, server, ops, 
                                          neighbours, targets, tmp_targets, op, 
                                          iteration, last_op, write_request, 
                                          read_request, ops_ >>

client(self) == Run(self) \/ IncRun(self) \/ WriteToReplicas(self)
                   \/ StoreInLocalVolume(self) \/ StoreInServerVolume(self)
                   \/ ReadFromReplicas(self)

RunServer(self) == /\ pc[self] = "RunServer"
                   /\ \/ /\ IF self \in OnlineServers
                               THEN /\ OnlineServers' = OnlineServers \ {self}
                               ELSE /\ OnlineServers' = (OnlineServers \union {self})
                         /\ pc' = [pc EXCEPT ![self] = "RunServer"]
                      \/ /\ IF self \in OnlineServers
                               THEN /\ pc' = [pc EXCEPT ![self] = "ServiceRequest"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "ServiceRequest"]
                         /\ UNCHANGED OnlineServers
                      \/ /\ pc' = [pc EXCEPT ![self] = "GossipState"]
                         /\ UNCHANGED OnlineServers
                   /\ UNCHANGED << ServerQueues, ServerData, ClientCrdts, 
                                   ServerCrdts, WrittenFiles, ConfirmedFiles, 
                                   stack, server, ops, neighbours, targets, 
                                   tmp_targets, op, iteration, send_iteration, 
                                   send_written_to, last_op, write_request, 
                                   read_request, ops_ >>

ServiceRequest(self) == /\ pc[self] = "ServiceRequest"
                        /\ IF ServerQueues[self].write # <<>>
                              THEN /\ write_request' = [write_request EXCEPT ![self] = Head(ServerQueues[self].write)]
                                   /\ ServerQueues' = [ServerQueues EXCEPT ![self].write = Tail(ServerQueues[self].write)]
                                   /\ ServerData' = [ServerData EXCEPT ![self] = ServerData[self] \union {write_request'[self]}]
                                   /\ ConfirmedFiles' = (ConfirmedFiles \union {write_request'[self]})
                                   /\ UNCHANGED << ServerCrdts, op, 
                                                   read_request, ops_ >>
                              ELSE /\ IF ServerQueues[self].read # <<>>
                                         THEN /\ read_request' = [read_request EXCEPT ![self] = Head(ServerQueues[self].read)]
                                              /\ ServerQueues' = [ServerQueues EXCEPT ![self].read = Tail(ServerQueues[self].read)]
                                              /\ TRUE
                                              /\ UNCHANGED << ServerCrdts, op, 
                                                              ops_ >>
                                         ELSE /\ IF ServerQueues[self].crdt # <<>>
                                                    THEN /\ op' = [op EXCEPT ![self] = Head(ServerQueues[self].crdt)]
                                                         /\ ServerQueues' = [ServerQueues EXCEPT ![self].crdt = Tail(ServerQueues[self].crdt)]
                                                         /\ ServerCrdts' = [ServerCrdts EXCEPT ![self] = CrdtSet!SetApplyOp(ServerCrdts[self], op'[self])]
                                                         /\ ops_' = [ops_ EXCEPT ![self] = Append(ops_[self], op'[self])]
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED << ServerQueues, 
                                                                         ServerCrdts, 
                                                                         op, 
                                                                         ops_ >>
                                              /\ UNCHANGED read_request
                                   /\ UNCHANGED << ServerData, ConfirmedFiles, 
                                                   write_request >>
                        /\ pc' = [pc EXCEPT ![self] = "RunServer"]
                        /\ UNCHANGED << ClientCrdts, WrittenFiles, 
                                        OnlineServers, stack, server, ops, 
                                        neighbours, targets, tmp_targets, 
                                        iteration, send_iteration, 
                                        send_written_to, last_op >>

GossipState(self) == /\ pc[self] = "GossipState"
                     /\ /\ neighbours' = [neighbours EXCEPT ![self] = 1]
                        /\ ops' = [ops EXCEPT ![self] = ops_[self]]
                        /\ server' = [server EXCEPT ![self] = self]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "GossipBroadcast",
                                                                 pc        |->  "RunServer",
                                                                 targets   |->  targets[self],
                                                                 tmp_targets |->  tmp_targets[self],
                                                                 op        |->  op[self],
                                                                 server    |->  server[self],
                                                                 ops       |->  ops[self],
                                                                 neighbours |->  neighbours[self] ] >>
                                                             \o stack[self]]
                     /\ targets' = [targets EXCEPT ![self] = {}]
                     /\ tmp_targets' = [tmp_targets EXCEPT ![self] = {}]
                     /\ op' = [op EXCEPT ![self] = {}]
                     /\ pc' = [pc EXCEPT ![self] = "SetupTargets"]
                     /\ UNCHANGED << ServerQueues, ServerData, ClientCrdts, 
                                     ServerCrdts, WrittenFiles, ConfirmedFiles, 
                                     OnlineServers, iteration, send_iteration, 
                                     send_written_to, last_op, write_request, 
                                     read_request, ops_ >>

server_(self) == RunServer(self) \/ ServiceRequest(self)
                    \/ GossipState(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: GossipBroadcast(self))
           \/ (\E self \in Clients: client(self))
           \/ (\E self \in Servers: server_(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Sat Dec 24 14:06:03 CET 2022 by leon
\* Created Tue Dec 20 19:55:07 CET 2022 by leon
