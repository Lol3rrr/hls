-------------------------------- MODULE hls --------------------------------


EXTENDS Integers, Sequences, TLC, FiniteSets
 
CONSTANT REQS
ASSUME REQS \in 0..10

CONSTANT Clients
CONSTANT Servers
ASSUME Clients \intersect Servers = {}

CONSTANT Replicas
ASSUME Replicas \in 1..5


(*--algorithm hls
variables
  ServerWriteQueues = [t \in Servers |-> <<>>];
  ServerReadQueues = [t \in Servers |-> <<>>];
  OnlineServers = Servers;
  ServerData = [t \in Servers |-> {}];
  WrittenFiles = {};
  ConfirmedFiles = {};

define
    ContainsFile(file) == \E x \in OnlineServers: file \in ServerData[x]
    AllFilesOnline == \A f \in ConfirmedFiles: ContainsFile(f)
    AllDone == \A t \in (Clients \union Servers): pc[t] = "Done"

    IsCorrect ==
        /\ Cardinality(Servers \ OnlineServers) = 0 => AllFilesOnline
        /\ Cardinality(Servers \ OnlineServers) < Replicas => AllFilesOnline
end define;

macro send_write(written_to, value) begin
    with target \in OnlineServers \ written_to do
      written_to := written_to \union {target};
      ServerWriteQueues[target] := Append(ServerWriteQueues[target], value);
      WrittenFiles := WrittenFiles \union {value};
    end with;
end macro

macro send_read(written_to, value) begin
    with target \in OnlineServers \ written_to do
      written_to := written_to \union {target};
      ServerReadQueues[target] := Append(ServerReadQueues[target], value);
    end with;
end macro

process client \in Clients
variables
    iteration = 0;
    send_iteration = 0;
    send_written_to = {};
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
        end either;
    ServiceRequest:
        if ServerWriteQueues[self] # <<>> then
            write_request := Head(ServerWriteQueues[self]);
            ServerWriteQueues[self] := Tail(ServerWriteQueues[self]);
            
            ServerData[self] := ServerData[self] \union {write_request};
            ConfirmedFiles := ConfirmedFiles \union {write_request};
        end if;
        
        goto RunServer;
end process

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6c39d42d" /\ chksum(tla) = "eec6dfe")
VARIABLES ServerWriteQueues, ServerReadQueues, OnlineServers, ServerData, 
          WrittenFiles, ConfirmedFiles, pc

(* define statement *)
ContainsFile(file) == \E x \in OnlineServers: file \in ServerData[x]
AllFilesOnline == \A f \in ConfirmedFiles: ContainsFile(f)
AllDone == \A t \in (Clients \union Servers): pc[t] = "Done"

IsCorrect ==
    /\ Cardinality(Servers \ OnlineServers) = 0 => AllFilesOnline
    /\ Cardinality(Servers \ OnlineServers) < Replicas => AllFilesOnline

VARIABLES iteration, send_iteration, send_written_to, write_request

vars == << ServerWriteQueues, ServerReadQueues, OnlineServers, ServerData, 
           WrittenFiles, ConfirmedFiles, pc, iteration, send_iteration, 
           send_written_to, write_request >>

ProcSet == (Clients) \cup (Servers)

Init == (* Global variables *)
        /\ ServerWriteQueues = [t \in Servers |-> <<>>]
        /\ ServerReadQueues = [t \in Servers |-> <<>>]
        /\ OnlineServers = Servers
        /\ ServerData = [t \in Servers |-> {}]
        /\ WrittenFiles = {}
        /\ ConfirmedFiles = {}
        (* Process client *)
        /\ iteration = [self \in Clients |-> 0]
        /\ send_iteration = [self \in Clients |-> 0]
        /\ send_written_to = [self \in Clients |-> {}]
        (* Process server *)
        /\ write_request = [self \in Servers |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Run"
                                        [] self \in Servers -> "RunServer"]

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
             /\ UNCHANGED << ServerWriteQueues, ServerReadQueues, 
                             OnlineServers, ServerData, WrittenFiles, 
                             ConfirmedFiles, iteration, write_request >>

IncRun(self) == /\ pc[self] = "IncRun"
                /\ iteration' = [iteration EXCEPT ![self] = iteration[self] + 1]
                /\ pc' = [pc EXCEPT ![self] = "Run"]
                /\ UNCHANGED << ServerWriteQueues, ServerReadQueues, 
                                OnlineServers, ServerData, WrittenFiles, 
                                ConfirmedFiles, send_iteration, 
                                send_written_to, write_request >>

WriteToReplicas(self) == /\ pc[self] = "WriteToReplicas"
                         /\ IF send_iteration[self] < Replicas
                               THEN /\ \E target \in OnlineServers \ send_written_to[self]:
                                         /\ send_written_to' = [send_written_to EXCEPT ![self] = send_written_to[self] \union {target}]
                                         /\ ServerWriteQueues' = [ServerWriteQueues EXCEPT ![target] = Append(ServerWriteQueues[target], self)]
                                         /\ WrittenFiles' = (WrittenFiles \union {self})
                                    /\ send_iteration' = [send_iteration EXCEPT ![self] = send_iteration[self] + 1]
                                    /\ pc' = [pc EXCEPT ![self] = "WriteToReplicas"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "IncRun"]
                                    /\ UNCHANGED << ServerWriteQueues, 
                                                    WrittenFiles, 
                                                    send_iteration, 
                                                    send_written_to >>
                         /\ UNCHANGED << ServerReadQueues, OnlineServers, 
                                         ServerData, ConfirmedFiles, iteration, 
                                         write_request >>

ReadFromReplicas(self) == /\ pc[self] = "ReadFromReplicas"
                          /\ IF send_iteration[self] < Replicas
                                THEN /\ \E target \in OnlineServers \ send_written_to[self]:
                                          /\ send_written_to' = [send_written_to EXCEPT ![self] = send_written_to[self] \union {target}]
                                          /\ ServerReadQueues' = [ServerReadQueues EXCEPT ![target] = Append(ServerReadQueues[target], self)]
                                     /\ send_iteration' = [send_iteration EXCEPT ![self] = send_iteration[self] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "ReadFromReplicas"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "IncRun"]
                                     /\ UNCHANGED << ServerReadQueues, 
                                                     send_iteration, 
                                                     send_written_to >>
                          /\ UNCHANGED << ServerWriteQueues, OnlineServers, 
                                          ServerData, WrittenFiles, 
                                          ConfirmedFiles, iteration, 
                                          write_request >>

client(self) == Run(self) \/ IncRun(self) \/ WriteToReplicas(self)
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
                   /\ UNCHANGED << ServerWriteQueues, ServerReadQueues, 
                                   ServerData, WrittenFiles, ConfirmedFiles, 
                                   iteration, send_iteration, send_written_to, 
                                   write_request >>

ServiceRequest(self) == /\ pc[self] = "ServiceRequest"
                        /\ IF ServerWriteQueues[self] # <<>>
                              THEN /\ write_request' = [write_request EXCEPT ![self] = Head(ServerWriteQueues[self])]
                                   /\ ServerWriteQueues' = [ServerWriteQueues EXCEPT ![self] = Tail(ServerWriteQueues[self])]
                                   /\ ServerData' = [ServerData EXCEPT ![self] = ServerData[self] \union {write_request'[self]}]
                                   /\ ConfirmedFiles' = (ConfirmedFiles \union {write_request'[self]})
                              ELSE /\ TRUE
                                   /\ UNCHANGED << ServerWriteQueues, 
                                                   ServerData, ConfirmedFiles, 
                                                   write_request >>
                        /\ pc' = [pc EXCEPT ![self] = "RunServer"]
                        /\ UNCHANGED << ServerReadQueues, OnlineServers, 
                                        WrittenFiles, iteration, 
                                        send_iteration, send_written_to >>

server(self) == RunServer(self) \/ ServiceRequest(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: client(self))
           \/ (\E self \in Servers: server(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Dec 21 14:58:48 CET 2022 by leon
\* Created Tue Dec 20 19:55:07 CET 2022 by leon
