-------------------------------- MODULE crdt --------------------------------

EXTENDS Integers, Sequences, TLC

EmptySet == {}

_Lookup(set, e) == \E s \in set: s.val = e

_Add(proc, e) == {[key |-> ToString(proc) \o ToString(e), val |-> e]}

_Remove(set, e) == IF _Lookup(set, e) THEN
  {CHOOSE s \in set: s.val = e}
ELSE
  {}

AddOp(proc, val) == [op |-> "A", set |-> _Add(proc, val)]
RemoveOp(cset, val) == [op |-> "R", set |-> _Remove(cset, val)]

SetApplyOp(set, op) == IF op.op = "A" THEN
    set \union op.set
ELSE
    IF op.op = "R" THEN
        set \ op.set
    ELSE
        set

=============================================================================
\* Modification History
\* Last modified Sat Dec 24 00:16:02 CET 2022 by leon
\* Created Fri Dec 23 23:47:01 CET 2022 by leon
