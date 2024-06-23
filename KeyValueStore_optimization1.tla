------------------------- MODULE KeyValueStore_optimization1 -------------------------
(**************************************************************************)
(* A simple key-value store exhibiting snapshot isolation. If two         *)
(* concurrent transactions write to the same key, the one merging later   *)
(* will be rejected. If they write different keys both will succeed. For  *)
(* a more-detailed specification of snapshot isolation, look at the       *)
(* specifications/SnapshotIsolation specs in the tlaplus/examples repo.   *)
(**************************************************************************)

EXTENDS FiniteSets, Integers

CONSTANTS   
     Key,
     Val,
     TxId
     
VARIABLES
    store,
    tx,
    snapshotStore,
    written,
    missed,
    fnDomain
----------------------------------------------------------------------------
vars == << store, tx, snapshotStore, written, missed >>
traceVars == << tx, snapshotStore >>

NoVal ==    \* Choose something to represent the absence of a value.
    CHOOSE v : v \notin Val
    
Store ==    \* The set of all key-value stores.
    [Key -> Val \cup {NoVal}]

S == 
    [ store_ |-> store, 
      tx_ |-> tx,
      written_ |-> written,
      snapshotStore_ |-> snapshotStore,
      missed_ |-> missed ]

mustTrace == 
    DOMAIN [ tx_ |-> tx, snapshotStore_ |-> snapshotStore ]

Init == \* The initial predicate.
    /\ store = [k \in Key |-> NoVal]        \* All store values are initially NoVal.
    /\ tx = {}                              \* The set of open transactions is initially empty.
    /\ snapshotStore =                      \* All snapshotStore values are initially NoVal.
        [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ written = [t \in TxId |-> {}]        \* All write logs are initially empty.
    /\ missed = [t \in TxId |-> {}]         \* All missed writes are initially empty.
    /\ fnDomain \in SUBSET DOMAIN S
    
TypeInvariant ==    \* The type invariant.
    /\ store \in Store
    /\ tx \subseteq TxId
    /\ snapshotStore \in [TxId -> Store]
    /\ written \in [TxId -> SUBSET Key]
    /\ missed \in [TxId -> SUBSET Key]
    
TxLifecycle ==
    /\ \A t \in tx :    \* If store != snapshot & we haven't written it, we must have missed a write.
        \A k \in Key : (store[k] /= snapshotStore[t][k] /\ k \notin written[t]) => k \in missed[t]
    /\ \A t \in TxId \ tx : \* Checks transactions are cleaned up after disposal.
        /\ \A k \in Key : snapshotStore[t][k] = NoVal
        /\ written[t] = {}
        /\ missed[t] = {}

OpenTx(t) ==    \* Open a new transaction.
    /\ t \notin tx
    /\ tx' = tx \cup {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    /\ UNCHANGED <<written, missed, store>>

Add(t, k, v) == \* Using transaction t, add value v to the store under key k.
    /\ t \in tx
    /\ snapshotStore[t][k] = NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>
    
Update(t, k, v) ==  \* Using transaction t, update the value associated with key k to v.
    /\ t \in tx
    /\ snapshotStore[t][k] \notin {NoVal, v}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>
    
Remove(t, k) == \* Using transaction t, remove key k from the store.
    /\ t \in tx
    /\ snapshotStore[t][k] /= NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = NoVal]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>
    
RollbackTx(t) ==    \* Close the transaction without merging writes into store.
    /\ t \in tx
    /\ tx' = tx \ {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]
    /\ missed' = [missed EXCEPT ![t] = {}]
    /\ UNCHANGED << store >>


CloseTx(t) ==   \* Close transaction t, merging writes into store.
    /\ t \in tx
    /\ missed[t] \cap written[t] = {}   \* Detection of write-write conflicts.
    /\ store' =                         \* Merge snapshotStore writes into store.
        [k \in Key |-> IF k \in written[t] THEN snapshotStore[t][k] ELSE store[k]]
    /\ tx' = tx \ {t}
    /\ missed' =    \* Update the missed writes for other open transactions.
        [otherTx \in TxId |-> IF otherTx \in tx' THEN missed[otherTx] \cup written[t] ELSE {}]
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]

Next == \* The next-state relation.
    /\ UNCHANGED << fnDomain >>
    /\  \/ \E t \in TxId : OpenTx(t)
        \/ \E t \in tx : \E k \in Key : \E v \in Val : Add(t, k, v)
        \/ \E t \in tx : \E k \in Key : \E v \in Val : Update(t, k, v)
        \/ \E t \in tx : \E k \in Key : Remove(t, k)
        \/ \E t \in tx : RollbackTx(t)
        \/ \E t \in tx : CloseTx(t)
        
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<store, tx, snapshotStore, written, missed, fnDomain>>

----------------------------------------------------------------------------
\*  modified actions

OpenTxState(state, t) ==
    IF   t \notin state.tx_
    THEN LET s == [state EXCEPT !.tx_ = state.tx_ \cup {t} ]
             s2 == [s EXCEPT !.snapshotStore_ = [s.snapshotStore_ EXCEPT ![t] = s.store_] ]
         IN  { s2 }
    ELSE {}
    
OpenTxStates(state) ==
    UNION {OpenTxState(state, t) : t \in TxId}
    
    
AddState(state, t, k, v) ==
    IF t \in state.tx_ /\ state.snapshotStore_[t][k] = NoVal
    THEN LET s == [ state EXCEPT !.snapshotStore_ = [state.snapshotStore_ EXCEPT ![t][k] = v] ] 
             s2 ==  [ s EXCEPT !.written_ = [state.written_ EXCEPT ![t] = @ \cup {k}] ]
             IN { s2 }
    ELSE {}

AddStates(state) ==
    UNION {AddState(state, t, k, v) : t \in TxId, k \in Key, v \in Val}   


UpdateState(state, t, k, v) ==
    IF t \in state.tx_ /\ state.snapshotStore_[t][k] \notin {NoVal, v}
    THEN LET s == [ state EXCEPT !.snapshotStore_ = [state.snapshotStore_ EXCEPT ![t][k] = v] ]
             s2 == [s EXCEPT !.written_ = [state.written_ EXCEPT ![t] = @ \cup {k}] ]
         IN { s2 }
    ELSE {}

UpdateStates(state) ==
    UNION {UpdateState(state, t, k, v) : t \in TxId, k \in Key, v \in Val}
    

RemoveState(state, t, k) ==
    IF t \in state.tx_ /\ state.snapshotStore_[t][k] /= NoVal    
    THEN LET s == [state EXCEPT !.snapshotStore_ = [state.snapshotStore_ EXCEPT ![t][k] = NoVal]]
             s2 == [s EXCEPT !.written_ = [state.written_ EXCEPT ![t] = @ \cup {k}]]
             IN { s2 }
    ELSE {}

RemoveStates(state) == 
    UNION {RemoveState(state, t, k) : t \in TxId, k \in Key} 


RollbackState(state, t) ==
    IF t \in state.tx_
    THEN LET s == [ state EXCEPT !.tx_ = state.tx_ \ {t} ]
             s2 == [ s EXCEPT !.snapshotStore_ = [state.snapshotStore_ EXCEPT ![t] = [k \in Key |-> NoVal]] ]
             s3 == [ s2 EXCEPT !.written_ = [state.written_ EXCEPT ![t] = {}] ]
             s4 == [ s3 EXCEPT !.missed_ = [state.missed_ EXCEPT ![t] = {}] ]
         IN { s4 }
    ELSE {}

RollbackStates(state) ==
    UNION {RollbackState(state, t) : t \in TxId} 


CloseTxState(state, t) ==
    IF t \in state.tx_ /\  state.missed_[t] \cap state.written_[t] = {}
    THEN LET s == [ state EXCEPT !.store_ = [k \in Key |-> IF k \in state.written_[t] THEN state.snapshotStore_[t][k] ELSE state.store_[k]] ]
             s2 == [ s EXCEPT !.tx_ = state.tx_ \ {t} ]
             s3 == [ s2 EXCEPT !.missed_ = [otherTx \in TxId |-> IF otherTx \in s2.tx_ THEN state.missed_[otherTx] \cup state.written_[t] ELSE {}]]
             s4 == [ s3 EXCEPT !.snapshotStore_ = [state.snapshotStore_ EXCEPT ![t] = [k \in Key |-> NoVal]] ]
             s5 == [ s4 EXCEPT !.written_ = [state.written_ EXCEPT ![t] = {}] ]
         IN { s5 }
    ELSE {}
    
CloseTxStates(state) ==
    UNION {CloseTxState(state, t) : t \in TxId}

----------------------------------------------------------------------------
    
Trace(s) ==
    [
     storeT |-> s.store_,
     txT |-> s.tx_,
     snapshotStoreT |-> s.snapshotStore_,
     writtenT |-> s.written_,
     missedT |-> s.missed_
    ]
 
TraceAuto(state) ==
    [ x \in fnDomain |-> state[x] ]
    
TraceLearned(state) ==
    [ x \in mustTrace |-> state[x] ]
    
AutoRules ==
    S # S' => TraceAuto(S) # TraceAuto(S')

LearnedRules ==
    S # S' => TraceLearned(S) # TraceLearned(S')

WeakTraceRule ==
    [][vars # vars' => traceVars # traceVars']_<<vars, traceVars>>

UsefulTraceRules == 
   /\ \A s1, s2 \in OpenTxStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in AddStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in UpdateStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in RemoveStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in RollbackStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in CloseTxStates(S) : s1 # s2 => Trace(s1) # Trace(s2)

TraceRules ==
   /\ OpenTxStates(S) # AddStates(S) =>
        {Trace(s) : s \in OpenTxStates(S)} # {Trace(s) : s \in AddStates(S)}
   /\ OpenTxStates(S) # UpdateStates(S) =>
        {Trace(s) : s \in OpenTxStates(S)} # {Trace(s) : s \in UpdateStates(S)}
   /\ OpenTxStates(S) # RemoveStates(S) =>
        {Trace(s) : s \in OpenTxStates(S)} # {Trace(s) : s \in RemoveStates(S)}
   /\ OpenTxStates(S) # RollbackStates(S) =>
        {Trace(s) : s \in OpenTxStates(S)} # {Trace(s) : s \in RollbackStates(S)}
   /\ OpenTxStates(S) # CloseTxStates(S) =>
        {Trace(s) : s \in OpenTxStates(S)} # {Trace(s) : s \in CloseTxStates(S)}
   /\ AddStates(S) # UpdateStates(S) =>
        {Trace(s) : s \in AddStates(S)} # {Trace(s) : s \in UpdateStates(S)}
   /\ AddStates(S) # RemoveStates(S) =>
        {Trace(s) : s \in AddStates(S)} # {Trace(s) : s \in RemoveStates(S)}
   /\ AddStates(S) # RollbackStates(S) =>
        {Trace(s) : s \in AddStates(S)} # {Trace(s) : s \in RollbackStates(S)}
   /\ AddStates(S) # CloseTxStates(S) =>
        {Trace(s) : s \in AddStates(S)} # {Trace(s) : s \in CloseTxStates(S)}
   /\ UpdateStates(S) # RemoveStates(S) =>
        {Trace(s) : s \in UpdateStates(S)} # {Trace(s) : s \in RemoveStates(S)}
   /\ UpdateStates(S) # RollbackStates(S) =>
        {Trace(s) : s \in UpdateStates(S)} # {Trace(s) : s \in RollbackStates(S)}
   /\ UpdateStates(S) # CloseTxStates(S) =>
        {Trace(s) : s \in UpdateStates(S)} # {Trace(s) : s \in CloseTxStates(S)}
   /\ RemoveStates(S) # RollbackStates(S) =>
        {Trace(s) : s \in RemoveStates(S)} # {Trace(s) : s \in RollbackStates(S)}
   /\ RemoveStates(S) # CloseTxStates(S) =>
        {Trace(s) : s \in RemoveStates(S)} # {Trace(s) : s \in CloseTxStates(S)}
   /\ RollbackStates(S) # CloseTxStates(S) =>
        {Trace(s) : s \in RollbackStates(S)} # {Trace(s) : s \in CloseTxStates(S)}
   
----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ TxLifecycle)

THEOREM Spec => WeakTraceRule

THEOREM Spec => []TraceRules 

THEOREM Spec => []UsefulTraceRules
=============================================================================
\* Modification History
\* Last modified Sat Jun 22 22:28:34 PDT 2024 by user
\* Created Mon Jun 03 17:44:12 PDT 2024 by user
