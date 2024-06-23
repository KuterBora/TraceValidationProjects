------------------------- MODULE KeyValueStoreTyped -------------------------
(**************************************************************************)
(* A simple key-value store exhibiting snapshot isolation. If two         *)
(* concurrent transactions write to the same key, the one merging later   *)
(* will be rejected. If they write different keys both will succeed. For  *)
(* a more-detailed specification of snapshot isolation, look at the       *)
(* specifications/SnapshotIsolation specs in the tlaplus/examples repo.   *)
(**************************************************************************)

(* @typeAlias:  store = (Int -> Str);
   @typeAlias:  state = { store: $store, 
                          tx: Set(Int), 
                          snapshotStore: Int -> $store,
                          written: Int -> Set(Int),
                          missed: Int -> Set(Int) };
   @typeAlias:  vars = << $store, 
                          Set(Int),
                          Int -> $store,
                          Int -> Set(Int),
                          Int -> Set(Int) >>; 
   @typeAlias: traceVars = << Set(Int),
                               Int -> $store >>; *)
KeyValueStore_typedefs == TRUE


CONSTANTS   
     \* The set of all keys.
     \* @type: Set(Int);
     Key,
     \* The set of all values.
     \* @type: Set(Str);
     Val,
     \* The set of all transaction IDs.
     \* @type: Set(Int);
     TxId

VARIABLES
    \* A data store mapping keys to values.
    \* @type: $store;
    store,
    \* The set of open snapshot transactions.
    \* @type: Set(Int);
    tx,
    \* Snapshots of the store for each transaction.
    \* @type: Int -> $store;
    snapshotStore,
     \* A log of writes performed within each transaction.
     \* @type: Int -> Set(Int);
    written,
    \* The set of writes invisible to each transaction.
    \* @type: Int -> Set(Int);
    missed
----------------------------------------------------------------------------

\* @type: $vars;
vars == <<store, tx, snapshotStore, written, missed>>

\* @type: $traceVars;
traceVars == <<tx, snapshotStore>>

\* @type: Str;    
NoVal ==    \* Choose something to represent the absence of a value.
    "-1"
\*    CHOOSE v \in STRING : \notin Val
\*  CHOOSE v : v \notin Val

\* @type: Set($store);    
Store ==    \* The set of all key-value stores.
    [Key -> Val \cup {NoVal}]

(*
Init == \* The initial predicate.
    /\ store = [k \in Key |-> NoVal]        \* All store values are initially NoVal.
    /\ tx = {}                              \* The set of open transactions is initially empty.
    /\ snapshotStore =                      \* All snapshotStore values are initially NoVal.
        [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ written = [t \in TxId |-> {}]        \* All write logs are initially empty.
    /\ missed = [t \in TxId |-> {}]         \* All missed writes are initially empty.*)
    
Init ==
    /\ store \in Store
    /\ tx \in SUBSET TxId
    /\ snapshotStore \in [TxId -> Store]
    /\ written \in [TxId -> SUBSET Key]
    /\ missed \in [TxId -> SUBSET Key]
    
\*@type: (() => Bool);      
TypeInvariant ==    \* The type invariant.
    /\ store \in Store
    /\ tx \subseteq TxId
    /\ snapshotStore \in [TxId -> Store]
    /\ written \in [TxId -> SUBSET Key]
    /\ missed \in [TxId -> SUBSET Key]
 
\*@type: (() => Bool);   
TxLifecycle ==
    /\ \A t \in tx :    \* If store != snapshot & we haven't written it, we must have missed a write.
        \A k \in Key : (store[k] /= snapshotStore[t][k] /\ k \notin written[t]) => k \in missed[t]
    /\ \A t \in TxId \ tx : \* Checks transactions are cleaned up after disposal.
        /\ \A k \in Key : snapshotStore[t][k] = NoVal
        /\ written[t] = {}
        /\ missed[t] = {}

\* @type: Int => Bool;
OpenTx(t) ==    \* Open a new transaction.
    /\ t \notin tx
    /\ tx' = tx \cup {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    /\ UNCHANGED <<written, missed, store>>

\* @type: ( Int, Int, Str ) => Bool;
Add(t, k, v) == \* Using transaction t, add value v to the store under key k.
    /\ t \in tx
    /\ snapshotStore[t][k] = NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>

\* @type: ( Int, Int, Str ) => Bool; 
Update(t, k, v) ==  \* Using transaction t, update the value associated with key k to v.
    /\ t \in tx
    /\ snapshotStore[t][k] \notin {NoVal, v}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>

\* @type: ( Int, Int ) => Bool;    
Remove(t, k) == \* Using transaction t, remove key k from the store.
    /\ t \in tx
    /\ snapshotStore[t][k] /= NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = NoVal]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>

\* @type: Int => Bool;      
RollbackTx(t) ==    \* Close the transaction without merging writes into store.
    /\ t \in tx
    /\ tx' = tx \ {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]
    /\ missed' = [missed EXCEPT ![t] = {}]
    /\ UNCHANGED store

\* @type: Int => Bool; 
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

\*@type: (() => Bool);  
Next == \* The next-state relation.
    \/ \E t \in TxId : OpenTx(t)
    \/ \E t \in tx : \E k \in Key : \E v \in Val : Add(t, k, v)
    \/ \E t \in tx : \E k \in Key : \E v \in Val : Update(t, k, v)
    \/ \E t \in tx : \E k \in Key : Remove(t, k)
    \/ \E t \in tx : RollbackTx(t)
    \/ \E t \in tx : CloseTx(t)

\*@type: (() => Bool);          
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<store, tx, snapshotStore, written, missed>>
----------------------------------------------------------------------------

\*  modified actions

\* @type: ( $state, Int ) => Set( $state );
OpenTxState(state, t) ==
    IF   t \notin state.tx
    THEN LET s == [state EXCEPT !.tx = state.tx \cup {t} ]
             s2 == [s EXCEPT !.snapshotStore = [s.snapshotStore EXCEPT ![t] = s.store] ]
         IN  { s2 }
    ELSE {}

\* @type: $state => Set( $state );
OpenTxStates(state) ==
    UNION {OpenTxState(state, t) : t \in TxId}
    
\* @type: ( $state, Int, Int, Str ) => Set( $state );    
AddState(state, t, k, v) ==
    IF t \in tx /\ snapshotStore[t][k] = NoVal
    THEN LET s == [ state EXCEPT !.snapshotStore = [state.snapshotStore EXCEPT ![t][k] = v] ] 
             s2 ==  [ s EXCEPT !.written = [state.written EXCEPT ![t] = @ \cup {k}] ]
             IN { s2 }
    ELSE {}

\* @type: $state => Set( $state );
AddStates(state) ==
    UNION {AddState(state, t, k, v) : t \in TxId, k \in Key, v \in Val}   

\* @type: ( $state, Int, Int, Str ) => Set( $state );   
UpdateState(state, t, k, v) ==
    IF t \in tx /\ snapshotStore[t][k] \notin {NoVal, v}
    THEN LET s == [ state EXCEPT !.snapshotStore = [state.snapshotStore EXCEPT ![t][k] = v] ]
             s2 == [s EXCEPT !.written = [state.written EXCEPT ![t] = @ \cup {k}] ]
         IN { s2 }
    ELSE {}

\* @type: $state => Set( $state );
UpdateStates(state) ==
    UNION {UpdateState(state, t, k, v) : t \in TxId, k \in Key, v \in Val}
    
\* @type: ( $state, Int, Int ) => Set( $state );   
RemoveState(state, t, k) ==
    IF t \in tx /\ snapshotStore[t][k] /= NoVal    
    THEN LET s == [state EXCEPT !.snapshotStore = [state.snapshotStore EXCEPT ![t][k] = NoVal]]
             s2 == [s EXCEPT !.written = [state.written EXCEPT ![t] = @ \cup {k}]]
             IN { s2 }
    ELSE {}

\* @type: $state => Set( $state );
RemoveStates(state) == 
    UNION {RemoveState(state, t, k) : t \in TxId, k \in Key} 

\* @type: ( $state, Int ) => Set( $state );   
RollbackState(state, t) ==
    IF t \in tx
    THEN LET s == [ state EXCEPT !.tx = state.tx \ {t} ]
             s2 == [ s EXCEPT !.snapshotStore = [state.snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]] ]
             s3 == [ s2 EXCEPT !.written = [state.written EXCEPT ![t] = {}] ]
             s4 == [ s3 EXCEPT !.missed = [state.missed EXCEPT ![t] = {}] ]
         IN { s4 }
    ELSE {}

\* @type: $state => Set( $state );
RollbackStates(state) ==
    UNION {RollbackState(state, t) : t \in TxId} 

\* @type: ( $state, Int ) => Set( $state );   
CloseTxState(state, t) ==
    IF t \in tx /\  missed[t] \cap written[t] = {}
    THEN LET s == [ state EXCEPT !.store = [k \in Key |-> IF k \in state.written[t] THEN state.snapshotStore[t][k] ELSE state.store[k]] ]
             s2 == [ s EXCEPT !.tx = state.tx \ {t} ]
             s3 == [ s2 EXCEPT !.missed = [otherTx \in TxId |-> IF otherTx \in s2.tx THEN state.missed[otherTx] \cup state.written[t] ELSE {}]]
             s4 == [ s3 EXCEPT !.snapshotStore = [state.snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]] ]
             s5 == [ s4 EXCEPT !.written = [state.written EXCEPT ![t] = {}] ]
         IN { s5 }
    ELSE {}

\* @type: $state => Set( $state );    
CloseTxStates(state) ==
    UNION {CloseTxState(state, t) : t \in TxId}

----------------------------------------------------------------------------

\* @type: $state;
S == [store |-> store, 
      tx |-> tx,
      snapshotStore |-> snapshotStore,
      written |-> written,
      missed |-> missed]

\* @type: $state => $state;
TraceAll(s) ==
    [
     store |-> s.store,
     tx |-> s.tx,
     snapshotStore |-> s.snapshotStore,
     written |-> s.written,
     missed |-> s.missed
    ]

\* @type: $state => { tx: Set(Int), snapshotStore: Int -> $store };
TraceSome(s) ==
    [
     \*store |-> s.store,
     tx |-> s.tx,
     snapshotStore |-> s.snapshotStore
     \*written |-> s.written
     \*missed |-> s.missed
    ]
      
Trace(s) ==
    TraceSome(s)

\*@type: (() => Bool);  
WeakTraceRule ==
     [][vars # vars' => traceVars # traceVars']_<<vars, traceVars>>

\*@type: (() => Bool);  
UsefulTraceRules == 
   /\ \A s1, s2 \in OpenTxStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in AddStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in UpdateStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in RemoveStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in RollbackStates(S) : s1 # s2 => Trace(s1) # Trace(s2)
   /\ \A s1, s2 \in CloseTxStates(S) : s1 # s2 => Trace(s1) # Trace(s2)

\*@type: (() => Bool);  
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
\* Last modified Thu Jun 20 10:31:31 PDT 2024 by user
\* Created Mon Jun 03 17:44:12 PDT 2024 by user
