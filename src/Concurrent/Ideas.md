Lessons learned:
- PIDsOf cannot be defined for the co-inductive representation of the process pool/ether - new fresh PIDs cannot be generated
- Using functions for process pools is
  - simple for the definitions;
  - hard, if its properties (e.g., dom) are needed, for example for fresh variable generation.
- Bisimulations
  - Playing with bisimulation in Erlang -> this paper only considers ethers
    and defines observations based on the "dangling" messages
  - The usual notion of bisimulations involves checking equality on actions, 
    however, in this case we could not reason about systems using different 
    PIDs (e.g., two systems could communicate on different input PIDs).
  - Bisimulations + bijective function on the PIDs? Drawback: we have to 
    somehow rename all PIDs in signals/messages, which might be impossible
    for closure values (because they include a body expression which could
    contain e.g., "self()" calls, where the PID is not syntactically there).
      ^---- would be enough to observe the "type" of these actions?
    - How "deep" action parameters should be investigated? Should they
      be equivalent, or check only the type, or nothing?
    - Could we rename PIDs in the bisimilar systems for the first time,
      so that PID bijection is not needed (the currently existing PIDs
      of the system), and then suppose that the processes spawn with the same
      PIDs? <- probably not
    - Observable behaviour: signals exiting the system, but not the internal
      signals and communication -> unTaken PIDs should be observed in the ether
  - Strong bisimulation: the two systems have to do the same steps
    - I don't see a relation besides equality that could satisfy this
  - Weak bisimulation: the two systems have to do the same communication steps
    - Too restrictive to reason about systems that use a different number of
      communication steps (e.g., server that catches errors vs server that is
      re-created when errors occur)
  - "Barbed bisimulation": the two systems should produce the same signals to
    the outside world + the evolution of the systems should preserve the relation
    - Too many soft definitions in the papers - e.g., "used PID"
      - Does it include only dangling signals, or all used pids?

    - Does Lemma 1 (compatible reductions create compatible nodes) of Playing with Bisimulation in Erlang hold for us? e.g.,
      (ether, ι ↦ ι' ! 'cat') -[arrive(exit, ι)]-> (ether, ι ↦ deadproc)
      (ether, ι ↦ ι' ! 'cat') -[send('cat', ι')]-> (ether ∪ {(ι, ι', 'cat')}, ι ↦ 'cat')

    - In Lanese et al., Lemma 9 does not hold for this semantics,
      because arrival can change the semantics of receive primops!!!
      E.g., recv_peek_message returns None for empty mailbox, while the
      first message if it is nonempty (and arrival can put a message into the
      empty mailbox).
- Renaming
  - Concurrent renaming won't work with stdpp's map formalism - it is required for `kmap` that the function used for mapping is injective,
    while we use renaming to replace the spawned PID with a fresh PID, if it is used in the renaming (to avoid accidental capture in the renaming). E.g., 
    
        1 : P || 2 : Q || ∅ -[spawn 4]-> 1: P || 2: Q || 4: R || ∅
        rename 3 into 4
        1 : P || 2 : Q || ∅ -[spawn 5]-> 1: P || 2: Q || 5: R || ∅

    the function `fun x => match x with | 3 => 4 | 4 => 5 | y => y end` used for this is not injective!
  - For sequential renaming, we need to use symmetrical renamings to preserve injectivity (for abstractions expressed with stdpp's maps - ethers, pools, dead processes).
- Simulation equivalence vs bisimulation
  - The latter implies the former
  - Simulation equivalence is less restrictive
- Confluence
  - There are a number of actions that affect the confluence of the process:
    - `'trap_exit'` flag, list of linked processes - if these are modified in one reduction, then an exit message can arrive in different ways before and after the modification.
    - If the mailbox is modified (e.g., by `remove_message`), then it potentially affects the semantics of other mailbox operations (e.g., `recv_peek_message` potentially fails after the removal).
    
