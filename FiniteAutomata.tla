---------------------------- MODULE FiniteAutomata ----------------------------

EXTENDS TLC, Sequences

\* Finite automata structure and methods

NFA(alphabet, initial, final, states) ==
    [alphabet |-> alphabet,
     initial  |-> initial, 
     final    |-> final, 
     states   |-> states]

StateIds(nfa) == DOMAIN nfa.states

Transitions(nfa, state) == nfa.states[state]

TransitionLabel(nfa, from, dest) == nfa.states[from][dest]

TransitionsNotEmpty(nfa, from) ==
    {dest \in DOMAIN Transitions(nfa, from): TransitionLabel(nfa, from, dest) # {}}

RemoveEmptyTransitions(nfa) ==
    LET stateIds  == StateIds(nfa) 
        newStates == [from \in stateIds |-> [dest \in TransitionsNotEmpty(nfa, from)
                        |-> TransitionLabel(nfa, from, dest)]]
    IN NFA(nfa.alphabet, nfa.initial, nfa.final, newStates) 

AutomataProduct(nfa1, nfa2) ==
    LET newIDs      == StateIds(nfa1) \X StateIds(nfa2)
        newAlphabet == nfa1.alphabet \intersect nfa2.alphabet
        newInitial  == nfa1.initial \X nfa2.initial
        newFinal    == nfa1.final \X nfa2.final
        newStates   == [from \in newIDs |-> [dest \in newIDs |->
                        {label \in newAlphabet:
                            /\ dest[1] \in DOMAIN Transitions(nfa1, from[1])
                            /\ dest[2] \in DOMAIN Transitions(nfa2, from[2])
                            /\ label \in TransitionLabel(nfa1, from[1], dest[1])
                            /\ label \in TransitionLabel(nfa2, from[2], dest[2])
                        }]]
    IN RemoveEmptyTransitions(NFA(newAlphabet, newInitial, newFinal, newStates))

RECURSIVE Path_aux(_, _, _, _)
Path_aux(nfa, from, dest, visited) ==
            IF from = dest THEN <<dest>>
            ELSE LET paths == 
                    {path \in {Path_aux(nfa, state, dest, visited \union {state}):
                            state \in (DOMAIN Transitions(nfa, from) \ visited)}:
                        path # <<>>}
                 IN IF paths = {} THEN <<>>
                    ELSE LET path == CHOOSE p \in paths: TRUE
                         IN <<from>> \o path

Path(nfa, state1, state2) == Path_aux(nfa, state1, state2, {state1})

StateIsUseful(nfa, state) ==
    \E initial \in nfa.initial: \E final \in nfa.final:
        /\ Path(nfa, initial, state) # <<>>
        /\ Path(nfa, state, final)   # <<>>

Trim(nfa) ==
    LET usefulStates == {s \in StateIds(nfa): StateIsUseful(nfa, s)}
    IN NFA(
        nfa.alphabet,
        nfa.initial \intersect usefulStates,
        nfa.final \intersect usefulStates,
        [state \in usefulStates |-> nfa.states[state]]
    )

InSameComponent(nfa, state1, state2) ==
    /\ Path(nfa, state1, state2) # <<>>
    /\ Path(nfa, state2, state1) # <<>> 

AmbiguityTest(nfa) ==
    LET conj == Trim(AutomataProduct(nfa,nfa))
    IN \E s \in StateIds(conj): s[1] # s[2]    

EDATest(nfa) ==
    LET conj     == Trim(AutomataProduct(nfa,nfa))
        stateIds == StateIds(conj)
    IN  \E state1 \in stateIds: \E state2 \in stateIds:
            /\ state1 # state2
            /\ InSameComponent(conj, state1, state2)
            /\ state1[1] = state1[2]
            /\ state2[1] # state2[2]

IDATest(nfa) ==
    LET conj     == Trim(AutomataProduct(nfa,nfa))
        conj2    == Trim(AutomataProduct(conj,nfa))
        stateIds == StateIds(nfa)
    IN  \E p \in stateIds: \E q \in stateIds:
            /\ p # q
            /\ <<<<p,p>>,q>> \in StateIds(conj2)
            /\ <<<<p,q>>,q>> \in StateIds(conj2)
            /\ Path(conj2, <<<<p,p>>,q>>, <<<<p,q>>,q>>) # <<>>

-------------------------------------------------------------------------------

\* Sample finite automata

n0 == "n0"
n1 == "n1"
n2 == "n2"
n3 == "n3"

\* unambiguous automaton
UFA == 
    NFA({"a"}, {n0}, {n0}, [
        n0 |-> [n0 |-> {"a"}]
    ])

\* finitely ambiguous automaton
FNFA ==
    NFA({"a"}, {n0}, {n1,n2}, [
        n0 |-> [n1 |-> {"a"}, n2 |-> {"a"}],
        n1 |-> [n1 |-> {"a"}],
        n2 |-> [n2 |-> {"a"}]
    ])

\* polynomially ambiguous automaton
PNFA ==
    NFA({"a"}, {n0}, {n1},[
        n0 |-> [n0 |-> {"a"}, n1 |-> {"a"}],
        n1 |-> [n1 |-> {"a"}]
    ])

\* exponentially ambiguous automaton
ENFA ==
    NFA({"a"}, {n0}, {n0},[
        n0 |-> [n1 |-> {"a"}, n2 |-> {"a"}],
        n1 |-> [n0 |-> {"a"}],
        n2 |-> [n0 |-> {"a"}]
    ])

Example ==
    NFA({"a","b"}, {n0},{n2}, [
        n0 |-> [n1 |-> {"a"}, n3 |-> {"b"}],
        n1 |-> [n0 |-> {"b"}, n2 |-> {"a"}],
        n2 |-> <<>>,
        n3 |-> <<>>
    ])

-------------------------------------------------------------------------------

\* Test

ASSUME PrintT("AmbiguityTest")

ASSUME PrintT(AmbiguityTest(UFA))
ASSUME PrintT(AmbiguityTest(FNFA))
ASSUME PrintT(AmbiguityTest(PNFA))
ASSUME PrintT(AmbiguityTest(ENFA))

ASSUME PrintT("EDATest")

ASSUME PrintT(EDATest(UFA))
ASSUME PrintT(EDATest(FNFA))
ASSUME PrintT(EDATest(PNFA))
ASSUME PrintT(EDATest(ENFA))

ASSUME PrintT("IDATest")

ASSUME PrintT(IDATest(UFA))
ASSUME PrintT(IDATest(FNFA))
ASSUME PrintT(IDATest(PNFA))
ASSUME PrintT(IDATest(ENFA))

===============================================================================