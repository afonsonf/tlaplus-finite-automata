---------------------------- MODULE FiniteAutomata ----------------------------

EXTENDS TLC

\* Finite automata structure and methods

NFA(alphabet, initial, final, states) ==
    [alphabet |-> alphabet,
     initial  |-> initial, 
     final    |-> final, 
     states   |-> states]

StateIds(nfa) == DOMAIN nfa.states

Transitions(nfa, state) == nfa.states[state]

TransitionLabel(nfa, from, dest) == nfa.states[from][dest]

AutomataProduct(nfa1, nfa2) ==
    LET newIDs      == StateIds(nfa1) \X StateIds(nfa2)
        newAlphabet == nfa1.alphabet \intersect nfa2.alphabet
        newInitial  == nfa1.initial \X nfa2.initial
        newFinal    == {}
        newStates   == [from \in newIDs |-> [dest \in newIDs |->
                        {label \in newAlphabet:
                            /\ dest[1] \in DOMAIN Transitions(nfa1, from[1])
                            /\ dest[2] \in DOMAIN Transitions(nfa2, from[2])
                            /\ label \in TransitionLabel(nfa1, from[1], dest[1])
                            /\ label \in TransitionLabel(nfa2, from[2], dest[2])
                        }]]
    IN NFA(newAlphabet, newInitial, newFinal, newStates)

RemoveEmptyTransitions(nfa) ==
    LET stateIds  == StateIds(nfa) 
        newStates == [from \in stateIds |->
                        [dest \in {dest_aux \in stateIds: TransitionLabel(nfa, from, dest_aux) # {}}
                            |-> TransitionLabel(nfa, from, dest)]]
    IN NFA(nfa.alphabet, nfa.initial, nfa.final, newStates) 

-------------------------------------------------------------------------------

\* Sample finite automata

n0 == "n0"
n1 == "n1"
n2 == "n2"

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

-------------------------------------------------------------------------------

\* Test

ASSUME PrintT(RemoveEmptyTransitions(AutomataProduct(UFA, UFA)))
ASSUME PrintT(RemoveEmptyTransitions(AutomataProduct(FNFA, FNFA)))
ASSUME PrintT(RemoveEmptyTransitions(AutomataProduct(PNFA, PNFA)))
ASSUME PrintT(RemoveEmptyTransitions(AutomataProduct(ENFA, ENFA)))

===============================================================================