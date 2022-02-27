------------------------- MODULE PowersetConstruction -------------------------

EXTENDS TLC, FiniteSetsExt

FiniteAutomata == INSTANCE FiniteAutomata
NFA == FiniteAutomata!FNFA

VARIABLE DFA_alphabet
VARIABLE DFA_initial
VARIABLE DFA_final
VARIABLE DFA_states

VARIABLE toExpand

DFA == FiniteAutomata!NFA(DFA_alphabet, DFA_initial, DFA_final, DFA_states)

empty == {"empty"}

Init == 
    /\ DFA_alphabet = NFA.alphabet
    /\ DFA_initial  = {NFA.initial}
    /\ DFA_final    = {}
    /\ DFA_states    = <<>>
    /\ toExpand     = {NFA.initial}

addTransition(states, from, token, dest) ==
    LET existPrev == from \in DOMAIN states
    IN  [state \in (DOMAIN states \union {from}) |->
            IF state # from
            THEN states[state]
            ELSE [t \in DFA_alphabet |->
                    IF t # token
                    THEN IF existPrev /\ t \in DOMAIN states[from]
                         THEN states[from][t] ELSE {}
                    ELSE IF existPrev /\ token \in DOMAIN states[from]
                         THEN {dest} \union states[from][token]
                         ELSE {dest}]]

RECURSIVE expandTokens(_, _, _, _)
expandTokens(stateToExpand, tokens, leftToExpand, states) ==
    IF tokens = {}
    THEN /\ toExpand' = (toExpand \ {stateToExpand}) \union leftToExpand
         /\ DFA_states' = states
    ELSE
        LET token      == CHOOSE t \in tokens: TRUE
            fromToken_ == FlattenSet({NFA.states[n][token]:
                n \in {s \in stateToExpand \ empty: token \in DOMAIN NFA.states[s]}})
            fromToken  == IF fromToken_ = {} THEN empty ELSE fromToken_
            newStates  == addTransition(states, stateToExpand, token, fromToken)
            toExpand_  == IF fromToken \in DOMAIN DFA_states
                          THEN {} ELSE {fromToken}
        IN  /\ expandTokens(
                stateToExpand,
                tokens \ {token},
                leftToExpand \union toExpand_,
                newStates)

expand(stateToExpand) ==
    /\ IF \E state \in stateToExpand: state \in NFA.final
       THEN DFA_final' = DFA_final \union {stateToExpand}
       ELSE UNCHANGED DFA_final
    /\ expandTokens(stateToExpand, DFA_alphabet, {}, DFA_states)


Next ==
    /\ LET state == CHOOSE n \in toExpand: TRUE
       IN  expand(state)
    /\ UNCHANGED <<DFA_alphabet,DFA_initial>>

Inv == toExpand # {}

Alias ==[toExpand |-> toExpand,
         dfa |-> DFA,
         test |-> FiniteAutomata!AmbiguityTest(DFA)]

===============================================================================