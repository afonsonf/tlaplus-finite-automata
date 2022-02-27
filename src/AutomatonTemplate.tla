--------------------------- MODULE AutomatonTemplate ---------------------------

EXTENDS TLC, IOUtils, HTML, Sequences, FiniteSetsExt

FiniteAutomata == INSTANCE FiniteAutomata

\***** Helpers
StateIds(x) == FiniteAutomata!StateIds(x)

ReachableFromState(nfa, from) ==
    FiniteAutomata!ReachableFromState(nfa, from)

TransitionLabel(nfa, from, dest) ==
    FiniteAutomata!TransitionLabel(nfa, from, dest)

ConcatenateStringSet(stringSet) ==
    FoldSet(LAMBDA x,y: x \o y, "", stringSet)

\***** Classes

Classes == <<
    HTMLClass(".ClassInfo", <<
        HTMLAttribute("margin", "auto"),
        HTMLAttribute("border-bottom", "0px"),
        HTMLAttribute("text-align", "center")
    >>),
    HTMLClass(".ClassPage", <<
        HTMLAttribute("margin", "auto")
    >>)
>>

\***** Body

Page == HTMLFrame("layout", <<
    HTMLBox("info", <<"ClassInfo">>, HTMLSize("90%", "100%"), <<
        "Initial State: Square node || Final State: Green node">>),
    HTMLBox("page", <<"ClassPage">>, HTMLSize("90%", "400px"), <<>>)
>>)

\***** Draw NFA

Node(vars, state) ==
    LET shape == IF state \in vars.nfa.initial
                 THEN "box" ELSE "ellipse"
        color == IF state \in vars.nfa.final
                 THEN "lightgreen" ELSE "lightblue"
    IN HTMLFill(
        "{ id: \"%nameID%\", label: \"   %name%   \""\o
        ", color: {border: \"black\", background: \"%color%\"}"\o
        ", shape: \"%shape%\", borderWidth: 2"\o
        ", margin: {top: 10, bottom: 10} },\n",
        << <<"%nameID%", state>>,
           <<"%name%", state>>,
           <<"%shape%", shape>>,
           <<"%color%", color>> >>)

NodesVar(vars) ==
    "var nodes = new vis.DataSet([ \n" \o
    ConcatenateStringSet(
        {Node(vars, state): state \in StateIds(vars.nfa)}) \o
    "]);"

Edge(vars, from, dest) == HTMLFill(
    "{ from: \"%from%\", to: \"%dest%\", label: \"%label%\", arrows: \"to\"},\n",
    << <<"%from%", from>>,
       <<"%dest%", dest>>,
       <<"%label%", TransitionLabel(vars.nfa, from, dest)>> >>)

EdgesVar(vars) ==
    "var edges = new vis.DataSet([ \n" \o
    ConcatenateStringSet(FlattenSet({
        {Edge(vars, from, dest):
            dest \in ReachableFromState(vars.nfa, from)}:
        from \in StateIds(vars.nfa)})) \o
    "]);"

ContainerVar(name) == HTMLFill(
    "var container = document.getElementById(\"%name%\");",
    << <<"%name%", name>> >>)

CreateNetwork ==
    "var data = { nodes: nodes, edges: edges }; \n" \o
    "var options = {}; \n" \o
    "var network = new vis.Network(container, data, options);"

DrawNFA(vars) == HTMLScript(<<
    NodesVar(vars),
    EdgesVar(vars),
    ContainerVar("page"),
    CreateNetwork
>>)

\***** Template Main

Body == HTMLBody( Page )

Header == HTMLHeader("Automaton", <<>>, Classes)

Scripts(vars) == <<
    HTMLScriptFile("https://unpkg.com/vis-network/standalone/umd/vis-network.min.js"),
    DrawNFA(vars)
>>

Template(vars) == HTMLDocument(Header, Body, Scripts(vars))

\***** Test Template

PrintNFA(nfa, name) ==
    PrintT(Serialize(Template([nfa |-> nfa]), "../html/examples/" \o name \o ".html",
           [format      |-> "TXT",
            charset     |-> "UTF-8",
            openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]))

ASSUME PrintNFA(FiniteAutomata!Example, "example")
ASSUME PrintNFA(FiniteAutomata!UFA, "ufa")
ASSUME PrintNFA(FiniteAutomata!FNFA, "fnfa")
ASSUME PrintNFA(FiniteAutomata!PNFA, "pnfa")
ASSUME PrintNFA(FiniteAutomata!ENFA, "enfa")

================================================================================
