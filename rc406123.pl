% Rafał Czarnecki - 406123
ensure_loaded(library(lists)).


% Array utilites:
checkVal(_, []).
checkVal(Val, [H|T]) :- H = Val, checkVal(Val, T).
% Creates an array of length Length with values Val
initArray(Val, Length, Arr) :- 
    integer(Val), 
    length(Arr, Length), 
    checkVal(Val, Arr).

replace(0, Val, [_|T], L) :- L = [Val|T].
replace(N, Val, [H|T], L) :- N1 is N - 1, replace(N1, Val, T, TL), L = [H|TL].


% Expressions:
arithmExpr(X) :- simpleExpr(X); oper(X).

simpleExpr(X) :- integer(X); variable(X).

array(X, Y) :- atom(X), arithmExpr(Y).

variable(X) :- atom(X).
variable(array(X, Y)) :- array(X, Y).

oper(S1+S2) :- simpleExpr(S1), simpleExpr(S2).
oper(S1-S2) :- simpleExpr(S1), simpleExpr(S2).
oper(S1*S2) :- simpleExpr(S1), simpleExpr(S2).
oper(S1/S2) :- simpleExpr(S1), simpleExpr(S2).

:- op(700, xfx, <>).
logicExpr(S1<S2) :- simpleExpr(S1), simpleExpr(S2).
logicExpr(S1=S2) :- simpleExpr(S1), simpleExpr(S2).
logicExpr(S1<>S2) :- simpleExpr(S1), simpleExpr(S2).


% Instructions:
assign(X, Y) :- variable(X), arithmExpr(Y).
goto(X) :- integer(X).
condGoto(X, Y) :- logicExpr(X), integer(Y).
sekcja.


% Input file:
variables(X) :- is_list(X).
arrays(X) :- is_list(X).

checkInstructions([]).
checkInstructions([assign(X, Y)|T]) :- assign(X, Y), checkInstructions(T).
checkInstructions([goto(X)|T]) :- goto(X), checkInstructions(T).
checkInstructions([condGoto(X, Y)|T]) :- condGoto(X, Y), checkInstructions(T).
checkInstructions([sekcja|T]) :- checkInstructions(T).
program(X) :- is_list(X), checkInstructions(X).


% State:
variableState(Name, Value) :- atom(Name), integer(Value).
arrayState(Name, Array) :- atom(Name), is_list(Array).
instrState(List) :- is_list(List).
criticalState(List) :- is_list(List).

% State consists of program instructions (Instr), variables as a list of
% variableStates (Var), arrays as a list of arrayStates (Arr), a list of length
% Pid where InstrNum[Pid] is a number of a next line of code process Pid will
% run and a list of length Pid where Crit[Pid] is 1 if process Pid is in the
% critical state. If is equal to 0 otherwise. 
state(Instr, Var, Arr, InstrNum, Crit) :- 
    program(Instr),
    is_list(Var),
    is_list(Arr),
    instrState(InstrNum),
    criticalState(Crit).
    
emptyState(N, Instr, Var, Arr, State) :- 
    initArray(1, N, InstrNum),
    initArray(0, N, Critical),
    program(Instr),
    State = state(Instr, Var, Arr, InstrNum, Critical).
    
initState(program(Var, Arr, Instr), N, State) :- 
    emptyState(N, Instr, Var, Arr, State).


% Reading state from the file
initVariableState([], S) :- S = [].
initVariableState([V|T], S) :- 
    initVariableState(T, TS), 
    S = [variableState(V, 0)|TS].

initArrayState(_, [], S) :- S = [].
initArrayState(N, [A|T], S) :- 
    initArrayState(N, T, TS), 
    initArray(0, N, Arr), 
    S = [arrayState(A, Arr)|TS].

readProg(N, Filename, State) :- 
    exists_file(Filename),
    see(Filename),
    read(variables(V)),
    read(arrays(A)),
    read(program(P)),
    seen,
    initVariableState(V, Var),
    initArrayState(N, A, Arr),
    initState(program(Var, Arr, P), N, State).

readProg(_, Filename, _) :-
    not(exists_file(Filename)),
    format("Error: no file named - ~s\n", [Filename]).


% Evaluate expressions
eval(_, _, X, Result) :- integer(X), Result = X. % Evaluate integers

eval(Pid, State, array(X, Y), Result) :- % Evaluate arrays
    eval(Pid, State, Y, Index),
    State = state(_, _, ArrState, _, _),
    member(arrayState(X, Arr), ArrState),
    nth0(Index, Arr, Result).
    
eval(Pid, _, pid, Result) :- Result = Pid. % Evaluate Pid
eval(_, State, X, Result) :- % Evaluate variable
    atom(X),
    State = state(_, VarState, _, _, _),
    member(variableState(X, Result), VarState).
    
eval(Pid, State, S1+S2, Result) :- % Evaluate arithmetic operations
    eval(Pid, State, S1, RS1),
    eval(Pid, State, S2, RS2),
    Result is RS1 + RS2.
eval(Pid, State, S1-S2, Result) :- 
    eval(Pid, State, S1, RS1),
    eval(Pid, State, S2, RS2),
    Result is RS1 - RS2.
eval(Pid, State, S1*S2, Result) :- 
    eval(Pid, State, S1, RS1),
    eval(Pid, State, S2, RS2),
    Result is RS1 * RS2.
eval(Pid, State, S1/S2, Result) :- 
    eval(Pid, State, S1, RS1),
    eval(Pid, State, S2, RS2),
    Result is RS1 // RS2. % Since the tasks specifies that the variables 
                          % are integers, I'm using an integer division.
         
eval(Pid, State, S1<S2, Result) :- % Evaluate logic operators
    eval(Pid, State, S1, RS1),
    eval(Pid, State, S2, RS2),
    ((RS1 < RS2, Result = 1); (RS1 >= RS2, Result = 0)).         
eval(Pid, State, S1=S2, Result) :- 
    eval(Pid, State, S1, RS1),
    eval(Pid, State, S2, RS2),
    ((RS1 =:= RS2, Result = 1); (RS1 =\= RS2, Result = 0)).         
eval(Pid, State, S1<>S2, Result) :- 
    eval(Pid, State, S1, RS1),
    eval(Pid, State, S2, RS2),
    ((RS1 =\= RS2, Result = 1); (RS1 =:= RS2, Result = 0)).


% Run instructions
nextInstr(Pid, Max, InstrNum, NewInstrNum) :- 
    nth0(Pid, InstrNum, Num),
    Num1 is Num + 1,
    Num1 =< Max,
    replace(Pid, Num1, InstrNum, NewInstrNum).
    
nextInstr(Pid, Max, InstrNum, NewInstrNum) :- 
    nth0(Pid, InstrNum, Num),
    Num1 is Num + 1,
    Num1 > Max,
    replace(Pid, 1, InstrNum, NewInstrNum).
    
run(Pid, State, assign(X, Y), OutState) :- 
    atom(X),
    State = state(Instr, VarState, Arr, InstrNum, Crit),
    replace(Pid, 0, Crit, NewCrit),
    length(Instr, InstrLen),
    nextInstr(Pid, InstrLen, InstrNum, NewInstrNum),
    member(variableState(X, Var), VarState),
    eval(Pid, State, Y, EvalY),
    select(variableState(X, Var), VarState, variableState(X, EvalY), NewVarState),
    OutState = state(Instr, NewVarState, Arr, NewInstrNum, NewCrit).
    
run(Pid, State, assign(array(ArrName, ArrIndex), Y), OutState) :- 
    State = state(Instr, Var, ArrState, InstrNum, Crit),
    replace(Pid, 0, Crit, NewCrit),
    length(Instr, InstrLen),
    nextInstr(Pid, InstrLen, InstrNum, NewInstrNum),
    member(arrayState(ArrName, Arr), ArrState),
    eval(Pid, State, Y, EvalY),
    eval(Pid, State, ArrIndex, Index),
    replace(Index, EvalY, Arr, NewArr),
    select(arrayState(ArrName, Arr), ArrState, arrayState(ArrName, NewArr), NewArrState),
    OutState = state(Instr, Var, NewArrState, NewInstrNum, NewCrit).
    

run(Pid, State, goto(X), OutState) :- 
    State = state(Instr, Var, Arr, InstrNum, Crit),
    replace(Pid, 0, Crit, NewCrit),
    replace(Pid, X, InstrNum, NewInstrNum),
    OutState = state(Instr, Var, Arr, NewInstrNum, NewCrit).
    
run(Pid, State, condGoto(X, Y), OutState) :- 
    State = state(Instr, Var, Arr, InstrNum, Crit),
    replace(Pid, 0, Crit, NewCrit),
    eval(Pid, State, X, EvalX),
    ((EvalX == 1, replace(Pid, Y, InstrNum, NewInstrNum));
     (EvalX == 0, length(Instr, InstrLen), nextInstr(Pid, InstrLen, InstrNum, NewInstrNum))),
    OutState = state(Instr, Var, Arr, NewInstrNum, NewCrit).
    
run(Pid, State, sekcja, OutState) :- 
    State = state(Instr, Var, Arr, InstrNum, Crit),
    replace(Pid, 1, Crit, NewCrit),
    length(Instr, InstrLen),
    nextInstr(Pid, InstrLen, InstrNum, NewInstrNum),
    OutState = state(Instr, Var, Arr, NewInstrNum, NewCrit).

step(_, InState, Pid, OutState) :- 
    InState = state(Instr, _, _, InstrNum, _),
    nth0(Pid, InstrNum, InstrIndex),
    nth1(InstrIndex, Instr, CurrentInstr),
    run(Pid, InState, CurrentInstr, OutState).
    

% Writing logs
trace(_Pid, _InstrNum).
status(_State, _Trace).

writeCrit(MaxInstr, InstrNum, Crit) :- 
    write("=== Processes in the critical section ===\n"), 
    writeCritProcesses(MaxInstr, 0, InstrNum, Crit).

writeCritProcesses(MaxInstr, Pid, [I|IT], [C|CT]) :- 
    C == 1, 
    ((I =\= 1, PrevI is I - 1);
     (I =:= 1, PrevI is MaxInstr)),
    format("Process ~d: entered the critical section in (~d) line\n", [Pid, PrevI]),
    Pid1 is Pid + 1,
    writeCritProcesses(MaxInstr, Pid1, IT, CT).   

writeCritProcesses(MaxInstr, Pid, [_|IT], [C|CT]) :- 
    C == 0,
    Pid1 is Pid + 1,
    writeCritProcesses(MaxInstr, Pid1, IT, CT).

writeCritProcesses(_, _, [], []).

writeTrace(Trace) :- 
    write("=== Trace ===\n"), 
    writeTraceProcesses(Trace, []).

writeTraceProcesses([trace(Pid, Instr)|T], VisitedPids) :- 
    member(Pid, VisitedPids),
    writeTraceProcesses(T, VisitedPids),
    format("Process ~d: ~d\n", [Pid, Instr]).

writeTraceProcesses([trace(Pid, _)|T], VisitedPids) :- 
    not(member(Pid, VisitedPids)),
    writeTraceProcesses(T, [Pid|VisitedPids]).   

writeTraceProcesses([], _).

writeLog(Status) :- 
    Status = status(state(Instr, _, _, InstrNum, Crit), Trace),
    length(Instr, MaxInstr),
    writeCrit(MaxInstr, InstrNum, Crit),
    writeTrace(Trace).
    

% Verify
% Checks if there are at least two processes in the critical section
notSafe(State) :- 
    State = status(state(_, _, _, _, Crit), _),
    notSafe(Crit, Res),
    Res >= 2.
    
notSafe([H|T], Res) :- 
    notSafe(T, R),
    ((H == 1, Res is R + 1);
     (H == 0, Res is R)).
    
notSafe([], Res) :- Res is 0.

checkIfNotSafe(H, Status) :- not(is_list(H)), notSafe(H), Status = H.
checkIfNotSafe([H|T], Status) :- 
    (notSafe(H), Status = H); 
    (not(notSafe(H)), checkIfNotSafe(T, Status)).

% Generates all possible states
getStates(_, _, State, _, CurrentlyVisitedStated, VisitedStates) :- 
    member(status(State, _), CurrentlyVisitedStated),
    VisitedStates = CurrentlyVisitedStated.
    
getStates(N, Pid, State, Trace, CurrentlyVisitedStated, VisitedStates) :- 
    Pid =:= N,
    VisitedStates = [status(State, Trace)|CurrentlyVisitedStated].

getStates(_, _, State, Trace, CurrentlyVisitedStated, VisitedStates) :- 
    notSafe(State),
    VisitedStates = [status(State, Trace)|CurrentlyVisitedStated].
    
getStates(N, Pid, State, Trace, CurrentlyVisitedStated, VisitedStates) :- 
    not(member(status(State, _), CurrentlyVisitedStated)),
    Pid < N,
    not(notSafe(State)),
    step(N, State, Pid, NextState),
    State = state(_, _, _, InstrNum, _),
    nth0(Pid, InstrNum, Num),
    NextTrace = [trace(Pid, Num)|Trace],
    getStates(N, 0, NextState, NextTrace, [status(State, Trace)|CurrentlyVisitedStated], NewStates),
    Pid1 is Pid + 1,
    select(status(State, _), NewStates, NewStates2),
    getStates(N, Pid1, State, Trace, NewStates2, VisitedStates).
    
verify(N, Prog) :- 
    integer(N),
    N > 0,
    atom(Prog),
    exists_file(Prog),
    readProg(N, Prog, State),
    getStates(N, 0, State, [], [], VisitedStates),
    checkIfNotSafe(VisitedStates, Status),
    write("Program is unsafe.\n"),
    writeLog(Status).

verify(N, Prog) :- 
    integer(N),
    N > 0,
    atom(Prog),
    exists_file(Prog),
    readProg(N, Prog, State),
    getStates(N, 0, State, [], [], VisitedStates),
    not(checkIfNotSafe(VisitedStates, _)),
    write("Program is safe.\n").
                   
verify(N, _) :-
    not(integer(N)),
    format("Error: parameter ~w should be an integer > 0\n", [N]). 

verify(N, _) :-
    integer(N),
    N =< 0,
    format("Error: parameter ~w should be an integer > 0\n", [N]). 

verify(_, Filename) :-
    atom(Filename),
    not(exists_file(Filename)),
    format("Error: no file named - ~s\n", [Filename]).

verify(_, Filename) :-
    not(atom(Filename)),
    format("Error: no file named - ~w\n", [Filename]).

verify :-
    current_prolog_flag(argv, Argv),
    nth0(1, Argv, NAtom),
    nth0(2, Argv, Prog),
    atom_number(NAtom, N),
    verify(N, Prog).
    