% Katarzyna Herba
% Reprezentacja automatu: automat(Goto, Action).
% Goto: Lista elementów postaci goto(Nr1, Nieterminal, Nr2), gdzie Nr1 i Nr2
% to numery stanów.
% Action: Lista elementów postaci action(Nr1, Symbol, akcja), gdzie Nr1 to numer
% stanu, Symbol to jeden z {terminal, #, all}, a akcja to jeden z {accept,
% reduce(Produkcja), shift(Nr)}.
% Stan początkowy ma nr 0.

:- use_module(library(lists)).

% addStart(+Grammar1, -Grammar2)
% Grammar2 is same as Grammar1, but its start symbol is 'Z' and contains
% additional production Z -> S#, where S is start symbol od Grammar1.
addStart(gramatyka(S, P), gramatyka('Z', NewP)) :-
    Prod = prod('Z', [[nt(S), #]]),
    append([Prod], P, NewP) .

% constructRhsWithDots(+Rhs, +Number, -RhsListWithDots)
% As singleRhsWithDots, Number is the length of Rhs. XY@Z is represented as
% (XYZ, 2).                  
constructRhsWithDots(Rhs, N, RhsWithDots) :-
    N >= 0,
    N0 is N - 1,
    Z = [(Rhs, N)],
    constructRhsWithDots(Rhs, N0, Rhs_N0),
    append(Rhs_N0, Z, RhsWithDots) .
constructRhsWithDots(_, N, RhsWithDots) :-
    N < 0,
    RhsWithDots = [] .

% singleRhsWithDots(+Rhs, -RhsListWithDots)
% If Rhs is XYZ, RhsWithDots contains @XYZ, X@YZ, XY@Z, XYZ@.
singleRhsWithDots([], []) .
singleRhsWithDots(Rhs, RhsWithDots) :-
    % write('singleRhsWithDots '), write(Rhs), nl,
    length(Rhs, N),
    % write(N),
    constructRhsWithDots(Rhs, N, RhsWithDots) .


% singleProductionWithDots(+Production, -ProductionWithDots)
% As productionsWithDots but for productions from one symbol.
singleProductionWithDots(prod(S, []), prod(S, [])) .
singleProductionWithDots(prod(S, [Rhs | Xs]), prod(S, Prods)) :-
    % write('singleProductionWithDots\n'),
    singleRhsWithDots(Rhs, RhsWithDots),
    singleProductionWithDots(prod(S, Xs), prod(S, XsWithDots)),
    append(RhsWithDots, XsWithDots, Prods) .

% productionsWithDots(+ProductionList, -ProductionListWithDots)
% For each element of ProductionList of the form A -> XYZ,
% ProductionListWithDots contains A -> @XYZ, A -> X@YZ, A -> XY@Z, A -> XYZ@.
productionsWithDots([], []) .
productionsWithDots([Prod | Ps], ProdsWithDots) :-
    singleProductionWithDots(Prod, ProdWithDots),
    productionsWithDots(Ps, PsWithDots),
    append([ProdWithDots], PsWithDots, ProdsWithDots) .

isNonTerminal(nt(_)) .

% nextSymbol(+Prod, -Symbol)
% If Production1 is A -> X@YZ, then Symbol is Y.
nextSymbol(prod(_, [(Prod, N)]), Symbol) :- nth0(N, Prod, Symbol) .

% noNextSymbol(+Prod)
% True if Prod is of the form A -> XYZ@.
noNextSymbol(prod(_, [(Prod, N)])) :- length(Prod, M), M =:= N .

prodLength(prod(_, [(_, N)]), N) .

prodLhs(prod(S, _), S) .

% moveNext (+Production1, -Production2)
% If Production1 is A -> X@YZ, then Production2 is A -> XY@Z.
moveNext(prod(Z, [(Prod, N)]), prod(Z, [(Prod, M)])) :- M is N + 1 .

% moveAllNext (+ProductionList1, -ProductionList1)
% Does the same as moveNext, bbut for a list of productions.
moveAllNext([], []) .
moveAllNext([Prod | Prods], [MovedProd | MovedProds]) :-
    moveNext(Prod, MovedProd),
    moveAllNext(Prods, MovedProds) .

indexOf([X | _], X, 0) .
indexOf([_ | Xs], Elem, N) :-
    indexOf(Xs, Elem, M),
    N is M + 1 .

isConflict(konflikt(_, _, _, _, _)) .


% startingProductions(+RhsList, +Symbol, -ProductionList)
% ProductionList contains productions of form (prod(Symbol, [Rhs])) where Rhs is
% fo the form @ XYZ.
startingProductions([], _, []) .
startingProductions([(Prod, N) | Prods], Symbol, StartingProds) :-
    startingProductions(Prods, Symbol, StartingProdsFromProds),
    (N is 0 ->
        append([prod(Symbol, [(Prod, N)])], StartingProdsFromProds,
               StartingProds)
    ;   StartingProds = StartingProdsFromProds
    ) .

% startingProductionsFromSymbol(+ProductionList1, +Symbol, -ProductionList2)
% ProductionList2 contains productions from ProductionList1 of the form
% Symbol -> @ XYZ.
startingProductionsFromSymbol([], _, []) .
startingProductionsFromSymbol([prod(X, Rhs)| Prods], Symbol, ProdsFromSymbol) :-
    (X = Symbol ->
        startingProductions(Rhs, Symbol, ProdsFromSymbol);
        startingProductionsFromSymbol(Prods, Symbol, ProdsFromSymbol)) .


% productionClosure(+Production, +ProductionList1, +DoneProductions1,
%                   -ProductionList2, -DoneProductions2)
% ProductionList2 is the closure of Production.
productionClosure(Prod, Prods, Done, Closure, NewDone) :-
    %write('productionClosure: '),
    %write(Start), write('->'), write(Prod), nl,
    (noNextSymbol(Prod) ->
        % write('noNextSymbol'), nl,
        Closure = [Prod], NewDone = Done
    ;   nextSymbol(Prod, Symbol),
        %write(Symbol),nl,
        (isNonTerminal(Symbol) ->
            % write('nonTerm'), nl,
            (member(Prod, Done) ->
                % write('isMember'), nl,
                Closure = [], NewDone = Done
            ;   nt(UnwrappedSymbol) = Symbol,
                %write('UnwrappedSymbol '),
                %write(UnwrappedSymbol), nl,
                startingProductionsFromSymbol(Prods, UnwrappedSymbol,
                                              ProdsFromSymbol),
                %write('Prods from symbol '),write(ProdsFromSymbol), nl,
                append(Done, [Prod], DoneWithProd),
                %write('Done '), write(DoneWithProd), nl,
                closureWithDone(ProdsFromSymbol, Prods, DoneWithProd,
                                   ProdsFromSymbolClosure, NewDone),
                append([Prod], ProdsFromSymbolClosure, Closure)
            )
        ;   Closure = [Prod], NewDone = Done
        )
    ) .

% closureWithDone(+ProductionList1, +ProductionList2, +DoneProductions1,
%                 -ProductionList3, -DoneProductions2)
% closureWithDone does the same as closure but DoneProductions1 contains the
% productions from ProductionList1 that wre already closed and DoneProductions2
% productions closed after the function executes.
closureWithDone([], _, _, [], _) .
closureWithDone([ProdToClose | ProdsToClose], Prods, Done, Closure, NewDone) :-
    %write('closureWithDone '), write(Done), nl,
    %write('withProds '), write(ProdToClose), write(ProdsToClose), nl,
    productionClosure(ProdToClose, Prods, Done, ProdClosure, DoneAfterProd),
    %write('closureWithDone after single'), write(ProdClosure), nl,
    closureWithDone(ProdsToClose, Prods, DoneAfterProd, ProdsClosure, NewDone),
    append(ProdClosure, ProdsClosure, ClosureWithDups),
    remove_dups(ClosureWithDups, Closure) .


% closure(+ProductionList1, +ProductionList2, -ProductionList3)
% ProductionList3 is the closure of ProductionList1, where ProductionList2
% contains all productions.
closure(ProdsToClose, Prods, Closure) :-
    % write('closure'), nl,
    closureWithDone(ProdsToClose, Prods, [], Closure, _) .
    % TODO(Kasia): Sort closure

% prodsMoveableBySymbol(+ProductionList1, +Symbol, -ProductionList2)
% ProductionList2 contains all productions in ProductionList1 that were of the
% form X -> A@SymbolB.
prodsMoveableBySymbol([], _, []) .
prodsMoveableBySymbol([Prod | Prods], Symbol, MovedProds) :-
    prodsMoveableBySymbol(Prods, Symbol, MovedFromProds),
    % write(Prod), nl,
    (noNextSymbol(Prod) ->
        MovedProds = MovedFromProds
    ;   nextSymbol(Prod, ProdSymbol),
        % write(ProdSymbol), nl,
        (ProdSymbol = Symbol ->
            append([Prod], MovedFromProds, MovedProds)
            % write(MovedProds), nl
        ;   MovedProds = MovedFromProds
        )   
    ) .

% statesFromState(+State, +ProductionList, +DoneSymbols, -StatesList,
%                 -SymbolList)
% StatesList is all the states thaat can be reached from State in one move, and
% SymbolList contains symbols through which the move happens.
statesFromState([], _, _, [], []) .
statesFromState([StateElem | Rest], AllProds, DoneSymbols, States, Symbols) :-
    % write('statesFromState '), write(StateElem), nl,
    % write('rest '), write(Rest), nl,
    (noNextSymbol(StateElem) ->
        % write('No next'), nl,
        statesFromState(Rest, AllProds, DoneSymbols, States, Symbols)
    ;   nextSymbol(StateElem, Symbol),
        (member(Symbol, DoneSymbols) ->
            % write('symbol done'), nl,
            statesFromState(Rest, AllProds, DoneSymbols, States, Symbols)
        ;   % write('symbol done '), write(Symbol), nl,
            moveNext(StateElem, StateNext),
            % write(StateNext), nl,
            prodsMoveableBySymbol(Rest, Symbol, MoveableStates),
            moveAllNext(MoveableStates, MovedStates),
            % write('moved states '), write(MovedStates), nl,
            append([StateNext], MovedStates, StatesFromSymbol),
            % write('StatesFromSymbol '), write(StatesFromSymbol), nl,
            closure(StatesFromSymbol, AllProds, NewState),
            % write('NewState '), write(NewState), nl,
            append([Symbol], DoneSymbols, Done),
            statesFromState(Rest, AllProds, Done, StatesFromRest,
                               SymbolsFromRest),
            append([NewState], StatesFromRest, States),
            append([Symbol], SymbolsFromRest, Symbols)
        ) 
    ) .

% moves(+State, +StatesList, +SymbolList, -MovesList)
% MovesList is list of elements of the form move(State, SymbolList[i],
% StatesList[i]).
moves(_, [], [], []) .
moves(InitState, [State | Rest], [Symbol | Symbols], Moves) :-
    moves(InitState, Rest, Symbols, MovesFromRest),
    append([move(InitState, Symbol, State)], MovesFromRest, Moves) .

% statesWithDone(+StatesList1, +ProductionsList, +DoneStates,
%                   -StatesList2, -MovesList)
% Same as states but keeps DoneStates - list of already processed states
% of the automaton and StatesList1 is the list of states by moves from which we
% find the new states.
statesWithDone([], _, _, [], []) .
statesWithDone([InitState | InitStates], Prods, Done, States, Moves) :-
    (member(InitState, Done) -> 
        % skip already processed state
        statesWithDone(InitStates, Prods, Done, States, Moves)
    ;   statesFromState(InitState, Prods, [], StatesFromState, Symbols),
        moves(InitState, StatesFromState, Symbols, MovesFromState),
        append([InitState], Done, NewDone),
        append(InitStates, StatesFromState, StatesToDoWithDups),
        remove_dups(StatesToDoWithDups, StatesToDo),
        statesWithDone(
            StatesToDo, Prods, NewDone, StatesFromRest, MovesFromRest),
        append(StatesFromState, StatesFromRest, StatesWithDups),
        remove_dups(StatesWithDups, States),
        append(MovesFromState, MovesFromRest, Moves)
    ) .
    

% states(+ProductionList, +Symbol, -StatesList, -State, -MoveList)
% StatesList is the list of states of automaton for the grammar with start
% symbol Symbol, and all Productions in ProductionList. State is the starting
% state of the automaton and MoveList contains moves between states.
states(Prods, StartSymbol, States, StartState, Moves) :-
    closure([prod('Z', [([nt(StartSymbol), '#'],0)])], Prods, StartState),
    statesWithDone(
        [StartState], Prods, [], StatesFromStart, Moves),
    append([StartState], StatesFromStart, States) .

% finished(+ProductionList1, -ProductionList2)
% ProductionList2 contains all finished productions (A -> xyz@) from
% ProductionList1.
finished([], []) .
finished([Prod | Prods], Finished) :-
    finished(Prods, FinishedInProds),
    (noNextSymbol(Prod) ->
        append([Prod], FinishedInProds, Finished)
    ;   Finished = FinishedInProds
    ) .

% reductions(+StatesList, +StatesList, -ActionList)
% ActionList contains all reductions of the automaton.
reductions([], _, []) .
reductions([State | States], OriginalStates, Action) :-
    finished(State, Finished),
    % write('finished'), write(Finished), nl,
    length(Finished, N),
    (N > 1 -> % we have more than 1 finished productions in the state
        % write('Too many accepting states - conflict'), nl,
        nth0(0, Finished, Konf1),
        nth0(1, Finished, Konf2),
        Action = konflikt('Konflikt reduce-reduce', Konf1, Konf2, 'in state', State)
    ;   reductions(States, OriginalStates, StatesAction),
        (isConflict(StatesAction) ->
            Action = StatesAction
        ;   (N > 0 ->
                % write('One accepting state'), nl,
                [Prod] = Finished,
                % write(Prod), nl,
                % write(OriginalStates), nl,
                indexOf(OriginalStates, State, M),
                % write(M), nl,
                append([action(M, all, reduce(Prod))], StatesAction, Action)
            ;   % write('No accepting states'), nl,
                Action = StatesAction
            )
        )
    ) .

% accepting(+StatesList, +StatesList, +StartSymbol, -ActionList)
% ActionList contains all accepting actions of the automaton.
accepting([], _, _, []) .
accepting([State | States], OriginalStates, StartSymbol, Action) :-
    accepting(States, OriginalStates, StartSymbol, ActionFromStates),
    % write('State '), write(State), nl,
    (member(prod('Z', [([nt(StartSymbol), '#'], 1)]), State) ->
        indexOf(OriginalStates, State, N),
        append([action(N, #, accept)], ActionFromStates, Action)
    ;   Action = ActionFromStates
    ) .


% gotoAndAction(+MovesList, +ActionList, -GotoList, -ActionList)
% Fills Goto and Action tables of the automaton, based on a list of moves
% between states and given a list of all reductions.
getGotoActionFromMoves([], _, _, [], []) .
getGotoActionFromMoves([move(P, X, Q) | Moves], States, Reductions, Goto, Action) :-
    % write('getGotoActionFromMoves'), nl,
    getGotoActionFromMoves(Moves, States, Reductions, MovesGoto, MovesAction),
    % write('MovesToGo '), write(MovesGoto), nl,
    (isConflict(MovesAction) ->
        % write('Konflikt returned'), nl,
        Action = MovesAction, Goto = []
    ;   (isNonTerminal(X) ->
            % write('P X Q'), write(P), write(->), write(X), write(->), write(Q), nl,
            append([goto(P, X, Q)], MovesGoto, Goto),
            Action = MovesAction
            % write('exiting'), nl
        ;   (member(action(P, all, R), Reductions) ->
                % nl, write('Konflikt'), nl, nl,
                nth0(Q, States, State),
                prodsMoveableBySymbol(State, X, MovedByX),
                nth0(0, MovedByX, ConflictProduction),
                reduce(ReduceProd) = R,
                Action = konflikt('Konflikt shift-reduce', ReduceProd,
                                  ConflictProduction, ' in state ', State),
                Goto = []
            ;   % nl, write('No konflikt'), nl, nl,
                append([action(P, X, shift(Q))], MovesAction, Action),
                Goto = MovesGoto
            )
        )
    ) .

% gotoAndAction(+MovesList, +StatesList, +Symbol, -GotoList,
%                  -ActionList)
% Fills Goto and Action tables of the automaton.
gotoAndAction(Moves, States, StartSymbol, Goto, Action) :-
    reductions(States, States, Reductions), % all reductions in the automaton
    (isConflict(Reductions) ->
        Action = Reductions, Goto = []
    ;   % write('No conflict in reductions'), nl,
        % length(Reductions, LR),
        % write('Reductions length '), write(LR), nl,
        % write('Reductions '), write(Reductions), nl,
        getGotoActionFromMoves(
            Moves, States, Reductions, MovesGoto, MovesAction),
        % length(MovesAction, LM),
        % write('MovesAction length '), write(LM), nl,
        % write(MovesAction), nl,
        (isConflict(MovesAction) ->
            % write('gotoAndAction konflikt'), nl,
            Action = MovesAction, Goto = []
        ;   % write('no conflict'), nl,
            append(Reductions, MovesAction, ActionWithoutAccept),
            % write('ActionWithoutAccept'), write(ActionWithoutAccept), nl,
            accepting(States, States, StartSymbol, AcceptAcction),
            % length(AcceptAcction, LA),
            % write('AcceptAcction length '), write(LA), nl,
            % write('AcceptAcction'), write(AcceptAcction), nl,
            append(ActionWithoutAccept, AcceptAcction, Action),
            Goto = MovesGoto
        )
    ) .

% translateMoves(+MovesList, +StatesList, -MovesList)
% Translates moves of the form move(state, symbol, state) to
% move(state_nr, symbol, state_nr).
translateMoves([], _, []) .
translateMoves([Move | Rest], States, [NewMove | NewRest]) :-
    move(P, X, Q) = Move,
    indexOf(States, P, N),
    indexOf(States, Q, M),
    NewMove = move(N, X, M),
    translateMoves(Rest, States, NewRest) .

% createLR(+Grammar, -Automaton, -Info)
createLR(Grammar, Automata, Info) :-
    gramatyka(StartSymbol, _) = Grammar,
    addStart(Grammar, NewGrammar),
    % write('New grammar '), write(NewGrammar), nl,
    gramatyka(_, Prods) = NewGrammar,
    % write('Prods '), write(Prods), nl,
    productionsWithDots(Prods, ProdsDotted),
    % write('ProdsDotted '), write(ProdsDotted), nl,
    states(ProdsDotted, StartSymbol, States, StartState, MovesWithStates),
    % length(States, LS),
    % write('States length '), write(LS), nl,
    % write('States '), write(States), nl, nl,
    translateMoves(MovesWithStates, States, Moves),
    % write('Moves '), write(Moves), nl,
    gotoAndAction(Moves, States, StartSymbol, Goto, Action),
    % length(Goto, LG),
    % write('Goto length '), write(LG), nl,
    % write('Goto '), write(Goto), nl,
    % length(Action, LA),
    % write('Action length '), write(LA), nl,
    % write('Action '), write(Action), nl,
    (isConflict(Action) ->
        Automata = null,
        Info = Action
    ;   Info = yes,
        Automata = automat(Goto, Action)
    ) .

% topStack(+Stack, -Element)
topStack([Top | _], Top) .

% popStack(+Stack, -Stack)
popStack([_| Rest], Rest) .

% pushStack(+Stack, +Element, -Stack)
pushStack(Stack, Elem, [Elem | Stack]) .

% popStackN(+Stack, +Number, -Stack)
popStackN(Stack, N, NewStack) :-
    (N > 0 ->
        [_ | Rest] = Stack,
        M is N - 1,
        popStackN(Rest, M, NewStack)
    ;   NewStack = Stack
    ) .

% executeAction(+Action, +Stack, +GotoList, -Stack)
executeAction(shift(Q), Stack, _, NewStack) :-
    %write(Stack),
    pushStack(Stack, Q, NewStack) .
    %write(NewStack) .
executeAction(reduce(Prod), Stack, Goto, NewStack) :-
    % write('Executing reduce'), nl,
    prodLength(Prod, N),
    % write(N), nl,
    prodLhs(Prod, Lhs),
    % write(Lhs), nl,
    popStackN(Stack, N, StackTmp),
    % write(StackTmp), nl,
    topStack(StackTmp, Top),
    % write(Top), nl,
    (member(goto(Top, nt(Lhs), X), Goto) ->
        pushStack(StackTmp, X, NewStack)
    ) .

% acceptWithStack(+Automaton, +Stack, +Word)
acceptWithStack(automat(Goto, Action), Stack, []) :-
    % write('end of word'), nl,
    % write('Stack '), write(Stack), nl,
    topStack(Stack, Top),
    (member(action(Top, '#', accept), Action) -> 
        true
    ;   (member(action(Top, all, Act), Action) ->
            % write('Action is '), write(Act), nl,
            executeAction(Act, Stack, Goto, NewStack),
            acceptWithStack(automat(Goto, Action), NewStack, [])
        )
    ).
acceptWithStack(automat(Goto, Action), Stack, [Term | Rest]) :-
    % write('Stack '), write(Stack), nl,
    % write('Term '), write(Term), nl,
    topStack(Stack, Top),
    (member(action(Top, Term, Act), Action) ->
        % write('Action is '), write(Act), nl,
        executeAction(Act, Stack, Goto, NewStack),
        acceptWithStack(automat(Goto, Action), NewStack, Rest)
    ;   (member(action(Top, all, Act), Action) ->
            % write('Action is '), write(Act), nl,
            executeAction(Act, Stack, Goto, NewStack),
            acceptWithStack(automat(Goto, Action), NewStack, [Term|Rest])
        )
    ) . 

% accept(+Automaton, +Word)
accept(automat(Goto, Action), Word) :-
    Stack = [0],
    acceptWithStack(automat(Goto, Action), Stack, Word) .

test(G, W) :-
    createLR(G, A, I),
    (isConflict(I) ->
        write('Mamy konflikt: '),
        write(I), nl, false
    ;   accept(A, W) 
    ) .
