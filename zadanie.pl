% prod(NazwaNieterminala, ListaPrawychStronProdukcji)
% gramatyka(SymbolPoczątkowy, ZbiórProdukcji)
% nt(Nieterminal)

% automat(stany, terminale, nieterminale, goto, action)
% move(state, symbol, state)
% prod

% createLR(+Gramatyka, -Automat, -Info)
% Info yes / konflikt(Opis) (wtedy automat null)

:- use_module(library(lists)).

% addStart(+Gramatyka, -Gramatyka)
addStart(gramatyka(S, P), gramatyka('Z', NewP)) :-
    Prod = prod('Z', [[nt(S), #]]),
    append([Prod], P, NewP) .


% ListaPrawychStronProdukcjiZeZnaczniekiem = [(PrawaStronaProdukcji, Liczba)]

% constructRhsWithDots(+PrawaStronaProdukcji, +Liczba,
%                      -ListaPrawychStronProdukcjiZeZnaczniekiem)
constructRhsWithDots(Rhs, N, RhsWithDots) :-
    N >= 0,
    N0 is N - 1,
    Z = [(Rhs, N)],
    constructRhsWithDots(Rhs, N0, Rhs_N0),
    append(Rhs_N0, Z, RhsWithDots) .

constructRhsWithDots(_, N, RhsWithDots) :-
    N < 0,
    RhsWithDots = [] .

% singleRhsWithDots(+PrawaStronaProdukcji,
%                   -ListaPrawychStronProdukcjiZeZnaczniekiem)
singleRhsWithDots([], []) .
singleRhsWithDots(Rhs, RhsWithDots) :-
    % write('singleRhsWithDots '), write(Rhs), nl,
    length(Rhs, N),
    % write(N),
    constructRhsWithDots(Rhs, N, RhsWithDots) .


% singleProductionWithDots(+Produkcja, -ProdukcjaZeZnacznikiem)
singleProductionWithDots(prod(S, []), prod(S, [])) .
singleProductionWithDots(prod(S, [Rhs | Xs]), prod(S, Prods)) :-
    % write('singleProductionWithDots\n'),
    singleRhsWithDots(Rhs, RhsWithDots),
    singleProductionWithDots(prod(S, Xs), prod(S, XsWithDots)),
    append(RhsWithDots, XsWithDots, Prods) .

% productionsWithDots(+Produkcje, -ProdukcjeZeZnacznikiem)
productionsWithDots([], []) .
productionsWithDots([Prod | Ps], ProdsWithDots) :-
    singleProductionWithDots(Prod, ProdWithDots),
    productionsWithDots(Ps, PsWithDots),
    append([ProdWithDots], PsWithDots, ProdsWithDots) .

% getNonterminals(+ListaProdukcji, -ListaNieterminali)
getNonterminals([], []) .
getNonterminals([prod(X, _)| Prods], Nonterminals) :-
    getNonterminals(Prods, ProdsNonterminals),
    append([X], ProdsNonterminals, NonterminalsWithDups),
    remove_dups(NonterminalsWithDups, Nonterminals) .

isNonTerminal(nt(_)) .

getAllSymbolsFromSingleRhs([], []) .
getAllSymbolsFromSingleRhs([S | Rest], Terminals) :-
    getAllSymbolsFromSingleRhs(Rest, TerminalsFromRest),
    (isNonTerminal(S) ->
        nt(X) = S,
        append([X], TerminalsFromRest, Terminals)
    ;   append([S], TerminalsFromRest, Terminals)
    ) .

getAllSymbolsFromRhs([], []) .
getAllSymbolsFromRhs([S| Rhs], Symbols) :-
    getAllSymbolsFromSingleRhs(S, SymbolsFromS),
    getAllSymbolsFromRhs(Rhs, SymbolsFromRhs),
    append(SymbolsFromS, SymbolsFromRhs, Symbols) .


% getAllSymbols(+ListaProdukcji, -ListaTerminali)
getAllSymbols([], []) .
getAllSymbols([prod(_, Rhs) | Prods], Terminals) :-
    getAllSymbolsFromRhs(Rhs, TerminalsFromRhs),
    getAllSymbols(Prods, TerminalsFromProds),
    remove_dups(TerminalsFromRhs, TerminalsFromRhsSet),
    append(TerminalsFromRhsSet, TerminalsFromProds, Terminals) .


% getTerminals(+ListaProdukcji, +ListaNieterminali, -ListaTerminali)
getTerminals(Prods, NonTerminals, Terminals) :-
    getAllSymbols(Prods, AllSymbols),
    % write(NonTerminals),
    subseq(AllSymbols, NonTerminals, Terminals) .
    % write(Terminals) .

% getNextSymbol(+ProdukcjaZeZnacznikiem, -Symbol)
getNextSymbol(prod(_, [(Prod, N)]), Symbol) :- nth0(N, Prod, Symbol) .

noNextSymbol(prod(_, [(Prod, N)])) :- length(Prod, M), M =:= N .

prodLength(prod(_, [(_, N)]), N) .

prodLhs(prod(S, _), S) .

moveNext(prod(Z, [(Prod, N)]), prod(Z, [(Prod, M)])) :- M is N + 1 .

indexOf([X | _], X, 0) .
indexOf([X | Xs], Elem, N) :-
    indexOf(Xs, Elem, M),
    N is M + 1 .


isConflict(konflikt(_)) .

getAllStartingProds([], _, []) .
getAllStartingProds([(Prod, N) | Prods], Symbol, StartingProds) :-
    getAllStartingProds(Prods, Symbol, StartingProdsFromProds),
    (N is 0 ->
        append([prod(Symbol, [(Prod, N)])], StartingProdsFromProds,
               StartingProds)
    ;   StartingProds = StartingProdsFromProds
    ) .

getAllStartingProdsFromSymbol([], _, []) .
getAllStartingProdsFromSymbol([prod(X, Rhs)| Prods], Symbol, ProdsFromSymbol) :-
    (X = Symbol ->
        getAllStartingProds(Rhs, Symbol, ProdsFromSymbol);
        getAllStartingProdsFromSymbol(Prods, Symbol, ProdsFromSymbol)) .


% getSingleProdClosure(+ProdukcjaZeZnacznikiem, +ListProdukcjiZeZnaczikiem,
%                      +ListProdukcjiZeZnaczikiem, -ListaProdukcjiZeZnacznikiem)
getSingleProdClosure(Prod, Prods, Done, Closure, NewDone) :-
    %write('getSingleProdClosure: '),
    %write(Start), write('->'), write(Prod), nl,
    (noNextSymbol(Prod) ->
        % write('noNextSymbol'), nl,
        Closure = [Prod], NewDone = Done
    ;   getNextSymbol(Prod, Symbol),
        %write(Symbol),nl,
        (isNonTerminal(Symbol) ->
            % write('nonTerm'), nl,
            (member(Prod, Done) ->
                % write('isMember'), nl,
                Closure = [], NewDone = Done
            ;   nt(UnwrappedSymbol) = Symbol,
                %write('UnwrappedSymbol '),
                %write(UnwrappedSymbol), nl,
                getAllStartingProdsFromSymbol(Prods, UnwrappedSymbol,
                                              ProdsFromSymbol),
                %write('Prods from symbol '),write(ProdsFromSymbol), nl,
                append(Done, [Prod], DoneWithProd),
                %write('Done '), write(DoneWithProd), nl,
                getClosureWithDone(ProdsFromSymbol, Prods, DoneWithProd,
                                   ProdsFromSymbolClosure, NewDone),
                append([Prod], ProdsFromSymbolClosure, Closure)
            )
        ;   Closure = [Prod], NewDone = Done
        )
    ) .

% _getClosure(+ListaProdukcjiZeZnacznikiem, +ListaProdukcjiZeZnacznikiem
%             +ListaProdukcjiZeZnacznikiem, -ListaProdukcjiZeZnacznikiem,
%             -ListaProdukcjiZeZnacznikiem)
getClosureWithDone([], _, _, [], _) .
getClosureWithDone([ProdToClose | ProdsToClose], Prods, Done, Closure, NewDone) :-
    %write('getClosureWithDone '), write(Done), nl,
    %write('withProds '), write(ProdToClose), write(ProdsToClose), nl,
    getSingleProdClosure(ProdToClose, Prods, Done, ProdClosure, DoneAfterProd),
    %write('getClosureWithDone after single'), write(ProdClosure), nl,
    getClosureWithDone(ProdsToClose, Prods, DoneAfterProd, ProdsClosure, NewDone),
    append(ProdClosure, ProdsClosure, ClosureWithDups),
    remove_dups(ClosureWithDups, Closure) .


% getClosure(+ListaProdukcjiZeZnacznikiem, +ListProdukcjiZeZnaczikiem,
%            -ListaProdukcjiZeZnacznikiem)
getClosure(ProdsToClose, Prods, Closure) :-
    % write('getClosure'), nl,
    getClosureWithDone(ProdsToClose, Prods, [], Closure, _) .
    % TODO(Kasia): Sort closure

prodsMovedBySymbol([], _, []) .
prodsMovedBySymbol([Prod | Prods], Symbol, MovedProds) :-
    prodsMovedBySymbol(Prods, Symbol, MovedFromProds),
    % write(Prod), nl,
    (noNextSymbol(Prod) ->
        MovedProds = MovedFromProds
    ;   getNextSymbol(Prod, ProdSymbol),
        write(ProdSymbol), nl,
        (ProdSymbol = Symbol ->
            % write('Moving'), nl,
            moveNext(Prod, ProdNext),
            append([ProdNext], MovedFromProds, MovedProds)
            % write(MovedProds), nl
        ;   MovedProds = MovedFromProds
        )   
    ) .

getStatesFromState([], _, _, [], []) .
getStatesFromState([StateElem | Rest], AllProds, DoneSymbols, States, Symbols) :-
    % write('getStatesFromState '), write(StateElem), nl,
    % write('rest '), write(Rest), nl,
    (noNextSymbol(StateElem) ->
        % write('No next'), nl,
        getStatesFromState(Rest, AllProds, DoneSymbols, States, Symbols)
    ;   getNextSymbol(StateElem, Symbol),
        (member(Symbol, DoneSymbols) ->
            % write('symbol done'), nl,
            getStatesFromState(Rest, AllProds, DoneSymbols, States, Symbols)
        ;   % write('symbol done '), write(Symbol), nl,
            moveNext(StateElem, StateNext),
            % write(StateNext), nl,
            prodsMovedBySymbol(Rest, Symbol, MovedStates),
            % write('moved states '), write(MovedStates), nl,
            append([StateNext], MovedStates, StatesFromSymbol),
            % write('StatesFromSymbol '), write(StatesFromSymbol), nl,
            getClosure(StatesFromSymbol, AllProds, NewState),
            % write('NewState '), write(NewState), nl,
            append([Symbol], DoneSymbols, Done),
            getStatesFromState(Rest, AllProds, Done, StatesFromRest,
                               SymbolsFromRest),
            append([NewState], StatesFromRest, States),
            append([Symbol], SymbolsFromRest, Symbols)
        ) 
    ) .

getMoves(_, [], [], []) .
getMoves(InitState, [State | Rest], [Symbol | Symbols], Moves) :-
    getMoves(InitState, Rest, Symbols, MovesFromRest),
    append([move(InitState, Symbol, State)], MovesFromRest, Moves) .

% getStatesWithDone(+ListaStanów, +ListaNieterminali, +ListaTerminali,
%                   +ListaStanów, -ListaStanów, -ListaPrzejść, -ListaStanów)
getStatesWithDone([], _, _, [], []) .
getStatesWithDone([InitState | InitStates], Prods, Done, States, Moves) :-
    (member(InitState, Done) -> 
        getStatesWithDone(InitStates, Prods, Done, States, Moves)
    ;   getStatesFromState(InitState, Prods, [], StatesFromState, Symbols),
        getMoves(InitState, StatesFromState, Symbols, MovesFromState),
        append([InitState], Done, NewDone),
        append(InitStates, StatesFromState, StatesToDoWithDups),
        remove_dups(StatesToDoWithDups, StatesToDo),
        getStatesWithDone(
            StatesToDo, Prods, NewDone, StatesFromRest, MovesFromRest),
        append(StatesFromState, StatesFromRest, StatesWithDups),
        remove_dups(StatesWithDups, States),
        append(MovesFromState, MovesFromRest, Moves)
    ) .
    

% getStates(+Gramatyka, +ListaNieterminali, +ListaTerminali, -ListaStanów,
%           -ListaPrzejść)
getStates(Prods, StartSymbol, States, StartState, Moves) :-
    getClosure([prod('Z', [([nt(StartSymbol), '#'],0)])], Prods, StartState),
    getStatesWithDone(
        [StartState], Prods, [], StatesFromStart, Moves),
    append([StartState], StatesFromStart, States) .

emptyList(N, List) :-
    (N > 0 ->
        M is N - 1,
        emptyList(M, ListM),
        append([null], ListM, List)
    ;   List = []
    ) .

emptyMatrix(N, M, Matrix) :-
    (N > 0 ->
        K is N - 1,
        emptyMatrix(K, M, MatrixK),
        emptyList(M, List),
        append([List], MatrixK, Matrix)
    ; Matrix = [[]]
    ) .

finished([], []) .
finished([Prod | Prods], Finished) :-
    finished(Prods, FinishedInProds),
    (noNextSymbol(Prod) ->
        append([Prod], FinishedInProds, Finished)
    ;   Finished = FinishedInProds
    ) .

reductions([], _, []) .
reductions([State | States], OriginalStates, Action) :-
    finished(State, Finished),
    write('finished'), write(Finished), nl,
    length(Finished, N),
    (N > 1 ->
        nth0(0, Finished, Konf1),
        nth0(1, Finished, Konf2),
        Action = konflikt('Konflikt reduce-reduce')
    ;   reductions(States, OriginalStates, StatesAction),
        (isConflict(StatesAction) ->
            Action = StatesAction
        ;   (N > 0 ->
                [Prod] = Finished,
                indexOf(OriginalStates, Finished, M),
                append([action(M, all, reduce(Prod))], StatesAction, Action)
            ;   Action = StatesAction
            )
        )
    ) .

accepting([], _, _, []) .
accepting([State | States], OriginalStates, StartSymbol, Action) :-
    accepting(States, OriginalStates, StartSymbol, ActionFromStates),
    write('State '), write(State), nl,
    (member(prod('Z', [([nt(StartSymbol), '#'], 1)]), State) ->
        indexOf(OriginalStates, State, N),
        append([action(N, #, accept)], ActionFromStates, Action)
    ;   Action = ActionFromStates
    ) .

getGotoActionFromMoves([], _, [], []) .
getGotoActionFromMoves([move(P, X, Q) | Moves], Reductions, Goto, Action) :-
    % write('getGotoActionFromMoves'), nl,
    getGotoActionFromMoves(Moves, Reductions, MovesGoto, MovesAction),
    % write('MovesToGo '), write(MovesGoto), nl,
    (isConflict(MovesAction) ->
        Action = MovesAction, Goto = []
    ;   (isNonTerminal(X) ->
            % write('P X Q'), write(P), write(->), write(X), write(->), write(Q), nl,
            append([goto(P, X, Q)], MovesGoto, Goto),
            Action = MovesAction
            % write('exiting'), nl
        ;   (member(action(P, all, R), Reductions) ->
                % nl, write('Konflikt'), nl, nl,
                Action = konflikt('Konflikt shift-reduce'), Goto = []
            ;   % nl, write('No konflikt'), nl, nl,
                append([action(P, X, shift(Q))], MovesAction, Action),
                Goto = MovesGoto
            )
        )
    ) .

getGoToAndAction(Moves, States, StartSymbol, Goto, Action) :-
    reductions(States, States, Reductions),
    length(Reductions, LR),
    write('Reductions length '), write(LR), nl,
    write('Reductions '), write(Reductions), nl,
    (isConflict(Reductions) ->
        Action = Reductions, Goto = []
    ;   % write('No conflict in reductions'), nl,
        getGotoActionFromMoves(Moves, Reductions, MovesGoto, MovesAction),
        length(MovesAction, LM),
        write('MovesAction length '), write(LM), nl,
        write(MovesAction), nl,
        (isConflict(MovesAction) ->
            Action = MovesAction, Goto = []
        ;   % write('no conflict'), nl,
            append(Reductions, MovesAction, ActionWithoutAccept),
            % write('ActionWithoutAccept'), write(ActionWithoutAccept), nl,
            accepting(States, States, StartSymbol, AcceptAcction),
            length(AcceptAcction, LA),
            write('AcceptAcction length '), write(LA), nl,
            write('AcceptAcction'), write(AcceptAcction), nl,
            append(ActionWithoutAccept, AcceptAcction, Action),
            Goto = MovesGoto
        )
    ) .

translateMoves([], _, []) .
translateMoves([Move | Rest], States, [NewMove | NewRest]) :-
    move(P, X, Q) = Move,
    indexOf(States, P, N),
    indexOf(States, Q, M),
    NewMove = move(N, X, M),
    translateMoves(Rest, States, NewRest) .

createLR(Grammar, Automata, Info) :-
    gramatyka(StartSymbol, _) = Grammar,
    addStart(Grammar, NewGrammar),
    write('New grammar '), write(NewGrammar), nl,
    gramatyka(_, Prods) = NewGrammar,
    write('Prods '), write(Prods), nl,
    productionsWithDots(Prods, ProdsDotted),
    write('ProdsDotted '), write(ProdsDotted), nl,
    getStates(ProdsDotted, StartSymbol, States, StartState, MovesWithStates),
    length(States, LS),
    write('States length '), write(LS), nl,
    write('States '), write(States), nl, nl,
    translateMoves(MovesWithStates, States, Moves),
    write('Moves '), write(Moves), nl,
    getGoToAndAction(Moves, States, StartSymbol, Goto, Action),
    length(Goto, LG),
    write('Goto length '), write(LG), nl,
    write('Goto '), write(Goto), nl,
    length(Action, LA),
    write('Action length '), write(LA), nl,
    write('Action '), write(Action), nl,
    (isConflict(Action) ->
        Automata = null,
        Info = Action
    ;   Info = yes,
        Automata = automat(StartState, Goto, Action)
    ) .

topStack([Top | _], Top) .
popStack([_| Rest], Rest) .
pushStack(Stack, Elem, [Elem | Stack]) .
popStackN(Stack, N, NewStack) :-
    (N > 0 ->
        [_ | Rest] = Stack,
        M is N - 1,
        popStackN(Rest, M, NewStack)
    ;   NewStack = Stack
    ) .

executeAction(shift(Q), Stack, _, NewStack) :-
    %write(Stack),
    pushStack(Stack, Q, NewStack) .
    %write(NewStack) .
executeAction(reduce(Prod), Stack, Goto, NewStack) :-
    write('Executing reduce'), nl,
    prodLength(Prod, N),
    write(N), nl,
    prodLhs(Prod, Lhs),
    write(Lhs), nl,
    popStackN(Stack, N, StackTmp),
    write(StackTmp), nl,
    topStack(StackTmp, Top),
    write(Top), nl,
    (member(goto(Top, nt(Lhs), X), Goto) ->
        pushStack(StackTmp, X, NewStack)
    ) .

acceptWithStack(automat(StartState, Goto, Action), Stack, []) :-
    write('end of word'), nl,
    write('Stack '), write(Stack), nl,
    topStack(Stack, Top),
    (member(action(Top, '#', accept), Action) -> 
        true
    ;   (member(action(Top, all, Act), Action) ->
            write('Action is '), write(Act), nl,
            executeAction(Act, Stack, Goto, NewStack),
            acceptWithStack(automat(StartState, Goto, Action), NewStack, [])
        )
    ).
acceptWithStack(automat(StartState, Goto, Action), Stack, [Term | Rest]) :-
    write('Stack '), write(Stack), nl,
    write('Term '), write(Term), nl,
    topStack(Stack, Top),
    (member(action(Top, Term, Act), Action) ->
        write('Action is '), write(Act), nl,
        executeAction(Act, Stack, Goto, NewStack),
        acceptWithStack(automat(StartState, Goto, Action), NewStack, Rest)
    ;   (member(action(Top, all, Act), Action) ->
            write('Action is '), write(Act), nl,
            executeAction(Act, Stack, Goto, NewStack),
            acceptWithStack(automat(StartState, Goto, Action), NewStack, [Term|Rest])
        )
    ) . 


addHash(Word, WordWithHash) :-
    reverse(Word, WordReversed),
    %WordTmp = ['#' | WordReversed],
    reverse(WordTmp, WordWithHash) .

% accept(+Automat, +Słowo)
accept(automat(StartState, Goto, Action), Word) :-
    Stack = [0],
    % addHash(Word, WordWithHash),
    acceptWithStack(automat(StartState, Goto, Action), Stack, Word) .

test(G, W) :-
    createLR(G, A, I),
    (isConflict(I) ->
        write(I), nl, false
    ;   accept(A, W) 
    ) .
