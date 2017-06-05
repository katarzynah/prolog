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
    append([prod('Z', [nt(S), #])], P, NewP) .

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
    %write('singleRhsWithDots\n'),
    length(Rhs, N),
    %write(N),
    constructRhsWithDots(Rhs, N, RhsWithDots) .


% singleProductionWithDots(+Produkcja, -ProdukcjaZeZnacznikiem)
singleProductionWithDots(prod(S, []), prod(S, [])) .
singleProductionWithDots(prod(S, [Rhs | Xs]), prod(S, Prods)) :-
    %write('singleProductionWithDots\n'),
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

getNonTerminal(nt(_), _) .

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
    write(NonTerminals),
    subseq(AllSymbols, NonTerminals, Terminals),
    write(Terminals) .

% getNextSymbol(+ProdukcjaZeZnacznikiem, -Symbol)
getNextSymbol(prod(_, [(Prod, N)]), Symbol) :- nth0(N, Prod, Symbol) .

noNextSymbol(prod(_, [(Prod, N)])) :- length(Prod, M), M =:= N .

moveNext(prod(Z, [(Prod, N)]), prod(Z, [(Prod, M)])) :- M is N + 1 .

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
    write(Prod), nl,
    (noNextSymbol(Prod) ->
        MovedProds = MovedFromProds
    ;   getNextSymbol(Prod, ProdSymbol),
        write(ProdSymbol), nl,
        (ProdSymbol = Symbol ->
            write('Moving'), nl,
            moveNext(Prod, ProdNext),
            append([ProdNext], MovedFromProds, MovedProds),
            write(MovedProds), nl
        ;   MovedProds = MovedFromProds)   
    ) .

getStatesFromState([], _, _, [], []) .
getStatesFromState([StateElem | Rest], AllProds, DoneSymbols, States, Symbols) :-
    write('getStatesFromState '), write(StateElem), nl,
    write('rest '), write(Rest), nl,
    (noNextSymbol(StateElem) ->
        write('No next'), nl,
        getStatesFromState(Rest, AllProds, DoneSymbols, States, Symbols)
    ;   getNextSymbol(StateElem, Symbol),
        (member(Symbol, DoneSymbols) ->
            write('symbol done'), nl,
            getStatesFromState(Rest, AllProds, DoneSymbols, States, Symbols)
        ;   write('symbol done '), write(Symbol), nl,
            moveNext(StateElem, StateNext),
            write(StateNext), nl,
            prodsMovedBySymbol(Rest, Symbol, MovedStates),
            write('moved states '), write(MovedStates), nl,
            append([StateNext], MovedStates, StatesFromSymbol),
            write('StatesFromSymbol '), write(StatesFromSymbol), nl,
            getClosure(StatesFromSymbol, AllProds, NewState),
            write('NewState '), write(NewState), nl,
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
getStates(Prods, States, Moves) :-
    getClosure([prod('Z', [([nt('S'), '#'],0)])], Prods, StartClosure),
    getStatesWithDone(
        [StartClosure], Prods, [], States, Moves) .

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

reductions([], []) .
reductions([State | States], Action) :-
    finished(State, Finished),
    write('finished'), write(Finished), nl,
    length(Finished, N),
    (N > 1 ->
        nth0(0, Finished, Konf1),
        nth0(1, Finished, Konf2),
        Action = konflikt('Konflikt reduce-reduce')
    ;   reductions(States, StatesAction),
        (isConflict(StatesAction) ->
            Action = StatesAction
        ;   (N > 0 ->
                [Prod] = Finished,
                append([action(State, all, reduce(Prod))], StatesAction, Action)
            ;   Action = StatesAction
            )
        )
    ) .

getGotoAndAction([], [], []) .
getGotoAndAction([Move | Moves], Goto, Action) .
    
    

% prepareAutomaton(+Gramatyka, -ListaStanów, -ListaNieterminali,
%                  -ListaTerminali, -ListaPrzejść)
%prepareAutomaton(G, States, Nonterminals, Terminals, Moves) :-
%    addStart(G, gramatyka(Z, P)),
%    productionsWithDots(P, PDots),
%    getNonTerminals(gramatyka(Z, P), Nonterminals),
%    getTerminals(gramatyka(Z, P), Terminals),
%    getStates(gramatyka(Z, P), Nonterminals, Terminals, States, Moves) .

%createLR(G, automat(States, Terminals, Nonterminals, Goto, Action), yes) :- 
%    prepareAutomaton(G, States, Nonterminals, Terminals, Moves),
%    getGoToAndAction(States, Nonterminals, Terminals, Moves, Goto, Action) .

%createLR(G, null, konflikt(Opis)) :-
%    prepareAutomaton(G, States, Nonterminals, Terminals, Moves),
%    getGoToAndAction(States, Nonterminals, Terminals, Moves, konflikt(Opis),
%                     Action) .



% getClosure(+Produkcje, -Closure)



% accept(+Automat, +Słowo)