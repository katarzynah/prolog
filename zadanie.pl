% prod(NazwaNieterminala, ListaPrawychStronProdukcji)
% gramatyka(SymbolPoczątkowy, ZbiórProdukcji)
% nt(Nieterminal)

% automat(stany, terminale, nieterminale, goto, action)
% move(state, symbol, state)
% prod

% createLR(+Gramatyka, -Automat, -Info)
% Info yes / konflikt(Opis) (wtedy automat null)

% addStart(+Gramatyka, -Gramatyka)
addStart(gramatyka(S, P), gramatyka('Z', NewP)) :-
    append(P, [prod('Z', [nt(S), #])], NewP) .

% singleRHSWithDots(+PrawaStronaProdukcji,
%                   -ListaPrawychStronProdukcjiZeZnaczniekiem)

constructRHSWithDots(RHS, N, RHSWithDots) :-
    %write('constructRHSWithDots\n'),
    N >= 0,
    N0 is N - 1,
    Z = [(RHS, N)],
    constructRHSWithDots(RHS, N0, RHS_N0),
    append(RHS_N0, Z, RHSWithDots) .

constructRHSWithDots(_, N, RHSWithDots) :-
    N < 0,
    RHSWithDots = [] .

singleRHSWithDots([], []) .
singleRHSWithDots(RHS, RHSWithDots) :-
    %write('singleRHSWithDots\n'),
    length(RHS, N),
    %write(N),
    constructRHSWithDots(RHS, N, RHSWithDots) .


% singleProductionWithDots(+Produkcja, -ProdukcjaZeZnacznikiem)
singleProductionWithDots(prod(S, []), prod(S, [])) .
singleProductionWithDots(prod(S, [RHS | Xs]), prod(S, Prods)) :-
    %write('singleProductionWithDots\n'),
    singleRHSWithDots(RHS, RHSWithDots),
    singleProductionWithDots(prod(S, Xs), prod(S, XsWithDots)),
    append(RHSWithDots, XsWithDots, Prods) .

% productionsWithDots(+Produkcje, -ProdukcjeZeZnacznikiem)
productionsWithDots([], []) .
productionsWithDots([Prod | Ps], ProdsWithDots) :-
    singleProductionWithDots(Prod, ProdWithDots),
    productionsWithDots(Ps, PsWithDots),
    append([ProdWithDots], PsWithDots, ProdsWithDots) .

% getNonterminals(+Gramatyka, -ListaNieterminali)
getNonterminals([], []) .
getNonterminals([prod(X, _)| Prods], Nonterminals) :-
    getNonterminals(Prods, ProdsNonterminals),
    append([X], ProdsNonterminals, Nonterminals) .


% getTerminals(+Gramatyka, -ListaTerminali)

% getStates(+Gramatyka, +ListaNieterminali, +ListaTerminali, -ListaStanów,
%           -ListaPrzejść)

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