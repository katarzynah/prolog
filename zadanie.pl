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
    N >= 0,
    succ(N0, N),
    Z = [(RHS, N)],
    constructRHSWithDots(RHS, N0, RHS_N0),
    append(Z, RHS_N0, RHSWithDots) .

singleRHSWithDots([], []) .
singleRHSWithDots(RHS, RHSWithDots) :-
    length(RHS, N),
    constructRHSWithDots(RHS, N, RHSWithDots) .


% singleProductionWithDots(+Produkcja, -ProdukcjaZeZnacznikiem)
singleProductionWithDots(prod(S, []), prod(S, [])) .
singleProductionWithDots(prod(S, [RHS | Xs]), prod(S, Prods)) :-
    singleRHSWithDots(RHS, RHSWithDots),
    singleProductionWithDots(prod(S, Xs), prod(S, XsWithDots)),
    append(RHSWithDots, XsWithDots, Prods) .

% productionsWithDots(+Produkcje, -ProdukcjeZeZnacznikiem)
productionsWithDots([], []) .
productionsWithDots([Prod | Ps], ProdsWithDots) :-
    singleProductionWithDots(Prod, ProdWithDots),
    productionsWithDots(Ps, PsWithDots),
    append([ProdWithDots], PsWithDots, ProdsWithDots) .

% getNonTerminals(+Gramatyka, -ListaNieterminali)

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