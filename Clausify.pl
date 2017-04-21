%%%%%% 793181 Ghetti Omar %%%%%%
%%%%%% 794692 Grazioli Andrea %%%%%%

/* definisco le varie fbf */

fbf(and).
fbf(or).
fbf(every).
fbf(implies).
fbf(exist).
fbf(not).
fbf(is_predicato).
fbf(X) :- compound(X).

is_predicato(X) :- atomic(X), !.
is_predicato(X) :- 
			compound(X),
			X =.. [H | T],
			atomic(H),
			validafbf_2(T).

is_termine(X) :- var(X).
is_termine(X):- atomic(X).

/* definisco le arity delle fbf */

arita(not, 1).
arita(and, X) :- 
			 X > 1.
arita(or, X) :- 
			X > 1.
arita(implies, 2).
arita(exist, 2).
arita(every,2).
calcola_arita([], 0).
calcola_arita([ _ | Ts], N) :-
				calcola_arita(Ts, N1),
				N is N1+1.

/* Verifico la validita della fbf in input tramite queste procedure */

validafbf(X) :- 
	X =.. [H | T],
	is_termine(H),
	fbf(H),
	calcola_arita(T, C),
	arita(H, C),
	validafbf_2(T), !.

validafbf(X) :- 
	X =.. [ H | []],
	is_termine(H), !.

validafbf(X) :- 
	X =.. [ H | _],
	is_termine(H),
	not(fbf(H)),
	is_predicato(X).

validafbf_2([X | []]) :-
	is_termine(X), !.

validafbf_2([X | []]) :-
	compound(X),
	validafbf(X), !.

validafbf_2([X | Xs]) :-
	is_termine(X),
	validafbf_2(Xs), !.

validafbf_2([X | Xs]) :-
	compound(X),
	validafbf(X),
	validafbf_2(Xs).
	
/*
  PREDICATO TOCNF
  questo predicato gestisce la trasformazione di una FBF in una CNF
  la regola 9 e la regola 10 riguardanti i quantificatori "every" ed "exist" vengono direttamente gestite da questo predicato.
  Per le restanti viene richamata la procedura tocnf_2 che gestisce le restanti trasformazioni
*/
 
tocnf(FBF, CNFFBF) :-
	is_termine(FBF),
	CNFFBF = FBF, !.

tocnf(FBF, CNFFBF) :-
	is_predicato(FBF),
	FBF =.. [H | Ts],
	H \= not,
	H \= and,
	H \= or,
	H \= implies,
	H \= exist,
	H \= every,
	Ts \=[],
	validafbf(FBF),
	CNFFBF = FBF ,!.

tocnf(FBF, CNFFBF) :-
	compound(FBF),
	FBF =.. [H | _],
	H \= exist,
	validafbf(FBF),
	tocnf_2([FBF], CNF2),
	CNFFBF = CNF2, !.
	
/* gestione regola 9 */

tocnf(FBF, CNFFBF) :-
	compound(FBF),
	FBF =.. [H | Ts],
	H = exist,
	Ts = [VAR | T2],
	T2 = [HT2 | _], 
	NFBF = HT2,
	tocnf(NFBF, FBF2),
	FBF2 =.. L,
	skolem_function([], SK),
	esiste_2(VAR, SK, L, [], F),
	VAR = SK,
	FBF_R =.. F,
	tocnf(FBF_R, CNF),
	CNFFBF = CNF, !.

/* Gestione Regola 10 */

tocnf(FBF, CNFFBF) :-
	compound(FBF),
	FBF =.. [H | Ts],
	H = every,
	Ts = [VAR1 | T2],
	T2 = [HT2 | _ ],
	HT2 =.. [Q | T3],
	T3 = [VAR2 | T4],
	T4 = [H5 | _ ],
	Q = exist,
	skolem_function([VAR1], SF),
	VAR2 = SF,
	FBF_R = H5,
	tocnf(FBF_R, CNF),
	CNFFBF = CNF, !.

tocnf(FBF, CNFFBF) :-
	compound(FBF),
	FBF =.. [H | Ts],
	H = every,
	Ts = [_ | T2],
	T2 = [H2 | _ ],
	H2 =.. [Q | _],
	Q \= exist,
	tocnf(H2, CNF),
	CNFFBF = CNF, !.
	
/* 
TOCNF_2
procedura interna per computare i restanti casi di trasformazione
*/

tocnf_2([H | _], CNFFBF) :-
	is_termine(H),
	CNFFBF = H, !.

/* regola 9 */
tocnf_2([H | _], CNF) :-
	H =.. [H1 | Ts],
	H1 = exist,
	Ts \= [],
	Ts = [_ | T2],
	FBF =.. T2,
	esiste(V, FBF),
	CNF = V.

tocnf_2(L, CNF) :-
	L = [H | _],
	H =.. [H1 | Ls],
	H1 = and,
	validafbf(H),
	congiunzione(H1, Ls, CNF1),
	CNF2 =.. CNF1,
	semplifica_and(CNF2, NL),
	append([and], NL, Temp),
	Final =.. Temp,
	CNF = Final, !.

tocnf_2(L, CNF) :-
	L = [H | _],
	H =.. [H1 | Ls],
	H1 = or,
	validafbf(H),
	disgiunzione(H1, Ls, CNF1),
	CNF2 =.. CNF1,
	semplifica_or(CNF2, NL),
	append([or], NL, Temp),
	Final =.. Temp,
	CNF = Final, !.

tocnf_2([H | _], CNF) :-
	H =.. [H1 | _],
	H1 = not,
	negazione(H, M),
	CNF = M.

tocnf_2([H | _], CNF) :-
	H =.. [H1 | T],
	H1 = implies,
	implicazione(T, M),
	tocnf(M, M1),
	CNF = M1, !.
	
 /* Qua un elenco di procedure di appoggio usate in tocnf_2

	predicato per costruire la disgiunzione */
 
 disgiunzione(X, [], CNF) :-
	append([X], [], CNF).

disgiunzione(X, [H | Ts], CNF) :-
	is_predicato(H),
	tocnf(H, CNF_R),
	disgiunzione(CNF_R, Ts, NCNF),
	append([X], NCNF, FCNF),
	CNF = FCNF, !.

/* predicato per costruire la congiunzione */

congiunzione(X, [], CNF) :-
	append([X], [], CNF).

congiunzione(X, [H | Ts], CNF) :-
	is_predicato(H),
	tocnf(H, CNF_R),
	congiunzione(CNF_R, Ts, NCNF),
	append([X], NCNF, FCNF),
	CNF = FCNF, !.
	
	/* predicati per semplificare congiunzioni e disgiunzioni*/
	
semplifica_or(FBF, NL) :-
	FBF =.. [H | Ts],
	H = or,
	semplifica_or_2(Ts, Final),
	NL = Final, !.

semplifica_or(FBF, NL) :-
	FBF =.. [H | _],
	H \= or,
	append([FBF], [], Final),
	NL = Final, !.

semplifica_or_2([H | T] , NL) :-
	T \= [],
	compound(H),
	semplifica_or(H, L2),
	semplifica_or_2(T, L),
	append(L2, L, Final),
	NL = Final, !.

semplifica_or_2([H | []] , NL) :-
	compound(H),
	semplifica_or(H, L2),
	append(L2, [], Final),
	NL = Final, !.

semplifica_or_2([H | T] , NL) :-
	T \= [],
	is_termine(H),
	semplifica_or_2(T, L),
	append([H], L, Final),
	NL = Final, !.

semplifica_or_2([H | []], NL) :-
	is_termine(H),
	append([H], [], Final),
	NL = Final, !.
	
semplifica_and(FBF, NL) :-
	FBF =.. [H | Ts],
	H = and,
	semplifica_and_2(Ts, Final),
	NL = Final, !.

semplifica_and(FBF, NL) :-
	FBF =.. [H | _],
	H \= and,
	append([FBF], [], Final),
	NL = Final, !.

semplifica_and_2([H | T] , NL) :-
	T \= [],
	compound(H),
	semplifica_and(H, L2),
	semplifica_and_2(T, L),
	append(L2, L, Final),
	NL = Final, !.

semplifica_and_2([H | []] , NL) :-
	compound(H),
	semplifica_and(H, L2),
	append(L2, [], Final),
	NL = Final, !.

semplifica_and_2([H | T] , NL) :-
	T \= [],
	is_termine(H),
	semplifica_and_2(T, L),
	append([H], L, Final),
	NL = Final, !.

semplifica_and_2([H | []], NL) :-
	is_termine(H),
	append([H], [], L),
	NL = L, !.
	
/*Procedura di gestione dell' implicazione logica*/

implicazione([X, Y | []], CNF) :-
	tocnf(X, X1),
	tocnf(Y, Y1),
	CNF = or(not(X1), Y1),!.

implicazione([X, Y | []], CNF) :-
	tocnf(not(X), X1),
	tocnf(Y, Y1),
	CNF = or(X1, Y1),!.


/* procedura di supporto gestione quantificatore esistenziale */


esiste(V, FBF) :-
	compound(FBF),
	skolem_function([], SK),
	esiste_2(V, SK, [FBF], [], _),
	V = SK.

esiste_2(V, SK, [H | []], NL, Final) :-
	var(H),
	H == V,
	append([SK], NL, FNL),
	Final = FNL, !.

esiste_2(V, SK, [H | Ts], NL, Final) :-
	var(H),
	H == V,
	esiste_2(V, SK, Ts, NL, F_R),
	append([SK], F_R, FNL),
	Final = FNL, !.

esiste_2(_, _, [H | []], NL, Final) :-
	is_termine(H),
	append([H], NL, FNL),
	Final = FNL, !.

esiste_2(_, _, [H | Ts], NL, Final) :-
	is_termine(H),
	esiste_2(_, _, Ts, NL, F_R),
	append([H], F_R, FNL),
	Final = FNL, !.

esiste_2(V, SK, [H | []], _, Final) :-
	compound(H),
	H =.. [H_R | Ls],
	esiste_2(V, SK, Ls, [], F2),
	append([H_R], F2, NH),
	FH =.. NH,
	append([FH], [], FNL),
	Final = FNL, !.

esiste_2(V, SK, [H | Ts], NL, Final) :-
	compound(H),
	H =.. [H_R | Ls],
	esiste_2(V, SK, Ls, [], F2),
	append([H_R], F2, NH),
	FH =.. NH,
	esiste_2(V, SK, Ts, NL, F3),
	append([FH], F3, FNL),
	Final = FNL, !.
	
/* procedura per gestire la negazione come espressa nelle varie regole */

negazione(not(X), M) :-
	is_predicato(X),
	validafbf(X),
	negazione_2(not(X), M1 ,C1),
	C is C1 - 1,
	is_even(C),
	M = M1, !.

negazione(not(X), M) :-
	is_predicato(X),
	validafbf(X),
	negazione_2(not(X), M1 ,C1),
	C is C1 - 1, 
	not(is_even(C)),
	M = not(M1), !.

negazione_2(not(X), M, C) :-
	is_predicato(X),	
	negazione_2(X, M, C1),
	C is C1 +1.

negazione_2(not(X), M, 0) :-
	not(var(X)),
	X =.. [H | _],
	H \= not,
	tocnf(X, CNF),
	M = CNF.

negazione_2(not(X), M, C) :-
	not(var(X)),
	X =.. [H | T],
	H = not,
	validafbf(T),
	negazione_2(X, M, C1),
	C is C1 +1.

negazione_2(not(X), M, C) :-
	not(var(X)),
	X =.. [H, A | T],
	H = and,
	nega_congiunzione(A, T, FBF),
	append([or], FBF, NFBF),
	NFBF1 =.. NFBF,
	tocnf(NFBF1, NCNF),
	C is 0 +1,
	M = NCNF.

negazione_2(not(X), M, C) :-
	not(var(X)),
	X =.. [H | _],
	H = implies,
	tocnf_2([X], X1),
	tocnf(not(X1), X2),
	C = 1 ,
	M = X2.
	
negazione_2(not(X), M, C) :-
	not(var(X)),
	X =.. [H, A | T],
	H = or,
	nega_disgiunzione(A, T, FBF),
	append([and], FBF, NFBF),
	NFBF1 =.. NFBF,
	tocnf(NFBF1, NCNF),
	C is 0 +1,
	M = NCNF.
	
/* procedure per gestire negazione degli operatori universali e esistenziali */

negazione_2(not(X), M, C) :-
	not(var(X)),
	X =.. [H , A| T],
	H = every,
	append([not], T, NT),
	L =.. NT,
	append([A], [L], T2),
	append([exist], T2, NFBF),
	NFBF1 =.. NFBF,
	tocnf(NFBF1, NCNF),
	C is 0 +1,
	M = NCNF.

negazione_2(not(X), M, C) :-
	not(var(X)),
	X =.. [H , A| T],
	H = exist,
	append([not], T, NT),
	L =.. NT,
	append([A], [L], T2),
	append([every], T2, NFBF),
	NFBF1 =.. NFBF,
	tocnf(NFBF1, NCNF),
	C is 0 +1,
	M = NCNF.
	
/* predicato per controllare che i not siano pari o dispari */
	
is_even(P) :-
	M is P mod 2,
	M = 0.
	
/* procedure per gestire negazione di congiunzione e disgiunzione */

nega_congiunzione(A, [], CNF) :-
	append([not(A)], [], CNF).

nega_congiunzione(A, [H | FBF], CNF) :-
	tocnf(H, CNF3),
	nega_congiunzione(CNF3, FBF, CNF2),
	append([not(A)], CNF2, CNF1),
	CNF = CNF1, !.
	
nega_disgiunzione(A, [], CNF) :-
	append([not(A)], [], CNF).

nega_disgiunzione(A, [H | FBF], CNF) :-
	tocnf(H, CNF3),
	nega_disgiunzione(CNF3, FBF, CNF2),
	append([not(A)], CNF2, CNF1),
	CNF = CNF1, !.

/*
		IS_HORN
		il predicato prende una FBF, effettua la conversione in CNF e controlla che quest'ultima sia una clausola di horn
		
*/
is_horn(FBF) :-
	is_termine(FBF), !.

is_horn(FBF) :-
	compound(FBF),
	validafbf(FBF),
	tocnf_2([FBF], CNF),
	CNF =.. NCNF,
	is_horn_2(NCNF, C),
	C < 2,!.

is_horn_2([H | T], C) :-
	H = or,
	is_horn_2(T, C1),
	C is C1 + 0, !.

is_horn_2([H | T], C) :-
	H = and,
	is_horn_2(T, C1),
	C is C1 + 0, !.

is_horn_2([H | T], C) :-
	H \= and,
	H \= or,
	H \= not(_),
	is_horn_2(T, C1),
	C is C1 + 1.

is_horn_2([H | T], C) :-
	H \= and,
	H \= or,
	H = not(_),
	is_horn_2(T, C1),
	C is C1 + 0.

is_horn_2([H | []], C) :-
	H \= and,
	H \= or,
	H = not(_),
	C = 0.

is_horn_2([H | []], C) :-
	H \= and,
	H \= or,
	H \= not(_),
	C = 1.
	
	/* predicato di skolemizzazione */
	
skolem_variable(V, SK) :- var(V), gensym(skv, SK).
skolem_function([], SF) :- skolem_variable(_, SF).
skolem_function([A | ARGS], SF) :-
	gensym(skf, SF_op),
	SF =.. [SF_op, A | ARGS].