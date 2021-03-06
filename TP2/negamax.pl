	/*
	Ce programme met en oeuvre l'algorithme Minmax (avec convention
	negamax) et l'illustre sur le jeu du TicTacToe (morpion 3x3)
	*/
	
	
:- use_module(library(clpfd)).
:- [tictactoe].

/*
	negamax(+J, +Etat, +P, +Pmax, [?Coup, ?Val])

	SPECIFICATIONS :

	retourne pour un joueur J donne, devant jouer dans
	une situation donnee Etat, de profondeur donnee P,
	le meilleur couple [Coup, Valeur] apres une analyse
	pouvant aller jusqu'a la profondeur Pmax.

	Il y a 3 cas a decrire (donc 3 clauses pour negamax/5)
	
	1/ la profondeur maximale est atteinte : on ne peut pas
	developper cet Etat ; 
	il n'y a donc pas de coup possible a jouer (Coup = rien)
	et l'evaluation de Etat est faite par l'heuristique.

	2/ la profondeur maximale n'est pas  atteinte mais J ne
	peut pas jouer ; au TicTacToe un joueur ne peut pas jouer
	quand le tableau est complet (totalement instancie) ;
	il n'y a pas de coup a jouer (Coup = rien)
	et l'evaluation de Etat est faite par l'heuristique.

	3/ la profondeur maxi n'est pas atteinte et J peut encore
	jouer. Il faut evaluer le sous-arbre complet issu de Etat ; 

	- on determine d'abord la liste de tous les couples
	[Coup_possible, Situation_suivante] via le predicat
	 successeurs/3 (deja fourni, voir plus bas).

	- cette liste est passee a un predicat intermediaire :
	loop_negamax/5, charge d'appliquer negamax sur chaque
	Situation_suivante ; loop_negamax/5 retourne une liste de
	couples [Coup_possible, Valeur]

	- parmi cette liste, on garde le meilleur couple, c-a-d celui
	qui a la plus petite valeur (cf. predicat meilleur/2);
	soit [C1,V1] ce couple optimal. Le predicat meilleur/2
	effectue cette selection.

	- finalement le couple retourne par negamax est [Coup, V2]
	avec : V2 is -V1 (cf. convention negamax vue en cours).

*/

	/****************************************************
  	ALGORITHME MINMAX avec convention NEGAMAX : negamax/5
  	*****************************************************/
	
% Cas 1 : la profondeur maximale est atteinte
negamax(J,Etat,Pmax,Pmax,[nil,Val]):-heuristique(J,Etat,Val).

% Cas 2 : la profondeur maximale n'est pas  atteinte mais J ne peut pas jouer
negamax(J,Etat,P,Pmax,[_,Val]):-
	P < Pmax,
	situation_terminale(J,Etat),
	heuristique(J,Etat,Val).
	
% Cas 3 : la profondeur maxi n'est pas atteinte et J peut encore jouer
negamax(J,Etat,P,Pmax,[Coup,Val]):-
	P < Pmax,
	successeurs(J,Etat,Succ),
	loop_negamax(J,P,Pmax,Succ,Liste_Couples),
	meilleur(Liste_Couples,[Coup,V1]),
	Val is -V1.

	/*******************************************
	 DEVELOPPEMENT D'UNE SITUATION NON TERMINALE
	 successeurs/3 
	 *******************************************/

	 /*
   	 successeurs(+J,+Etat, ?Succ)

   	 retourne la liste des couples [Coup, Etat_Suivant]
 	 pour un joueur donne dans une situation donnee 
	 */

successeurs(J,Etat,Succ) :-
	copy_term(Etat, Etat_Suiv),
	findall([Coup,Etat_Suiv],
		    successeur(J,Etat_Suiv,Coup),
		    Succ).
/*	remove_sym_list(Succ2,Succ2,Succ).
			
remove_sym_list([],Res,Res).

remove_sym_list([S1|L1],Inter,Res):-
	remove_sym(S1,Inter ,L2),	
	remove_sym_list(L1,L2,Res).
	
remove_sym(_,[],[]).
remove_sym(S1,[S2|L2],[S2|L3]):-
	not(situation_symetrique(S1,S2)),
	remove_sym(S1,L2,L3).
	
remove_sym(S1,[S2|L2],L3):-
	situation_symetrique(S1,S2),
	remove_sym(S1,L2,L3).*/
	

	/*************************************
         Boucle permettant d'appliquer negamax 
         a chaque situation suivante :
	*************************************/

	/*
	loop_negamax(+J,+P,+Pmax,+Successeurs,?Liste_Couples)
	retourne la liste des couples [Coup, Valeur_Situation_Suivante]
	a partir de la liste des couples [Coup, Situation_Suivante]
	*/

loop_negamax(_,_, _  ,[],                []).
loop_negamax(J,P,Pmax,[[Coup,Suiv]|Succ],[[Coup,Vsuiv]|Reste_Couples]) :-
	% On r?cup?re le couple [Coup,Suiv] dans Successeurs et 
	% on met le couple [Coup,Vsuiv] dans Liste_Couples
	loop_negamax(J,P,Pmax,Succ,Reste_Couples), 
	% On alterne de joueur
	adversaire(J,A),
	% On actualise la profondeur (+1)
	Pnew is P+1,
	% On relance negamax avec le nouveau joueur, la nouvelle profondeur et l'?tat suivant
	% On met _ ? la place du coup car on ne sait pas encore quel est le meilleur coup
	negamax(A,Suiv,Pnew,Pmax,[_,Vsuiv]).

	/*

A FAIRE : commenter chaque litteral de la 2eme clause de loop_negamax/5,
	en particulier la forme du terme [_,Vsuiv] dans le dernier
	litteral ?
	*/

	/*********************************
	 Selection du couple qui a la plus
	 petite valeur V 
	 *********************************/

	/*
	meilleur(+Liste_de_Couples, ?Meilleur_Couple)

	SPECIFICATIONS :
	On suppose que chaque element de la liste est du type [C,V]
	- le meilleur dans une liste a un seul element est cet element
	- le meilleur dans une liste [X|L] avec L \= [], est obtenu en comparant
	  X et Y,le meilleur couple de L 
	  Entre X et Y on garde celui qui a la petite valeur de V.

A FAIRE : ECRIRE ici les clauses de meilleur/2
	*/
meilleur([],[]).
% Cas 1 : le meilleur dans une liste a un seul element est cet element
meilleur([Couple],Couple).
% Cas 2 : le meilleur dans une liste [X|L] avec L \= [], est obtenu en comparant
%	  X et Y,le meilleur couple de L 
%	  Entre X et Y on garde celui qui a la petite valeur de V.
meilleur([[Coup,Vsuiv]|Reste_Couples],Meilleur_Couple):-
	Reste_Couples \= [],
	meilleur(Reste_Couples,[McoupSuiv,MVSuiv]),
	(Vsuiv < MVSuiv 
		% Si X < Y, on garde X
		-> Meilleur_Couple=[Coup,Vsuiv]
		% Sinon, on garde Y
		;  Meilleur_Couple=[McoupSuiv,MVSuiv]
	).
	
/*meilleur([[Coup,Vsuiv]|Reste_Couples],Meilleur_Couple):-
	Reste_Couples \= [],
	meilleur(Reste_Couples,[McoupSuiv,MVSuiv]),
	Vsuiv < MVSuiv,
	Meilleur_Couple=[Coup,Vsuiv].
	
meilleur([[Coup,Vsuiv]|Reste_Couples],Meilleur_Couple):-
	Reste_Couples \= [],
	meilleur(Reste_Couples,[McoupSuiv,MVSuiv]),
	Vsuiv >= MVSuiv,
	Meilleur_Couple=[McoupSuiv,MVSuiv].*/
	

% Test
	
test_meilleur() :-
	writeln("Test meilleur(+Liste_de_Couples, ?Meilleur_Couple)"),
	write("meilleur([[a,-1],[b,-51],[c,-62],[d,-4]],[Mcoup,MV]) : ["),
	meilleur([[a,-1],[b,-51],[c,-62],[d,-4]],[Mcoup,MV]),
	write(Mcoup),write(","),write(MV),writeln(']').

	/******************
  	PROGRAMME PRINCIPAL
  	*******************/

main(B,V, Pmax) :-
	situation_initiale(Etat),
	joueur_initial(J),
	negamax(J,Etat,0,Pmax,[B,V]).
	
	/******************
  	SITUATION SYMETRIQUE
  	*******************/	
	
matrix_rotated(Xss, Zss) :-
	transpose(Xss, Yss),
	maplist(reverse, Yss, Zss).

nrotate(0,M,M).

nrotate(N,M,M2) :-
	not(N = 0),
	N1 is N-1,
	matrix_rotated(M,M3),
	nrotate(N1,M3,M2).
	
situation_symetrique(S1,S2) :- % Rotation
	between(1,3,N), % 4eme rotation = lui-meme
	nrotate(N,S1,S2).
	
situation_symetrique(S1,S2) :- % Symetrie horizontale + rotation
	reverse(S1,S3),
	between(1,3,N), % 4eme rotation = lui-meme
	nrotate(N,S3,S2).

	/*
A FAIRE :
	Compl?ter puis tester le programme principal pour plusieurs valeurs de la profondeur maximale.
	Pmax = 1, 2, 3, 4 ...
	Commentez les r?sultats obtenus.
	*/

