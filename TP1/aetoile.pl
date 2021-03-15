%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de façon synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************
% Main
%*******************************************************************************

main :-
	% état initial
	initial_state(S0),
	% Calcul de H0, G0 = 0 et F0 = H0
	heuristique(S0,H0),
	G0 is 0,
	F0 is H0+G0,
	% initialisations Pf, Pu et Q 
	% 3 AVLs vides
	empty(Pf),
	empty(Pu),
	empty(Q),
	% Insertion de [ [F0,H0,G0], S0 ] dans Pf 
	% et de [S0, [F0,H0,G0], nil, nil] dans Pu
	insert([[F0,H0,G0],S0],Pf,Pf2),
	insert([S0,[F0,H0,G0],nil,nil],Pu,Pu2),
	% lancement de Aetoile
	aetoile(Pf2,Pu2,Q).


%*******************************************************************************
% Aetoile
%*******************************************************************************

% Cas Trivial 1 : si Pf et Pu sont vides, il n’y a aucun état pouvant 
% être développé donc pas de solution au problème

aetoile(nil,nil,_) :- 
    write("PAS DE SOLUTION : L'ÉTAT FINAL N'EST PAS ATTEIGNABLE.").

% Cas Trivial 2 : si le noeud de valeur F minimum de Pf correspond 
% à la situation terminale, alors on a trouvé une solution 
% et on peut l’afficher (prédicat affiche_solution)
	
aetoile(Pf,Pu,Q) :-
	suppress_min([_,U],Pf,_),
	final_state(U),
	affiche_solution(U,Pu,Q).
	
% Cas Général 

aetoile(Pf,Pu,Q) :-
	% on enlève le noeud de Pf correspondant à l’état U 
	% à développer (celui de valeur F minimale)
	% et on enlève aussi le noeud frère associé dans Pu
	suppress_min([[F,H,G],U],Pf,Pf2),
	not(final_state(U)),
	suppress([U,[F,H,G],Pere,Action],Pu,Pu2),
	% développement de U
	expand(U,Lsucc,G),
	loop_successors(Lsucc,Pf2,Pu2,Q,Pf_new,Pu_new),
	% U ayant été développé et supprimé de P, il reste à l’insérer 
	% le noeud [U,Val,…,..] dans Q,
	insert([U,[F,H,G],Pere,Action],Q,Q_new),
	% Appeler récursivement aetoile avec les nouveaux ensembles 
	% Pf_new, Pu_new et Q_new
	aetoile(Pf_new,Pu_new,Q_new).
	
	

%*******************************************************************************
% Affiche_solution
%*******************************************************************************

affiche_solution(nil,_,_).

affiche_solution(U,Pu,Q):-
	U \= nil,
	belongs([U,_,Pere,Action],Q), 
	affiche_solution(Pere,Pu,Q),
	write(Action),
    write('->'),
    write_state(U),
    writeln(" ").
	
affiche_solution(U,Pu,Q):-
	U \= nil,
	belongs([U,_,Pere,Action],Pu),
	affiche_solution(Pere,Pu,Q),
	write(Action),
    write('->'),
    write_state(U),
    writeln(" ").
	
			
%*******************************************************************************
% Expand
%*******************************************************************************

expand(U,Lsucc,G):-
	% déterminer tous les noeuds contenant un état 
	% successeur S de la situation U et calculer leur 
	% évaluation [Fs, Hs, Gs] connaissant Gu et le coût 
	% pour passer de U à S.
	findall([Succ,[Fsucc,Gsucc,Hsucc],U,Action], 
		(rule(Action,Cout,U,Succ),
			Gsucc is G+Cout,
			heuristique(Succ,Hsucc),
			Fsucc is Gsucc+Hsucc),
		Lsucc).


%*******************************************************************************
% Loop_successors
%*******************************************************************************
	
% Cas trivial : terminaison
loop_successors([],Pf,Pu,_,Pf,Pu).
	
% traiter chaque noeud successeur (prédicat loop_successors) :

% - si S est connu dans Q alors oublier cet état 
% (S a déjà été développé)
loop_successors([[Succ,_,_,_]|Rest],Pf,Pu,Qs,Pf_new,Pu_new):-
	belongs([Succ,_,_,_],Qs),
	loop_successors(Rest,Pf,Pu,Qs,Pf_new,Pu_new).
	
% - si S est connu dans Pu alors garder le terme associé 
% à la meilleure évaluation (dans Pu et dans Pf)
%	* F<Fsucc, on continue sans rien modifier
loop_successors([[Succ,[Fsucc,_,_],_,_]|Rest],
					Pf,Pu,Qs,Pf_new,Pu_new):-
	not(belongs([Succ,_,_,_],Qs)),
	belongs([Succ,[F,_,_],_,_],Pu),
	F<Fsucc,
	loop_successors(Rest,Pf,Pu,Qs,Pf_new,Pu_new).
%	* F>Fsucc, on a trouvé un meilleur chemin : 
%	on modifie Pu et Pf
loop_successors([[Succ,[Fsucc,Hsucc,Gsucc],Pere,Action]|Rest],
									Pf,Pu,Qs,Pf_new,Pu_new):-
	not(belongs([Succ,_,_,_],Qs)),
	belongs([Succ,[F,H,G],_,_],Pu),
	F>Fsucc,
	suppress([Succ,[F,H,G],_,_],Pu,Pu2),
	insert([Succ,[Fsucc,Hsucc,Gsucc],Pere,Action],Pu2,Pu3),
	suppress([[F,H,G],Succ],Pf,Pf2),
	insert([[Fsucc,Hsucc,Gsucc],Succ],Pf2,Pf3),
	loop_successors(Rest,Pf3,Pu3,Qs,Pf_new,Pu_new).
	
% - sinon (S est une situation nouvelle) il faut créer 
% un nouveau terme à insérer dans Pu (idem dans Pf)
loop_successors([[Succ,[Fsucc,Hsucc,Gsucc],Pere,Action]|Rest],
									Pf,Pu,Qs,Pf_new,Pu_new):-
	not(belongs([Succ,_,_,_],Qs)),
	not(belongs([Succ,_,_,_],Pu)),
	insert([Succ,[Fsucc,Hsucc,Gsucc],Pere,Action],Pu,Pu2),
	insert([[Fsucc,Hsucc,Gsucc],Succ],Pf,Pf2),
	loop_successors(Rest,Pf2,Pu2,Qs,Pf_new,Pu_new).
	

%*******************************************************************************
% Test_expand
%*******************************************************************************
	
	
test_expand :-
    initial_state(U),
	writeln("Etat initial"),
    write(U),
    expand(U,Lsuc,0),
	writeln(" "),
	writeln("Liste des Successeurs"),
    write(Lsuc).