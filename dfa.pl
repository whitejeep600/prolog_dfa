% Antoni Maciąg
% my internal representation of an automaton consists simply in storing balanced
% BSTs representing the transition function and final states. 
use_module(library(lists)).

% given a list of terms of form fp(A, B, C), succeeds if the third element is the
% list of all As for N=1, Bs for N=2 or Cs for N=3.
project_nth(_, [], []).
project_nth(N, [fp(A, B, C) | Rest], [X | Projected_rest]) :-
    project_nth(N, Rest, Projected_rest), nth1(N, [A, B, C], X).

% similar as above, but succeeds if the third elements is a list of [A, B] pairs.
project_first_two([], []).
project_first_two([fp(A, B, _) | Rest], [[A, B] | Projected_rest]) :-
    project_first_two(Rest, Projected_rest).

remove_duplicates([], []).
remove_duplicates([F | R], Rest_removed) :-
    member(F, R), remove_duplicates(R, Rest_removed).
remove_duplicates([F | R], [F | Rest_removed]) :-
    \+ member(F, R), remove_duplicates(R, Rest_removed).

project_nth_without_duplicates(N, A, B) :-
    project_nth(N, A, C), remove_duplicates(C, B).

no_doubles([]).
no_doubles([F | R]) :- member(F, R), !, fail.
no_doubles([_ | R]) :- no_doubles(R).

% auxiliary predicate for cartesian_product - combinations(X, L, R) succeeds if
% R is the list of pairs [X, l] for l in L.
combinations(_, [], []).
combinations(A, [F | Rest], [[A, F] | Rest_combinations]) :-
    combinations(A, Rest, Rest_combinations).

cartesian_product([], _, []).
cartesian_product([_|_], [], []).
cartesian_product([A | Arest], B, R) :- no_doubles([A | Arest]),
                                        no_doubles(B),
                                        B \= [],
                                        combinations(A, B, X),
                                        cartesian_product(Arest, B, Y),
                                        append(X, Y, R).

% each pair [s, q] for s in states, q in alphabet has to appear exactly ones,
% which happens if the list of [s, q] is a cartesian product of states and
% alphabet letters.
is_complete_function(F, Q, S) :- project_nth_without_duplicates(1, F, S),
                                 project_nth_without_duplicates(2, F, Q),
                                 project_nth_without_duplicates(3, F, Cs),
                                 project_first_two(F, As_and_Bs),
                                 cartesian_product(S, Q, Cartesian),
                                 permutation(As_and_Bs, Cartesian),
                                 subset(Cs, S).

dfa(F, S0, Fin) :- is_complete_function(F, _, S),
                   member(S0, S),
                   subset(Fin, S),
                   no_doubles(Fin).

valid_automaton(A) :- A = dfa(F, S0, Fin),
                      \+ var(A),
                      dfa(F, S0, Fin).

prefix_length(List, Prefix, Length) :-
    prefix(Prefix, List),
    length(Prefix, Length).

suffix_length(List, Suffix, Length) :-
   reverse(List, Reversed),
   prefix_length(Reversed, Reverse_prefix, Length),
   reverse(Reverse_prefix, Suffix).

merge_sorted(X, [], X).
merge_sorted([], X, X) :- X \= [].
merge_sorted([A_first | A_rest], [B_first | B_rest], [A_first | Rest_sorted]) :-
    @=<(A_first, B_first),
    merge_sorted(A_rest, [B_first | B_rest], Rest_sorted).
merge_sorted([A_first | A_rest], [B_first | B_rest], [B_first | Rest_sorted]) :-
    @<(B_first, A_first),
    merge_sorted([A_first | A_rest], B_rest, Rest_sorted).

merge_sort([], []).
merge_sort([X], [X]).
merge_sort(List, Sorted) :-
    length(List, Length),
    Length > 1,
    Half_length is Length // 2,
    Suf_length is Length - Half_length,
    prefix_length(List, First_half, Half_length),
    suffix_length(List, Second_half, Suf_length),
    merge_sort(First_half, First_half_sorted),
    merge_sort(Second_half, Second_half_sorted),
    merge_sorted(First_half_sorted, Second_half_sorted, Sorted).

% two child-subtrees of a node can differ in size by no more than 1, so the
% tree is balanced. This is an auxiliary (aux) predicate for ease of use.
% The list is assumed to be sorted, which is assured by the main below below.
create_balanced_bst_aux([], tree(empty)).
create_balanced_bst_aux(List, tree(Left_tree, Pivot, Right_tree)) :-
    List \= [],
    length(List, Length),
    Half_length is Length // 2,
    prefix_length(List, First_half, Half_length),
    nth0(Half_length, List, Pivot),
    Suf_length is Length - Half_length - 1,
    suffix_length(List, Second_half, Suf_length),
    create_balanced_bst_aux(First_half, Left_tree),
    create_balanced_bst_aux(Second_half, Right_tree).

create_balanced_bst(List, Tree) :- merge_sort(List, Sorted),
                                   create_balanced_bst_aux(Sorted, Tree).

bst_contains(Element, tree(_, Element, _)).
bst_contains(Element, tree(Left, _, _)) :- bst_contains(Element, Left).
bst_contains(Element, tree(_, _, Right)) :- bst_contains(Element, Right).

% the representation of a tree is simply the tree with transition function list
% and final state list replaced by balanced BSTs for quicker lookup.
correct(dfa(F, S0, Fin), rep(F_tree, S0, Fin_tree)) :-
    valid_automaton(dfa(F, S0, Fin)),
    create_balanced_bst(F, F_tree),
    create_balanced_bst(Fin, Fin_tree).

accept_aux(rep(_, S0, Fin), []) :- bst_contains(S0, Fin).
accept_aux(rep(F, S0, Fin), [First | Rest]) :-
    accept_aux(rep(F, Snew, Fin), Rest),
    bst_contains(fp(S0, First, Snew), F).

accept(Automaton, Word) :- correct(Automaton, Representation),
                           accept_aux(Representation, Word).

% children-nodes in graph search.
children([], _, []).
children([fp(Node, _, Child) | Rest], Node, [Child | Rest_found]) :-
    children(Rest, Node, Rest_found). 
children([fp(Node1, _, _) | Rest], Node2, Rest_found) :-
    Node1 \= Node2, children(Rest, Node2, Rest_found).

lists_difference([], _, []).
lists_difference([LFirst | LRest], L2, RRest) :-
    member(LFirst, L2),
    lists_difference(LRest, L2, RRest).
lists_difference([LFirst | LRest], L2, [LFirst | RRest]) :-
    \+ member(LFirst, L2),
    lists_difference(LRest, L2, RRest).

% auxiliary predicate for the predicate below implementing a depth-first graph
% search, used to find all the states reachable from the start state of an automaton.
reachable_aux(_, [], Already_found, Already_found).
reachable_aux(F, [Stack_first | Stack_rest], Already_found, Result) :-
    children(F, Stack_first, Children_with_reps),
    remove_duplicates(Children_with_reps, Children),
    lists_difference(Children, Already_found, New_found_children),
    append(New_found_children, Already_found, Found_until_now),
    append(New_found_children, Stack_rest, New_stack),
    reachable_aux(F, New_stack, Found_until_now, Result).

reachable(F, S0, X) :- reachable_aux(F, [S0], [S0], X).

% to check for emptiness, it is checked if any of the final states is
% reachable from the start state.
empty(dfa(F, S0, Fin)) :- valid_automaton(dfa(F, S0, Fin)),
                          reachable(F, S0, Reachable_states),
                          intersection(Reachable_states, Fin, Intersection),
                          Intersection = [].

% to check if an automaton A is a subset of another automaton B, it will be checked
% if the complement automaton of B has non-empty intersection with automaton A
% (vide https://www.mimuw.edu.pl/~szymtor/jao/skrypt.pdf)
% the method of finding complement automatons is described below. Intersection is
% found by constructing the so-called product automaton.
automaton_product(dfa(F1, S01, Fin1), dfa(F2, S02, Fin2), dfa(F3, [S01, S02], Fin3)) :-
    transition_product(F1, F2, F3),
    cartesian_product(Fin1, Fin2, Fin3).

% auxiliary for the function below - list processing.
transition_product_one(_, [], []).
transition_product_one(fp(P, A, R),
                      [fp(Q, A, S) | T2_rest],
                      [fp([P, Q], A, [R, S]) | Rest_found]) :-
    transition_product_one(fp(P, A, R), T2_rest, Rest_found).
transition_product_one(fp(P, A, R), [fp(_, B, _) | T2_rest],  Rest_found) :-
    A \= B,
    transition_product_one(fp(P, A, R), T2_rest, Rest_found).

% finds the transition function of the product of two automatons.
transition_product([], _, []).
transition_product([L1_first | L1_rest], L2, R) :-
    transition_product_one(L1_first, L2, From_first),
    transition_product(L1_rest, L2, From_rest),
    append(From_first, From_rest, R).

% automaton complement of A is obtained from A by swapping its final and
% non-final states.
automaton_complement(dfa(F, S0, Fin), dfa(F, S0, New_fin)) :-
    project_nth_without_duplicates(1, F, States),
    lists_difference(States, Fin, New_fin).

same_alphabets(dfa(F1, _, _), dfa(F2, _, _)) :-
    project_nth_without_duplicates(2, F1, Alph_1),
    project_nth_without_duplicates(2, F2, Alph_2),
    permutation(Alph_1, Alph_2).

subsetEq(A1, A2) :- valid_automaton(A1),
                    valid_automaton(A2),
                    automaton_complement(A2, A2_complement),
                    automaton_product(A1, A2_complement, Product),
                    empty(Product),
                    same_alphabets(A1, A2).

equal(A1, A2) :- subsetEq(A1, A2), subsetEq(A2, A1).

example(a11, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1)], 1, [2,1])).
example(a12, dfa([fp(x,a,y),fp(x,b,x),fp(y,a,x),fp(y,b,x)], x, [x,y])).
example(a2, dfa([fp(1,a,2),fp(2,b,1),fp(1,b,3),fp(2,a,3), fp(3,b,3),fp(3,a,3)], 1, [1])).
example(a3, dfa([fp(0,a,1),fp(1,a,0)], 0, [0])).
example(a4, dfa([fp(x,a,y),fp(y,a,z),fp(z,a,x)], x, [x])).
example(a5, dfa([fp(x,a,y),fp(y,a,z),fp(z,a,zz),fp(zz,a,x)], x, [x])).
example(a6, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1)], 1, [])).
example(a7, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1), fp(3,b,3),fp(3,a,3)], 1, [3])).

example(b1, dfa([fp(1,a,1),fp(1,a,1)], 1, [])).
example(b2, dfa([fp(1,a,1),fp(1,a,2)], 1, [])).
example(b3, dfa([fp(1,a,2)], 1, [])).
example(b4, dfa([fp(1,a,1)], 2, [])).
example(b4, dfa([fp(1,a,1)], 1, [1,2])).
example(b5, dfa([], [], [])).

test :- example(a2, A), accept(A, [a]), !, fail.
test :- example(b1, A), correct(A, _), !, fail.
test :- example(b2, A), correct(A, _), !, fail.
test :- example(b3, A), correct(A, _), !, fail.
test :- example(b4, A), correct(A, _), !, fail.
test :- example(b5, A), correct(A, _), !, fail.
test :- example(a2, A), empty(A), !, fail.
test :- example(a5, A5), example(a3, A3), subsetEq(A3, A5), !, fail.
test :- example(a4, A), example(a3, B), subsetEq(A, B).
test :- example(a3, A), example(a4, B), equal(A, B), !, fail.
test :- dfa([fp(x,a,y),fp(x,b,x),fp(y,a,x),fp(y,b,x)], x, [x,y]),
        dfa([fp(1,a,2),fp(2,b,1),fp(1,b,3),fp(2,a,3), fp(3,b,3),fp(3,a,3)], 1, [1]),
        dfa([fp(0,a,1),fp(1,a,0)], 0, [0]),
        dfa([fp(x,a,y),fp(y,a,z),fp(z,a,x)], x, [x]),
        dfa([fp(x,a,y),fp(y,a,z),fp(z,a,zz),fp(zz,a,x)], x, [x]),
        dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1)], 1, []),
        dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1), fp(3,b,3),fp(3,a,3)], 1, [3]),
        example(a2, A2), accept(A2, []),
        example(a11, A11), findall([X, Y, Z], accept(A11, [X, Y, Z]), W),
        permutation(W, [[a, a, a], [a, a, b], [a, b, a], [a, b, b], [b, a, a], [b, a, b], [b, b, a], [b, b, b]]),
        example(a6, A6), empty(A6),
        example(a7, A7), empty(A7),
        example(a11, A11), subsetEq(A2, A11),
        example(a5, A5), example(a3, A3), subsetEq(A5, A3),
        example(a11, A), example(a12, B), equal(A, B).
