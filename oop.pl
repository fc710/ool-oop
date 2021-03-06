%%%% -*- Mode : Prolog -*-

%%% True if class/3 is a valid predicate and C is a class name
is_class(C) :- current_predicate(class/3), class(C, _, _).

%%% True if instance/3 is a valid predicate and I is a valid object
is_instance(I):- current_predicate(instance/3), instance(I, _, _).

%%% True if 'method' is the functor of X
%%% with 2 arguments (parameters and body)
is_method(X) :- functor(X, method, 2).

%%% pair_slots(L, P)
%%% collect the pairs in P
%%% A = B -> A-B
pair_slots([], []).
pair_slots([H | T], [K-Y | R]) :-
    =(H, K = Y), atomic(K), pair_slots(T, R).

%%% SK contains all slots keys of class C
slots_keys(C, SK) :-
    is_class(C),
    class(C, _, S),
    pairs_keys(S, SK).

%%% append_if_key(R1, R2, R12)
%%% adds in R12, the K-V pair from R1, if K key isn't in R2

append_if_key([], R2, R2).
append_if_key([K-_ | R1], R2, R12) :-
    member(K-_, R2),
    append_if_key(R1, R2, R12),!.
append_if_key([K-V | R1], R2, [K-V| R12]) :-
    \+ member(K-_, R2),
    append_if_key(R1, R2, R12).

all_slots_keys(C, SKs) :-
    superclass(C, Super),
    maplist(slots_keys, [C | Super], L),
    flatten(L, F), sort(F, SKs).

superclass(Class, []) :-
    is_class(Class),
    class(Class, [], _), !.
superclass(Class, Result) :-
    is_class(Class),
    class(Class, Parents, _),
    maplist(superclass,Parents,R),
    flatten(R,F),
    append(F, Parents, F1),
    list_to_set(F1, Result).

%%% Deleting this...
%%% split_slots_(Slots, Attrib, Methods): Split the Slots
%%%in Attrib and Methods

split_slots([], [], []).
split_slots([K-V | S], [K-V | A], M) :-
    \+ functor(V, method, _),
    split_slots(S, A, M), !.
split_slots([K-V | S], A, [K-V | M]) :-
    functor(V, method, _),
    split_slots(S, A, M).

%%% create_head(Name, T, Args, Head)
%%% Create the head of the method named
%%% 'Name'. T is a free variable for 'this'

create_head(K, T, [], F) :-
    var(T),
    F =.. [K, T], !.
create_head(K, T, A, F) :-
    var(T),
    F =.. [K, T | A].

%%% create_body(Name, T, Args, Body)
%%% Create the body of the method named
%%% 'Name'. T is a free variable for 'this

create_body(N, T, A, B) :-
    var(T),
    B = (getv(T, N, [A, X]),
	 call(X)).

%%% build_method(Name, Args)
%%% Create the method given a name and its args
%%% and add it to the knowledge base if not already present

build_method(N, A) :-
    create_head(N, T, A, H),
    create_body(N, T, A, B),
    clause(H, B), !.
build_method(N, A) :-
    create_head(N, T, A, H),
    create_body(N, T, A, B),
    assert(H :- B).

%%% Deleting this...
%%% process_methods(Methods, Instance, Result)
%%% For each method in Methods
%%% changes 'this' with Instance, adds method call in knowledge base, updates
%%% slot pair and pass it to Result
process_methods([], _, []).
process_methods([M | Ms], Instance, [K-[A, Cj] | Rs]) :-
    M = K-M1,
    M1 =.. [_, A ,B],
    %unpack_body(B, BE),
    %applies univ to all sub-terms
    %maplist(=.., BE, Lb),
    %replaces all occurences of 'this' with Instance
    %maplist(replace(this, Instance),
    %	    Lb, Cb),
    %reverse with the new changes
    %   maplist(=.., C, Cb),
    %  repack_body(C, Cj),
    %make the method callable
    replace(this, Instance, B, Cj),
    %create_head(K, G, A, F),
    %create_method(F, K, G, A),
    build_method(K, A),
    process_methods(Ms, Instance, Rs).

%%% process-slots.... new def

process_slots([], _, []).
process_slots([K-S | Ss], I, [K-S | Rs]) :-
    \+ is_method(S), !,
    process_slots(Ss, I, Rs).
process_slots([K-M | Ss], I, [K-[A, Cj] | Rs]) :-
    is_method(M),
    M =.. [_, A, B],
    replace(this, I, B, Cj),
    build_method(K, A),
    process_slots(Ss, I, Rs).

%%% parents_slots_(Parents, Slots)
%%% Slots has all the slots from Parents list

parents_slots_([],[]).
parents_slots_([H | T], Slots) :-
    class(H, _, S),
    parents_slots_(T, SP),
    append_if_key(S, SP, Slots).

%%% all_slots(Class, Slots)
%%% Slots is a list of all valid default slots for Class

all_slots(C, S) :-
    superclass(C, SC),
    reverse([C | SC], RS),
    parents_slots_(RS, S).

%%% def_class(Class, Parents, Slots)
%%% Create a fact 'class(Class, Parents, Slots)' if Class isn't already a class,
%%% Slots is a list elements like A = B

def_class(Class, Parents, Slots) :-
    atomic(Class),
    \+ is_class(Class),
    maplist(is_class, Parents),
    pair_slots(Slots, Pairs),
    assert(class(Class, Parents, Pairs)).

%%% new(Instance, Class, DSlots)
%%% if DSlots are valid slots for class 'Class', create an object 'Instance'
%%% with all the appropriate slots inherited

new(Instance, Class, DSlots) :-
    atomic(Instance), is_class(Class),
    \+ is_instance(Instance),
    pair_slots(DSlots, Pairs),
    all_slots_keys(Class, S),
    pairs_keys(Pairs, P),
    subset(P, S),
    all_slots(Class, Cslots),
    append_if_key(Cslots, Pairs, Fslots),
    process_slots(Fslots, Instance, Ps),
    %%split_slots(Fslots, Att, Methods),
    %%process_methods(Methods, Instance, Fm),
    %%append(Fm, Att, Final),
    assert(instance(Instance, Class, Ps)).

%%% new(Instance, Class):

new(I, C) :-
    new(I, C, []).

%%% getv(Instance, Key, Value)

getv(I, K, V) :-
    is_instance(I),
    instance(I, _, S),
    member(K-V,S), !.

%%% getvx(Instance, Keys, Values)

getvx(I, [K | []], V) :-
    is_instance(I),
    getv(I, K, V), !.

getvx(I, [K | Ks], V) :-
    is_instance(I),
    getv(I, K, V1),
    getvx(V1, Ks, V).

%%% replace(Old, New, L, R)
%%% Replace every occurence of Old in L
%%% with New and store the result in R

replace(S0, S, T0, S) :-
    T0 == S0, !.
replace(_, _, T0, T0) :-
    var(T0).
replace(S0, S, T0, T) :-
    T0 =.. [F | A0],
    maplist(replace(S0, S), A0, A),
    T =.. [F | A], !.

/*discarded predicates

replace1(S0, S, T0, T) :-
    ( T0 == S0 -> T = S;
      var(T0) -> T = T0;
      T0 =.. [F|A0],
      maplist(replace1(S0, S), A0, A),
      T =..[F|A]).

%unpack_body(Body, Unpacked): prepares the method body for the
%transform predicate

%B is already a conjunction of terms
unpack_body(B, UB) :-
    functor(B, ',', _),
    transform(UB, B), !.
%B isn't a conjunction of terms yet
unpack_body(B, [A,C | E]) :-
    \+ functor(B, ',', _),
    B =.. [A,C,D],
    transform(E, D), !.
%B is a single term
unpack_body(B, BE) :-
    \+ functor(B, ',', _),
    B =.. BE.

%reverse of unpack_body
repack_body([X | B], RB) :-
    atomic(X),
    RB =.. [X | B], !.

repack_body([X | B], RB) :-
    compound(X),
    transform([X | B], RB).
univ_arguments(Term, List) :-
    nonvar(Term),
    Term =.. P,
    univ_arguments_(P,List).
univ_arguments(Term, List) :-
    var(Term),
    back_univ_arguments_(List, P),
    Term =.. P.


univ_arguments_([], []).
univ_arguments_([H | T], [H | R]) :-
    \+ compound(H),
    univ_arguments_(T, R), !.
univ_arguments_([H | T], [P | R]) :-
    compound(H),
    H =.. P,
    univ_arguments_(T, R), !.


%replace(Old, New, L1, L2): reimplements select/4
% doesn't fail if Old isn't in L1 and replaces only non-free variables from L1
replace(X, Y, L1, L2) :- replace_(X, Y, L1, L2), !.
replace_(_, _, [], []) :- !.
replace_(X, Y, [Z | List], [Y | List]) :- ground(Z), Z = X.
replace_(X, Y, [X0 | XList], [X0 | YList]) :-
    replace_(X, Y, XList, YList).
%replace(O, _, L1, L1) :- \+ member(O, L1).

%transform(List, Conjunctions) : trasform a conjunctions of terms in a list
transform([A| Tail], L):-
    L=..[',',A,T],
   % univ_arguments(A,U),
    transform(Tail, T), !.	
%transform([A,B], (A,B)):-
%    B=..[_].
transform([C], A):-
    A=..C.
%transform([], []).

%create_method(Head, Name, Instance, Args): creates the predicate
%H :- B, where B calls the appropriate method

%avoids the assert if true clause(Head ,Body)
create_method(H, Name, This, Args) :-
    nonvar(H), var(This),
    B = (getv(This, Name, [Args, X]),
	 call(X)),
    clause(H, B), !.
%predicate doesn't exists
create_method(H, Name, This, Args) :-
    nonvar(H), var(This),
    B = (getv(This, Name, [Args, X]),
	 call(X)),
    \+ clause(H, B),
    assert(H :- B), !.
%redefinition? needs test
create_method(H, Name, This, Args) :-
    nonvar(H), var(This),
    B = (getv(This, Name, [Args, X]),
	 call(X)),
    clause(H, X), X \= B,
    assert(H :- B).

 superclass(Class, Super), Super is a list of all superclasses of Class
superclass1(Class, []) :-
    is_class(Class),
    class(Class, [], _), !.
superclass1(Class, Result) :-
    is_class(Class),
    class(Class, Parents, _),
    superclasses_(Parents, Ss),
    append(Ss, Parents,  Ls),
    list_to_set(Ls, Result), !.
superclasses_([], []).
superclasses_([Class | Cs], Result) :-
    is_class(Class),
    class(Class, Parents, _),
    %Parents \= [],
    append(Parents, Cs, Css),
    append(Ss, Parents, Result),
    superclasses_(Css, Ss), !.
superclasses_([Class | Cs], Ss) :-
    is_class(Class),
    class(Class, [], _),
    superclasses_(Cs, Ss).
*/
