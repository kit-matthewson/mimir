first([H|_], H).

last([X], X).
last([_|T], X) :- last(T, X).

all_less(_, []).
all_less(X, [Y | Ys]) :-
    X < Y,
    all_less(X, Ys).

append([], Ys, Ys).
append([X|Xs], Ys, [X|Zs]) :- append(Xs, Ys, Zs).

member(X, [X|_]).
member(X, [_|T]) :- member(X, T).

reverse([], []).
reverse([H|T], R) :- reverse(T, RT), append(RT, [H], R).
