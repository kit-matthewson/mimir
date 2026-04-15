first([H|_], H).

last([X], X).
last([_|T], X) :- last(T, X).


append([], Ys, Ys).
append([X|Xs], Ys, [X|Zs]) :- append(Xs, Ys, Zs).

member(X, [X|_]).
member(X, [_|T]) :- member(X, T).
