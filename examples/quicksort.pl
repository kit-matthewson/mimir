append([], Ys, Ys).
append([X|Xs], Ys, [X|Zs]) :- append(Xs, Ys, Zs).

partition(_, [], [], []).
partition(Pivot, [X|Xs], [X|Less], Greater) :-
    X < Pivot,
    partition(Pivot, Xs, Less, Greater).
partition(Pivot, [X|Xs], Less, [X|Greater]) :-
    X >= Pivot,
    partition(Pivot, Xs, Less, Greater).

quicksort([], []).
quicksort([H|T], Sorted) :-
    partition(H, T, Less, Greater),
    quicksort(Less, SortedLess),
    quicksort(Greater, SortedGreater),
    append(SortedLess, [H|SortedGreater], Sorted).
