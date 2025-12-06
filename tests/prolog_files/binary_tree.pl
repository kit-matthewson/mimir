all_less(_, []).
all_less(X, [Y | Ys]) :-
    X < Y,
    all_less(X, Ys).

all_greater(_, []).
all_greater(X, [Y | Ys]) :-
    X > Y,
    all_greater(X, Ys).

is_bst(nil, _, _).
is_bst(node(Value, Left, Right), Min, Max) :-
    Value > Min,
    Value < Max,
    is_bst(Left, Min, Value),
    is_bst(Right, Value, Max).
