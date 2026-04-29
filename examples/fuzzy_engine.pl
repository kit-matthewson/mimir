trap(X, A, _, _, _, F) :-
  X < A,
  F = 0.
trap(X, A, B, _, _, F) :-
  X >= A,
  X <= B,
  F = (X - A) / (B - A).
trap(X, _, B, C, _, F) :-
  X > B,
  X < C,
  F = 1.
trap(X, _, _, C, D, F) :-
  X >= C,
  X <= D,
  F = (D - X) / (D - C).
trap(X, _, _, _, D, F) :-
  X > D,
  F = 0.

not(X, Y) :-
  Y = 1 - X.

cold(T, F) :-
  trap(T, -100, -100, 15, 17, F).
hot(T, F) :-
  trap(T, 17, 28, 100, 100, F).

heating(on, T) :~
  cold(T, F),
  F.
heating(off, T) :~
  cold(T, F),
  not(F, G),
  G.

cooling(on, T) :~
  hot(T, F),
  F.
cooling(off, T) :~
  hot(T, F),
  not(F, G),
  G.

output(H, C, T) :-
  heating(H, T),
  cooling(C, T).
