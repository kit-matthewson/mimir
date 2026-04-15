edge(a, b).
edge(b, c).
edge(c, d).

connected(X, Y) :- edge(X, Y).
connected(X, Y) :- edge(X, Z), connected(Z, Y).
