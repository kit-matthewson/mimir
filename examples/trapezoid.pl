trap(X, A, _, _, _) :~
  X < A,
  0.
trap(X, A, B, _, _) :~
  X >= A,
  X <= B,
  (X - A) / (B - A).
trap(X, _, B, C, _) :~
  X > B,
  X < C,
  1.
trap(X, _, _, C, D) :~
  X >= C,
  X <= D,
  (D - X) / (D - C).
trap(X, _, _, _, D) :~
  X > D,
  0.
