tff(type_s, type, s: $tType).
tff(type_f, type, f: s > s).
tff(type_p, type, p: s > $o).
tff(ef_parent, axiom,
  ! [X : s, Y : s] : (f(f(X)) = X | f(Y) = Y | p(Y))).
tff(neq_side, axiom, ! [X : s] : f(f(X)) != f(X)).
tff(eq_side, axiom, ! [X : s] : f(X) = X).
tff(not_p, axiom, ! [X : s] : ~p(X)).
