% This is the premise from Vampire's EqualityFactoring unit test.  It is
% satisfiable; `--show_new on` is used to inspect generated factoring clauses.
tff(type_s, type, s: $tType).
tff(type_f, type, f: s > s).
tff(type_g, type, g: s > s).
tff(type_p, type, p: s > $o).
tff(type_a, type, a: s).
tff(factor_parent, axiom,
  ! [X : s, Y : s] :
    (f(f(X)) = X | f(Y) = Y | g(X) = X | p(Y))).
tff(equal_fixed_point, axiom, f(a) = a).
tff(not_nested_equality, axiom, f(a) != f(f(a))).
tff(not_g_fixed_point, axiom, g(a) != a).
tff(not_p_fa, axiom, ~p(f(a))).
