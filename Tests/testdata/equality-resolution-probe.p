tff(type_s, type, s: $tType).
tff(type_a, type, a: s).
tff(type_p, type, p: s > $o).
tff(er_parent, axiom, ! [X : s] : (X != a | p(X))).
tff(not_p_a, axiom, ~p(a)).
