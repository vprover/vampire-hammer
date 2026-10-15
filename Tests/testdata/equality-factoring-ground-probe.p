% A small problem whose useful equality-factoring step is
%   a = b | a = c
%   ---------------- equality factoring
%   b != c | a = c
% Superposition is disabled when running this diagnostic so Vampire cannot
% replace the transitivity step with a direct rewrite.
tff(type_s, type, s: $tType).
tff(type_a, type, a: s).
tff(type_b, type, b: s).
tff(type_c, type, c: s).
tff(factor_parent, axiom, a = b | a = c).
tff(equal_sides, axiom, b = c).
tff(not_retained, axiom, a != c).
