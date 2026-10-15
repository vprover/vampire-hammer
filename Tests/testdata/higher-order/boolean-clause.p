thf(p_type,type,p:($o>$o)>$o).
thf(q_type,type,q:($o>$o)>$o).
thf(a_type,type,a:$o).
thf(pos,axiom,a | (((p @ (^[B:$o]:B)) & (q @ (^[B:$o]:B))) = $true)).
thf(neg_a,axiom,~a).
thf(neg_p,axiom,~(p @ (^[B:$o]:B))).
