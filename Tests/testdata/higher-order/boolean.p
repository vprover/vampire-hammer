thf(i_type,type,i:$tType).
thf(a_type,type,a:i).
thf(p_type,type,p:i>$o).
thf(q_type,type,q:i>$o).
thf(r_type,type,r:($o>$o)>$o).
thf(pos,axiom,r @ (^[B:$o]: (B & $true))).
thf(neg,axiom,~(r @ (^[B:$o]: B))).
