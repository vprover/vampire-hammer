thf(i_type,type,i:$tType).
thf(f_type,type,f:i>i>i>i).
thf(g_type,type,g:i>i>i>i).
thf(side_type,type,side:i>$o).
thf(pointwise,axiom,![X:i,Y:i,T:i]:((f @ X @ Y @ T) = (g @ X @ Y @ T))).
thf(neg,axiom,![X:i,Y:i,Z:i]:((side @ Z) | ((f @ X @ Y) != (g @ X @ Y)))).
thf(neg_side,axiom,![Z:i]:~(side @ Z)).
