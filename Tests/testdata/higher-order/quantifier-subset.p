thf(i_type,type,i:$tType).
thf(p_type,type,p:i>i>i>$o).
thf(side_type,type,side:i>$o).
thf(ex,axiom,![X:i,Y:i,Z:i]:((side @ Z) | ((? [T:i]:(p @ X @ Y @ T)) = $true))).
thf(neg,axiom,![X:i,Y:i,T:i]:~(p @ X @ Y @ T)).
thf(neg_side,axiom,![Z:i]:~(side @ Z)).
