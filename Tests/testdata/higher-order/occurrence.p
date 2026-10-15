thf(i_type,type,i:$tType).
thf(g_type,type,g:i>i).
thf(h_type,type,h:i>i).
thf(q_type,type,q:(i>i)>(i>i)>$o).
thf(eq,axiom,g=h).
thf(pos,axiom,q @ (^[X:i]:(g @ X)) @ (^[X:i]:(g @ X))).
thf(neg,axiom,~(q @ (^[X:i]:(h @ X)) @ (^[X:i]:(h @ X)))).
