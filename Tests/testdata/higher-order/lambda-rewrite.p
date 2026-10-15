thf(i_type,type,i:$tType).
thf(f_type,type,f:i>i).
thf(g_type,type,g:i>i).
thf(h_type,type,h:i>i).
thf(q_type,type,q:(i>i)>$o).
thf(eq,axiom,g=h).
thf(pos,axiom,q @ (^[X:i]: (f @ (g @ X)))).
thf(neg,axiom,~(q @ (^[X:i]: (f @ (h @ X))))).
