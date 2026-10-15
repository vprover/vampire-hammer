thf(i_type,type,i:$tType).
thf(a_type,type,a:i).
thf(b_type,type,b:i).
thf(p_type,type,p:i>$o).
thf(all,axiom,![F:i>i]: (p @ (F @ a))).
thf(neg,axiom,~(p @ b)).
