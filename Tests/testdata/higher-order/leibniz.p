thf(i_type,type,i:$tType).
thf(a_type,type,a:i).
thf(b_type,type,b:i).
thf(all,axiom,![P:i>$o]:((P @ a) | ~(P @ b))).
thf(neg,axiom,a != b).
