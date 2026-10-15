thf(i_type,type,i:$tType).
thf(a_type,type,a:i).
thf(p_type,type,p:i>(i>i)>$o).
thf(side_type,type,side:i>$o).
thf(ex,axiom,![X:i]:(side @ X | ((?[F:(i>i)]:(p @ X @ F)) = $true))).
thf(neg,axiom,![X:i,F:(i>i)]:~(p @ X @ F)).
thf(neg_side,axiom,![X:i]:~(side @ X)).
