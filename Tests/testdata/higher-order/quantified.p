thf(i_type,type,i:$tType).
thf(a_type,type,a:i).
thf(p_type,type,p:(i>i)>$o).
thf(ex,axiom,((? [F:(i>i)]:(p @ F)) = $true)).
thf(neg,axiom,! [F:(i>i)]:~(p @ F)).
