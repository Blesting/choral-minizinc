include "../Main.mzn";

var int: num_coms = sum( idx in DEPS )  % count the number of coms. if two (or more) dependencies with the same 
  (if( idx = DEPS[1] )                            % recipient are next to each other they are counted as one communication
    then 1
    else forall( other in DEPS[1]..idx-1 )
        ( (out_prog_idx[idx] != out_prog_idx[other])  \/
          (dep_to[idx] != dep_to[other] \/ dep_from[idx] != dep_from[other])  )
   endif );

solve minimize num_coms ;
output 
[ "Output program: \n" ]++
[ "[ \(out_prog_idx[DEPS[1]])" ] ++ 
[ ", \(out_prog_idx[i])" | i in DEPS where i > DEPS[1] ] ++ 
[ " ]\n" ] ++
[ concat(["- : \(dependencies[j]) -> \(dep_to[j])\n" | j in DEPS where fix(out_prog_idx[j]) = i ]) 
  ++ "\(i) : \(statements[i])\n" | i in IN_SIZE ] ++
[ "Communications: \(num_coms)\n" ];