include "../Main.mzn";

array[roles, 0..in_size] of var int: runtimes;

constraint forall( r in roles ) ( runtimes[r, 0] = 0 ); % first column is all zeros
constraint forall( r in roles, s in IN_SIZE ) (runtimes[r, s] >= runtimes[r, s-1]); % runtimes can never fall
constraint 
forall( role in roles )(
  forall( s in IN_SIZE )(
    forall( d in DEPS )(
       (runtimes[role, s] >= 
          if(out_prog_idx[d] == s /\ dep_to[d] == role) % the dependency is on this line and to this role
            then max( runtimes[dep_from[d], s-1]+1, runtimes[role, s-1] ) % simulates recipient waiting for sender
            else runtimes[role, s-1]
          endif +
         (if statements_roles[s] == role then statements_runtimes[s] else 0 endif) + % if this statement is executed by this role
         (sum( [ 1 | k in DEPS where % all the messages sent from this role at this statement
            dep_from[k] == role /\ 
            out_prog_idx[k] == s /\ 
            forall( k2 in DEPS[1]..k-1 where dep_from[k2] == role /\ out_prog_idx[k2] == s )
              ( dep_to[k] != dep_to[k2] ) ] )
         ) 
       )   
    ) 
  )
);
solve minimize max( [ runtimes[r, in_size] | r in roles ] );
output 
[ "Output program: \n" ]++
[ "[ \(out_prog_idx[DEPS[1]])" ] ++ 
[ ", \(out_prog_idx[i])" | i in DEPS where i > DEPS[1] ] ++ 
[ " ]\n" ] ++
[ concat(["- : \(dependencies[j]) -> \(dep_to[j])\n" | j in DEPS where fix(out_prog_idx[j]) = i ]) 
  ++ "\(i) : \(statements[i])\n" | i in IN_SIZE ] ++
[ "max runtime: \(max( [ runtimes[r, in_size] | r in roles ] ))\n" ] ++
[ concat( ["   "] ++ ["\(i), " | i in index_set_2of2(runtimes)] ++ ["\n"] ) ] ++
[ concat( ["\(i): "] ++ ["\(runtimes[i,j]), " | j in index_set_2of2(runtimes) ] ++ [ "\n" ] )  | i in index_set_1of2(runtimes)];
















