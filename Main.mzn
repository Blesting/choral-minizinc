include "globals.mzn";

int: in_size;
set of int: IN_SIZE = 1..in_size;
int: num_deps;
int: out_size = num_deps + in_size;
set of int: DEPS = in_size+1..out_size;
set of int: OUT_SIZE = 1..out_size;

array [IN_SIZE] of string: statements; % a list of all the original statements
array [DEPS] of string: dependencies;  % a list of all the dependency expressions
enum roles; 
array [DEPS] of roles: dep_to; % a list of all the dependency recipient roles
array [DEPS] of int: dep_def_at; % a list of the statements in which the dependency expressions were originally defined
array [int, 1..2] of int: dep_used_at; % a list of all the uses of dependencies
array [OUT_SIZE] of string: full_in = statements ++ dependencies;

array [OUT_SIZE] of var OUT_SIZE: out_prog_idx;
constraint all_different(out_prog_idx);

constraint forall( x,y in OUT_SIZE where x < y ) % keeps the order of the original statements
    ( if( out_prog_idx[x] in IN_SIZE /\ out_prog_idx[y] in IN_SIZE )
        then out_prog_idx[x] < out_prog_idx[y]
        else true 
       endif );
       
function var int: getIndex(var int: inp, array[int] of var int: arr) = % retruns the index of inp in array arr
   sum(  [ if inp = arr[i] 
              then i
           else 0 endif  
          | i in index_set(arr) ]
   );


constraint forall( x in OUT_SIZE ) % makes sure communmications inserted after dependency definition
    ( if( out_prog_idx[x] in DEPS )
      then x > getIndex(dep_def_at[ out_prog_idx[x] ], out_prog_idx)
      else true
      endif );

constraint forall( x in index_set_1of2(dep_used_at) ) % makes sure communications are inserted before every use of that dependency
  (getIndex( dep_used_at[x,1], out_prog_idx ) < getIndex( dep_used_at[x,2], out_prog_idx ));

var int: num_coms = sum( idx in OUT_SIZE )  % count the number of coms. if two (or more) dependencies with the same 
  (if( idx = 1 )                            % recipient are next to each other they are counted as one communication
    then bool2int(out_prog_idx[idx] in DEPS)
    else bool2int((out_prog_idx[idx] in DEPS /\ 
          not (out_prog_idx[idx-1] in DEPS) \/ 
          dep_to[out_prog_idx[idx]] != dep_to[out_prog_idx[idx-1]]))
   endif );

solve minimize num_coms;
output 
/*
[ "Statements: \n" ] ++ 
[ "\(i) : \(full_in[i])\n" | i in IN_SIZE ] ++ 
[ "Dependencies: \n" ] ++ 
[ "\(i) : \(full_in[i]) at role \(dep_to[i])\n" | i in DEPS ] ++ 
*/
[ "Output program: \n" ]++
[ "\(i) : \(full_in[fix(i)])\n" | i in out_prog_idx ]++
[ "Communications: \(num_coms)\n" ];


























