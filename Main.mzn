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

array [DEPS] of var IN_SIZE: out_prog_idx;

constraint forall( x in DEPS ) % makes sure communmications inserted after dependency definition
    ( out_prog_idx[ x ] > dep_def_at[ x ]);

constraint forall( x in index_set_1of2(dep_used_at) ) % makes sure communications are inserted before every use of that dependency
  ( if (dep_used_at[x,2] in IN_SIZE)
    then out_prog_idx[dep_used_at[x,1]] <= dep_used_at[x,2] % used in statement
    else out_prog_idx[dep_used_at[x,1]] < out_prog_idx[dep_used_at[x,2]] % used in dependency (nested dependency)
   endif );

var int: num_coms = sum( idx in DEPS )  % count the number of coms. if two (or more) dependencies with the same 
  (if( idx = DEPS[1] )                            % recipient are next to each other they are counted as one communication
    then 1
    else forall( other in DEPS[1]..idx-1 )
        ( (out_prog_idx[idx] != out_prog_idx[other])  \/
          (dep_to[idx] != dep_to[other]) )
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
[ "[ \(out_prog_idx[DEPS[1]])" ] ++ 
[ ", \(out_prog_idx[i])" | i in DEPS where i > DEPS[1] ] ++ 
[ " ]\n" ] ++
[ concat(["- : \(dependencies[j]) -> \(dep_to[j])\n" | j in DEPS where fix(out_prog_idx[j]) = i ]) 
  ++ "\(i) : \(statements[i])\n" | i in IN_SIZE ] ++
[ "Communications: \(num_coms)\n" ];


























