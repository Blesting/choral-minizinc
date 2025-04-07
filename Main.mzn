include "globals.mzn";

% --=== Parameters ===--
% Ranges:
int: in_size; % the number of input statements
set of int: IN_SIZE = 1..in_size;
int: num_deps; % the nubmer of dependencies
int: out_size = num_deps + in_size;
set of int: DEPS = in_size+1..out_size;
set of int: OUT_SIZE = 1..out_size;
enum roles;

% Lists
array[IN_SIZE] of string: statements; % a list of all the original statements
array[IN_SIZE] of roles: statements_roles; % a list of the roles of the originals statements
array[IN_SIZE] of int: statements_runtimes = [1 | i in IN_SIZE]; % a list of runtimes for each statement 
                                                                  % (default if 1 for every statement)
% array[IN_SIZE, 1..2] of 0..in_size: statements_blocks;
array[DEPS] of string: dependencies;  % a list of all the dependency expressions
array[DEPS] of roles: dep_to; % a list of all the dependency recipient roles
array[DEPS] of roles: dep_from; % a list of all the dependency sender roles
array[DEPS] of int: dep_def_at; % a list of the statements in which the dependency expressions were originally defined
array[int, 1..2] of int: dep_used_at; % a list of all the uses of dependencies
array[OUT_SIZE] of string: full_in = statements ++ dependencies;

% --=== Variables ===--
array[DEPS] of var IN_SIZE: out_prog_idx;

% --=== Constraints ===--
constraint forall( x in DEPS ) % makes sure communmications inserted after dependency definition
    ( out_prog_idx[ x ] > dep_def_at[ x ]);

constraint forall( x in index_set_1of2(dep_used_at) ) % makes sure communications are inserted before every use of that dependency
  ( if (dep_used_at[x,2] in IN_SIZE)
    then out_prog_idx[dep_used_at[x,1]] <= dep_used_at[x,2] % used in statement
    else out_prog_idx[dep_used_at[x,1]] < out_prog_idx[dep_used_at[x,2]] % used in dependency (nested dependency)
   endif );

























