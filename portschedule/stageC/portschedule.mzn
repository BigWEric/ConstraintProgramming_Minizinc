int: nr; % number of reclaimers
         % number of rails = nr for stages A,B,C,D,E
         % number of rails = (nr + 1) div 2 for stage F
set of int: RECLAIMER = 1..nr;
bool: stageF; % is this stage F data

int: ns; % number of stockpiles
set of int: STOCKPILE = 1..ns;
array[STOCKPILE] of int: size; % size in 10000 tonnes
array[STOCKPILE] of SHIP: ship; % which ship carries stockpile

constraint forall(sh in SHIP)
                 (assert(exists(s in STOCKPILE)(ship[s] = sh),
                 "Ship " ++ show(sh) ++ " has no cargo!"));
 
int: maxtime; % time considered
set of int: TIME = 0..maxtime;

int: nsh; % number of ships
set of int: SHIP = 1..nsh;
array[SHIP] of TIME: arrival; % when ship arrives in port

int: len; % length of pad
set of int: POSITION = 0..len;

int: stack_time;
int: reclaim_time;
int: reclaim_speed;

array[STOCKPILE] of var POSITION: westend;
array[STOCKPILE] of var TIME: stack;
array[STOCKPILE] of var TIME: reclaim;
array[STOCKPILE] of var RECLAIMER: which;
array[STOCKPILE] of var POSITION : eastend = [westend[i]+size[i]| i in STOCKPILE];
array[STOCKPILE] of var TIME: finished = [reclaim[i]+reclaim_time*size[i] | i in STOCKPILE];
array[STOCKPILE] of var TIME: endstack = [stack[i]+stack_time*size[i]|i in STOCKPILE];
predicate nonoverlap_time(var int:s1,var int:d1,var int:s2,var int:d2)=(s1+d1<=s2\/s2+d2<=s1);
predicate nonoverlap(var int:s1,var int:d1,var int:s2, var int:d2,var int:p1,var int :size1,var int:p2, var int:size2)= 
 (s1 + d1 <= s2 \/ s2 + d2 <= s1\/ p1+size1<=p2\/p2+size2<=p1); 
%constraint forall(i in STOCKPILE)(which[i]=1);
constraint forall(t1,t2 in STOCKPILE where t1<t2)
((which[t1]=which[t2]/\nonoverlap_time(reclaim[t1],finished[t1]-reclaim[t1],reclaim[t2],finished[t2]-reclaim[t2]))
\/which[t1]!=which[t2]);
constraint forall(i in STOCKPILE)(stack[i]+size[i]*stack_time <=reclaim[i]);

constraint forall(t1,t2 in STOCKPILE where t1<t2)(nonoverlap(stack[t1],(reclaim[t1]+reclaim_time*size[t1]-stack[t1]),stack[t2],(reclaim[t2]+reclaim_time*size[t2]-stack[t2]),westend[t1],size[t1],westend[t2],size[t2]));

constraint forall(i in STOCKPILE)(arrival[ship[i]] <= reclaim[i]);
constraint forall(t1,t2 in STOCKPILE where t1<t2)((ship[t1]=ship[t2]/\nonoverlap_time(reclaim[t1],finished[t1]-reclaim[t1],reclaim[t2],finished[t2]-reclaim[t2]))
\/ship[t1]!=ship[t2]);
%forall(i in STOCKPILE)()
%forall(t1,t2 in STOCKPILE where t1<t2)(which[t1]=which[t2]/\)

var int: obj = 0;

%solve satisfy;
solve :: int_search(westend, input_order, indomain_random, complete)
         satisfy;
output 
["westend  = ", show(westend), ";\n"] ++
["eastend  = ", show(eastend), ";\n"] ++
["stack    = ", show(stack), ";\n"] ++
["endstack = ", show(endstack), ";\n"] ++
["reclaim  = ", show(reclaim), ";\n"] ++
["finish   = ", show(finished) , ";\n"] ++
["which    = ", show(which), ";\n"]++
["obj      = ", show(obj), ";\n"]
;
