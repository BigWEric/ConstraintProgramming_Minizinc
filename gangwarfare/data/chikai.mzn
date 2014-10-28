include "alldifferent.mzn";
include "inverse.mzn";
int: n;
set of int: k =1..n;
array[k] of int: m;
int : r;
array[1..r]of int: g1;
array[1..r]of int: g2;
int : t= sum(m);
set of int: num=1..t;
array[num] of var num :order;%position
array[k] of var int:leader;
array[num] of var k: team;

array[num]of var num: member;%member

constraint inverse(member,order);






constraint forall(i in k)(leader[i]=(sum(a in 1..i-1)(m[a])+1));
constraint forall(i in 1..t-1, j in 1..n)(((order[i]>=leader[j])/\order[i]<(leader[j]+m[j]))->((order[i+1]<leader[j])\/(order[i+1]>=(leader[j]+m[j]))));

%constraint forall(i in 1..t-3, j in 1..r)(((order[i]>=leader[g1[j]])/\(order[i]<(leader[g1[j]]+m[g1[j]])))->((order[i]>=leader[g2[j]])/\(order[i]<(leader[g2[j]]+m[g2[j]]))));
%constraint forall(i in 1..t-3, j in 1..r)(((order[i]>=leader[g2[j]])/\(order[i]<(leader[g2[j]]+m[g2[j]])))->((order[i]>=leader[g1[j]])/\(order[i]<(leader[g1[j]]+m[g1[j]]))));


%constraint forall(i in 1..t-2, j in 1..r)(((order[i]>=leader[g1[j]])/\(order[i]<(leader[g1[j]]+m[g1[j]])))->(((order[i+1]<leader[g2[j]])\/(order[i+1]>=(leader[g2[j]]+m[g2[j]])))/\((order[i+2]<leader[g2[j]])\/(order[i+2]>=(leader[g2[j]]+m[g2[j]])))));
%constraint forall(i in 1..t-2, j in 1..r)(((order[i]>=leader[g2[j]])/\(order[i]<(leader[g2[j]]+m[g2[j]])))->(((order[i+1]<leader[g1[j]])\/(order[i+1]>=(leader[g1[j]]+m[g1[j]])))/\((order[i+2]<leader[g1[j]])\/(order[i+2]>=(leader[g1[j]]+m[g1[j]])))));


constraint forall(i in 1..t-1, j in 1..r)(((order[i]>=leader[g1[j]])/\(order[i]<(leader[g1[j]]+m[g1[j]])))->((order[i+1]<leader[g2[j]])\/(order[i+1]>=(leader[g2[j]]+m[g2[j]]))));
constraint forall(i in 1..t-1, j in 1..r)(((order[i]>=leader[g2[j]])/\(order[i]<(leader[g2[j]]+m[g2[j]])))->((order[i+1]<leader[g1[j]])\/(order[i+1]>=(leader[g1[j]]+m[g1[j]]))));

constraint forall(i in 1..t, j in k)(((i>=leader[j])/\(i<(leader[j]+m[j])))->team[i]=j);
%constraint forall(i in 1..n, j in 1..r)(if team[i]==g1[r] then member[i]-member)
%constraint (sum(i in 1..n)(bool2int(member[leader[i]]<(t div 2))))>=(n div 2);
%constraint forall(i in 1..(t div 2)-1)((order[i]!=leader[team[i]])->i<member[leader[team[i]]]);%

%constraint (sum(i in 1..n)(bool2int(member[leader[i]]>=(t-(t div 3))))>(n div 4))/\(sum(i in 1..n)(bool2int(member[leader[i]]<=(t-(t div 3))))<=(n div 3));
%constraint forall(j in 1..t, i in 1..r)(team[j]==g1[i])
%solve satisfy;

solve :: int_search (order, input_order, indomain_max, complete)maximize obj;

var int:obj=condition1+condition2;

var int: condition1=sum(i in 1..t)(bool2int((i>leader[team[i]])/\(i<leader[team[i]]+m[team[i]])/\member[i]<member[leader[team[i]]]));

var int: condition2=sum(i in 1..n )(3*bool2int((sum(a in 1..r)(bool2int((i==g1[a]/\(sum(b in 0..m[g2[a]]-1)(bool2int(member[leader[i]]<=member[leader[g2[a]]+b]))==0))\/(i==g2[a]/\(sum(b in 0..m[g1[a]]-1)(bool2int(member[leader[i]]<=member[leader[g1[a]]+b]))==0))))>0)\/(member[leader[i]]<(t div 2)))+(2*sum(p in 1..m[i]-1)(bool2int(member[leader[i]]<member[leader[i]+p])))*bool2int(sum(a in 1..r)(bool2int((i==g1[a]/\(sum(b in 0..m[g2[a]]-1)(bool2int(member[leader[i]]<=member[leader[g2[a]]+b]))==0))\/(i==g2[a]/\(sum(b in 0..m[g1[a]]-1)(bool2int(member[leader[i]]<=member[leader[g1[a]]+b]))==0))))>0));


%var int: condition3=3*(sum(i in 1..n)(bool2int(sum(a in 1..r)(bool2int(((i!=g1[a]/\i!=g2[a])\/(bool2int((i==g1[a]/\(sum(b in 0..m[g2[a]]-1)(bool2int(member[leader[i]]<=member[leader[g2[a]]+b]))>0))\/(i==g2[a]/\(sum(b in 0..m[g1[a]]-1)(bool2int(member[leader[i]]<=member[leader[g1[a]]+b]))>0)))>0))/\(member[leader[i]]<(t div 2))))>0)));

output["order = ",show(order),";\n","obj = ",show(obj),";\n"];
%output[show(order),"\n",show(member),"\n",show(obj),"\n"];



