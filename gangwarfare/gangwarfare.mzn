include "alldifferent.mzn";
include "inverse.mzn";
int :n;
array[1..n] of int: m;
int :r;
array[1..r] of int: g1;
array[1..r] of int: g2;
int:total=sum(m);
array[1..total] of int:GangNum=[sum(j in 1..n)(bool2int(i>sum(k in 1..j)(m[k])))+1|i in 1..total ];
array[1..n] of int:Leader=[sum(i in 1..j)(m[i])+1| j in 0..n-1 ];
set of int : pos = 1..total;
array [1..total] of var pos : Iorder;
array [1..total] of var pos : order;

%var bool:c=against(Iorder[1],1);
%%%predicate against(var int:t,int:i)=against1(t,i)\/against2(t,i);
%predicate Nagainst(var int:t)=NotAgainst1(t)/\NotAgainst2(t);

%predicate inGang(var pos: t,int: j)=(t<=sum(k in 1..j)(m[k])/\t>sum(k in 1..j-1)(m[k]));
%predicate NotAgainst1(var int:t,int:j)=forall(i in 1..n)((GangNum[t]==i)->forall(k in 1..r)((g1[k]==i)->( sum(c in 1..j)(bool2int(GangNum[order[c]]==g2[k]))!=m[g2[k]])));
%predicate NotAgainst2(var int:t,int:j)=forall(i in 1..n)((GangNum[t]==i)->forall(k in 1..r)((g2[k]==i)->( sum(c in 1..j)(bool2int(GangNum[order[c]]==g1[k]))!=m[g1[k]])));
%predicate NotAgainst(var int:t,int:j)=NotAgainst1(t,j)/\NotAgainst2(t,j);




constraint alldifferent(Iorder);
constraint alldifferent(order);
%constraint alldifferent(Iorder);
constraint forall(i in 1..total-1)(GangNum[order[i]]!=GangNum[order[i+1]] );
constraint forall(i in 1..total-1,j in 1..r)((GangNum[order[i]]==g2[j])->(GangNum[order[i+1]]!=g1[j]));
constraint forall(i in 1..total-1,j in 1..r)((GangNum[order[i]]==g1[j])->(GangNum[order[i+1]]!=g2[j]));
%constraint forall(i in 1..total-1)((GangNum[i]==GangNum[i+1]->Iorder[i]==Iorder[i+1]+2)\/(GangNum[i]==GangNum[i+1]->Iorder[i]==Iorder[i+1]-2));
%constraint forall(i in 1..total-1)(if (GangNum[i]==GangNum[i+1])/\(i!=Leader[GangNum[i]]) then Iorder[i]<Iorder[i+1] else true endif);
%constraint forall(j in 1..n)((sum(i in 1..total)(bool2int((GangNum[order[i]]==GangNum[order[i+2]])/\GangNum[order[i]]==j)))==m[j]-1);

constraint forall(i in 1..n)(forall(j in 1..m[i]-2)(Iorder[Leader[i]+j]+2==Iorder[Leader[i]+j+1]));
constraint forall(i in 1..n)(forall(j in 1..r)(i != g1[j] /\ i !=g2[j] ) -> Iorder[Leader[i]] < total div 2);
%constraint order[1]==1;
%constraint order[total]==total;
%constraint forall(i in 1..total-1,j in 1..r)(GangNum[order[i]]==g1[j]->GangNum[order[i+1]]!=g2[j]);
%constraint forall(i in 1..total,j in 1..total)(Iorder[i]==Iorder[j]+1->GangNum[i]!=GangNum[j]);

%constraint forall(i in 1..total,j in 1..total)(Iorder[i]==Iorder[j]-1->GangNum[i]!=GangNum[j]);
%constraint forall(i in 1..total,k in 1..total,j in 1..r)(Iorder[i]==Iorder[k]+1->if g1[j]==GangNum[i] then g2[j]!=GangNum[k] else true endif);
%constraint forall(i in 1..total,k in 1..total,j in 1..r)(Iorder[i]==Iorder[k]-1->if g1[j]==GangNum[i] then g2[j]!=GangNum[k] else true endif);
%constraint forall(i in 1..total,k in 1..total,j in 1..r)(Iorder[i]==Iorder[k]+1->if g2[j]==GangNum[i] then g1[j]!=GangNum[k] else true endif);
%constraint forall(i in 1..total,k in 1..total,j in 1..r)(Iorder[i]==Iorder[k]-1->if g2[j]==GangNum[i] then g1[j]!=GangNum[k] else true endif);
%constraint forall(i in 1..total-1)((GangNum[i]==GangNum[i+1])->(abs(Iorder[i]-Iorder[i+1])==2));
%constraint forall(i in 1..n)((order[Leader[i]]<(total div 2))->(Iorder[Leader[i]]>Iorder[Leader[i]+m[i]-1]));
constraint inverse(Iorder,order);
solve :: int_search(order, input_order, indomain_max, complete) maximize obj;

var int:obj=obj1+obj2+obj3;

var int: obj1=sum(i in 1..total)(bool2int(i!=Leader[GangNum[i]]/\Iorder[i]<Iorder[Leader[GangNum[i]]]));

var int: obj2=sum(i in 1..n )(3*bool2int((sum(a in 1..r)(bool2int((i==g1[a]/\(sum(b in 0..m[g2[a]]-1)(bool2int(Iorder[Leader[i]]<=Iorder[Leader[g2[a]]+b]))==0))\/(i==g2[a]/\(sum(b in 0..m[g1[a]]-1)(bool2int(Iorder[Leader[i]]<=Iorder[Leader[g1[a]]+b]))==0))))>0)\/(Iorder[Leader[i]]<(total div 2))));
var int: obj3=sum(i in 1..n)((2*sum(p in 1..m[i]-1)(bool2int(Iorder[Leader[i]]<Iorder[Leader[i]+p])))*bool2int(sum(a in 1..r)(bool2int((i==g1[a]/\(sum(b in 0..m[g2[a]]-1)(bool2int(Iorder[Leader[i]]<=Iorder[Leader[g2[a]]+b]))==0))\/(i==g2[a]/\(sum(b in 0..m[g1[a]]-1)(bool2int(Iorder[Leader[i]]<=Iorder[Leader[g1[a]]+b]))==0))))>0));

output ["order = "++show(order)++";"++"\n"++"obj = "++show(obj)++";"];