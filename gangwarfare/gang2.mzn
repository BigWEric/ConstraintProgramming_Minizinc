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
var int :obj1;
var int :obj2;
var int :obj3;
%var bool:c=against(Iorder[1],1);
%%%predicate against(var int:t,int:i)=against1(t,i)\/against2(t,i);
%predicate Nagainst(var int:t)=NotAgainst1(t)/\NotAgainst2(t);

%predicate inGang(var pos: t,int: j)=(t<=sum(k in 1..j)(m[k])/\t>sum(k in 1..j-1)(m[k]));
predicate NotAgainst1(var int:t,int:j)=forall(i in 1..n)((GangNum[t]==i)->forall(k in 1..r)((g1[k]==i)->( sum(c in 1..j)(bool2int(GangNum[order[c]]==g2[k]))!=m[g2[k]])));
predicate NotAgainst2(var int:t,int:j)=forall(i in 1..n)((GangNum[t]==i)->forall(k in 1..r)((g2[k]==i)->( sum(c in 1..j)(bool2int(GangNum[order[c]]==g1[k]))!=m[g1[k]])));
predicate NotAgainst(var int:t,int:j)=NotAgainst1(t,j)/\NotAgainst2(t,j);


%predicate OutOfGang(var int :t,int:GN)=

constraint alldifferent(Iorder);
constraint alldifferent(order);
%constraint alldifferent(Iorder);
constraint forall(i in 1..total-1)(GangNum[order[i]]!=GangNum[order[i+1]] );
constraint forall(i in 1..total-1,j in 1..r)((GangNum[order[i]]==g2[j])->(GangNum[order[i+1]]!=g1[j]));
constraint forall(i in 1..total-1,j in 1..r)((GangNum[order[i]]==g1[j])->(GangNum[order[i+1]]!=g2[j]));
%constraint forall(i in 1..total-1)((GangNum[i]==GangNum[i+1]->Iorder[i]==Iorder[i+1]+2)\/(GangNum[i]==GangNum[i+1]->Iorder[i]==Iorder[i+1]-2));
constraint forall(i in 1..n)(((GangNum[i]==GangNum[i+1])/\(i!=Leader[GangNum[i]])/\(i+1!=Leader[GangNum[i+1]])) -> Iorder[i]<Iorder[i+1] );

%constraint forall(i in 1..total-1,j in 1..r)(GangNum[order[i]]==g1[j]->GangNum[order[i+1]]!=g2[j]);
%constraint forall(i in 1..total,j in 1..total)(Iorder[i]==Iorder[j]+1->GangNum[i]!=GangNum[j]);

%constraint forall(i in 1..total,j in 1..total)(Iorder[i]==Iorder[j]-1->GangNum[i]!=GangNum[j]);
%constraint forall(i in 1..total,k in 1..total,j in 1..r)(Iorder[i]==Iorder[k]+1->if g1[j]==GangNum[i] then g2[j]!=GangNum[k] else true endif);
%constraint forall(i in 1..total,k in 1..total,j in 1..r)(Iorder[i]==Iorder[k]-1->if g1[j]==GangNum[i] then g2[j]!=GangNum[k] else true endif);
%constraint forall(i in 1..total,k in 1..total,j in 1..r)(Iorder[i]==Iorder[k]+1->if g2[j]==GangNum[i] then g1[j]!=GangNum[k] else true endif);
%constraint forall(i in 1..total,k in 1..total,j in 1..r)(Iorder[i]==Iorder[k]-1->if g2[j]==GangNum[i] then g1[j]!=GangNum[k] else true endif);

constraint inverse(Iorder,order);


constraint obj1=sum(i in 1..total)(bool2int(i!=Leader[GangNum[i]]/\Iorder[i]<Iorder[Leader[GangNum[i]]]));
constraint obj2=sum(i in 1..total,k in 1..n)((bool2int(order[i]==Leader[k]/\not NotAgainst(order[i],i)))*(3+2*sum(u in i+1..total)(bool2int(GangNum[order[i]]==GangNum[order[u]]))));
constraint obj3=sum(i in 1..total,j in 1..n)(bool2int(order[i]==Leader[j]/\NotAgainst(order[i],i)/\i <total div 2)*3);
%solve satisfy;
%var int :obj =obj1+obj2+obj3;
solve :: int_search(order, input_order, indomain_max, complete) maximize obj1+obj2+obj3;

 
output ["order = "++show(order)++";"++"\n"++"obj = "++show(obj1+obj2+obj3)++";"];