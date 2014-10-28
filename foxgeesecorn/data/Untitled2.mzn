int: f;
int: g;
int: c;
int: k;
set of int: Cap = 0..k;
int: t;
set of int: Trips = 1..t;
set of int: Trips2 = 1..t+1;
int: pf;
int: pg;
int: pc;

array[Trips] of var Cap: fox;
array[Trips] of var Cap: geese;
array[Trips] of var Cap: corn;

var 1..t: trips;
array[Trips,1..3] of var Cap:carry;

array[Trips2,1..3] of var 0..max([f,g,c]):wGoods;
%array[Trips2,1..3] of var 0..max([f,g,c]):sGoods;


%%%%%%%%%%%%%%%%%%%%%%%%%%% ADD constraints in here %%%%%%%%%%%%%

predicate EnoGoods(int:tripNum)=if sum(i in 1..3)(bool2int((wGoods[tripNum,i]-carry[tripNum,i])=0))==3 then 
             forall(j in 1..3)(wGoods[tripNum+2,j]=0+carry[tripNum+1,j]) else true endif;

predicate EoneGoods(int :tripNum)=
          if sum(i in 1..3)(bool2int((wGoods[tripNum,i]-carry[tripNum,i])=0))==2 then 
             forall(j in 1..3)(wGoods[tripNum+2,j]=wGoods[tripNum,j]-carry[tripNum,j]+carry[tripNum+1,j])
          else true endif;
predicate EnoGeese(int :tripNum)=
          if sum(i in 1..3)(bool2int(wGoods[tripNum,i]-carry[tripNum,i]=0))==1/\(wGoods[tripNum,2]-carry[tripNum,2]=0)then 
              forall(j in [1,3])(wGoods[tripNum+2,j]=wGoods[tripNum,j]-carry[tripNum,j]-1+carry[tripNum+1,j])
              /\(wGoods[tripNum+2,2]=wGoods[tripNum,2]-carry[tripNum,2]+carry[tripNum+1,2]) 
           else true endif;
predicate EFoxAndGeese(int :tripNum)=
          if wGoods[tripNum,1]-carry[tripNum,1]!=0/\wGoods[tripNum,2]-carry[tripNum,2]!=0 then 
              if wGoods[tripNum,1]-carry[tripNum,1]> wGoods[tripNum,2]-carry[tripNum,2] then 
                 (wGoods[tripNum+2,1]=wGoods[tripNum,1]-carry[tripNum,1]-1+carry[tripNum+1,1] /\ 
                 forall(i in [1,3])(wGoods[tripNum+2,i]=wGoods[tripNum,i]-carry[tripNum,i]+carry[tripNum+1,i])) 
              else wGoods[tripNum+2,2]=(wGoods[tripNum,2]-carry[tripNum,2]-(wGoods[tripNum,1]-carry[tripNum,1])+carry[tripNum+1,2])
                   /\forall(i in [1,3])(wGoods[tripNum+2,i]=wGoods[tripNum,i]-carry[tripNum,i]+carry[tripNum+1,i])
              endif
           else true endif;
predicate EGeeseAndCorn(int :tripNum)=
              if wGoods[tripNum,1]-carry[tripNum,1]=0/\sum(i in 1..3)(bool2int((wGoods[tripNum,i]-carry[tripNum,i])=0))==1 
              then wGoods[tripNum+2,1]=0+carry[tripNum+1,1]/\
                 if (wGoods[tripNum,2]-carry[tripNum,2])<=(wGoods[tripNum,3]-carry[tripNum,3]) then
                 wGoods[tripNum+2,3]=wGoods[tripNum,3]-carry[tripNum,3]-(wGoods[tripNum,2]-carry[tripNum,2])+carry[tripNum+1,3]/\
                 wGoods[tripNum+2,2]=wGoods[tripNum,2]-carry[tripNum,2]+carry[tripNum+1,2]
                else
                 forall(i in 2..3)(wGoods[tripNum+2,i]=wGoods[tripNum,i]-carry[tripNum,i]-1+carry[tripNum+1,i])
                endif
               else true endif;










constraint forall(i in Trips)(carry[i,1]=fox[i]/\carry[i,2]=geese[i]/\carry[i,3]=corn[i]);
constraint forall(i in Trips)(fox[i]<=f);
constraint forall(i in Trips)(geese[i]<=g);
constraint forall(i in Trips)(corn[i]<=c);
constraint forall(i in Trips)((fox[i]+geese[i]+corn[i]<=k)/\wGoods[i,1]<=f/\wGoods[i,2]<=g/\wGoods[i,3]<=c);
constraint forall(i in Trips2,j in 1..3)(i>trips+1->(wGoods[i,j]=0));


 
constraint wGoods[1,1]=f/\wGoods[1,2]=g/\wGoods[1,3]=c/\wGoods[2,1]=fox[1]/\wGoods[2,2]=geese[1]/\wGoods[2,3]=corn[1];

%constraint sGoods[1,1]=0/\sGoods[1,2]=0/\sGoods[1,3]=0;
constraint forall(i in 1..t-1)(EnoGoods(i)/\EoneGoods(i)/\EnoGeese(i)/\EFoxAndGeese(i)/\EGeeseAndCorn(i));
constraint forall(j in Trips,i in 1..3)( carry[j,i]<=wGoods[j,i]);
%constraint pf*wGoods[trips+1,1]+pg*wGoods[trips+1,2]+pc*wGoods[trips+1,3]=obj;
constraint forall(i in Trips where i>trips+1)(fox[i]=0/\geese[i]=0/\corn[i]=0);
constraint trips mod 2 =1;
constraint not forall(i in 1..3)(carry[1,i]=0);

%constraint trips=5;
%constraint forall(i in Trips)(if i mod 2=0 then corn[i]=0 else corn[i]=1 endif);

%constraint fox[1]=1/\geese[3]=1;
%constraint not forall(j in 1..3)(carry[1,j]=0);
%constraint trips<=(t+1) div 2;

%%%%%%%%%%%%%%%%% you may want to modify the search strategy below
%solve satisfy;
solve :: int_search([trips], first_fail, indomain_median, complete)
         maximize obj;
var int:obj=max([pf*wGoods[i,1]+pg*wGoods[i,2]+pc*wGoods[i,3]| i in Trips2 where i mod 2 =0]);
%var int:obj=pf*sGoods[trips,1]+pg*sGoods[trips,2]+pc*sGoods[trips,3];
output ["fox = ", show(fox),
        ";\ngeese = ", show(geese),
	";\ncorn = ", show(corn),
	";\ntrips = ", show(trips), 
	";\nobj = ", show(obj), ";\n",show(wGoods)];


       	
 
			       
