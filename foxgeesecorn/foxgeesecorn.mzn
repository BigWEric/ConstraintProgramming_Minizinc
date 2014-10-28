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
array[1..3*t] of var Cap:kk=[if i mod 3=1 then fox[(i div 3) +1] else if i mod 3=2 then geese[(i div 3)+1] else corn[i div 3] endif endif | i in 1..3*t];
array[Trips,1..3] of var Cap:carry=array2d(Trips,1..3,kk);

array[Trips2,1..3] of var 0..max([f,g,c]):wGoods;
array[Trips2,1..3] of var 0..max([f,g,c]):sGoods;


%%%%%%%%%%%%%%%%%%%%%%%%%%% ADD constraints in here %%%%%%%%%%%%%

predicate EnoGoods(int:tripNum)=sum(i in 1..3)(bool2int((wGoods[tripNum,i]-carry[tripNum,i])=0))==3 /\ 
             forall(j in 1..3)(wGoods[tripNum+1,j]=0)\/sum(i in 1..3)(bool2int((wGoods[tripNum,i]-carry[tripNum,i])=0))!=3 ;

predicate EoneGoods(int :tripNum)=
          sum(i in 1..3)(bool2int((wGoods[tripNum,i]-carry[tripNum,i])=0))==2 /\
             forall(j in 1..3)(wGoods[tripNum+1,j]=wGoods[tripNum,j]-carry[tripNum,j])
          \/sum(i in 1..3)(bool2int((wGoods[tripNum,i]-carry[tripNum,i])=0))!=2;
predicate EnoGeese(int :tripNum)=
          sum(i in 1..3)(bool2int(wGoods[tripNum,i]-carry[tripNum,i]=0))==1/\(wGoods[tripNum,2]-carry[tripNum,2]=0) /\ 
              forall(j in [1,3])(wGoods[tripNum+1,j]=wGoods[tripNum,j]-carry[tripNum,j]-1)
              /\(wGoods[tripNum+1,2]=wGoods[tripNum,2]-carry[tripNum,2]) 
           \/(sum(i in 1..3)(bool2int(wGoods[tripNum,i]-carry[tripNum,i]=0))!=1\/(wGoods[tripNum,2]-carry[tripNum,2]!=0));
predicate EFoxAndGeese(int :tripNum)=
           (wGoods[tripNum,1]-carry[tripNum,1]!=0/\wGoods[tripNum,2]-carry[tripNum,2]!=0) /\ 
               (wGoods[tripNum,1]-carry[tripNum,1]> wGoods[tripNum,2]-carry[tripNum,2]) /\ 
                 (wGoods[tripNum+1,1]=wGoods[tripNum,1]-carry[tripNum,1]-1 /\ 
                 forall(i in [1,3])(wGoods[tripNum+1,i]=wGoods[tripNum,i]-carry[tripNum,i])) 
              \/(wGoods[tripNum,1]-carry[tripNum,1]<= wGoods[tripNum,2]-carry[tripNum,2])/\ wGoods[tripNum+1,2]=(wGoods[tripNum,2]-carry[tripNum,2]-(wGoods[tripNum,1]-carry[tripNum,1]))
                   /\forall(i in [1,3])(wGoods[tripNum+1,i]=wGoods[tripNum,i]-carry[tripNum,i])
              
           \/ (wGoods[tripNum,1]-carry[tripNum,1]=0\/wGoods[tripNum,2]-carry[tripNum,2]=0);
predicate EGeeseAndCorn(int :tripNum)=
              (wGoods[tripNum,1]-carry[tripNum,1]=0/\sum(i in 1..3)(bool2int((wGoods[tripNum,i]-carry[tripNum,i])=0))==1) /\
              wGoods[tripNum+1,1]=0/\
                 (wGoods[tripNum,2]-carry[tripNum,2])<=(wGoods[tripNum,3]-carry[tripNum,3]) /\
                 wGoods[tripNum+1,3]=wGoods[tripNum,3]-carry[tripNum,3]-(wGoods[tripNum,2]-carry[tripNum,2])/\
                 wGoods[tripNum+1,2]=wGoods[tripNum,2]-carry[tripNum,2]
               \/ (wGoods[tripNum,2]-carry[tripNum,2])>(wGoods[tripNum,3]-carry[tripNum,3]) /\
                 forall(i in 2..3)(wGoods[tripNum+1,i]=wGoods[tripNum,i]-carry[tripNum,i]-1)
                
              \/(wGoods[tripNum,1]-carry[tripNum,1]!=0\/sum(i in 1..3)(bool2int((wGoods[tripNum,i]-carry[tripNum,i])=0))!=1);


%%%%%%%%%%%%%%%%%%%%%%%%%To west
predicate WnoGoods(int:tripNum)=sum(i in 1..3)(bool2int((sGoods[tripNum,i]-carry[tripNum,i])=0))==3 /\ 
             forall(j in 1..3)(sGoods[tripNum+1,j]=0) \/ sum(i in 1..3)(bool2int((sGoods[tripNum,i]-carry[tripNum,i])=0))!=3;
predicate WoneGoods(int :tripNum)=
          sum(i in 1..3)(bool2int((sGoods[tripNum,i]-carry[tripNum,i])=0))==2 /\ 
             forall(j in 1..3)((sGoods[tripNum+1,j]=sGoods[tripNum,j]-carry[tripNum,j]))
          \/sum(i in 1..3)(bool2int((sGoods[tripNum,i]-carry[tripNum,i])=0))!=2;
predicate WnoGeese(int :tripNum)=
           (sum(i in 1..3)(bool2int(sGoods[tripNum,i]-carry[tripNum,i]=0))==1/\(sGoods[tripNum,2]-carry[tripNum,2]=0)) /\
              forall(j in [1,3])(sGoods[tripNum+1,j]=sGoods[tripNum,j]-carry[tripNum,j]-1)
              /\(sGoods[tripNum+1,2]=sGoods[tripNum,2]-carry[tripNum,2]) 
           \/(sum(i in 1..3)(bool2int(sGoods[tripNum,i]-carry[tripNum,i]=0))!=1\/(sGoods[tripNum,2]-carry[tripNum,2]!=0));
predicate WFoxAndGeese(int :tripNum)=
          sGoods[tripNum,1]-carry[tripNum,1]!=0/\sGoods[tripNum,2]-carry[tripNum,2]!=0 /\ 
              ((sGoods[tripNum,1]-carry[tripNum,1]> sGoods[tripNum,2]-carry[tripNum,2]) /\ 
                 (sGoods[tripNum+1,1]=sGoods[tripNum,1]-carry[tripNum,1]-1 /\ 
                 forall(i in [1,3])(sGoods[tripNum+1,i]=sGoods[tripNum,i]-carry[tripNum,i])) 
              \/ (sGoods[tripNum,1]-carry[tripNum,1]<= sGoods[tripNum,2]-carry[tripNum,2])/\sGoods[tripNum+1,2]=(sGoods[tripNum,2]-carry[tripNum,2]-(sGoods[tripNum,1]-carry[tripNum,1]))
                   /\forall(i in [1,3])(sGoods[tripNum+1,i]=sGoods[tripNum,i]-carry[tripNum,i]))
           \/(sGoods[tripNum,1]-carry[tripNum,1]=0\/sGoods[tripNum,2]-carry[tripNum,2]=0);
predicate WGeeseAndCorn(int :tripNum)=
              ( sGoods[tripNum,1]-carry[tripNum,1]=0/\sum(i in 1..3)(bool2int((sGoods[tripNum,i]-carry[tripNum,i])=0))==1)
              /\ sGoods[tripNum+1,1]=0 /\ 
                ( (sGoods[tripNum,2]-carry[tripNum,2]<=sGoods[tripNum,3]-carry[tripNum,3]) /\
                 (sGoods[tripNum+1,3]=(sGoods[tripNum,3]-carry[tripNum,3]-(sGoods[tripNum,2]-carry[tripNum,2]))
                 /\sGoods[tripNum+1,2]=(sGoods[tripNum,2]-carry[tripNum,2]))
                 \/(sGoods[tripNum,2]-carry[tripNum,2]>sGoods[tripNum,3]-carry[tripNum,3]) /\
                 forall(i in 2..3)(sGoods[tripNum+1,i]=sGoods[tripNum,i]-carry[tripNum,i]-1))
              \/ ( sGoods[tripNum,1]-carry[tripNum,1]!=0\/sum(i in 1..3)(bool2int((sGoods[tripNum,i]-carry[tripNum,i])=0))!=1);








%constraint forall(i in Trips)(carry[i,1]=fox[i]/\carry[i,2]=geese[i]/\carry[i,3]=corn[i]);
constraint forall(i in Trips where i <=trips)(fox[i]<=f/\geese[i]<=g/\corn[i]<=c);
%constraint forall(i in Trips)(geese[i]<=g);
%constraint forall(i in Trips)(corn[i]<=c);
constraint forall(i in Trips)((fox[i]+geese[i]+corn[i]<=k)/\wGoods[i,1]<=f/\wGoods[i,2]<=g/\wGoods[i,3]<=c/\sGoods[i,1]<=f
                              /\sGoods[i,2]<=g/\sGoods[i,3]<=c);
constraint forall(i in Trips2 where i>trips+1)(forall(j in 1..3)(sGoods[i,j]=0/\wGoods[i,j]=0));
%constraint forall(i in 2..t where i mod 2=0)(if fox[i]!=0 then fox[i]!=fox[i-1] else true endif);
%constraint forall(i in 2..t where i mod 2=0)(if geese[i]!=0 then geese[i]!=geese[i-1] else true endif);
%constraint forall(i in 2..t where i mod 2=0)(if corn[i]!=0 then corn[i]!=corn[i-1] else true endif);
%constraint forall(i in Trips where i <trips)((sum(j in 1..3)(bool2int(carry[i,j]=0))=3)->(sum(k in 1..3)(bool2int(carry[i+1,k]=0))!=3));
constraint wGoods[1,1]=f/\wGoods[1,2]=g/\wGoods[1,3]=c;
constraint sGoods[1,1]=0/\sGoods[1,2]=0/\sGoods[1,3]=0;
constraint forall(i in 1..t where i <=trips)((i mod 2 =1)
                               /\ (forall(j in 1..3)(sGoods[i+1,j]=sGoods[i,j]+carry[i,j])/\
                                    (EnoGoods(i)/\EoneGoods(i)/\EnoGeese(i)/\EFoxAndGeese(i)/\EGeeseAndCorn(i)))
                               \/ (i mod 2 !=1)/\(forall(j in 1..3)(wGoods[i+1,j]=wGoods[i,j]+carry[i,j])/\
                                    (WnoGoods(i)/\WoneGoods(i)/\WnoGeese(i)/\WFoxAndGeese(i)/\WGeeseAndCorn(i))));
constraint forall(j in Trips where j<=trips)(forall(i in 1..3)( (j mod 2 =0 /\ carry[j,i]<=sGoods[j,i]) \/ (j mod 2 !=0/\carry[j,i]<=wGoods[j,i] )));
%constraint pf*sGoods[trips+1,1]+pg*sGoods[trips+1,2]+pc*sGoods[trips+1,3]=obj;
constraint forall(i in Trips where i>trips)(fox[i]=0/\geese[i]=0/\corn[i]=0);
constraint trips mod 2 =1;

%constraint forall(i in Trips)(if i mod 2=0 then corn[i]=0 else corn[i]=1 endif);

%constraint fox[1]=1/\geese[3]=1;
%constraint not forall(j in 1..3)(carry[1,j]=0);
%constraint trips<=(t+1) div 2;

%%%%%%%%%%%%%%%%% you may want to modify the search strategy below
%solve satisfy;
solve :: int_search([trips], input_order, indomain_median, complete)
         maximize obj;
var int:obj=pf*sGoods[trips+1,1]+pg*sGoods[trips+1,2]+pc*sGoods[trips+1,3];
%max([pf*sGoods[i,1]+pg*sGoods[i,2]+pc*sGoods[i,3]| i in Trips2]);
%var int:obj=pf*sGoods[trips,1]+pg*sGoods[trips,2]+pc*sGoods[trips,3];
output ["fox = ", show(fox),
        ";\ngeese = ", show(geese),
	";\ncorn = ", show(corn),
	";\ntrips = ", show(trips), 
	";\nobj = ", show(obj), ";\n"];


       	
 
			       
