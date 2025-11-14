Read("jacon_arikikoike.g"); Read("jacon_crystal.g");



comp:=function(x,y)
return Length(x[2])<Length(y[2]);
end;






Indexcolumns:=function(P,positions)
local x, y, i, j, doms, N, M, kk, ll, l1, l2;
ll:=List(positions, x->P[x]);
N:=Length(ll);                                                                                 
M:=Length(ll[1]);                       
ll:=List([1..N],x->Filtered([1..M],y->ll[x][y]<>0));
l1:=List([1..N],x->0);
l2:=List([1..M],x->0);
doms:=[];
for i in [1..N] do
	kk:=Filtered(List([1..N],x->[x,ll[x]]),y->Length(y[2])<=i);
	kk:=List(kk,x->[x[1],Difference(Set(x[2]),Set(l1))]);
	kk:=Filtered(kk,x->Length(x[2])=1);
	for j in kk do
		l1[j[1]]:=j[2][1];
		l2[j[2][1]]:=j[1];
		doms:=Concatenation(doms,List(ll[j[1]],x->[j[2][1],x]));
	od;
od;
doms:=Filtered(Set(doms),x->x[1]<>x[2]);
return [l1,doms,l2];
end;














RegularizationsList:=function(parameters,e,l,n)
local N, M, i, j, k, x, y, z, L, kk, P, pos, K, ll, doms ;
L:=Matricedecompo(parameters,e,l,n);
kk:=Kleshchevgeneralise(l,[parameters[1],5*e+parameters[2]],e,n)[n+1][2];
P:=TransposedMat(L[4]);
N:=Length(P);
M:=Length(P[1]);
ll:=List([1..N],x->Set(Filtered([1..M],y->P[x][y]<>0)));
pos:=List(kk,x->Position(L[1],x));
K:=Indexcolumns(P,pos);
doms:=List([1..M],z->Set(List(Filtered(K[2],x->x[1]=z),y->y[2])));
for i in [1..M] do
	doms:=List(doms,x->Set(Concatenation(x,Concatenation(List(x,y->doms[y])))));
od;
for i in [1..N] do
	for j in ll[i] do
		ll[i]:=Difference(ll[i],doms[j]);
	od;
od;
return  [List([1..N], i -> [ L[1][i], List( ll[i], x->kk[ K[3][x] ] ) ]),pos];
end;










Indexcolspec:=function(parameters,e,l,n)
local N, M, i, j, k, x, y, z, L, kk, P, pos, K, ll, doms ;
L:=Matricedecompo(parameters,e,l,n);
kk:=Kleshchevgeneralise(l,[parameters[1],5*e+parameters[2]],e,n)[n+1][2];
P:=TransposedMat(L[4]);
N:=Length(P);
M:=Length(P[1]);
ll:=List([1..N],x->Set(Filtered([1..M],y->P[x][y]<>0)));
pos:=List(kk,x->Position(L[1],x));
K:=Indexcolumns(P,pos);
doms:=List([1..M],z->Set(List(Filtered(K[2],x->x[1]=z),y->y[2])));
for i in [1..M] do
	doms:=List(doms,x->Set(Concatenation(x,Concatenation(List(x,y->doms[y])))));
od;
return [K[1],doms,K[3]];
end;



Printbipartition:=function(b)
local i;
Print("(");
if b[1]<>[] then
for i in [1..Length(b[1])] do
	Print(b[1][i]);
	if i<Length(b[1]) then Print("."); fi;
od;
else Print(" "); fi;
Print(" , ");
if b[2]<>[] then 
for i in [1..Length(b[2])] do
	Print(b[2][i]);
	if i<Length(b[2]) then Print("."); fi;
od;
else Print(" "); fi;
Print(")");
end;


Showregularizations:=function(parameters,e,l,n)
local i, j, N, k, K;
k:=RegularizationsList(parameters,e,l,n);
K:=k[1];
N:=Length(K);
for i in [1..N] do 
	Printbipartition(K[i][1]);
	Print("    -->     ");
	for j in [1..Length(K[i][2])] do
		Printbipartition(K[i][2][j]);
		if j<Length(K[i][2]) then Print("  or  "); fi;
	od;
	if i in k[2] then Print("   kleshchev   "); fi;
	Print("\n");
od;
end;



Verifyindexcols:=function(parameters,e,l,n)
local N, M, i, j, k, x, y, z, L, kk, P, pos, K, ll, Q ;
L:=Matricedecompo(parameters,e,l,n);
kk:=Kleshchevgeneralise(l,[parameters[1],5*e+parameters[2]],e,n)[n+1][2];
P:=TransposedMat(L[4]);
N:=Length(P);
M:=Length(P[1]);
ll:=List([1..N],x->Set(Filtered([1..M],y->P[x][y]<>0)));
pos:=List(kk,x->Position(L[1],x));
K:=Indexcolumns(P,pos);
Q:=List(K[3],x->P[pos[x]]);
return [Q,IsLowerTriangularMat(Q)];
end;


Showregsorted:=function(parameters,e,l,n)
local i, j, N, k, l, K;
k:=RegularizationsList(parameters,e,l,n);
K:=k[1];
N:=Length(K);
l:=[1..N];
SortParallel(K,l);
for i in [1..N] do 
	Printbipartition(K[i][1]);
	Print("    -->     ");
	for j in [1..Length(K[i][2])] do
		Printbipartition(K[i][2][j]);
		if j<Length(K[i][2]) then Print("  or  "); fi;
	od;
	if l[i] in k[2] then Print("   kleshchev   "); fi;
	Print("\n");
od;
end;






Abacusdiplay:=function(b,range,charge)
local i, j, x, y, bb, abrep, 1to1stempty ;
if IsInt(charge) then
	1to1stempty:=charge-Length(b);
else 1to1stempty:=0;
fi;
bb:=List(Set(b),x->[x,Length(Filtered(b,y->y=x))]);
bb:=Concatenation([[0,1]],bb);
abrep:=[];
for i in [2..Length(bb)] do
	for j in [bb[i-1][1]+1..bb[i][1]] do
		Add(abrep,"-");
	od;
	for j in [1..bb[i][2]] do 
		Add(abrep,"O");
	od;
od;

Print("... ");
for i in [range[1]..1to1stempty] do
	Print("O"); 
od;
for i in [1to1stempty+1..Minimum(range[2],1to1stempty+Length(abrep))] do
	Print(abrep[i-1to1stempty]);
od;
for i in [Length(abrep)+1to1stempty+1..range[2]] do
	Print("-");
od;
Print(" ...");
end;







# The function below shows the regularization of a bipartition b on the abacus. The second
# parameter needs to always be RegularizationsList(parameters,e,l,n).

Showregonabacus:=function(b,charge,range,k)
local i, j, x, K;
K:=k[1];
i:=Position(List(K,x->x[1]),b);
	Printbipartition(K[i][1]);
	Print("    -->     ");
	for j in [1..Length(K[i][2])] do
		Printbipartition(K[i][2][j]);
		if j<Length(K[i][2]) then Print("  or  "); fi;
	od;
	if i in k[2] then Print("   kleshchev   "); fi;
	Print("\n\n");
Abacusdiplay(K[i][1][1],range,charge[1]); Print("\n"); Abacusdiplay(K[i][1][2],range,charge[2]); 


Print("\n reg|\n");
Print(" reg|\n");


Abacusdiplay(K[i][2][1][1],range,charge[1]); Print("\n"); Abacusdiplay(K[i][2][1][2],range,charge[2]); Print("\n");


end;



#the following might get too big 

Showregsortedonabacus:=function(parameters,e,l,n,range)
local i, j, N, k, l, K, charge;
charge:=parameters;
k:=RegularizationsList(parameters,e,l,n);
K:=k[1];
N:=Length(K);
l:=[1..N];
SortParallel(K,l);
for i in [1..N] do 
	Printbipartition(K[i][1]);
	Print("    -->     ");
	for j in [1..Length(K[i][2])] do
		Printbipartition(K[i][2][j]);
		if j<Length(K[i][2]) then Print("  or  "); fi;
	od;
	if l[i] in k[2] then Print("   kleshchev   "); fi;
Print("\n\n Abacus display: \n\n");
Abacusdiplay(K[i][1][1],range,charge[1]); Print("\n"); Abacusdiplay(K[i][1][2],range,charge[2]); 


Print("\n   \n");

Abacusdiplay(K[i][2][1][1],range,charge[1]); Print("\n"); Abacusdiplay(K[i][2][1][2],range,charge[2]); Print("\n\n\n\n");



od;
end;


