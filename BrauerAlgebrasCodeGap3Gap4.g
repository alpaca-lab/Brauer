#The following piece of code refers to the paper "The Representations of the Brauer-Chen Algebra" (arXiv:2404.16011) and the paper's author's thesis "Brauer algebras of complex reflection groups" (which can be found here: https://theses.hal.science/tel-04357165).











# The following function, implemented in GAP3, with input a complex reflection group W and a string docname, creates a text file with the necessary data from CHEVIE for the rest of the program. These are: W: the input complex reflection group, as a group of permutations, gens: a list of generators of W, R_dist: a list of the elements of W corresponding to the distinguished reflections, Fieldofdef: the field of definition of W, RootsofW: a list containing a root for each distin- guished reflection, in the order in which they appear in R_dist. The argument docname modifies part of the text file’s title.



obtaindata := function(W)
local R_d, gens, Fielddef, Ro, nR, K, racines, x, docname ;
R_d:= Reflections(W);
gens:= Generators(W);
Fielddef:=Field(Flat(W.roots));
Ro:=W.roots;
nR:=Length(R_d);
K:=List([1..Length(Ro)],x->Reflection(W,x));
racines:=List(R_d,x->Ro[Position(K,x)]);
docname:=Concatenation("BrCh_GAP4data_",String(W),".gap");
PrintTo(docname,"gens:=", gens, ";\n", "W:=Group(gens,());\n", "R_dist:=", R_d, ";\n", "Fieldofdef:=", Fielddef, ";\n", "RootsofW:=", racines, ";\n");
end;



GAP4 PART BELOW


#In this part we consider given the data provided by the function obtaindata, above.




#This function creates a list of all reflections of W. Concerning the way it does this, note that in the exceptional complex reflection groups, a reflection has order at most 5.

allreflections := function()
local x, i, L;
L:=R_dist;
for i in [2..4] do 
	L := Concatenation(L,List(R_dist,x->x^i));
od;
return Filtered(L,x->x<>());
end;




R:=Set(allreflections());;
Rw1:=Concatenation(R,[()]);





#The following function is a more general conjugation for a list of elements L by an element z.



Con := function(L,z)
return z*L*z^(-1);
end;

#From now on, a hyperplane will be represented as a position in the list R_dist, and a reflection (resp. distinguished reflection) as a position in R (resp. R_dist). The following function gives the conjugate of a collection of hyperplanes B by a reflection x.



Cjcol := function(B,x)
local y ;
return List(Con(R_dist{B},Rw1[x]),y->Position(R_dist,y));
end;



#The following function constructs a pre-version of table F, containing only the transversality relations between the reflecting hyperplanes of W.


tabtran := function(W)
local N, a, b, ra, rb, rr, vv, tabtran, nR, KK, r, x, Ro;
KK:=Fieldofdef;
nR:=Length(R_dist);
N:=RootsofW;
tabtran:=List([1..nR],x->[1..nR]);
for a in [1..nR] do
	for b in [1..nR] do
		if a=b then tabtran[a][b] := false; 
		elif R_dist[a]*R_dist[b]<>R_dist[b]*R_dist[a] then tabtran[a][b] := false;
		else
			ra := N[a];
			rb := N[b];
			rr := Difference(N,[ra,rb]);
			vv := VectorSpace([ra,rb],KK);
			if ForAny(rr,r-> r in vv) then 
				tabtran[a][b] := false;
			else
				tabtran[a][b] := true;
			fi;
		fi;
	od;
od;
return tabtran;
end;



pretab:=tabtran(W);;


#The following function constructs the table F.

tabwhole := function()
local T, x, i, n, K, j, m ;
n:=Length(R_dist);
m:=Length(R);
T:=List([1..n],x->[1..n]);
for i in [1..n] do
	for j in [1..n] do
		T[i][j]:=pretab[i][j];
		if T[i][j]=false then T[i][j]:=[]; fi;

	od;
od;
for i in [1..m] do
	K:=List(R_dist,x->Position(R_dist,Con(x,R[i])));
	for j in [1..n] do
		Add(T[j][K[j]],i);
	od;
od;
return T;
end;


F:= tabwhole();


#The following function checks whether a collection of hyperplanes B is transverse.

istrancol := function(B)
local x, y ;
return ForAll(B,x->(ForAll(B,y->(x=y or F[x][y]=true))));
end;


# The following function calculates the orbit of a transverse collection B.

orbitof := function(B)
local O, x, y ;
O:=Orbit(W,Set(R_dist{B}),OnSets);
O:= List(O,x->List(x,y->Position(R_dist,y)));
return Set(List(O,Set));
end;


#The following function returns a list of all transverse collections of cardinality r.

transversecolls := function(r)
local oldcolls,newcolls,g;
if r= 1 then return List([1..Length(R_dist)],y->[y]);
else
	oldcolls := transversecolls(r-1);
	newcolls := [];
	for g in oldcolls do
		newcolls := Set(Concatenation(newcolls,List(Filtered(Difference([1..Length(R_dist)],g),y->ForAll(g,z->pretab[z][y])),u->Set(Concatenation(g,[u]))))); 
	od;
	return newcolls;
fi;
end;



#The following function creates a list of all transverse collections.

transversetotal := function()
local n;
n := Length(gens);
return Concatenation(List([1..n],y->transversecolls(y)));
end;




#The following function creates a list containing a representative from each orbit of transverse collections.

orbites := function()
local tout,res,pr;
tout := List(transversetotal(),Set);
res := [];
while Length(tout)>0 do
	pr := List(orbitof(tout[1]),Set);
	Add(res,pr[1]);
	tout := Difference(tout,pr);
od;
return res;
end;


OrbReps := orbites();




#The following function creates a list with the images of a transverse collection B under all reflections.

smallorbit := function(B)
local x, N, n ;
n:=Length(R_dist);
N:=List([1..n],x->Cjcol(B,x));
return Set(List(N,Set));
end;






#This function returns the list R_B for a transverse collection B.
R_B := function(B)
local x, L, i ; 
L:=[];
for i in [1..4] do
	L:=Concatenation(L,List(R_dist{B},x->x^i));
od;
L:=Filtered(L,x->x<>());
L:=List(L,x->Position(Rw1,x));
return Set(L);
end;




# This function returns a vector of length n with 1 in position i and zeros everywhere else, (i.e., the vector u(i,n)).

basvec := function(n,i)
local res ;
res := List([1..n],y->0);
res[i] := 1;
return res;
end;





#Verification of the First Computational Result.

# This function returns the table F’(A,B) for transverse collections A,B.


Fspec := function(A,B)
local LA, LB, n, T, i, j, x, y ;
LA:=Difference(A,B);
LB:=Difference(B,A);
n:=Length(LA);
T:=List([1..n], x-> [1..n]);
	for i in [1..n] do
		for j in [1..n] do
			T[i][j]:=Filtered(F[LA[i]][LB[j]], y->Set(Cjcol(A,y))=Set(B));
		od;
	od;
return T;
end;




#This function, applied to a table Fspec(B,A) for transverse collections A,B (thelists of positions in R_dist representing A,B, to be precise), returns a list with the vectors representing the set πA(ΣB). 

relsoftable := function(T)
local N, n, L, i, j, k, v1, v2, x ;
N:=Length(Rw1);
L:=[];
n:=Length(T);
for i in [1..n] do
	for j in [1..n] do
		for k in [1..n] do
			v1:=Sum(List(T[i][k],x->basvec(N,x)));
			v2:=Sum(List(T[j][k],x->basvec(N,x)));
			Add(L,v1-v2);
		od;
	od;
od;
return L;
end;




#This function creates the list Rel_Bar.

Rel_Bar :=function(B)
local N, O, L, i ;
N:=Length(Rw1);
O:=smallorbit(B);
L:=[];
for i in O do
	L:=Concatenation(L,relsoftable(Fspec(B,i)));
od;
for i in R_B(B) do
	Add(L,basvec(N,i)-basvec(N,N));
od;
return Filtered(L,x->x<>0);
end;


#This function takes as input a list of vectors T of common length n and returns a list with all vectors v(i,n) − v(j,n) in the Q-linear span of T.

diffinspan := function(T)
local C, L, x, V, n ;
V:=VectorSpace(T,Rationals);
n:=Length(T[1]);
C:=Combinations([1..n],2);
C:=Filtered(C, x-> (basvec(n,x[1])-basvec(n,x[2])) in V);
L:=List(C,x->basvec(n,x[1])-basvec(n,x[2]) );
return [L,C];
end;


#This function creates the list D_B.
D_B := function(B)
return diffinspan(Rel_Bar(B))[1];
end;


#This function creates the list P_B.
P_B := function(B)
local C, x ;
C:=diffinspan(Rel_Bar(B))[2];
C:=Filtered(C,x-> ( not(x[1] in R_B(B)) and not(x[2] in R_B(B)) ) );
return C;
end;


# This function creates the subgroup KB for (a list representing) a transverse collection B.
K_B := function(B)
local M, C, x, l1, l2, l3, y ;
M:=Length(R);
C:=Combinations([1..M],2);
l1:= x -> (Set(Cjcol(B,x[1]))<>Set(B));
l2:= x -> Set(Cjcol(B,x[1]))=Set(Cjcol(B,x[2])); 
l3:= x -> ForAll(Difference(B, Cjcol(B,x[1])), y -> Set(Cjcol([y],x[1]))<>Set(Cjcol([y],x[2]))); C:=Filtered(C,x-> (l1(x) and l2(x) and l3(x) ) );
C:=List(C,x-> R[x[2]]^(-1)*R[x[1]]);
return Subgroup(W,Concatenation(C,R_dist{B}));
end;



# This function gives the subgroup generated by R_B(B) and RR[2]^(-1)*RR[1], for [i,j] in P_B

K_B_0 := function(B)
local L, x ;
L:=List(P_B(B), x-> R[x[2]]^(-1)*R[x[1]]);
L:=Concatenation(R_dist{B},L);
return Subgroup(W,L);
end;



#This function verifies the assumptions of the First Computational Result for a transverse collection B. If the argument is W, it verifies it for each representative of an orbit of transverse collections and returns the corresponding list.

FiCR :=function(B)
local L, N, x, s ;
N:=Length(Rw1);
s:=false;
if B<>W then 
	L:=Rel_Bar(B);
	if ForAny([1..N],x->basvec(N,x) in Rel_Bar(B)) then s:=true; fi;
	if Rank(D_B(B))=Rank(Rel_Bar(B)) and K_B(B)=K_B_0(B) then s:=true; fi;
fi;
if B=W then
	s:=List(OrbReps,x->FiCR(x));
fi;
return s;
end;





#Verification of the Second and Third Computational Results

#This function returns a list of the pairs [i,j] in P_B(B) with R[i],R[j] not conjugate, for a transverse collection B. If the argument is W, it returns a list containing the output of the function for every representative of an orbit of transverse collections.

condpairs := function(B)
local L, x ;
if B<>W then 
L:=Filtered(P_B(B),x->not(IsConjugate(W,R[x[1]],R[x[2]])));
fi;
if B=W then L:=List(OrbReps,x->condpairs(x)); fi;
return L;
end;



# This function verifies whether a transverse collection B is of conditional type. It is used to verify the Second Computational Result.

iscond := function(B) 
local s ;
if B<>W then s:=((Rank(D_B(B))=Rank(Rel_Bar(B)) and condpairs(B)<>[])); 
else s:=List(OrbReps, iscond);
fi;
return s;
end;


#This function returns a list of the orders of the elements R[j]−1,R[j], for [i,j] in P_B(B) with R[i],R[j] not conjugate, for a transverse collection B. If the argument is W, it returns a list containing the output of the function for every representative of an orbit of transverse collections.


condpairsorder := function(B)
local x, L ;
if B<>W then
	L:= List(condpairs(B),x->Order(W,R[x[2]]^(-1)*R[x[1]]));
fi;
if B=W then
	L:= List(OrbReps,x->condpairsorder(x));
fi;
return L;
end;


#This function returns a list with 2 entries, for a transverse collection B. If W ̸ = G25,G32 these entries are equal: 0 if B is non-admissible, or Stab(B)/KB otherwise. In the case of G25,G32 the entries display the same type of data but the second entry corresponds to proper fields of definition where µ6 = 1, in which case, collections of conditional type are admissible.



admissibility := function(B)
local L, N, x, s, v ;
if B<>W then
	L:=Rel_Bar(B);
	N:=Length(Rw1);
	s:=false;
	if ForAny([1..N],x->basvec(N,x) in L) then s:=[0,0];
	elif Rank(D_B(B))=Rank(L) then
		v:=Size(Stabilizer(W,Set(R_dist{B}),OnSets))
			/Size(K_B(B));
		if iscond(B) then s:=[0,v]; else s:=[v,v]; fi;
	fi;
else s:=List(OrbReps,x->admissibility(x));
fi;
return s;
end;
	


#Verification of the second part of the Third Computational Result


# This part concerns only the cases of groups G25,G32.
#This function creates the list DBstab for a transverse collection B and a root of unity m corresponding to the parameter µ.


DBstab := function(B,m)
local stabelems, N, orb1, orb2, L1, L2, L, posinstab, x, v, y ;
stabelems:=Elements(Stabilizer(W,Set(R_dist{B}),OnSets));
N:=Length(stabelems);
orb1:=List(R_dist,x->Position(R,x));
orb2:=Difference([1..Length(R)],orb1);
L1:=P_B(B);
L2:=condpairs(B);
L1:=Difference(L1,L2);
L:=[];
posinstab := x-> Position(stabelems, R[x[2]]^(-1)*R[x[1]]);
for x in L1 do 
	v:=basvec(N,posinstab(x));
	Add(L,v-basvec(N,1));
od;
for x in L2 do 
	v:=basvec(N,posinstab(x));
	if x[1] in orb1 and x[2] in orb2 then 
		Add(L,v-m*basvec(N,1));
	fi;
	if x[2] in orb1 and x[1] in orb2 then 
		Add(L,v-m^(-1)*basvec(N,1));
	fi;
od;
for x in R_B(B) do
	y:=[x,1];
	v:=basvec(N,posinstab(y));
	Add(L,v-basvec(N,1));
od;
return L;
end;



#This function, with inputs: a group S, a field k and list L of vectors representing elements of kS in the basis S, computes the dimension of theideal of kS generated by the elements represented by L.


dimofideal := function(S,L,k)
local elems, N, gens, lmgens, rmgens, n, l, i, j, x, z, V ;
elems:=Elements(S);
N:=Length(elems); 
gens:=Generators(S);
lmgens:=List(gens, g->  List([1..N], x-> basvec(N,Position(elems,g*elems[x])))   );
rmgens:=List(gens, g->  List([1..N], x-> basvec(N,Position(elems,elems[x]*g)))   );
n:=Length(gens);
i:=0;
V:=VectorSpace(L,k);
j:=Dimension(V);
while i<j do
l:=[]; 
i:=Dimension(V);
	for z in [1..n] do
	l:=Concatenation(l,L*lmgens[z]);
	od;
	for z in [1..n] do
	l:=Concatenation(l,L*rmgens[z]);
	od;
L:=Concatenation(L,l);
V:=VectorSpace(L,k);
j:=Dimension(V);
L:=V.basis.vectors;
od;
return j;
end;


#This function verifies the assumptions of the Third Computational Result for a transverse collection B. If the argument is W, it verifies it for all repre sentatives of an orbit of transverse collections and returns the corresponding list.




ThCR := function(B)
local S, n, k, x, s;
if B<>W then
	S:=Stabilizer(W,Set(R_dist{B}),OnSets);
	n:=Size(S);
	k:=Size(K_B(B));
	s:=false;
	if condpairs(B)=[] then s:=true ; 
	elif ( Set(condpairsorder(B))=[6] ) and ( ForAll([1..6], x-> 	dimofideal(S,DBstab(B,E(6)^x),CF(3))=n-n/k) ) then s:=true; 
	fi;
else s:=List(OrbReps,ThCR); 
fi;
return s;
end;






#Verification of the Fourth Computational Result





#This function creates the list Rel for a transverse collection B.

Rel := function(B)
local L, i, j, k, n, N, x, v1, v2 ;
n:=Length(R_dist);
N:=Length(Rw1);
L:=[];
for k in [1..n] do
	for i in B do 
		for j in B do
			if  (F[i][k]<>true and F[j][k]<>true) then
				v1:=Sum(List(F[i][k],x->basvec(N,x)));	
				v2:=Sum(List(F[j][k],x->basvec(N,x)));
				Add(L,v1-v2);
			fi;
		od;
	od;
od;
for i in R_B(B) do
	Add(L,basvec(N,i)-basvec(N,N));
od;
return Filtered(L,x->x<>0);
end;





#This function checks whether a hyperplane h is acceptable with respect to a transverse collection B.

isaccept := function(B,h)
local s, x, y, L, L1 ;
L1:= x->List(F[x][h], y->Set(Cjcol(B,y)));
s:=false;
L:=Filtered(B,x-> F[x][h]<>true);
if not(h in B) and L<>[] and ForAll(L,x->Length(Set(L1(x)))=1) then s:=true; fi;
return s;
end;




#This function returns a list with the acceptable pairs of hyperplanes with respect to a transverse collection B.


acceptpairs := function(B)
local C, O, x, y ; 
C:=Combinations([1..Length(R_dist)],2);
O:=smallorbit(B); 
C:=Filtered(C,x-> (isaccept(B,x[1]) and isaccept(B,x[2])) );
C:=Filtered(C,x-> ForAny(O,y-> (x[1] in y and x[2] in y)));
return C;
end;



#This function creates the list Rel_Tau for a transverse collection B.

Rel_Tau :=function(B)
local L,  C, x, y, z, y, v1, v2, N, z, l ;
N:=Length(Rw1);
L:=[];
C:=acceptpairs(B);
for x in C do
	l:=Filtered(B,y-> (F[y][x[1]]<>true and F[y][x[2]]<>true) );
	for z in l do	
		v1:=Sum(List(F[z][x[1]],y->basvec(N,y)));
		v2:=Sum(List(F[z][x[2]],y->basvec(N,y)));
		Add(L,v1-v2);
	od;
od;
return Filtered(L,x->x<>0);
end;
		











#This function verifies the bar condition for each element represented by a vector in Rel(B).


Bar_condition := function(B)
local L, x, y, z ;
L:=Rel(B);
L:=List(L,x->Filtered(List([1..Length(x)],y->(x[y]^2)*y),z->z<>0));
L:=List(L,x->Set(Concatenation(List(x,y->Cjcol(B,y)))));
return ForAll(L,x->istrancol(x));
end;




#This function checks whether a list of vectors a lies in the Z-span of a list of vectors p.


lindep := function(p,a)
local L, n, smithrec, S, Q, C, v, vQ, diagS, x, y, i, nn, intheimage ;
L:=[];
n:=Length(p[1]);
smithrec:=SmithNormalFormIntegerMatTransforms(p);
S:=smithrec.normal;
Q:=smithrec.coltrans;
diagS:=List(S,x->Filtered(x,y->y<>0));
diagS:=Filtered(diagS,x->x<>[]);
nn:=Length(diagS);
intheimage:=v->(ForAll([1..nn],x->(Mod(v[x],diagS[x][1])=0)) and ForAll([(nn+1)..n],x->v[x]=0));
return ForAll(a,x->intheimage(x*Q));
end;







#This function verifies the assumptions of the Fourth Computational Result for a transverse collection B. If the argument is W, it verifies the result for every representative of an orbit of transverse collections and returns the corresponding list.

FoCR:= function(B)
local s, x, N;
if B<>W then
	s:=false; 
	N:=Length(Rw1);
	if ForAny([1..N],x->basvec(N,x) in Rel(B)) or (Bar_condition(B) and lindep(Concatenation(Rel_Bar(B),Rel_Tau(B)),D_B(B))) then s:=true; fi;
else s:=List(OrbReps,x->FoCR(x));
fi;
return s;
end;



