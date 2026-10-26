/*
This code computes the algebraic Brauer groups of the Fermat near miss U:x^4+y^4-n=w^2 and
its projectivization X:x^4+y^4-nz^4=w^2, in the case when n is a square.
We use the conic bundle structure and the fact that the splitting field of X is a Galois extension
with Galois group (Z/2Z)^3, acting on the lines of X.
This code is based on the code in Algebraic_Brauer_Group.m used in the paper by Dan Loughran and Vladimir Mitankin,
" Integral Hasse principle and strong approximation for Markoff surfaces", International Mathematics Research Notices, 2021.
*/

/* Returns true if the given set of lines is special in that sense
that it might consist of the degenerate fibers of a conic bundle. */
is_special := function(O, M)
 for i in O do
  sum := 0;
  for j in O do
   sum := sum + M[i,j];
  end for;
  if sum ne 0 then
   return false;
  end if;
 end for;
 return true;
end function;

/* Variation: returns false if some line of O
   already meets the other lines with total intersection >= 2. Off-diagonal entries
   of M are >= 0, so adding more lines can never repair this */
is_feasible := function(O, M)
 for i in O do
  sum := 0;
  for j in O do
   sum := sum + M[i,j];
  end for;
  if sum gt 0 then
   return false;
  end if;
 end for;
 return true;
end function;

/* Take all nonempty unions of special orbits. The result does not depend on
   the order of the orbits: every special union is reached through its prefixes, and
   each prefix is a subset of it, hence feasible. */
all_special_unions := function(orbs, M)
 partial := [ {Integers() | } ];
 for O in orbs do
  extended := [];
  for S in partial do
   T := S join O;
   if is_feasible(T, M) then
    Append(~extended, T);
   end if;
  end for;
  partial cat:= extended;
 end for;
 return [ S : S in partial | #S gt 0 and is_special(S, M) ];
end function;


/* Select only the Galois groups that we need acting, in our case is (Z/2)^3 */
galois_group8:= function(list)
    erg := [];
    for rec in list do
    gr := rec`subgroup;
    if IsElementaryAbelian(gr) and #gr eq 8 then
    Append(~erg, gr);
    end if;
    end for;
    return erg;
end function;

/* Creates W(E_7) together with its action on the 56 lines on a dP2 */
printf "W(E_7)\n";
R_e7 := RootDatum("E7");
Cox_e7 := CoxeterGroup(R_e7);
we7 := StandardActionGroup(Cox_e7); 
deg:= 56;

L := RootLattice(R_e7);

list_we7 := SubgroupClasses(we7);
printf "%o conjugacy classes of subgroups in total,\n", #list_we7;

subs2 := Subsets(Set(GSet(we7)), 2);
orb := Orbits(we7, GSet(we7, subs2));
//#orb; //this should have size 3
//#orb[1];
//28
//#orb[2];
//756
//#orb[3];
//756

/* We have to build the intersection matrix of the graph so that it has rank 8.
Since orb[2] and orb[3] have the same size, we build two matrices and chose
the one with the desired rank
*/
/* The intersection matrix of the graph*/
M_cand:=[];
for k:= 1 to 2 do
M_cand[k]:= ZeroMatrix(Integers(), 56,56);
	for i := 1 to 56 do
	 for j := 1 to 56 do
	  if i eq j then M_cand[k][i,j] := -1; end if;
	  if {i,j} in orb[1] then M_cand[k][i,j] := 2; end if;
	  if {i,j} in orb[k+1] then M_cand[k][i,j] := 1; end if;
	 end for;
	 end for;
	 if Rank(M_cand[k]) eq 8 then
	   M:=M_cand[k];
	 end if;
end for;
/*Rank(M);
8
*/
// sanity checks: M must be symmetric and invariant under W(E_7)
/*M eq Transpose(M);
for g in Generators(we7) do
    assert forall{ i : i in [1..56] | forall{ j : j in [1..56] | M[i^g, j^g] eq M[i,j] } };
end for;
*/

/* Runs through all conjugacy classes to select the Galois groups isomorphic to (Z/2)^3 */
list:= galois_group8(list_we7);

count:=0; //counting the number of special sets with at least 4 swapped lines
msquare:=0; //counting the number of cases where H1(Pic X) has dimension 2, which corresponds to the case when n is a square

for gr in list do
    
    Div := PermutationModule(gr, Integers());
    FDiv := VectorSpace(Div); // Forget the group action
    
    // Relations coming from intersection matrix
    PDiv := sub<FDiv | Kernel(M)>;
    
    //Construct Pic(X)
    PicX, classX := quo< FDiv | PDiv >;
    dimX := Dimension(PicX);   // should be 8
    assert dimX eq 8;
    
    //Construct the matrix representing the quotient map
    ClassMatrixX := Matrix([ classX(FDiv.i) : i in [1..56] ]); //56=DImension(Div)
    IdX := IdentityMatrix(Integers(), dimX);

    //Construct a section of the matrix
    ClassSectionX := Solution(ClassMatrixX, IdX);

    // Now we construct the G-module corresponding to Pic(X)
    BMod := GModule(gr, [ ClassSectionX * g * ClassMatrixX : g in ActionGenerators(Div) ] );

    // We can compute H1(Pic X)
    CB := CohomologyModule(gr, BMod);
    H1X := CohomologyGroup(CB, 1);
    
    if Dimension(H1X) ne 2 then
    	continue;
    end if;
    msquare := msquare + 1;    
    
    orbs := [ { Integers() ! x : x in O } : O in Orbits(gr) ];

    best := 0;
    best_S := {Integers() | };
    best_pairs := [];
    
    for S in all_special_unions(orbs, M) do
        // orbits of size 2 inside S whose two lines meet (a candidate singular fibre)
        pairs := [];
        for O in orbs do
            if O subset S and #O eq 2 then
                p := Sort(Setseq(O));
                if M[p[1], p[2]] eq 1 then
                    Append(~pairs, p);
                end if;
            end if;
        end for;

	    // group the pairs by the class of L+L' in Pic X and keep the largest group
        classes := [ classX(FDiv.(p[1]) + FDiv.(p[2])) : p in pairs ];
        c := 0;
        top_pairs := [];
        for x in Set(classes) do
            same := [ pairs[t] : t in [1..#pairs] | classes[t] eq x ];
            if #same gt c then
                c := #same;
            top_pairs := same;
            end if;
	    end for;
	
	    if c gt best then
            best := c;
            best_S := S;
            best_pairs := top_pairs;
        end if;
    end for;
    
    if best lt 4 then
        continue;
    end if;
    count := count + 1;
    
    print "H1(Pic X) =", H1X;
    print "This is a case where n is a square.";
        
    // To compute H1(PicU), we need to first build PicU
    // The affine surface U is given by X\D where D is an anticanonical divisor -KX
    // We build -KX using the relation that the sum of the 56 lines is linearly equivalent to -28K
    K:= Zero(FDiv);
    for i in [1..56] do
        K := K + FDiv.i;
    end for;
    
    //Project into PicX
    KX := classX(K); 
    //KX := KX div GCD(Eltseq(KX));
    KX := KX div 28;

    //Build PicU
    PicU, classU := quo< PicX | sub<PicX | KX> >; //Quotient by KX
    dimU := Dimension(PicU);
    assert dimU eq 7;
    
    // As above, we need to construct the G-module corresponding to Pic(U) in order to compute H1(Pic U)
    // Construct the matrix representing the quotient map
    ClassMatrixU := Matrix([ classU(PicX.i) : i in [1..dimX] ]);

    IdU :=IdentityMatrix(Integers(), dimU);

    // Construct a section of the matrix
    ClassSectionU := Solution(ClassMatrixU, IdU);

    // Now we construct the G-module corresponding to Pic(U)
    AMod := GModule(gr, [ ClassSectionU * g * ClassMatrixU : g in ActionGenerators(BMod) ] );
    
    // We can compute H1(Pic U)
    CA := CohomologyModule(gr, AMod);
    H1U := CohomologyGroup(CA, 1);

    print "H1(Pic U) =", H1U;

    print "H1(Pic X) = H1(Pic U):", Dimension(H1X) eq Dimension(H1U);
    print "-------------------------------------------------------";
end for;

print "Number of H1(Pic X) of dimension 2:", msquare;
print "of which have special sets with at least 4 swapped lines:", count;
