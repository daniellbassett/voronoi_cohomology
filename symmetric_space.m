//Voronoi Cohomology Library - Written by Daniel Bassett, 2025
//---------------------------------------------------------------------------symmetric_space.m---------------------------------------------------------------------------
/*
TODO: write description
*/

import "voronoi.m" : voronoi_data;

//Record of the data associated with a homogeneous cone, and methods needed for calculating Voronoi tessellations
homogeneous_cone_data := recformat<
	type,
	coefficients,
	matrix_field,
	matrix_size : Integers(),
	
	ambient_space,
	basepoint,
	
	boundary_point_database : SeqEnum
>;

homogeneous_cone_functions := recformat<
	innerProduct : UserProgram,
	norm : UserProgram,
	
	isInteriorPoint : UserProgram,
	stabiliser : UserProgram,
	minimalVectors : UserProgram,
	perfectionRank : UserProgram,
	
	boundaryPoints : UserProgram,
	equivalent : UserProgram,
	cellNormal : UserProgram,
	isOrientableCell : UserProgram,
	compatibleCellOrientation : UserProgram,
	compatibleInducedCellOrientation : UserProgram
>;

homogeneous_cone_point := recformat<
	point,
	minimal_vectors : SeqEnum,
	min : Rationals()
>;

homogeneous_cone := recformat<
	cone_data,
	cone_functions
>;

//--------------------------------------------------GENERIC FUNCTIONS--------------------------------------------------
function matrixGroupGenerators(G : optimised_representation := true)
	generators := [];
	
	H := MatrixGroup<NumberOfRows(G[1]), Rationals() | generators>;
	for g in G do
		if g notin H then
			Append(~generators, g);
			
			H := MatrixGroup<NumberOfRows(G[1]), Rationals() | generators>;
			if #H eq #G then
				break;
			end if;
		end if;
	end for;
	
	if optimised_representation then
		G_set := {g : g in G};
		for d in [1..#generators-1] do
			for S in Subsets(G_set, d) do
				H := MatrixGroup<NumberOfRows(G[1]), Rationals() | [g : g in S]>;
				if #H eq #G then
					return [s : s in S];
				end if;
			end for;
		end for;
		
		return generators;
	else
		return generators; //maybe replace with something to at least ensure the generating set is minimal by inclusion?
	end if;
end function;

function cellBasis(V, cone_data)
	basis := [];
	
	for v in V do
		if IsIndependent(basis cat [v]) then
			Append(~basis, v);
		end if;
	end for;
	
	return basis;
end function;

function facets(vertices)
	poly := Polytope([Eltseq(v) : v in vertices]);
	
	indices := FacetIndices(poly);
	facet_list := [];
	
	for facet in indices do
		Append(~facet_list, [vertices[i] : i in facet]);
	end for;
	
	return facet_list;
end function;

function barycentre(vertices)
	return (&+vertices)/#vertices;
end function;

//--------------------------------------------------REAL SYMMETRIC CONE--------------------------------------------------
//Generates a homogeneous cone record for the cone of real symmetric n x n matrices
function realCone(n)

end function;


//--------------------------------------------------BIANCHI HERMITIAN CONE--------------------------------------------------
function complex_innerProduct(M, N)
	if Parent(M[1,1]) eq Rationals() then
		return Trace(M*N) / 2;
	else
		return Trace(M*N);
	end if;
end function;

function complex_dagger(M, cone_data)
	K := cone_data`matrix_field;
	sigma := Automorphisms(K)[2];
	
	//print M, Type(M);
	for i in [1..NumberOfRows(M)] do
		for j in [1..NumberOfColumns(M)] do
			//print i,j;
			M[i,j] := sigma(M[i,j]);
		end for;
	end for;
	
	return Transpose(M);
end function;

function complex_norm(M)
	return Trace(M^2);
end function;

function complex_toHermitian(v, cone_data)
	K := cone_data`matrix_field;
	sigma := Automorphisms(K)[2];
	
	return Transpose(Transpose(Matrix(v)) * Matrix(VectorSpace(K, NumberOfColumns(v)) ! [sigma(v[i]) : i in [1..NumberOfColumns(v)]]));
end function;

function complex_evaluateBilinear(M, v, w, cone_data)
	return Rationals() ! (complex_innerProduct(M, complex_toHermitian(v+w, cone_data)) - complex_innerProduct(M, complex_toHermitian(v, cone_data)) - complex_innerProduct(M, complex_toHermitian(w, cone_data)))/2;
end function;

function complex_rationalToImaginary(M, cone_data)
	n := NumberOfRows(M) div 2;
	K := cone_data`matrix_field;
	
	theta := Basis(K)[2];
	
	mat := MatrixRing(K, n) ! 0;
	for i in [1..NumberOfRows(M) by 2] do
		for j in [1..NumberOfColumns(M) by 2] do
			mat[(i+1) div 2, (j+1) div 2] := M[i,j] + M[i,j+1] * theta;
		end for;
	end for;
	
	return mat;
end function;

function complex_latticeBasis(K, n)
	O<omega> := MaximalOrder(K);
	
	latticeBasis := [];
	for i in [1..n] do
		vector := VectorSpace(K, n) ! 0;
		
		vector[i] := 1;
		Append(~latticeBasis, vector);
		
		vector[i] := omega;
		Append(~latticeBasis, vector);		
	end for;
	
	return latticeBasis;
end function;

function complex_hermitianToGram(M, cone_data)
	K := cone_data`matrix_field;
	n := NumberOfRows(cone_data`basepoint) div 2;
	
	latticeBasis := complex_latticeBasis(K, n);
	
	gram := MatrixRing(Rationals(), 2*n) ! 0;
	
	for i in [1..2*n] do
		gram[i,i] := complex_innerProduct(M, complex_toHermitian(latticeBasis[i], cone_data));
		
		for j in [i+1..2*n] do
			gram[i,j] := complex_evaluateBilinear(M, latticeBasis[i], latticeBasis[j], cone_data);
			gram[j,i] := gram[i,j];
		end for;
	end for;
	
	return gram;
end function;

function complex_isInteriorPoint(M, cone_data)
	return IsPositiveDefinite(complex_hermitianToGram(complex_rationalToImaginary(M,cone_data), cone_data));
end function;

function complex_hermitianBasis(n, K, theta)
	basis := [];
	
	for i in [1..n] do
		Append(~basis, Matrix(K, n, n, [<i, i, 1>]));
		
		for j in [i+1..n] do
			Append(~basis, Matrix(K, n, n, [<i,j, 1>, <j, i, 1>]));
			Append(~basis, Matrix(K, n, n, [<i,j, theta>, <j, i, -theta>]));
		end for;
	end for;
	
	return basis;
end function;

function complex_clearDenoms(S)
	denoms := [];
	
	for s in S do
		for i in [1..NumberOfRows(s)] do
			for j in [1..NumberOfColumns(s)] do
				Append(~denoms, Denominator(s[i,j]));
			end for;
		end for;
	end for;
	
	scale_factor := LCM(denoms);
	return [s * scale_factor : s in S];
end function;

function complex_hermitianToTwistedGram(M, twist, cone_data)
	K := cone_data`matrix_field;
	n := NumberOfRows(cone_data`basepoint) div 2 ;
	
	latticeBasis := complex_latticeBasis(K, n);
	
	gram := MatrixRing(Rationals(), 2*n) ! 0;
	for i in [1..2*n] do
		for j in [1..2*n] do
			gram[i,j] := complex_evaluateBilinear(M, latticeBasis[i], twist * latticeBasis[j], cone_data);
		end for;
	end for;
	
	return gram;
end function;

function complex_imaginaryToRational(M)
	d := (Basis(Parent(M[1,1]))[2])^2;

	mat := [];
	for i in [1..NumberOfRows(M)] do
		row := [];
		for j in [1..NumberOfColumns(M)] do
			coords := Eltseq(M[i,j]);
			Append(~row, Matrix(Rationals(), 2, 2, [coords[1], coords[2], d*coords[2], coords[1]])); //d = theta^2
		end for;
		
		Append(~mat, HorizontalJoin(row));
	end for;
	
	return VerticalJoin(mat);
end function;

function complex_stabiliser(v_rec, cone_data : cone_voronoi_data := rec<voronoi_data | >)
	K := cone_data`matrix_field;
	n := NumberOfRows(cone_data`basepoint) div 2;
	O := MaximalOrder(K);
	omega := Basis(O)[2];

	v := complex_rationalToImaginary(v_rec`point,  cone_data);
		
	L := LatticeWithGram(complex_clearDenoms([complex_hermitianToGram(v, cone_data)])[1]);
	L_omega := ChangeRing(complex_clearDenoms([complex_hermitianToTwistedGram(v, omega, cone_data)])[1], Integers());
	
	G := AutomorphismGroup(L, [L_omega]); //consists of rational 2n x 2n matrices; need to convert to imaginary matrices
	gens := Generators(G);
	
	return [complex_dagger(complex_rationalToImaginary(gamma, cone_data), cone_data) : gamma in gens];
end function;

function complex_minimalVectors(M, cone_data)
	K := cone_data`matrix_field;
	n := NumberOfRows(cone_data`basepoint) div 2;
	
	M := complex_rationalToImaginary(M, cone_data);
	
	gram := complex_hermitianToGram(M, cone_data);
	L := LatticeWithGram(gram);
	
	coefficients := ShortestVectors(L);

	minimal_vectors := [];
	
	lattice_basis := complex_latticeBasis(K,n);
	for vec in coefficients do
		image := VectorSpace(K, n) ! 0;
		
		for j in [1..#lattice_basis] do
			image +:= vec[j] * lattice_basis[j];
		end for;
		
		Append(~minimal_vectors, complex_imaginaryToRational(complex_toHermitian(image, cone_data)));
		Append(~minimal_vectors, complex_imaginaryToRational(complex_toHermitian(-image, cone_data)));
	end for;
	
	minimal_vectors := SetToSequence(SequenceToSet(minimal_vectors));
	
	return complex_innerProduct(complex_imaginaryToRational(M), minimal_vectors[1]), minimal_vectors, cone_data;
end function;

function complex_perfectionRank(M, cone_data)
	_, minimal_vectors, _ := complex_minimalVectors(M, cone_data);
	return Dimension(sub<cone_data`ambient_space | minimal_vectors>), cone_data;
end function;

function complex_boundaryPoints(height, cone_data)
	K := cone_data`matrix_field;
	n := NumberOfRows(cone_data`basepoint) div 2;
	
	L := LatticeWithGram(IdentityMatrix(Integers(), 2*n));
	lattice_coefficients := ShortVectors(L, height, height+1);
	
	lattice_basis := complex_latticeBasis(K, n);
	vecs := [];
	for l in lattice_coefficients do
		if l[2] ne height then
			return vecs;
		end if;
		
		image := VectorSpace(K, n) ! 0;
		coefficients := Eltseq(l[1]);
		for j in [1..#lattice_basis] do
			image +:= coefficients[j] * lattice_basis[j];
		end for;
		
		Append(~vecs, complex_imaginaryToRational(complex_toHermitian(image, cone_data)));
	end for;
	
	return vecs;
end function;

function complex_equivalent(v_rec, w_rec, cone_data : cone_voronoi_data := [])
	v := complex_rationalToImaginary(v_rec`point, cone_data);
	w := complex_rationalToImaginary(w_rec`point, cone_data);
	
	K := cone_data`matrix_field;
	n := NumberOfRows(cone_data`basepoint) div 2;
	O<omega> := MaximalOrder(K);
	
	grams := complex_clearDenoms([complex_hermitianToGram(v, cone_data), complex_hermitianToGram(w, cone_data)]);
	twisted_grams := complex_clearDenoms([complex_hermitianToTwistedGram(v, omega, cone_data), complex_hermitianToTwistedGram(w, omega, cone_data)]);
	
	L_v := LatticeWithGram(grams[1]);
	L_w := LatticeWithGram(grams[2]);
	
	omega_v := ChangeRing(twisted_grams[1], Integers());	
	omega_w := ChangeRing(twisted_grams[2], Integers());
	
	equiv, equivBy := IsIsometric(L_v, [omega_v], L_w, [omega_w]); //this for some reason is not giving complex matrices when O =/= Z[theta]?
	
	if equiv then
		print equivBy * grams[1] * Transpose(equivBy) eq grams[2], equivBy * omega_v * Transpose(equivBy) eq omega_w;
		gamma := complex_dagger(complex_rationalToImaginary(equivBy, cone_data), cone_data);
		return true, complex_dagger(complex_rationalToImaginary(equivBy, cone_data), cone_data);
	else
		return false, false;
	end if;
end function;

function complex_cellNormal(V, cone_data)
	B := [complex_rationalToImaginary(b, cone_data) : b in Basis(cone_data`ambient_space)];
	K := cone_data`matrix_field;
	n := NumberOfRows(cone_data`basepoint) div 2;
	
	innerProductMatrix := RMatrixSpace(K, #B, #V) ! 0;
	for i in [1..#B] do
		for j in [1..#V] do
			innerProductMatrix[i,j] := complex_innerProduct(B[i], complex_rationalToImaginary(V[j], cone_data));
		end for;
	end for; 
	
	kernel := Kernel(innerProductMatrix);
	if Dimension(kernel) gt 0 then
		normal_coordinates := kernel.1;
		vec := MatrixRing(K,n) ! 0;
		
		for i in [1..NumberOfColumns(normal_coordinates)] do
			vec +:= normal_coordinates[i] * B[i]; 
		end for;
		
		return complex_imaginaryToRational(vec);
	else
		print "Error in computing cell normal: no normals found.";
		return false;
	end if;
end function;

function complex_matrixLinearCombination(basis, M)
	V := VectorSpace(Rationals(), NumberOfRows(M)^2);
	
	basis_as_vectors := [V ! HorizontalJoin(Rows(b)) : b in basis];
	W := VectorSpaceWithBasis(basis_as_vectors);
	
	return Coordinates(W, W ! HorizontalJoin(Rows(M)));
end function;

function complex_isOrientableCell(vertices, cone_data : cone_voronoi_data := rec<voronoi_data | >)
	v := barycentre(vertices);
	basis := cellBasis(vertices, cone_data);
	
	stab := complex_stabiliser(rec<homogeneous_cone_point | point := v, minimal_vectors := vertices>, cone_data);
	
	W := VectorSpace(Rationals(), #basis);
	for gamma in stab do
		images := [];
		
		gammaDaggerPrime := complex_imaginaryToRational(complex_dagger(gamma, cone_data));
		gammaPrime := complex_imaginaryToRational(gamma);
		
		for b in basis do
			Append(~images, W ! complex_matrixLinearCombination(basis, gammaDaggerPrime * b * gammaPrime));
		end for;
		
		M := VerticalJoin(images);
		if Determinant(M) lt 0 then
			return false, false, false;
		end if;
	end for;
	
	return true, basis, stab;
end function;

function complex_compatibleCellOrientation(basis1, basis2, gamma, cone_data)
	complex_basis1 := [complex_rationalToImaginary(b, cone_data) : b in basis1];	
	acted_basis1 := [complex_dagger(gamma, cone_data) * v * gamma : v in complex_basis1];
	acted_basis1 := [complex_imaginaryToRational(b) : b in acted_basis1];
	
	V := VectorSpace(Rationals(), #basis2);
	images := [];
	for v in acted_basis1 do
		Append(~images, V ! complex_matrixLinearCombination(basis2, v));
	end for;
	
	M := VerticalJoin(images);

	if Determinant(M) gt 0 then
		return 1;
	else
		return -1;
	end if;
end function;

function complex_compatibleInducedCellOrientation(low_basis, high_basis)
	for v in high_basis do
		if v notin low_basis then
			extra_vertex := v;
			break;
		end if;
	end for;
	
	V := VectorSpace(Rationals(), #high_basis);
	coords := [];
	for v in (low_basis cat [extra_vertex]) do
		Append(~coords, V ! complex_matrixLinearCombination(high_basis, v));
	end for;
	
	M := VerticalJoin(coords);
	
	if Determinant(M) gt 0 then
		return 1;
	else
		return -1;
	end if;
end function;

//Generates a homogeneous cone record for the cone of complex Hermitian n x n matrices, with an action by the O_K-points for K = Q(sqrt(-d))
function complexCone(n, d)
	K<theta> := QuadraticField(-d);
	complex_cone_data := rec<homogeneous_cone_data | 
		type := "complex",
		coefficients := -d,
		matrix_field := K,
		matrix_size := n,
		
		ambient_space := sub<RMatrixSpace(Rationals(), 2*n, 2*n) | [complex_imaginaryToRational(M) : M in complex_hermitianBasis(n,K,theta)]>,
		basepoint := IdentityMatrix(Rationals(), 2*n),
		
		boundary_point_database := []
	>;
	
	complex_cone_functions := rec<homogeneous_cone_functions |
		innerProduct := complex_innerProduct,
		norm := complex_norm,
		
		isInteriorPoint := complex_isInteriorPoint,
		stabiliser := complex_stabiliser,
		minimalVectors := complex_minimalVectors,
		perfectionRank := complex_perfectionRank,
		
		boundaryPoints := complex_boundaryPoints,
		equivalent := complex_equivalent,
		cellNormal := complex_cellNormal,
		isOrientableCell := complex_isOrientableCell,
		compatibleCellOrientation := complex_compatibleCellOrientation,
		compatibleInducedCellOrientation := complex_compatibleInducedCellOrientation
		
	>;
	
	complex_cone := rec<homogeneous_cone | 
		cone_data := complex_cone_data,
		cone_functions := complex_cone_functions
	>;
	
	return complex_cone;
end function;

//--------------------------------------------------HAMILTONIAN HERMITIAN CONE--------------------------------------------------
//Generates a homogeneous cone record for the cone of Hamiltonian Hermitian n x n matrices, with an action by the O-points for B = (-a, -b / Q)
function hamiltonianCone(n, a,b)

end function;

//--------------------------------------------------LORENTZ CONE--------------------------------------------------
function lorentz_innerProduct(v,w)
	return InnerProduct(v,w);
end function;

function lorentz_norm(v)
	return InnerProduct(v,v);
end function;

function lorentz_isInteriorPoint(v, cone_data)
	if v[NumberOfColumns(v)] le 0 then
		return false;
	else
		return lorentz_norm(v) gt 0;
	end if;
end function;

//----------Standard equivalence and automorphism group functions----------
function lorentz_clearDenoms(S) //scales a set of vectors S by a common factor so that they have integer coordinates
	denoms := [];
	
	for i in [1..NumberOfColumns(S[1])] do
		for j in [1..#S] do
			Append(~denoms, Denominator(S[j][i]));
		end for;
	end for;
	
	scale_factor := LCM(denoms);
	
	return [scale_factor * s : s in S];	
end function;

function lorentz_stabiliser_standard(v_rec, cone_data : cone_voronoi_data := rec<voronoi_data | >, special := true, optimised_generators := true)
	v := v_rec`point;
	v := lorentz_clearDenoms([v])[1];
	
	L := LatticeWithGram(2*MatrixRing(Rationals(), NumberOfColumns(v)) ! Eltseq(TensorProduct(v,v)) - DiagonalMatrix(Rationals(), NumberOfColumns(v), [-1 : i in [1..NumberOfColumns(v)-1]] cat [1]));
	G := AutomorphismGroup(L, [DiagonalMatrix(Integers(), NumberOfColumns(v), [-1 : i in [1..NumberOfColumns(v)-1]] cat [1])]);
	
	stab := [];
	for g in G do
		gamma := MatrixRing(Rationals(), NumberOfColumns(v)) ! Transpose(g);
		if v * gamma eq v then //could have v * gamma eq -v
			if Determinant(gamma) eq 1 or not special then
				Append(~stab, gamma);
			end if;
		end if;
	end for;
	
	return matrixGroupGenerators(stab : optimised_representation := optimised_generators);
end function;

function lorentz_equivalent_standard(v_rec, w_rec, cone_data : cone_voronoi_data := [])
	v := v_rec`point;
	w := w_rec`point;
	
	if lorentz_norm(v) eq lorentz_norm(w) then
		cleared := lorentz_clearDenoms([v,w]);
		v := cleared[1];
		w := cleared[2];
	
		J := DiagonalMatrix(Rationals(), NumberOfColumns(v), [-1 : i in [1..NumberOfColumns(v)-1]] cat [1]);
		J_int := DiagonalMatrix(Integers(), NumberOfColumns(v), [-1 : i in [1..NumberOfColumns(v)-1]] cat [1]);
		
		L1 := LatticeWithGram(2*MatrixRing(Rationals(), NumberOfColumns(v)) ! Eltseq(TensorProduct(v,v)) - J);
		L2 := LatticeWithGram(2*MatrixRing(Rationals(), NumberOfColumns(w)) ! Eltseq(TensorProduct(w,w)) - J_int);
		
		equiv, equivBy := IsIsometric(L1, [J_int], L2, [J_int]); //Isometries of L1 and L2 that preserve J_int i.e. O(n,1; Z)
		if equiv then
			equivBy := MatrixRing(Rationals(), NumberOfColumns(v)) ! Transpose(equivBy); //tells us that v equiv^T = +/- w, with equiv in O(n,1; Z). if standard_form, this implies equiv^T in O^(n,1; Z)
			if v * equivBy ne w then
				equivBy *:= -1;
			end if;
			
			//return true, equivBy;
			
			if Determinant(equivBy) ne 1 then
				stab := lorentz_stabiliser_standard(w_rec, cone_data : cone_voronoi_data := cone_voronoi_data, special := false, optimised_generators := false); //O(n,1) stabiliser
				for g in stab do
					if Determinant(g) eq -1 then
						return true, equivBy * g;
					end if;
				end for;
				
				print "this shouldn't happen";
				return false, false; //none with determinant 1, only determinant -1
			end if;
			
			return true, equivBy;
		else
			return false, false;
		end if;
	else
		return false, false;
	end if;
end function;

function lorentz_cellNormal(V, cone_data)
	M := InnerProduct(cone_data`ambient_space) * Transpose(VerticalJoin(V));
	return cone_data`ambient_space ! Kernel(M).1;
end function;

//----------Functions relating to minimal vectors----------
function lorentz_boundaryPoints(height, cone_data) //TODO: rewrite to only take those with positive entries
	n := Dimension(cone_data`ambient_space) - 1;
	q := [-InnerProduct(cone_data`ambient_space)[i,i] : i in [1..n]];
	
	L := LatticeWithGram(DiagonalMatrix(Rationals(), n, q));
	lattice_points := ShortVectors(L, height^2, height^2+1);
	
	vecs := [];
	for l in lattice_points do
		if l[2] eq height^2+1 then //all found of height^2
			return vecs;
		end if;
		
		Append(~vecs, cone_data`ambient_space ! (Eltseq(l[1]) cat [height]));
		Append(~vecs, cone_data`ambient_space ! (Eltseq(-l[1]) cat [height]));
	end for;
	
	return vecs;
end function;

function lorentz_minimalVectors(p, cone_data)
	min := Infinity();
	height_bound := Infinity();
	
	height := 1;
	while height lt height_bound do
		if height gt #cone_data`boundary_point_database then
			print "\t\tminvecs: finding points of height", height, "/", height_bound;
			Append(~cone_data`boundary_point_database, lorentz_boundaryPoints(height, cone_data));
		end if;
		
		for v in cone_data`boundary_point_database[height] do
			p_component := lorentz_innerProduct(p, v);
			if p_component lt min then //new minimum found
				min := p_component;
				minimal_vectors := [v];
				height_bound := Minimum(height_bound, 2 * p[NumberOfColumns(p)] * min / lorentz_norm(p));
			elif p_component eq min then
				Append(~minimal_vectors, v);
			end if;
		end for;
		
		height +:= 1;
	end while;
	
	return min, minimal_vectors, cone_data;
end function;

function lorentz_perfectionRank(v, cone_data)
	_, minimal_vectors, cone_data := lorentz_minimalVectors(v, cone_data);
	return Rank(VerticalJoin(minimal_vectors)), cone_data;
end function;

function lorentz_isOrientableCell_standard(vertices, cone_data : cone_voronoi_data := rec<voronoi_data | >)
	v := barycentre(vertices);
	basis := cellBasis(vertices, cone_data);
	
	stab := lorentz_stabiliser_standard(rec<homogeneous_cone_point | point := v, minimal_vectors := vertices>, cone_data);
	
	V := VectorSpaceWithBasis(basis);
	W := VectorSpace(Rationals(), Dimension(V));
	for gamma in stab do
		images := [];
		
		for b in basis do
			Append(~images, W ! Coordinates(V, V ! b*gamma));
		end for;
		
		M := VerticalJoin(images);
		if Sign(Determinant(M)) lt 0 then
			//print gamma;
			return false, false, false;
		end if;
	end for;
	
	return true, basis, stab;
end function;

function lorentz_compatibleCellOrientation(basis1, basis2, gamma, cone_data)
	acted_basis1 := [v * gamma : v in basis1];
	
	V := VectorSpace(Rationals(), #basis2);
	W := VectorSpaceWithBasis(basis2);
	images := [];
	for v in acted_basis1 do
		Append(~images, V ! Coordinates(W, W ! v));
	end for;
	
	M := VerticalJoin(images);

	if Determinant(M) gt 0 then
		return 1;
	else
		return -1;
	end if;
end function;

function lorentz_compatibleInducedCellOrientation(low_basis, high_basis)
	for v in high_basis do
		if v notin low_basis then
			extra_vertex := v;
			break;
		end if;
	end for;
	
	V := VectorSpace(Rationals(), #high_basis);
	W := VectorSpaceWithBasis(high_basis);
	
	coords := [];
	for v in (low_basis cat [extra_vertex]) do
		Append(~coords, V ! Coordinates(W, W ! v));
	end for;
	
	M := VerticalJoin(coords);
	
	if Determinant(M) gt 0 then
		return 1;
	else
		return -1;
	end if;
end function;

function lorentz_stabiliser_general(v_rec, cone_data : cone_voronoi_data := rec<voronoi_data | >)
	n := cone_data`matrix_size - 1;
	q := [-InnerProduct(cone_data`ambient_space)[i,i] : i in [1..n]];
	
	Q := RationalsAsNumberField();
	L := NumberFieldLatticeWithGram(DiagonalMatrix(Q, n+1, q cat [-1]));
	
	v := v_rec`point;
	v := L ! lorentz_clearDenoms([v])[1];
	
	G := AutomorphismGroup(L, v);
	stab := [];
	
	for g in G do
		if Determinant(g) eq 1 then
			Append(~stab, ChangeRing(g, Rationals()));
		end if;
	end for;
	
	return matrixGroupGenerators(stab);
end function;

function lorentz_equivalent_general(v_rec, w_rec, cone_data : cone_voronoi_data := rec<voronoi_data | >)
	n := cone_data`matrix_size - 1;
	q := [-InnerProduct(cone_data`ambient_space)[i,i] : i in [1..n]];
	
	Q := RationalsAsNumberField();
	L := NumberFieldLatticeWithGram(DiagonalMatrix(Q, n+1, q cat [-1]));
	
	v := v_rec`point;
	w := w_rec`point;
	
	rescaled := lorentz_clearDenoms([v,w]);
	v := rescaled[1];
	w := rescaled[2];
	
	v := L ! v;
	w := L ! w;
	
	equiv, equiv_by := IsIsometric(L, w, v);
	
	if equiv then
		if Determinant(equiv_by) eq 1 then
			return true, equiv_by;
		else
			G, _ := AutomorphismGroup(L, v);
			for g in G do
				if Determinant(g) eq -1 then
					return true, g * equiv_by;
				end if;
			end for; 
			return false, false; //no det -1 to multiply by :(
		end if;
	else
		return false, false;
	end if;
end function;

function lorentz_isOrientableCell_general(vertices, cone_data : cone_voronoi_data := rec<voronoi_data | >)
	v := barycentre(vertices);
	basis := cellBasis(vertices, cone_data);
	
	stab := lorentz_stabiliser_general(rec<homogeneous_cone_point | point := v, minimal_vectors := vertices>, cone_data : cone_voronoi_data := cone_voronoi_data);
	
	V := VectorSpaceWithBasis(basis);
	W := VectorSpace(Rationals(), Dimension(V));
	for gamma in stab do
		images := [];
		
		for b in basis do
			Append(~images, W ! Coordinates(V, V ! b*gamma));
		end for;
		
		M := VerticalJoin(images);
		if Sign(Determinant(M)) lt 0 then
			return false, false, false;
		end if;
	end for;
	
	return true, basis, stab;
end function;


//Generates a homogeneous cone record for the Lorentz cone of signature n,1 and quadratic form q
function lorentzCone(n, q)
	if #q ne n then
		print "Error in Lorentz cone generation: quadratic form has", #q, "coefficients provided;", n, "required.";
		return -1;
	elif q eq [1 : i in [1..n]] then //standard signature (n,1) form
		lorentz_cone_data := rec<homogeneous_cone_data |
			type := "lorentz",
			matrix_field := Rationals(),
			matrix_size := n+1,
			
			ambient_space := VectorSpace(Rationals(), n+1, DiagonalMatrix(Rationals(), n+1, [-q[i] : i in [1..n]] cat [1])),
			basepoint := VectorSpace(Rationals(), n+1, DiagonalMatrix(Rationals(), n+1, [-q[i] : i in [1..n]] cat [1])) ! ([0 : i in [1..n]] cat [1]),
			
			boundary_point_database := []
		>;
		
		lorentz_cone_functions := rec<homogeneous_cone_functions |
			innerProduct := lorentz_innerProduct,
			norm := lorentz_norm,
			
			isInteriorPoint := lorentz_isInteriorPoint,
			stabiliser := lorentz_stabiliser_standard,
			minimalVectors := lorentz_minimalVectors,
			perfectionRank := lorentz_perfectionRank,
			
			boundaryPoints := lorentz_boundaryPoints,
			equivalent := lorentz_equivalent_standard,
			cellNormal := lorentz_cellNormal,
			isOrientableCell := lorentz_isOrientableCell_standard,
			compatibleCellOrientation := lorentz_compatibleCellOrientation,
			compatibleInducedCellOrientation := lorentz_compatibleInducedCellOrientation
		>;
		
		return rec<homogeneous_cone | 	
			cone_data := lorentz_cone_data,
			cone_functions := lorentz_cone_functions
		>;
	else
		lorentz_cone_data := rec<homogeneous_cone_data |
			type := "lorentz",
			matrix_field := Rationals(),
			matrix_size := n+1,
			
			ambient_space := VectorSpace(Rationals(), n+1, DiagonalMatrix(Rationals(), n+1, [-q[i] : i in [1..n]] cat [1])),
			basepoint := VectorSpace(Rationals(), n+1, DiagonalMatrix(Rationals(), n+1, [-q[i] : i in [1..n]] cat [1])) ! ([0 : i in [1..n]] cat [1]),
			
			boundary_point_database := []
		>;
		
		lorentz_cone_functions := rec<homogeneous_cone_functions |
			innerProduct := lorentz_innerProduct,
			norm := lorentz_norm,
			
			isInteriorPoint := lorentz_isInteriorPoint,
			stabiliser := lorentz_stabiliser_general,
			minimalVectors := lorentz_minimalVectors,
			perfectionRank := lorentz_perfectionRank,
			
			boundaryPoints := lorentz_boundaryPoints,
			equivalent := lorentz_equivalent_general,
			cellNormal := lorentz_cellNormal,
			isOrientableCell := lorentz_isOrientableCell_general,
			compatibleCellOrientation := lorentz_compatibleCellOrientation,
			compatibleInducedCellOrientation := lorentz_compatibleInducedCellOrientation
		>;
		
		return rec<homogeneous_cone | 	
			cone_data := lorentz_cone_data,
			cone_functions := lorentz_cone_functions
		>;
	end if;
end function;
