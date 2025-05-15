//Voronoi Cohomology Library - Written by Daniel Bassett, 2025
//---------------------------------------------------------------------------module.m---------------------------------------------------------------------------
/*
TODO: write description
*/


//Record of the data associated with a coinduced module, 
coinduced_module := recformat<
	type,
	
	base_field : Fld, //the original module before coind
	level,
	
	coset_ring, //the coefficient ring of the representation of the cosets
	cosets : SeqEnum,
	coset_recog : UserProgram,
	action : UserProgram
>;

//--------------------------------------------------GENERIC FUNCTIONS--------------------------------------------------
function action_permutation(M, gamma)
	sigma := [1..#M`cosets];
	
	gamma := ChangeRing(gamma, M`coset_ring);
	for i in [1..#M`cosets] do
		image := M`coset_recog(M`action(M`cosets[i], gamma));
		
		//Append(~sigma, Index(M`cosets, image));
		sigma[Index(M`cosets, image)] := i;
	end for;
	
	return sigma;
end function;

function action_matrix(M, gamma)
	mat := MatrixRing(M`base_field, #M`cosets) ! 0;

	gamma := ChangeRing(gamma, M`coset_ring);
	for i in [1..#M`cosets] do
		image := M`coset_recog(M`action(M`cosets[i], gamma));
		
		mat[i, Index(M`cosets, image)] := 1;
	end for;
	
	return mat;
end function;

function invariants(M, generators)
	V := VectorSpace(M`base_field, #M`cosets);
	
	for gamma in generators do
		gamma_action := action_matrix(M, gamma);
		V := V meet Kernel(gamma_action - IdentityMatrix(M`base_field, #M`cosets));
	end for;
	
	return V;
end function;

//--------------------------------------------------BIANCHI GAMMA_0--------------------------------------------------
function fix_recog(recog)
	recog_fixed := function(point)
			_, recognised_point, _ := recog(point, false, false);
			return recognised_point;
		end function;
	
	return recog_fixed;
end function;

function bianchi_projectiveLine(field, level)
	O := MaximalOrder(field);
	R := quo<O | level>;
	
	points, recog := ProjectiveLine(R);	
	return Sort([p : p in points]), fix_recog(recog);
end function;

function bianchi_action(point, gamma)
	return point * gamma;
end function;

function bianchiGamma0Module(base_field, level, cone)
	if cone`cone_data`matrix_size ne 2 then
		print "Error in Bianchi Gamma_0 module generation: dimension of matrices in cone is not 2";
		return false;
	end if;
	
	field := cone`cone_data`matrix_field;	
	proj_line, recog := bianchi_projectiveLine(field, level);
		
	return rec<coinduced_module | 
		type := "bianchi",
		
		base_field := base_field,
		level := level,
		
		coset_ring := MaximalOrder(field),
		cosets := proj_line,
		coset_recog := recog,
		action := bianchi_action
	>;
end function;

//--------------------------------------------------LORENTZ GAMMA_0--------------------------------------------------
function projectiveStandardForm(v) //normalises so that the first non-zero coordinate is 1
	for i in [1..NumberOfColumns(v)] do
		if v[i] ne 0 then
			return v / v[i];
		end if;
	end for;
end function;

function isotropicPoints(level, cone_data)
	n := Dimension(cone_data`ambient_space) - 1;
	q := [-InnerProduct(cone_data`ambient_space)[i,i] : i in [1..n]];
	
	V_p := VectorSpace(level, n+1, DiagonalMatrix(level, n+1, [-q[i] : i in [1..n]] cat [1]));
	
	isotropic_points := [];
	for v in V_p do
		if v eq V_p ! 0 then
			continue;
		end if;
		
		if projectiveStandardForm(v) eq v then //take only one point on each line
			if Norm(v) eq 0 then
				Append(~isotropic_points, v);
			end if;
		end if;
	end for;
	
	return Sort(isotropic_points);
end function;

function lorentzGamma0_action(isotropic_point, gamma)
	return isotropic_point * gamma;
end function;

function lorentzGamma0Module(base_field, level, cone)
	if level eq 1 then
		return rec<coinduced_module | 
			type := "lorentz_dim1",
			
			base_field := base_field,
			level := level,
			
			coset_ring := base_field,
			cosets := [VectorSpace(base_field, 1).1],
			coset_recog := func<v | VectorSpace(base_field, 1).1>,
			action := func<v, w | VectorSpace(base_field, 1).1>
		>;
	elif not IsPrime(level) then
		print "Error in Lorentz Gamma_0 module generation: composite levels not yet supported.";
		return false;
	elif level eq 2 then
		print "Error in Lorentz Gamma_0 module generation: p=2 not yet supported.";
		return false;
	end if;
	
	return rec<coinduced_module | 
		type := "lorentz_dim1",
		
		base_field := base_field,
		level := level,
		
		coset_ring := FiniteField(level, 1),
		cosets := isotropicPoints(FiniteField(level,1), cone`cone_data),
		coset_recog := projectiveStandardForm,
		action := lorentzGamma0_action
	>;
end function;
