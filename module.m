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
	cosets,
	coset_recog : UserProgram,
	action : UserProgram,
	cartesian : BoolElt
>;

//--------------------------------------------------GENERIC FUNCTIONS--------------------------------------------------
function action_permutation(M, gamma : cartesian := false)
	if cartesian then
		components := NumberOfComponents(M`cosets);
		
		//generate permutations for each factor
		gamma := ChangeRing(gamma, M`coset_ring);
		permutations := [];
		for i in [1..components] do
			Append(~permutations, []);
			for j in [1..#M`cosets[i]] do
				image := M`coset_recog(M`action(M`cosets[i][j], gamma : factor := i) : factor := i);
				Append(~permutations[i], Index(M`cosets[i], image));
			end for;
		end for;
		
		component_sizes := [#M`cosets[i] : i in [1..components]];
		size_products := [&*[component_sizes[j] : j in [i+1..components]] : i in [1..components-1]];
		
		sigma := [];
		indices := [v : v in CartesianProduct([[1..component_sizes[i]] : i in [1..components]])];
		for i in [1..#indices] do
			permutation_indices := [permutations[j][indices[i][j]] : j in [1..components]];
			index := &+[(permutation_indices[j] - 1) * size_products[j] : j in [1..components-1]] + permutation_indices[components];
			
			Append(~sigma, index);
		end for;
		
		//return sigma;
		
		tau := [1..#sigma];
		for i in [1..#sigma] do
			tau[sigma[i]] := i;
		end for;
		
		return tau;
	else
		sigma := [1..#M`cosets];
		
		gamma := ChangeRing(gamma, M`coset_ring);
		for i in [1..#M`cosets] do
			image := M`coset_recog(M`action(M`cosets[i], gamma));
			sigma[Index(M`cosets, image)] := i;
		end for;
		
		return sigma;
	end if;
end function;

function action_matrix(M, gamma, character : cartesian := false)
	if cartesian then
		components := NumberOfComponents(M`cosets);
		
		//generate permutations for each factor
		//print "generating permutations";
		gamma := ChangeRing(gamma, M`coset_ring);
		permutations := [];
		for i in [1..components] do
			Append(~permutations, []);
			for j in [1..#M`cosets[i]] do
				image := M`coset_recog(M`action(M`cosets[i][j], gamma : factor := i) : factor := i);
				Append(~permutations[i], Index(M`cosets[i], image));
			end for;
		end for;
		//print "generated";
		
		//generate matrix for cartesian product
		mat := MatrixRing(M`base_field, #M`cosets) ! 0;
		component_sizes := [#M`cosets[i] : i in [1..components]];
		size_products := [&*[component_sizes[j] : j in [i+1..components]] : i in [1..components-1]];
		
		indices := [v : v in CartesianProduct([[1..component_sizes[i]] : i in [1..components]])];
		for i in [1..#indices] do
			permutation_indices := [permutations[j][indices[i][j]] : j in [1..components]];
			index := &+[(permutation_indices[j] - 1) * size_products[j] : j in [1..components-1]] + permutation_indices[components];
			
			mat[i, index] := character;
		end for;
		//print "matrix generated";
		
		return mat;
	else
		mat := MatrixRing(M`base_field, #M`cosets) ! 0;

		gamma := ChangeRing(gamma, M`coset_ring);
		for i in [1..#M`cosets] do
			image := M`coset_recog(M`action(M`cosets[i], gamma));
			mat[i, Index(M`cosets, image)] := character;
		end for;
		
		return mat;
	end if;
end function;

function invariants_orientable(M, generators : cartesian := false)
	if #generators eq 0 then
		return VectorSpace(M`base_field, #M`cosets);
	end if;
	
	cycles := [];
	cycle_indices := [];
	for i in [1..#generators] do
		Append(~cycle_indices, [1..#M`cosets]);
		g_permutation := action_permutation(M, generators[i] : cartesian := cartesian);
		
		g_cycles := [];
		unused := [1..#M`cosets];
		
		while #unused gt 0 do
			start := unused[1];
			cycle := [start];
			Exclude(~unused, start);
			
			cycle_indices[i][start] := #g_cycles + 1;
			
			while g_permutation[cycle[#cycle]] ne start do
				Exclude(~unused, g_permutation[cycle[#cycle]]);
				cycle_indices[i][g_permutation[cycle[#cycle]]] := #g_cycles + 1;
				Append(~cycle, g_permutation[cycle[#cycle]]);
			end while;
			
			Append(~g_cycles, cycle);
		end while;
		
		Append(~cycles, g_cycles);
	end for;
	
	unused := [1..#M`cosets];
	blocks := [];
	while #unused gt 0 do
		block := [unused[1]];
		new := [block[1]];
		Remove(~unused, 1);
		
		while #new gt 0 do
			for i in [1..#generators] do
				for j in cycles[i][cycle_indices[i][new[1]]] do
					if j notin block then
						Append(~block, j);
						Append(~new, j);
						
						Remove(~unused, Index(unused, j));
					end if;
				end for;
			end for;
			
			Remove(~new, 1);
		end while;
		
		Append(~blocks, block);
	end while;
	
	V := VectorSpace(M`base_field, #M`cosets);
	
	basis := [];
	for i in [1..#blocks] do
		v := V ! 0;
		for j in blocks[i] do
			v[j] := 1;
		end for;
		
		Append(~basis, v);
	end for;
	
	return sub<V | basis>;
end function;

function invariants(M, generators, orientation_character : cartesian := false)
	if #generators eq 0 then
		return VectorSpace(M`base_field, #M`cosets);
	elif #generators eq 1 then
		permutation := action_permutation(M, generators[1] : cartesian := cartesian);
		
		cycles := [];
		unused := [1..#M`cosets];
		while #unused gt 0 do
			start := unused[1];
			cycle := [start];
			Exclude(~unused, start);
			
			while permutation[cycle[#cycle]] ne start do
				Exclude(~unused, permutation[cycle[#cycle]]);
				Append(~cycle, permutation[cycle[#cycle]]);
			end while;
			
			Append(~cycles, cycle);
		end while;
		
		V := VectorSpace(M`base_field, #M`cosets);
		basis := [];
		if orientation_character[1] eq 1 then
			for cycle in cycles do
				v := V ! 0;
				for i in cycle do
					v[i] := 1;
				end for;
				
				Append(~basis, v);
			end for;
		else
			for cycle in cycles do
				if #cycle mod 2 eq 0 then
					v := V ! 0;
					for i in [1..#cycle] do
						v[i] := (-1)^i;
					end for;
					
					Append(~basis, v);
				end if;
			end for;
		end if;
		
		return sub<V | basis>;
	else
		//rearrange generators so that there is at most 1 with orientation_character = -1, and this is the last element
		orientable := true;
		first_index := 0;
		for i in [1..#orientation_character] do
			if orientation_character[i] eq -1 then
				if first_index eq 0 then
					first_index := i;
					orientable := false;
				else
					generators[i] := generators[i] * generators[first_index];
					orientation_character[i] := 1;
				end if;
			end if;
		end for;
		
		if orientable then
			return invariants_orientable(M, generators : cartesian := cartesian);
		else
			if first_index ne #orientation_character then
				swap := generators[first_index];
				generators[first_index] := generators[#generators];
				generators[#generators] := swap;
				orientation_character[first_index] := 1;
				orientation_character[#generators] := -1;
			end if;
		end if;
		
		//calculate cycles for generator
		cycles := [];
		cycle_indices := [];
		for i in [1..#generators] do
			Append(~cycle_indices, [1..#M`cosets]);
			g_permutation := action_permutation(M, generators[i] : cartesian := cartesian);
			
			g_cycles := [];
			unused := [1..#M`cosets];
			
			while #unused gt 0 do
				start := unused[1];
				cycle := [start];
				Exclude(~unused, start);
				
				cycle_indices[i][start] := #g_cycles + 1;
				
				while g_permutation[cycle[#cycle]] ne start do
					Exclude(~unused, g_permutation[cycle[#cycle]]);
					cycle_indices[i][g_permutation[cycle[#cycle]]] := #g_cycles + 1;
					Append(~cycle, g_permutation[cycle[#cycle]]);
				end while;
				
				Append(~g_cycles, cycle);
			end while;
			
			Append(~cycles, g_cycles);
		end for;
		
		//calculate blocks for orientation-preserving generators
		if #generators gt 2 then
			unused := [1..#M`cosets];
			blocks := [];
			block_indices := unused;
			while #unused gt 0 do
				block := [unused[1]];
				new := [block[1]];
				Remove(~unused, 1);
				
				block_indices[block[1]] := #blocks + 1;
				
				while #new gt 0 do
					for i in [1..#generators-1] do
						for j in cycles[i][cycle_indices[i][new[1]]] do
							if j notin block then
								Append(~block, j);
								Append(~new, j);
								block_indices[j] := #blocks + 1;
								
								Remove(~unused, Index(unused, j));
							end if;
						end for;
					end for;
					
					Remove(~new, 1);
				end while;
				
				Append(~blocks, block);
			end while;
		else
			blocks := cycles[1];
			block_indices := cycle_indices[1];
		end if;
		
		//calculate relations on blocks from the orientation-reversing generator
		block_same_indices := [*{} : i in [1..#blocks]*];
		block_opposite_indices := [*{} : i in [1..#blocks]*];
		for cycle in cycles[#generators] do
			if #cycle mod 2 eq 0 then
				//print cycle;
				positive_blocks := {block_indices[cycle[i]] : i in [2..#cycle by 2]};
				negative_blocks := {block_indices[cycle[i]] : i in [1..#cycle by 2]};
				
				for i in positive_blocks do
					block_same_indices[i] join:= positive_blocks;
					block_opposite_indices[i] join:= negative_blocks;
				end for;
				
				for i in negative_blocks do
					block_same_indices[i] join:= negative_blocks;
					block_opposite_indices[i] join:= positive_blocks;
				end for;
			else
				for i in cycle do
					Include(~block_same_indices[block_indices[i]], block_indices[i]);
					Include(~block_opposite_indices[block_indices[i]], block_indices[i]);
				end for;
			end if;
		end for;
		
		//construct basis from relations
		V := VectorSpace(M`base_field, #M`cosets);
		basis := [];
		
		unused := [1..#blocks];
		while #unused gt 0 do
			start := unused[1];
			
			positive_blocks := block_same_indices[start];
			negative_blocks := block_opposite_indices[start];
			
			if block_same_indices[start] meet block_opposite_indices[start] eq {} then
				new_positive := [i : i in block_same_indices[start]];
				new_negative := [i : i in block_opposite_indices[start]];
				
				while #new_positive + #new_negative gt 0 do
					if #new_positive gt 0 then
						for j in block_same_indices[new_positive[1]] do
							if j notin positive_blocks then
								Include(~positive_blocks, j);
								Append(~new_positive, j);
							end if;
						end for;
						
						for j in block_opposite_indices[new_positive[1]] do
							if j notin negative_blocks then
								Include(~negative_blocks, j);
								Append(~new_negative, j);
							end if;
						end for;
						
						Remove(~new_positive, 1);
					end if;
					
					if #new_negative gt 0 then
						for j in block_same_indices[new_negative[1]] do
							if j notin negative_blocks then
								Include(~negative_blocks, j);
								Append(~new_negative, j);
							end if;
						end for;
						
						for j in block_opposite_indices[new_negative[1]] do
							if j notin positive_blocks then
								Include(~positive_blocks, j);
								Append(~new_positive, j);
							end if;
						end for;
						
						Remove(~new_negative, 1);
					end if;
				end while;
				
				if positive_blocks meet negative_blocks eq {} then //success! this block is non-zero. time to build a basis vector
					v := V ! 0;
					for i in positive_blocks do
						for j in blocks[i] do
							v[j] := 1;
						end for;
					end for;
					
					for i in negative_blocks do
						for j in blocks[i] do
							v[j] := -1;
						end for;
					end for;
					
					Append(~basis, v);
				end if;
			end if;
			
			for i in positive_blocks join negative_blocks do
				if i in unused then
					Remove(~unused, Index(unused, i));
				end if;
			end for;			
		end while;
		
		return sub<V | basis>;
	end if;
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
		action := bianchi_action,
		cartesian := false
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

function projectiveStandardFormCartesian(v : factor := 0)
	if factor eq 0 then
		return <projectiveStandardForm(vec) : vec in v>;
	else
		return projectiveStandardForm(v);
	end if;
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

function isotropicOrbitLevelTwo(cone_data)
	n := Dimension(cone_data`ambient_space) - 1;
	q := [-InnerProduct(cone_data`ambient_space)[i,i] : i in [1..n]];
	level := FiniteField(2,1);
	
	V_p := VectorSpace(level, n+1, DiagonalMatrix(level, n+1, [-q[i] : i in [1..n]] cat [1]));
	
	G := DerivedGroup(IsometryGroup(V_p));
	initial_point := V_p ! ([1,1] cat [0 : i in [1..n-1]]);
	isotropic_points := [initial_point];
	for g in G do
		action := initial_point * g;
		if action notin isotropic_points then
			Append(~isotropic_points, action);
		end if;
	end for;
	
	return Sort(isotropic_points);
end function;

function lorentzGamma0_action(isotropic_point, gamma)
	return isotropic_point * gamma;
end function;

function isotropicPointsCartesian(level, cone_data)
	primes := PrimeFactors(level);
	
	prime_levels := <>;
	for p in primes do
		if p gt 2 then
			Append(~prime_levels, isotropicPoints(FiniteField(p,1), cone_data));
		else
			Append(~prime_levels, isotropicOrbitLevelTwo(cone_data));
		end if;
	end for;
	
	//print #CartesianProduct(prime_levels);
	//return [v : v in CartesianProduct(prime_levels)];
	return CartesianProduct(prime_levels);
end function;

function lorentzGamma0_actionCartesian(isotropic_point, gamma : factor := 0)
	primes := PrimeFactors(Characteristic(Parent(gamma[1,1])));
	if factor eq 0 then		
		return <isotropic_point[i] * ChangeRing(gamma, FiniteField(primes[i], 1)) : i in [1..#isotropic_point]>;
	else
		return isotropic_point * ChangeRing(gamma, FiniteField(primes[factor], 1));
	end if;
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
			action := func<v, w | VectorSpace(base_field, 1).1>,
			cartesian := false
		>;
	elif not IsSquarefree(level) then
		print "Error in Lorentz Gamma_0 module generation: only squarefree levels supported.";
		return false;
	elif not IsPrime(level) then
		return rec<coinduced_module | 
			type := "lorentz_dim1",
			
			base_field := base_field,
			level := level,
			
			coset_ring := quo<Integers() | level*Integers()>,
			cosets := isotropicPointsCartesian(level, cone`cone_data),
			coset_recog := projectiveStandardFormCartesian,
			action := lorentzGamma0_actionCartesian,
			cartesian := true
		>;
	elif level eq 2 then
		return rec<coinduced_module | 
			type := "lorentz_dim1",
			
			base_field := base_field,
			level := level,
			
			coset_ring := FiniteField(level, 1),
			cosets := isotropicOrbitLevelTwo(cone`cone_data),
			coset_recog := projectiveStandardForm,
			action := lorentzGamma0_action,
			cartesian := false
		>;
	else
		return rec<coinduced_module | 
			type := "lorentz_dim1",
			
			base_field := base_field,
			level := level,
			
			coset_ring := FiniteField(level, 1),
			cosets := isotropicPoints(FiniteField(level,1), cone`cone_data),
			coset_recog := projectiveStandardForm,
			action := lorentzGamma0_action,
			cartesian := false
		>;
	end if;
end function;


//--------------------------------------------------LORENTZ HIGHER ISOTROPIC STABILISERS--------------------------------------------------
function isotropicSpaces(level, dimension, cone_data)
	points := isotropicPoints(level, cone_data);
	
	n := Dimension(cone_data`ambient_space) - 1;
	q := [-InnerProduct(cone_data`ambient_space)[i,i] : i in [1..n]];
	V_p := VectorSpace(level, n+1, DiagonalMatrix(level, n+1, [-q[i] : i in [1..n]] cat [1]));
	
	if dimension eq 1 then
		return points;
	elif dimension eq 2 then
		spaces := [];
		for i in [1..#points] do
			for j in [i+1..#points] do
				if InnerProduct(points[i], points[j]) eq 0 then
					space := sub<V_p | [points[i], points[j]]>;
					if space notin spaces then
						Append(~spaces, space);
					end if;
				end if;
			end for;
		end for;
		
		return spaces;
	end if;
	
	codim_one := isotropicSpaces(level, dimension-1, cone_data);
	spaces := [];
	for space in codim_one do
		for point in points do
			if point in space then
				continue;
			end if;
			
			isotropic := true;
			for i in [1..Dimension(space)] do
				if InnerProduct(point, space.i) ne 0 then
					isotropic := false;
					break;
				end if;
			end for;
			
			if isotropic then
				subspace := sub<V_p | Basis(space) cat [point]>;
				if subspace notin spaces then
					Append(~spaces, subspace);
				end if;
			end if;
		end for;
	end for;
	
	return spaces;
end function;

function lorentzIsotropic_action(space, gamma)
	V_p := VectorSpace(Parent((space.1)[1]), NumberOfColumns(space.1), DiagonalMatrix(Parent((space.1)[1]), NumberOfColumns(space.1), [-1,-1,-1,-1,1]));
	
	basis := [space.i * gamma : i in [1..Dimension(space)]];
	return sub<V_p | basis>;
end function;

function lorentzIsotropicStabiliserModule(base_field, level, dimension, cone)
	if level eq 1 then
		return rec<coinduced_module | 
			type := "lorentz_higher",
			
			base_field := base_field,
			level := level,
			
			coset_ring := base_field,
			cosets := [VectorSpace(base_field, 1).1],
			coset_recog := func<v | VectorSpace(base_field, 1).1>,
			action := func<v, w | VectorSpace(base_field, 1).1>,
			cartesian := false
		>;
	elif not IsPrime(level) then
		print "Error in Lorentz isotropic stabiliser module generation: composite levels not yet supported";
	elif level eq 2 then
		print "Error in Lorentz isotropic stabiliser module generation: p=2 not yet supported";
	elif dimension gt cone`cone_data`matrix_size div 2 then
		print "Error in Lorentz isotropic stabiliser module generation: dimension > 1/2 (n+1) not allowed";
	else
		return rec<coinduced_module | 
			type := "lorentz_higher",
			
			base_field := base_field,
			level := level,
			
			coset_ring := FiniteField(level, 1),
			cosets := isotropicSpaces(FiniteField(level, 1), dimension, cone`cone_data),
			coset_recog := func<v | v>,
			action := lorentzIsotropic_action,
			cartesian := false
		>;
	end if;
end function;
