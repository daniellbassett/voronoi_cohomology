//Voronoi Cohomology Library - Written by Daniel Bassett, 2025
//---------------------------------------------------------------------------voronoi.m---------------------------------------------------------------------------
/*
TODO: write description
*/

import "symmetric_space.m" : cellBasis, facets, homogeneous_cone_point, sign_orbit, barycentre;
import "module.m" : disjointCycleDecomposition, unionEquivalenceRelations;

voronoi_data := recformat<
	perfect_points : SeqEnum,
	perfect_stabilisers : SeqEnum,
	
	neighbours : SeqEnum,
	neighbour_equiv_indices : SeqEnum,
	neighbour_equiv_witnesses : SeqEnum //takes the rep to the neighbour
>;

function buildInitialPoint(cone_data, cone_functions)
	min, min_vecs, cone_data := cone_functions`minimalVectors(cone_data`basepoint, cone_data);
	
	p := cone_data`basepoint / min;
	rank, cone_data := cone_functions`perfectionRank(p, cone_data);
	
	if rank eq Dimension(cone_data`ambient_space) then //perfect point found
		return rec<homogeneous_cone_point | point := p, minimal_vectors := min_vecs, min := min>, cone_data;
	end if;
	
	height := 1;
	min_rho_plus := Infinity();
	min_rho_minus := -Infinity();
	while true do //try to add vectors to increase rank, until reach a perfect vector
		//print height, rank;
		if height gt #cone_data`boundary_point_database then //find more vectors to try
			//print "finding points of height", height, "initial";
			Append(~cone_data`boundary_point_database, cone_functions`boundaryPoints(height, cone_data));
		end if;
	
		normal := cone_functions`cellNormal(min_vecs, cone_data);
		
		for v in cone_data`boundary_point_database[height] do
			normal_component := cone_functions`innerProduct(normal, v);
			
			if normal_component ne 0 then
				p_component := cone_functions`innerProduct(p, v);
				rho := (1-p_component) / normal_component;				
				
				if (rho gt 0 and rho lt min_rho_plus) or (rho lt 0 and rho gt min_rho_minus) then //if minvec, then we move a minimal amount in the normal (signed) direction
					candidate := p + normal * rho; //vector with minkowskiForm 1 with min_vecs and w. if minimum 1 then rank improvement
					
					if rho gt 0 then
						min_rho_plus := rho;
					else
						min_rho_minus := rho;
					end if;
					
					//print min_rho_minus, min_rho_plus;
					
					if cone_functions`isInteriorPoint(candidate, cone_data) then
						candidate_min, candidate_min_vecs, cone_data := cone_functions`minimalVectors(candidate, cone_data);
						
						if candidate_min eq 1 then
							min_vecs := candidate_min_vecs;
							p := candidate;
							
							rank, cone_data := cone_functions`perfectionRank(p, cone_data);
							if rank eq Dimension(cone_data`ambient_space) then //perfect point found
								return rec<homogeneous_cone_point | point := p, minimal_vectors := min_vecs, min := min>, cone_data;
							end if;
							
							min_rho_plus := Infinity();
							min_rho_minus := -Infinity();
						end if;
					end if;
				end if;
			end if;
		end for;		
		
		height +:= 1;
	end while;
end function;


function neighbour(p_rec, normal, cone_data, cone_functions)
	p := p_rec`point;
	min_vecs := p_rec`minimal_vectors;
	
	//fix correct choice of sign of normal
	for v in min_vecs do
		if cone_functions`innerProduct(v, normal) lt 0 then
			normal *:= -1;
			break;
		end if;
	end for;
	
	height := 1;
	min_rho := Infinity();
	
	
	if cone_data`type eq "lorentz" then
		p_signs := [Sign(p[i]) : i in [1..NumberOfColumns(p)]];
		
		sign_flip_indices := [];
		for i in [1..NumberOfColumns(p)-1] do
			if p_signs[i] ne 0 then			
				if Sign(normal[i]) eq -p_signs[i] then //can't tell for now, so have to keep checking
					Append(~sign_flip_indices, i);
				end if;
			else
				if Sign(normal[i]) ne 0 then
					p_signs[i] := Sign(normal[i]); //constructed perfect vector will have the same sign as the normal vector
				else
					p_signs[i] := 1;
					Append(~sign_flip_indices, i); //constructed perfect vector will be zero in the ith component
				end if;
			end if;
		end for;
		print #sign_flip_indices, "indices to flip";
		
		while true do
			if height gt #cone_data`boundary_point_database then //find more vectors to try
				print "\t\tneighbour: finding points of height", height;
				Append(~cone_data`boundary_point_database, cone_functions`boundaryPoints(height, cone_data));
			end if;
			
			for v in cone_data`boundary_point_database[height] do
				w := [v[i] * p_signs[i] : i in [1..NumberOfColumns(p)]];
				for x in sign_orbit(w, sign_flip_indices, cone_data) do
					normal_component := cone_functions`innerProduct(normal, x);
					
					if normal_component lt 0 then
						rho := (1-cone_functions`innerProduct(p, x)) / normal_component;
						
						if rho le min_rho then //possible candidate
							candidate := p + rho * normal;
							
							if cone_functions`isInteriorPoint(candidate, cone_data) then
								candidate_min, candidate_min_vecs, cone_data := cone_functions`minimalVectors(candidate, cone_data);
								
								if candidate_min eq 1 then //neighbour found
									return rec<homogeneous_cone_point | point := candidate, minimal_vectors := candidate_min_vecs, min := 1>, cone_data;
								end if;
							end if;
							
							min_rho := rho;
							
							i := 1;
							while i le #sign_flip_indices do
								if Sign(candidate[sign_flip_indices[i]]) eq p_signs[sign_flip_indices[i]] then //sign of neighbour agrees with p in coordinate sign_flip_indices[i]; no longer need to flip
									Remove(~sign_flip_indices, i);
									i -:= 1;
								end if;
								i +:= 1;
							end while;
						end if;
					end if;
				end for;
			end for;
			
			height +:= 1;
		end while;
	else
		while true do
			if height gt #cone_data`boundary_point_database then //find more vectors to try
				print "\t\tneighbour: finding points of height", height;
				Append(~cone_data`boundary_point_database, cone_functions`boundaryPoints(height, cone_data));
			end if;
			
			for v in cone_data`boundary_point_database[height] do
				normal_component := cone_functions`innerProduct(normal, v);
				
				if normal_component lt 0 then
					rho := (1-cone_functions`innerProduct(p, v)) / normal_component;
					
					if rho le min_rho then //possible candidate
						candidate := p + rho * normal;
						
						if cone_functions`isInteriorPoint(candidate, cone_data) then
							candidate_min, candidate_min_vecs, cone_data := cone_functions`minimalVectors(candidate, cone_data);
							
							if candidate_min eq 1 then //neighbour found
								return rec<homogeneous_cone_point | point := candidate, minimal_vectors := candidate_min_vecs, min := 1>, cone_data;
							end if;
						end if;
						
						min_rho := rho;
					end if;
				end if;
			end for;
			
			height +:= 1;
		end while;
	end if;
end function;

function voronoiData(cone)
	initial_point, cone`cone_data := buildInitialPoint(cone`cone_data, cone`cone_functions);
	
	print "initial point found:", #initial_point`minimal_vectors, "minimal vectors";
	
	perfect_point_list := [initial_point];
	//perfect_stabilisers := [cone`cone_functions`stabiliser(initial_point, cone`cone_data : special := false)];
	neighbour_list := [];
	neighbour_equiv_indices := [];
	neighbour_equiv_witnesses := [];
	
	next_to_test := 1;
	
	while next_to_test le #perfect_point_list do
		Append(~neighbour_list, []);
		Append(~neighbour_equiv_indices, []);
		Append(~neighbour_equiv_witnesses, []);
		
		//calculate equivalence classes of facets
		facet_list := facets(perfect_point_list[next_to_test]`minimal_vectors);
		print "facets calculated";
		
		facet_barycentres := [barycentre(facet) : facet in facet_list];
		
		//only consider facets up to equivalence under the cell stabiliser
		gens := cone`cone_functions`stabiliser(rec<homogeneous_cone_point | point:=barycentre(perfect_point_list[next_to_test]`minimal_vectors)>, cone`cone_data);
		print "cell stabiliser calculated";
		
		permutations := [];
		for g in gens do 
			sigma := [];
			for p in facet_barycentres do
				Append(~sigma, Index(facet_barycentres, p * g));
			end for;
			
			Append(~permutations, sigma);
		end for;
		
		cycles := [];
		indices := [];
		for sigma in permutations do
			cyc, ind := disjointCycleDecomposition(sigma);
			Append(~cycles, cyc);
			Append(~indices, ind);
		end for;
		
		orbits := unionEquivalenceRelations(cycles, indices);
		facet_reps := [o[1] : o in orbits];
		
		/*
		facet_reps := [];
		class_min_heights := [];
		unfound := [true : i in [1..#facet_list]];
		for i in [1..#facet_list] do
			if unfound[i] then
				print "will be testing facet", i;
				Append(~facet_reps, i);
				Append(~class_min_heights, facet_barycentres[i][5]);
				unfound[i] := false;
				
				for g in G do
					ind := Index(facet_barycentres, facet_barycentres[i] * g);
					if ind gt 0 then
						unfound[ind] := false;
						if facet_barycentres[i][5] lt class_min_heights[#class_min_heights] then
							print "better rep not the first one", class_min_heights[#class_min_heights], facet_barycentres[ind][5];
						end if;
					end if;
				end for;
			end if;
		end for;
		*/
		
		
		//no taking advantage of symmetry
		//facet_reps := [1..#facet_list];
		
		
		print "Facets to test:", facet_reps, "of", #facet_list;
		
		for facet_index in facet_reps do
			facet := facet_list[facet_index];
			print "Facet", facet_index, "of", #facet_list;
			normal := cone`cone_functions`cellNormal(facet, cone`cone_data);
			neighbouring_point, cone`cone_data := neighbour(perfect_point_list[next_to_test], normal, cone`cone_data, cone`cone_functions);
			print "	neighbour found";
			
			Append(~neighbour_list[#neighbour_list], neighbouring_point);
			
			new := true;
			for i in [1..#perfect_point_list] do
				//equiv, equiv_by := cone`cone_functions`equivalent(perfect_point_list[i], neighbouring_point, cone`cone_data : known_stabiliser := perfect_stabilisers[i]);
				equiv, equiv_by := cone`cone_functions`equivalent(perfect_point_list[i], neighbouring_point, cone`cone_data);
				if equiv then
					new := false;
					Append(~neighbour_equiv_indices[#neighbour_equiv_indices], i);
					Append(~neighbour_equiv_witnesses[#neighbour_equiv_witnesses], equiv_by);
					break;
				end if;
			end for;
			
			if new then
				print "\tNew class!";
				Append(~perfect_point_list, neighbouring_point);
				Append(~neighbour_equiv_indices[#neighbour_equiv_indices], #perfect_point_list);
				Append(~neighbour_equiv_witnesses[#neighbour_equiv_witnesses], MatrixRing(cone`cone_data`matrix_field, cone`cone_data`matrix_size) ! 1);
				//Append(~perfect_stabilisers, cone`cone_functions`stabiliser(neighbouring_point, cone`cone_data : special := false));
				
				print "Class", #perfect_point_list, "with", #neighbouring_point`minimal_vectors, "minimal vectors";
				print neighbouring_point`point;
			end if;
		end for;
		
		next_to_test +:= 1;
	end while;
	
	//return rec<voronoi_data | perfect_points := perfect_point_list, perfect_stabilisers := perfect_stabilisers, neighbours := neighbour_list, neighbour_equiv_indices := neighbour_equiv_indices, neighbour_equiv_witnesses := neighbour_equiv_witnesses>;
	return rec<voronoi_data | perfect_points := perfect_point_list, neighbours := neighbour_list, neighbour_equiv_indices := neighbour_equiv_indices, neighbour_equiv_witnesses := neighbour_equiv_witnesses>;
end function;

function voronoiFacets(cone)
	cone_voronoi_data := voronoiData(cone);
	return [point`minimal_vectors : point in cone_voronoi_data`perfect_points];
end function;
