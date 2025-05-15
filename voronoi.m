//Voronoi Cohomology Library - Written by Daniel Bassett, 2025
//---------------------------------------------------------------------------voronoi.m---------------------------------------------------------------------------
/*
TODO: write description
*/

import "symmetric_space.m" : cellBasis, facets, homogeneous_cone_point;

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


function neighbour(p, normal, cone_data, cone_functions)
	_, min_vecs, cone_data := cone_functions`minimalVectors(p, cone_data);
	
	//fix correct choice of sign of normal
	for v in min_vecs do
		if cone_functions`innerProduct(v, normal) lt 0 then
			normal *:= -1;
			break;
		end if;
	end for;
	
	height := 1;
	min_rho := Infinity();
	
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
end function;

function voronoiData(cone)
	initial_point, cone`cone_data := buildInitialPoint(cone`cone_data, cone`cone_functions);
	
	print "initial point found";
	
	perfect_point_list := [initial_point];
	neighbour_list := [];
	neighbour_equiv_indices := [];
	neighbour_equiv_witnesses := [];
	
	next_to_test := 1;
	
	while next_to_test le #perfect_point_list do
		Append(~neighbour_list, []);
		Append(~neighbour_equiv_indices, []);
		Append(~neighbour_equiv_witnesses, []);
		
		facet_list := facets(perfect_point_list[next_to_test]`minimal_vectors);
		
		print #facet_list, "facets to test";
		
		count := 1;
		for facet in facet_list do
			print "Facet", count, "of", #facet_list;
			normal := cone`cone_functions`cellNormal(facet, cone`cone_data);
			neighbouring_point, cone`cone_data := neighbour(perfect_point_list[next_to_test]`point, normal, cone`cone_data, cone`cone_functions);
			print "	neighbour found";
			
			Append(~neighbour_list[#neighbour_list], neighbouring_point);
			
			new := true;
			for i in [1..#perfect_point_list] do
				equiv, equiv_by := cone`cone_functions`equivalent(perfect_point_list[i], neighbouring_point, cone`cone_data);
				if equiv then
					new := false;
					Append(~neighbour_equiv_indices[#neighbour_equiv_indices], i);
					Append(~neighbour_equiv_witnesses[#neighbour_equiv_witnesses], equiv_by);
					break;
				end if;
			end for;
			
			if new then
				Append(~perfect_point_list, neighbouring_point);
				Append(~neighbour_equiv_indices[#neighbour_equiv_indices], #perfect_point_list);
				Append(~neighbour_equiv_witnesses[#neighbour_equiv_witnesses], MatrixRing(cone`cone_data`matrix_field, cone`cone_data`matrix_size) ! 1);
				
				print "Class", #perfect_point_list, "with", #neighbouring_point`minimal_vectors, "minimal vectors";
			end if;
			
			count +:= 1;
		end for;
		
		next_to_test +:= 1;
	end while;
	
	print "Calculating stabilisers";
	stabilisers := [];
	count := 1;
	for p in perfect_point_list do
		print "\tstabilisers:",count, "of", #perfect_point_list;
		Append(~stabilisers, MatrixGroup<cone`cone_data`matrix_size, cone`cone_data`matrix_field | cone`cone_functions`stabiliser(p, cone`cone_data)>);
		count +:= 1;
	end for;
	
	return rec<voronoi_data | perfect_points := perfect_point_list, perfect_stabilisers := stabilisers, neighbours := neighbour_list, neighbour_equiv_indices := neighbour_equiv_indices, neighbour_equiv_witnesses := neighbour_equiv_witnesses>;
end function;

function voronoiFacets(cone)
	cone_voronoi_data := voronoiData(cone);
	return [point`minimal_vectors : point in cone_voronoi_data`perfect_points];
end function;
