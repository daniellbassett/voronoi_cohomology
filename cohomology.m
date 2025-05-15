//Voronoi Cohomology Library - Written by Daniel Bassett, 2025
//---------------------------------------------------------------------------cohomology.m---------------------------------------------------------------------------
/*
TODO: write description
*/

import "module.m" : invariants, action_permutation, action_matrix;

function coboundaryMap(M, complex, d) //coboundary map in degree d: from dimension d-1 cells to dimension d cells
	codim := #complex`cell_reps-d;	
	
	total_matrix := <>;
	
	for i in [1..#complex`cell_reps[codim]] do //a higher-dim cell rep, sigma
		M_sigma := invariants(M, complex`cell_rep_stabilisers[codim][i], complex`orientation_characters[codim][i]);
		coord_space := VectorSpace(M`base_field, Dimension(M_sigma));
		
		M_taus := [invariants(M, complex`cell_rep_stabilisers[codim+1][j], complex`orientation_characters[codim+1][j]) : j in [1..#complex`cell_reps[codim+1]]];
		
		sigma_matrix := <RMatrixSpace(M`base_field, Dimension(M_taus[j]), Dimension(M_sigma)) ! 0 : j in [1..#complex`cell_reps[codim+1]]>;
		
		for j in [1..#complex`facets[codim][i]] do //a facet of sigma, tau
			if #complex`facet_cell_stabiliser_cosets[codim][i][j] eq 1 then //facet stabiliser contains cell stabiliser
				index := complex`facet_equiv_indices[codim][i][j];
				gamma := complex`facet_equiv_witnesses[codim][i][j];
				
				if gamma eq 1 then
					rows := [];
					
					for k in [1..Dimension(M_taus[index])] do
						Append(~rows, coord_space ! Coordinates(M_sigma, M_taus[index].k));
					end for;
					
					orientation_factor := complex`facet_equiv_orientation[codim][i][j] * complex`facet_cell_orientation[codim][i][j];
					sigma_matrix[index] +:= orientation_factor * VerticalJoin(rows);
					//if d eq 1 then
					//	print orientation_factor * VerticalJoin(rows);
					//end if;
				else
					//print "used in degree", d;
					permutation := action_permutation(M, gamma); //for some reason gamma^-1 makes it not crash but we still get negative answers
					rows := [];
					
					for k in [1..Dimension(M_taus[index])] do
						Append(~rows, coord_space ! Coordinates(M_sigma, M_sigma ! [Eltseq(M_taus[index].k)[permutation[l]] : l in [1..#permutation]]));
					end for;
					
					orientation_factor := complex`facet_equiv_orientation[codim][i][j] * complex`facet_cell_orientation[codim][i][j];
					sigma_matrix[index] +:= orientation_factor * VerticalJoin(rows);
					//if d eq 1 then
					//	print orientation_factor * VerticalJoin(rows);
					//end if;
				end if;
			else
				//corestriction map: must sum over cosets
				//print "cores used in degree", d;
				index := complex`facet_equiv_indices[codim][i][j];
				gamma := complex`facet_equiv_witnesses[codim][i][j];
				
				M_matrix := MatrixRing(M`base_field, #M`cosets) ! 0;
				for coset in complex`facet_cell_stabiliser_cosets[codim][i][j] do
					M_matrix +:= action_matrix(M, gamma * coset);
				end for;
				
				orientation_factor := complex`facet_equiv_orientation[codim][i][j] * complex`facet_cell_orientation[codim][i][j];
				M_matrix *:= orientation_factor;///#complex`facet_cell_stabiliser_cosets[codim][i][j];
				
				rows_uncoordinated := Rows(BasisMatrix(M_taus[index]) * M_matrix);
				rows := [];
				for k in [1..Dimension(M_taus[index])] do
					Append(~rows, coord_space ! Coordinates(M_sigma, M_sigma ! rows_uncoordinated[k]));
				end for;
				
				//print VerticalJoin(rows), i, index;
				sigma_matrix[index] +:= VerticalJoin(rows);
			end if;
		end for;
		
		Append(~total_matrix, VerticalJoin(sigma_matrix));
	end for;
	
	return Matrix(HorizontalJoin(total_matrix));
end function;

function cohomology(M, complex, degrees, with_torsion)
	required_coboundary_degrees := [];
	for d in degrees do
		if d gt 0 then
			Append(~required_coboundary_degrees, d);
		end if;
		
		if d+1 lt #complex`cell_reps then
			Append(~required_coboundary_degrees, d+1);
		end if;
	end for;
	
	required_coboundary_degrees := Sort(SetToSequence(SequenceToSet(required_coboundary_degrees)));
	
	coboundary_ranks := [];
	coboundary_nullities := [];
	coboundary_rows := [];
	coboundary_columns := [];
	coboundary_divisors := [];
	coboundary_maps := [**];

	for d in required_coboundary_degrees do
		map := coboundaryMap(M, complex, d);
		
		Append(~coboundary_ranks, Rank(map));
		Append(~coboundary_rows, NumberOfRows(map));
		Append(~coboundary_columns, NumberOfColumns(map));
		
		Append(~coboundary_maps, map);
		//print map;
		
		if with_torsion then
			map := ChangeRing(map, Integers());
			Append(~coboundary_divisors, ElementaryDivisors(map));
		end if;
	end for;
	map := Integers() ! 0;
	
	data := [];
	if with_torsion then
		for d in degrees do
			if d eq 0 then
				Append(~data, [coboundary_rows[1] - coboundary_ranks[1], 1]);
			elif d+1 ne #complex`cell_reps then
				i := Index(required_coboundary_degrees, d);
				Append(~data, [coboundary_rows[i+1] - coboundary_ranks[i+1] - coboundary_ranks[i], &*coboundary_divisors[i]]);
				
				//print coboundary_maps[i] * coboundary_maps[i+1] eq 0;
			else
				Append(~data, [coboundary_columns[#coboundary_columns] - coboundary_ranks[#coboundary_ranks], &*coboundary_divisors[#coboundary_divisors]]);
			end if;
		end for;
	else
		for d in degrees do
			if d eq 0 then
				Append(~data, coboundary_rows[1] - coboundary_ranks[1]);
				//print "ker:", coboundary_rows[1], "im:", coboundary_ranks[1];
			elif d+1 ne #complex`cell_reps then
				i := Index(required_coboundary_degrees, d);
				Append(~data, coboundary_rows[i+1] - coboundary_ranks[i+1] - coboundary_ranks[i]);
				//print "ker:", coboundary_rows[i+1] - coboundary_ranks[i+1], "im:", coboundary_ranks[i];
				
				//print coboundary_maps[i] * coboundary_maps[i+1] eq 0;
			else
				Append(~data, coboundary_columns[#coboundary_columns] - coboundary_ranks[#coboundary_ranks]);
				//print "ker:", coboundary_columns[#coboundary_columns], "im:", coboundary_ranks[#coboundary_ranks];
			end if;
		end for;
	end if;

	return data;
end function;
