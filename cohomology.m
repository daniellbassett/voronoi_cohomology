//Voronoi Cohomology Library - Written by Daniel Bassett, 2025
//---------------------------------------------------------------------------cohomology.m---------------------------------------------------------------------------
/*
TODO: write description
*/

import "symmetric_space.m" : barycentre;
import "module.m" : invariants, action_permutation, action_matrix;

function coboundaryMap(M, complex, d : verbosity := 0) //coboundary map in degree d: from dimension d-1 cells to dimension d cells
	codim := #complex`cell_reps-d;	
	
	total_matrix := <>;
	
	M_taus := [invariants(M, complex`cell_rep_stabilisers[codim+1][j], complex`orientation_characters[codim+1][j] : cartesian := M`cartesian) : j in [1..#complex`cell_reps[codim+1]]];
	for i in [1..#complex`cell_reps[codim]] do //a higher-dim cell rep, sigma
		if verbosity gt 0 then
			print "\t\tcoboundary: Cell", i, "of", #complex`cell_reps[codim];
		end if;
		
		M_sigma := invariants(M, complex`cell_rep_stabilisers[codim][i], complex`orientation_characters[codim][i] : cartesian := M`cartesian);
		coord_space := VectorSpace(M`base_field, Dimension(M_sigma));
		
		sigma_matrix := <RMatrixSpace(M`base_field, Dimension(M_taus[j]), Dimension(M_sigma)) ! 0 : j in [1..#complex`cell_reps[codim+1]]>;
		
		facet_barycentres := [barycentre(facet) : facet in complex`facets[codim][i]];
		for j in [1..#complex`facets[codim][i]] do //a facet of sigma, tau
			//check if facet is equivalent under Gamma_sigma to a previous facet
			if #complex`cell_rep_stabilisers[codim][i] gt 0 then
				equiv := false;
				G := MatrixGroup<NumberOfColumns(complex`cell_rep_stabilisers[codim][i][1]), Parent(complex`cell_rep_stabilisers[codim][i][1][1,1]) | complex`cell_rep_stabilisers[codim][i]>;
				for g in G do
					gIndex := Index(facet_barycentres, facet_barycentres[j] * g);
					
					if gIndex lt j then
						equiv := true;
						break;
					end if;
				end for;
				
				if equiv then
					if verbosity gt 1 then
						print"\t\t\tcoboundary: Facet", j, "of", #complex`facets[codim][i], "(skipping)";
					end if;
					
					continue;
				end if;
			end if;
			
			
			if #complex`facet_cell_stabiliser_cosets[codim][i][j] eq 1 then //facet stabiliser contains cell stabiliser
				index := complex`facet_equiv_indices[codim][i][j];
				if Dimension(M_taus[index]) eq 0 then
					continue;
				end if;
						
				gamma := complex`facet_equiv_witnesses[codim][i][j];
				
				if gamma eq 1 then
					if verbosity gt 1 then
						print "\t\t\tcoboundary: Facet", j, "of", #complex`facets[codim][i], "(standard)";
					end if;
					
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
					if verbosity gt 1 then
						print "\t\t\tcoboundary: Facet", j, "of", #complex`facets[codim][i], "(permutation)";
					end if;
					
					permutation := action_permutation(M, gamma : cartesian := M`cartesian);
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
				if verbosity gt 1 then
					print "\t\t\tcoboundary: Facet", j, "of", #complex`facets[codim][i], "(corestriction)";
				end if;
				
				index := complex`facet_equiv_indices[codim][i][j];
				if Dimension(M_taus[index]) eq 0 then
					continue;
				end if;
								
				gamma := complex`facet_equiv_witnesses[codim][i][j];
				
				M_matrix := MatrixRing(M`base_field, #M`cosets) ! 0;
				for k in [1..#complex`facet_cell_stabiliser_cosets[codim][i][j]] do
					if verbosity gt 2 then
						print "\t\t\t\tcorestriction: Coset", k, "of", #complex`facet_cell_stabiliser_cosets[codim][i][j];
					end if;
					M_matrix +:= action_matrix(M, gamma * complex`facet_cell_stabiliser_cosets[codim][i][j][k], complex`coset_character[codim][i][j][k] : cartesian := M`cartesian);
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
	
	mat := Matrix(HorizontalJoin(total_matrix));
	return mat;
end function;

function cohomology(M, complex, degrees, with_torsion : verbosity := 0)
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
	//coboundary_maps := [**];

	for d in required_coboundary_degrees do
		if verbosity gt 0 then
			print "\tcohomology: coboundary degree", d;
		end if;
		
		codim := #complex`cell_reps-d;
		if #complex`cell_reps[codim] eq 0 or #complex`cell_reps[codim+1] eq 0 then
			Append(~coboundary_ranks, 0);
			
			rows := 0;
			columns := 0;
			
			for i in [1..#complex`cell_reps[codim]] do
				columns +:= Dimension(invariants(M, complex`cell_rep_stabilisers[codim][i], complex`orientation_characters[codim][i] : cartesian := M`cartesian));
			end for;
			
			for i in [1..#complex`cell_reps[codim+1]] do
				rows +:= Dimension(invariants(M, complex`cell_rep_stabilisers[codim+1][i], complex`orientation_characters[codim+1][i] : cartesian := M`cartesian));
			end for;
			
			Append(~coboundary_rows, rows);
			Append(~coboundary_columns, columns);
			
			Append(~coboundary_divisors, [1]);
		else
			map := coboundaryMap(M, complex, d : verbosity := verbosity);
			
			Append(~coboundary_ranks, Rank(map));
			Append(~coboundary_rows, NumberOfRows(map));
			Append(~coboundary_columns, NumberOfColumns(map));
			
			//Append(~coboundary_maps, map);
			//print map;
			
			if with_torsion then
				map := ChangeRing(map, Integers());
				Append(~coboundary_divisors, ElementaryDivisors(map));
			end if;
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

function homology(M, complex, degrees, with_torsion)
	required_boundary_degrees := [];
	for d in degrees do
		if d gt 0 then
			Append(~required_boundary_degrees, d);
		end if;
		
		if d+1 lt #complex`cell_reps then
			Append(~required_boundary_degrees, d+1);
		end if;
	end for;
	
	boundary_ranks := [];
	boundary_nullities := [];
	boundary_rows := [];
	boundary_columns := [];
	boundary_divisors := [];
	
	boundary_maps := [**];
	
	required_boundary_degrees := Sort(SetToSequence(SequenceToSet(required_boundary_degrees)));	
	for d in required_boundary_degrees do
		print "\thomology: boundary degree", d;
		codim := #complex`cell_reps-d;
		
		if #complex`cell_reps[codim] eq 0 or #complex`cell_reps[codim+1] eq 0 then
			Append(~boundary_ranks, 0);
			
			rows := 0;
			columns := 0;
			
			for i in [1..#complex`cell_reps[codim]] do
				rows +:= Dimension(invariants(M, complex`cell_rep_stabilisers[codim][i], complex`orientation_characters[codim][i] : cartesian := M`cartesian));
			end for;
			
			for i in [1..#complex`cell_reps[codim+1]] do
				columns +:= Dimension(invariants(M, complex`cell_rep_stabilisers[codim+1][i], complex`orientation_characters[codim+1][i] : cartesian := M`cartesian));
			end for;
			
			Append(~boundary_rows, rows);
			Append(~boundary_columns, columns);
			
			Append(~boundary_divisors, [1]);
			
			Append(~boundary_maps, 0);
		else
			map := Transpose(coboundaryMap(M, complex, d : verbosity := 10));
			
			Append(~boundary_ranks, Rank(map));
			Append(~boundary_rows, NumberOfRows(map));
			Append(~boundary_columns, NumberOfColumns(map));
			
			if with_torsion then
				map := ChangeRing(map, Integers());
				Append(~boundary_divisors,  ElementaryDivisors(map));
			end if;
			
			Append(~boundary_maps, map);
		end if;
	end for;
	
	map := Integers() ! 0;
	
	data := [];
	if with_torsion then
		for d in degrees do
			if d eq 0 then
				Append(~data, [boundary_columns[1] - boundary_ranks[1], &*boundary_divisors[1]]);
			elif d+1 ne #complex`cell_reps then
				i := Index(required_boundary_degrees, d);
				Append(~data, [boundary_rows[i] - boundary_ranks[i] - boundary_ranks[i+1], &*boundary_divisors[i+1]]);
				
				if boundary_maps[i+1] * boundary_maps[i] ne 0 then
					print "not a chain complex :(";
				end if;
			else
				Append(~data, [boundary_rows[#boundary_rows] - boundary_ranks[#boundary_ranks], 1]);
			end if;
		end for;
	else
		for d in degrees do
			if d eq 0 then
				Append(~data, boundary_columns[1] - boundary_ranks[1]);
			elif d+1 ne #complex`cell_reps then
				i := Index(required_boundary_degrees, d);
				Append(~data, boundary_rows[i] - boundary_ranks[i] - boundary_ranks[i+1]);
			else
				Append(~data, boundary_rows[#boundary_rows] - boundary_ranks[#boundary_ranks]);
			end if;
		end for;
	end if;

	return data;
end function;
