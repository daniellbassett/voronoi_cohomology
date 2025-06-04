//Voronoi Cohomology Library - Written by Daniel Bassett, 2025
//---------------------------------------------------------------------------equivariant_complex.m---------------------------------------------------------------------------
/*
TODO: write description
*/

import "symmetric_space.m" : barycentre, cellBasis, facets, homogeneous_cone_point;
import "voronoi.m" : voronoi_data;

equivariant_complex := recformat<
	//Data about cells
	cell_reps : SeqEnum,
	cell_rep_stabilisers : SeqEnum,
	orientation_characters : SeqEnum,	
	
	//Data about facets
	facets : SeqEnum,
	facet_equiv_indices : SeqEnum,
	facet_equiv_witnesses : SeqEnum,
	facet_equiv_orientation : SeqEnum, //whether a facet is compatibly-oriented with its equivalent representative
	facet_cell_orientation : SeqEnum, //whether a facet is compatibly-oriented with its containing cell
	facet_stabilisers : SeqEnum,
	facet_cell_stabiliser_cosets : SeqEnum,
	coset_character : SeqEnum
>;

function right_cosets(H, G) //finds a transversal for the right cosets of H in G
	transversal := [];
	coset_union := [];
	
	for g in G do
		if g notin coset_union then
			Append(~transversal, g);
			
			for h in H do
				Append(~coset_union, h*g);
			end for;
		end if;
	end for;
	
	return transversal;
end function;


function intersection(H, K) //finds the intersection of two subgroups
	cap := [];
	
	for h in H do
		if h in K then
			Append(~cap, h);
		end if;
	end for;
	
	return cap;
end function;

function cellRepresentatives(top_cells, cone_data, cone_functions, cone_voronoi_data)
	//generate all cell reps from top_cells
	cell_reps := [top_cells];
	
	cell_facets := [];
	facet_equiv_indices := [];
	facet_equiv_witnesses := [];
	
	vertex_count := #cell_reps[1][1];
	while vertex_count gt 1 do
		print "retract:", vertex_count, "vertices";
		//generate facets of previous dimension cells
		Append(~cell_facets, []);
		
		for rep in cell_reps[#cell_reps] do
			facet_list := facets(rep);
			interior_facet_list := [];
			
			for facet in facet_list do
				if cone_functions`isInteriorPoint(barycentre(facet), cone_data) then
					Append(~interior_facet_list, facet);
				end if;
			end for;
			
			Append(~cell_facets[#cell_facets], interior_facet_list);
		end for;
		
		//find representatives for the cells in the new dimension
		Append(~cell_reps, []);
		Append(~facet_equiv_indices, []);
		Append(~facet_equiv_witnesses, []);
		
		for higher_cell_facets in cell_facets[#cell_facets] do
			Append(~facet_equiv_indices[#facet_equiv_indices], []);
			Append(~facet_equiv_witnesses[#facet_equiv_indices], []);
			
			for facet in higher_cell_facets do				
				if facet in cell_reps[#cell_reps] then
					Append(~facet_equiv_indices[#facet_equiv_indices][#facet_equiv_indices[#facet_equiv_indices]], Index(cell_reps[#cell_reps], facet));
					Append(~facet_equiv_witnesses[#facet_equiv_witnesses][#facet_equiv_witnesses[#facet_equiv_witnesses]], MatrixRing(cone_data`matrix_field, cone_data`matrix_size) ! 1);
				else
					new_class := true;
					
					if vertex_count gt 2 then
						for i in [1..#cell_reps[#cell_reps]] do
							equiv, equivBy := cone_functions`equivalent(rec<homogeneous_cone_point | point := barycentre(cell_reps[#cell_reps][i]), minimal_vectors := cell_reps[#cell_reps][i]>, rec<homogeneous_cone_point | point := barycentre(facet), minimal_vectors := facet>, cone_data : cone_voronoi_data := cone_voronoi_data);
							
							if equiv then
								new_class := false;
								
								Append(~facet_equiv_indices[#facet_equiv_indices][#facet_equiv_indices[#facet_equiv_indices]], i);
								Append(~facet_equiv_witnesses[#facet_equiv_witnesses][#facet_equiv_witnesses[#facet_equiv_witnesses]], equivBy);
								
								break;
							end if;
						end for;
					elif cone_functions`isInteriorPoint(facet[1], cone_data) then
						for i in [1..#cell_reps[#cell_reps]] do
							equiv, equivBy := cone_functions`equivalent(rec<homogeneous_cone_point | point := barycentre(cell_reps[#cell_reps][i]), minimal_vectors := cell_reps[#cell_reps][i]>, rec<homogeneous_cone_point | point := barycentre(facet), minimal_vectors := facet>, cone_data : cone_voronoi_data := cone_voronoi_data);
							
							if equiv then
								new_class := false;
								
								Append(~facet_equiv_indices[#facet_equiv_indices][#facet_equiv_indices[#facet_equiv_indices]], i);
								Append(~facet_equiv_witnesses[#facet_equiv_witnesses][#facet_equiv_witnesses[#facet_equiv_witnesses]], equivBy);
								
								break;
							end if;
						end for;
					else
						new_class := false;
					end if;
					
					
					if new_class then
						Append(~cell_reps[#cell_reps], facet);
						
						Append(~facet_equiv_indices[#facet_equiv_indices][#facet_equiv_indices[#facet_equiv_indices]], #cell_reps[#cell_reps]);
						Append(~facet_equiv_witnesses[#facet_equiv_witnesses][#facet_equiv_witnesses[#facet_equiv_witnesses]], MatrixRing(cone_data`matrix_field, cone_data`matrix_size) ! 1);
					end if;
				end if;
			end for;
		end for;
		
		if vertex_count gt 2 then
			vertex_count := #cell_reps[#cell_reps][1];
		else
			vertex_count := 1;
		end if;
	end while;
	
	return cell_reps, cell_facets, facet_equiv_indices, facet_equiv_witnesses;
end function;

function orientationCompatibility(orientable_reps, orientable_facets, orientable_equiv_indices, orientable_equiv_witnesses, cone_data, cone_functions)
	facet_equiv_compatibility := [];
	facet_cell_compatibility := [];
	
	for i in [1..#orientable_reps] do
		Append(~facet_equiv_compatibility, []);
		Append(~facet_cell_compatibility, []);
		
		for j in [1..#orientable_reps[i]] do
			Append(~facet_equiv_compatibility[i], []);
			Append(~facet_cell_compatibility[i], []);
			
			if i lt #orientable_reps and #orientable_reps[i+1] gt 0 then 
				for k in [1..#orientable_facets[i][j]] do				
					Append(~facet_cell_compatibility[i][j], cone_functions`compatibleInducedCellOrientation(cellBasis(orientable_facets[i][j][k], cone_data), cellBasis(orientable_reps[i][j], cone_data)));
					Append(~facet_equiv_compatibility[i][j], cone_functions`compatibleCellOrientation(cellBasis(orientable_reps[i+1][orientable_equiv_indices[i][j][k]], cone_data), cellBasis(orientable_facets[i][j][k], cone_data), orientable_equiv_witnesses[i][j][k], cone_data));
				end for;
			end if;
		end for;
	end for;
	
	return facet_equiv_compatibility, facet_cell_compatibility;
end function;

function stabilisers(orientable_reps, orientable_facets, cone_data, cone_functions : cone_voronoi_data := rec<voronoi_data | >)
	cell_rep_stabilisers := [];
	orientation_characters := [];
	
	facet_stabilisers := [];
	facet_cell_stabiliser_cosets := [];
	coset_character := [];
	
	for i in [1..#orientable_reps] do
		Append(~cell_rep_stabilisers, []);
		Append(~orientation_characters, []);
		Append(~facet_stabilisers, []);
		Append(~facet_cell_stabiliser_cosets, []);
		Append(~coset_character, []);
		
		for j in [1..#orientable_reps[i]] do
			Append(~cell_rep_stabilisers[i], cone_functions`stabiliser(rec<homogeneous_cone_point | point := barycentre(orientable_reps[i][j]), minimal_vectors := orientable_reps[i][j]>, cone_data : cone_voronoi_data := cone_voronoi_data));
			
			Append(~orientation_characters[i], []);
			for gamma in cell_rep_stabilisers[i][j] do
				Append(~orientation_characters[i][j], cone_functions`compatibleCellOrientation(cellBasis(orientable_reps[i][j], cone_data), cellBasis(orientable_reps[i][j], cone_data), gamma, cone_data));
			end for;
			
			Append(~facet_stabilisers[i], []);
			Append(~facet_cell_stabiliser_cosets[i], [**]);
			Append(~coset_character[i], []);
			
			if i lt #orientable_reps then	
				for k in [1..#orientable_facets[i][j]] do
					Append(~facet_stabilisers[i][j], cone_functions`stabiliser(rec<homogeneous_cone_point | point := barycentre(orientable_facets[i][j][k]), minimal_vectors := orientable_facets[i][j][k]>, cone_data : cone_voronoi_data := cone_voronoi_data, optimised_generators := false));
					
					cell_stab := MatrixGroup<cone_data`matrix_size, cone_data`matrix_field | cell_rep_stabilisers[i][j]>;
					facet_stab := MatrixGroup<cone_data`matrix_size, cone_data`matrix_field | facet_stabilisers[i][j][k]>;
					
					cap := intersection(cell_stab, facet_stab);
					
					Append(~facet_cell_stabiliser_cosets[i][j], [Matrix(m) : m in right_cosets(cap, cell_stab)]);
					Append(~coset_character[i][j], []);
					for g in facet_cell_stabiliser_cosets[i][j][k] do
						Append(~coset_character[i][j][k], cone_functions`compatibleCellOrientation(cellBasis(orientable_reps[i][j], cone_data), cellBasis(orientable_reps[i][j], cone_data), g, cone_data));
					end for;
				end for;
			end if;
		end for;
	end for;
	
	return cell_rep_stabilisers, facet_stabilisers, facet_cell_stabiliser_cosets, orientation_characters, coset_character;
end function;

function generateComplex(top_cells, cone : cone_voronoi_data := rec<voronoi_data | >)
	cell_reps, cell_facets, facet_equiv_indices, facet_equiv_witnesses := cellRepresentatives(top_cells, cone`cone_data, cone`cone_functions, cone_voronoi_data);

	facet_equiv_compatibility, facet_cell_compatibility := orientationCompatibility(cell_reps, cell_facets, facet_equiv_indices, facet_equiv_witnesses, cone`cone_data, cone`cone_functions);
	
	cell_rep_stabilisers, facet_stabilisers, facet_cell_stabiliser_cosets, orientation_characters, coset_character := stabilisers(cell_reps, cell_facets, cone`cone_data, cone`cone_functions : cone_voronoi_data := cone_voronoi_data);
	
	return rec<equivariant_complex | 
		cell_reps := cell_reps,
		cell_rep_stabilisers := cell_rep_stabilisers,
		orientation_characters := orientation_characters,
		
		facets := cell_facets,
		facet_equiv_indices := facet_equiv_indices,
		facet_equiv_witnesses := facet_equiv_witnesses,
		facet_equiv_orientation := facet_equiv_compatibility,
		facet_cell_orientation := facet_cell_compatibility,
		facet_stabilisers := facet_stabilisers,
		facet_cell_stabiliser_cosets := facet_cell_stabiliser_cosets,
		coset_character := coset_character>;
end function;
