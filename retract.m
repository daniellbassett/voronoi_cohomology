//Voronoi Cohomology Library - Written by Daniel Bassett, 2025
//---------------------------------------------------------------------------retract.m---------------------------------------------------------------------------
/*
TODO: write description
*/

import "symmetric_space.m" : facets, barycentre, homogeneous_cone_point;
import "equivariant_complex.m" : generateComplex;

function tessellation(top_cells)
	cells := [top_cells];
	
	//generate cells
	cell_vertex_count := #cells[#cells][1];
	while cell_vertex_count gt 1 do
		Append(~cells, []);
		for cell in cells[#cells-1] do //find facets of all cells of current lowest calculated dimension
			cell_facets := facets(cell);
			
			for facet in cell_facets do
				if not facet in cells[#cells] then
					Append(~cells[#cells], facet);
				end if;
			end for;
		end for;
		
		cell_vertex_count := #cells[#cells][1];
	end while;
	
	cell_facet_indices := [];
	codim := 1; //actually codim+1
	
	//calculate cell inclusions
	while codim lt #cells do
		Append(~cell_facet_indices, []);
		
		for high_cell in cells[codim] do
			Append(~cell_facet_indices[#cell_facet_indices], []);
			
			for i in [1..#cells[codim+1]] do
				if IsSubsequence(cells[codim+1][i], high_cell : Kind := "Setwise") then
					Append(~cell_facet_indices[#cell_facet_indices][#cell_facet_indices[#cell_facet_indices]], i);
				end if;
			end for;
		end for;
		
		codim +:= 1;
	end while;
	
	return cells, cell_facet_indices;
end function;

function retractTopCells(voronoi_data, cone_data, cone_functions);
	voronoi_top_cells := [point`minimal_vectors : point in voronoi_data`perfect_points];
	cells, cell_facet_indices := tessellation(voronoi_top_cells);
	
	vertices := [[barycentre(cell) : cell in cells[i]] : i in [1..#cells]];
	retract_top_cells := [];
	
	index_vector := [1 : i in [1..#cell_facet_indices]]; //flag of topdim, codim 1, ..., dim 2, dim 1. no dim 0 since we want cells without ideal vertices
	while index_vector[1] le #cells[1] do
		flag_indices := [index_vector[1]];
		while #flag_indices lt #cell_facet_indices do
			Append(~flag_indices, cell_facet_indices[#flag_indices][flag_indices[#flag_indices]][index_vector[#flag_indices+1]]);
		end while;
		
		Append(~retract_top_cells, [vertices[j][flag_indices[j]] : j in [1..#flag_indices]]); //top cell from flag
		
		//next top cell
		index_vector[#index_vector] +:= 1;
		for i in [#index_vector..2 by -1] do
			if index_vector[i] gt #cell_facet_indices[i-1][flag_indices[i-1]] then
				index_vector[i] := 1;
				index_vector[i-1] +:= 1;
			end if;
		end for;
	end while;
	
	print "retract:", #retract_top_cells, "top_cells calculated";
	
	retract_top_reps := [];
	last := 1000;
	for i in [1..#retract_top_cells] do
		if i ge last then
			print last;
			last +:= 1000;
		end if;
		
		new := true;
		for rep in retract_top_reps do
			if cone_functions`equivalent(rec<homogeneous_cone_point | point := barycentre(rep), minimal_vectors := rep>, rec<homogeneous_cone_point | point := barycentre(retract_top_cells[i]), minimal_vectors := retract_top_cells[i]>, cone_data : cone_voronoi_data := voronoi_data) then
				new := false;
				break;
			end if;
		end for;
		
		if new then
			Append(~retract_top_reps, retract_top_cells[i]);
		end if;
	end for;
	
	return retract_top_reps;
end function;


function retract(voronoi_data, cone);
	top_cells := retractTopCells(voronoi_data, cone`cone_data, cone`cone_functions);
	print "top cells generated";
	print #top_cells;
	return generateComplex(top_cells, cone : cone_voronoi_data := voronoi_data);
end function;
