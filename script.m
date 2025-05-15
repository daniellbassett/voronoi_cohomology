//Voronoi Cohomology Library - Written by Daniel Bassett, 2025
//---------------------------------------------------------------------------script.m---------------------------------------------------------------------------
/*
This is the main file for writing a script using the library. The library provides functions to calculate Voronoi tessellations of homogeneous cones,
a cell decomposition of a deformation retract of the cones, and the cohomology of arithmetic groups acting on these cones, in a variety of situations.

type determines which sort of homogeneous cone and modules will be used in calculations. Options are:
	- real (GL_n(R))
	- complex (GL_n(C))
	- hamiltonian (GL_n(H))
	- lorentz (SO(n,1))


*/

//library functions available for use in script
import "symmetric_space.m" : realCone, complexCone, hamiltonianCone, lorentzCone;
import "voronoi.m" : voronoiData, voronoiFacets;
import "equivariant_complex.m" : generateComplex;
import "retract.m" : retract;
import "module.m" : lorentzGamma0Module, bianchiGamma0Module;
import "cohomology.m" : cohomology;

//----------Lorentz example----------
n := 4;
q := [1,1,1,1];

C := lorentzCone(n,q);
voronoi_data := voronoiData(C);
r := retract(voronoi_data, C);

for p in [1,3,5,7,11,13] do
	print "level", p;
	M := lorentzGamma0Module(Rationals(), p, C);
	print cohomology(M, r, [0,1,2,3], true);
end for;
