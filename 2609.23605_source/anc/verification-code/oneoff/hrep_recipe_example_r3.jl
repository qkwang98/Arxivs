# hrep_recipe_example_r3.jl  --  run with: julia hrep_recipe_example_r3.jl
#
# Changelog (reverse chronological):
#   2026-09-06  Created. OSCAR/Polymake twin of hrep_recipe_example_r3.sage.
#
# Independent backend cross-check: Sage uses cddlib/PPL, OSCAR uses Polymake.
# Both give dim 4, 16 vertices, 9 facets, and identical normals and offsets for
# n = 3, a = (3,3,1), d = (0,1,2).
#
# Julia gotchas hit while writing this, recorded so the next person does not:
#   * nrows() does not accept a SubObjectIterator -- use n_vertices / n_facets.
#   * facets(R) yields AffineHalfspace objects; to get (A,b) with A x <= b use
#     halfspace_matrix_pair(facets(R)) rather than reaching into fields.
#   * a plain `ok = ok && ...` inside a for loop at top level is a SOFT SCOPE
#     assignment and silently becomes a new local; accumulate into a const array.

using Oscar
n=3; a=[binomial(n,j) for j in 1:n]; ds=[0,1,2]; N=n+maximum(ds); r=length(ds)
V(d)=[[zeros(Int,d); a[1:k]; zeros(Int,N-d-k)] for k in 1:n]
S=[convex_hull(reduce(hcat,V(d))') for d in ds]
pts=[sum(V(ds[i])[t[i]] for i in 1:r) for t in Iterators.product(ntuple(_->1:n,r)...)]
R=convex_hull(reduce(hcat,vec(pts))')
println("OSCAR (Polymake)    a=$a  d=$ds  N=$N")
println("  dim=$(dim(R))  vertices=$(n_vertices(R))  facets=$(n_facets(R))   r*n=$(r*n)")
hsup(P,u)=maximum(sum(u[i]*Rational{BigInt}(v[i]) for i in 1:N) for v in vertices(P))
A,b = halfspace_matrix_pair(facets(R))          # A x <= b, rows of A outward normals
const RES=Bool[]
println("\n  u (outward)              h_R    h_1+h_2+h_3   additive?")
for k in 1:nrows(A)
    u=[Rational{BigInt}(A[k,i]) for i in 1:N]
    hs=[hsup(P,u) for P in S]; hR=hsup(R,u)
    add=(hR==sum(hs)); push!(RES,add)
    println("  ", lpad(string(Int.(u)),22), "  ", lpad(string(hR),5), "     ", lpad(string(sum(hs)),5), "        ", add)
end
println("\n  additivity held for every facet: $(all(RES))")
