# kozlov_facet_list_crosscheck.jl  --  run with: julia kozlov_facet_list_crosscheck.jl
#
# Changelog (reverse chronological):
#   2026-09-06  Created. OSCAR/Polymake cross-check (independent of Sage's
#               cddlib/PPL) of the explicit facet list for conj-kozlov-facets:
#               for Kozlov a and strictly increasing shifts with gaps <= n-1,
#               the facet normals of R, mod lineality e(1) and positive scaling,
#               are claimed to be exactly
#                 e(2);  e(d(p)+j+1)/a(j+1)-e(d(p)+j)/a(j) for p=1..r, j=2..n-1;
#                 -e(N);  -e(d(p)+1) and +e(d(p-1)+n+1) for p=2..r.
#               See working-notes/conj-kozlov-facets-attempt.org.
#
# Julia gotchas (from hrep_recipe_example_r3.jl): n_facets not nrows on
# iterators; halfspace_matrix_pair for (A,b); no soft-scope assignments in
# top-level loops (accumulate into a const array).

using Oscar

function primitive(u::Vector{Rational{BigInt}})
    den = lcm([denominator(x) for x in u if x != 0])
    v = [BigInt(x*den) for x in u]
    g = gcd([x for x in v if x != 0])
    return [x ÷ g for x in v]
end

function predicted(n, a, ds)
    r = length(ds); N = n + maximum(ds)
    e(c) = begin v = zeros(Rational{BigInt}, N); v[c] = 1; v end
    L = Vector{Vector{BigInt}}()
    push!(L, primitive(e(2)))
    for p in 1:r, j in 2:n-1
        push!(L, primitive(e(ds[p]+j+1).//a[j+1] .- e(ds[p]+j).//a[j]))
    end
    push!(L, primitive(-e(N)))
    for p in 2:r
        push!(L, primitive(-e(ds[p]+1)))
        push!(L, primitive(e(ds[p-1]+n+1)))
    end
    return Set(L)
end

const RESULTS = Bool[]
for (n, ds) in [(4,[0,1,3]), (5,[0,2,3]), (4,[0,1,2,3]), (5,[0,4,8]), (6,[0,2,5])]
    a = [binomial(n,j) for j in 1:n]
    N = n + maximum(ds); r = length(ds)
    V(d) = [[zeros(Int,d); a[1:k]; zeros(Int,N-d-k)] for k in 1:n]
    pts = [sum(V(ds[i])[t[i]] for i in 1:r)
           for t in Iterators.product(ntuple(_->1:n, r)...)]
    R = convex_hull(reduce(hcat, vec(pts))')
    A, b = halfspace_matrix_pair(facets(R))
    actual = Set(primitive([Rational{BigInt}(A[k,i]) for i in 1:N])
                 for k in 1:n_facets(R))
    pred = predicted(n, a, ds)
    ok = (actual == pred) && (n_facets(R) == r*n)
    push!(RESULTS, ok)
    println("n=$n d=$ds  dim=$(dim(R)) facets=$(n_facets(R)) rn=$(r*n)  LIST MATCH: $ok")
    if !ok
        println("  actual-only:    ", collect(setdiff(actual, pred)))
        println("  predicted-only: ", collect(setdiff(pred, actual)))
    end
end
println("\nOSCAR cross-check, all matched: $(all(RESULTS))")
