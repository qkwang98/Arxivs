# Changelog (reverse chronological):
# 2026-08-01 - Claude: switched from plain comma-lines to JSON (via JSON3, now a direct
#   dependency of this project's Julia environment -- added at Jan's request once he learned
#   JSON3 was already cached on disk at 524K, a transitive Oscar dependency, so registering it
#   cost nothing). Output now mirrors parameter_space_n5d1.py's Sage output structure field for
#   field, including the same data-driven generic/special labeling, and pads f_vector with a
#   leading/trailing 1 to match Sage's f_vector convention -- see the module docstring.
# 2026-08-01 - Claude: created this file. Julia/Oscar counterpart to parameter_space_n5d1.py,
#   consuming the SAME shared point list so results are directly comparable against the Sage run
#   rather than relying on cross-language RNG parity.

"""
Julia/Oscar counterpart to parameter_space_n5d1.py's random-sampling experiment. Reads a shared
point list (produced by that file's write_random_points), computes f-vectors via Oscar, and
writes results to ../runs/ as JSON, mirroring the Sage output structure. Run as:

    julia parameter_space_n5d1.jl ../runs/paramspace_n5_d1_points_seed3_N500.json

Note on f-vector comparability: Oscar's `f_vector` omits the trivial empty-face/whole-polytope
entries that Sage's `Polyhedron.f_vector()` includes (Sage: (1, v0, v1, ..., v_{dim-1}, 1); Oscar:
(v0, v1, ..., v_{dim-1})) -- confirmed by direct comparison for a=(1,2,3,4,5): Sage gives
(1,16,45,55,34,10,1), Oscar gives [16,45,55,34,10]. This file pads Oscar's f_vector with a
leading/trailing 1 before writing it out, so both languages' JSON output has an f_vector field
with literally the same meaning -- compare_n5d1_tandem.py no longer needs to know about the
discrepancy.
"""

include("right_angle_simplex.jl")
using JSON3

const D = 1

function job_fvector(a::Vector{Int})
    R = right_angle_minkowski_sum(a, [0, D])
    return vcat([1], Int.(f_vector(R)), [1])  # match Sage's f_vector convention, see docstring
end

function run_on_points(points_path::String)
    data = JSON3.read(read(points_path, String))
    points = [Vector{Int}(a) for a in data.points]

    t0 = time()
    results = [(a, job_fvector(a)) for a in points]
    elapsed = time() - t0
    println("$(length(results)) points: $(round(elapsed, digits=1))s")

    counts = Dict{Vector{Int},Int}()
    for (_, fv) in results
        counts[fv] = get(counts, fv, 0) + 1
    end
    majority_fv = argmax(counts)
    distinct = sort(collect(counts), by = kv -> -kv[2])
    println("distinct f-vectors: ", [c for (_, c) in distinct])

    entries = [
        Dict("a" => a, "f_vector" => fv,
             "case" => fv == majority_fv ? "generic case" : "special case")
        for (a, fv) in results
    ]
    out = Dict(
        "_description" => "n=5, d=1 parameter-space exploration (Julia/Oscar), from $(basename(points_path)). " *
                           "Part of the \"fun, not important\" a-space investigation following " *
                           "n=4,d=1 (wall a2*a4=a3^2) -- see LOGBOOK.md 2026-08-01.",
        "n" => 5, "d" => D, "n_points" => length(results),
        "distinct_f_vectors" => [Dict("f_vector" => fv, "count" => c) for (fv, c) in distinct],
        "points" => entries,
    )

    outdir = dirname(points_path)
    out_path = joinpath(outdir, replace(basename(points_path), "points" => "results_julia"))
    open(out_path, "w") do io
        JSON3.write(io, out)
    end
    println("wrote $out_path")
    return out_path
end

if abspath(PROGRAM_FILE) == @__FILE__
    length(ARGS) != 1 && error("usage: julia parameter_space_n5d1.jl <points_file>")
    run_on_points(ARGS[1])
end
