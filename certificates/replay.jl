using QuickEnv
using SHA

include("cases.jl")
include("encoding.jl")
include("enclosure.jl")
include("eager.jl")
include("cuts.jl")
include("angular.jl")
include("darts.jl")

function write_formula(io, branch, mode)
    mode in ("base","strong","dart","angular-0-8","angular-0-0") || error("Unknown encoding $mode")
    angular = startswith(mode,"angular-")
    masks = witnessmasks(branch)
    if angular
        fields = split(mode,'-')
        extra = parse(Int,fields[3])
        small = witnessmasks(branch;augment=false)
        add = setdiff(masks,small)
        masks = sort!(union(small,first(add,min(extra,length(add)))))
    end
    enc = geometry(branch,masks,io)
    structural(enc)
    halfplane(enc)
    if mode=="strong"
        allpathcuts(enc)
        triangles(enc;alltri=true)
    else
        twohop(enc)
        missedpaths(enc)
        triangles(enc)
    end
    mode=="dart" && explicit_darts(enc)
    if angular
        signedareas(enc)
        radialorders(enc)
    else
        ordertype(enc)
    end
    return enc
end

function replay(row, out, checker)
    id, mode, expected_hash, expected_vars, expected_clauses = row
    branch = only(c for c in branches() if branchid(c) == id)
    root = joinpath(@__DIR__,"cases",id)
    cnf = joinpath(out,"$id.cnf")
    open(cnf,"w+") do io
        println(io," "^100)
        enc = write_formula(io,branch,mode)
        cuts = joinpath(root,"cuts.txt")
        isfile(cuts) && check_cuts!(enc,cuts)
        @assert enc.nvar == parse(Int,expected_vars)
        @assert enc.nclause == parse(Int,expected_clauses)
        seekstart(io)
        println(io,rpad("p cnf $(enc.nvar) $(enc.nclause)",100))
    end
    @assert open(io -> bytes2hex(sha256(io)),cnf) == expected_hash
    proof = joinpath(root,"proof.drat")
    log = joinpath(out,"$id.log")
    open(log,"w") do io
        run(pipeline(`$checker $cnf $proof -U -p -w`;stdout=io,stderr=io))
    end
    occursin("s VERIFIED",read(log,String)) || error("Proof failed for $id")
    println("$id verified")
    flush(stdout)
    rm(cnf)
end

function main()
    length(ARGS)>=2 || error("Use replay.jl SCRATCH_DIR DRAT_TRIM [CASE_ID ...]")
    out, checker = abspath(ARGS[1]), abspath(ARGS[2])
    mkpath(out)
    requested = Set(ARGS[3:end])
    rows = split.(readlines(joinpath(@__DIR__,"manifest.tsv"))[2:end],'\t')
    ids = [r[1] for r in rows]
    length(unique(ids))==length(ids) || error("Duplicate case")
    Set(ids)==Set(branchid.(branches())) || error("Manifest does not cover the enumerated cases")
    issubset(requested,ids) || error("Unknown case")
    for row in rows
        (isempty(requested) || row[1] in requested) && replay(row,out,checker)
    end
end
main()
