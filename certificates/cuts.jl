# Verify a cut directly from its negation, without using the SAT model that produced it.
# signs is a partial alternating sign table. Zero means undetermined.
function knownpath(signs, edges, u, v, side)
    pool = [i for i in axes(edges,1) if signs[u,v,i] == side]
    isempty(pool) && return false
    reached = falses(size(edges,1))
    reached[u] = true
    for depth in 1:length(pool)
        progress = false
        for k in pool
            reached[k] && continue
            if any(i -> reached[i] && edges[i,k], axes(edges,1))
                edges[k,v] && return true
                reached[k] = true
                progress = true
            end
        end
        progress || break
    end
    return false
end

function forces_conflict(signs, seen)
    n, targets = size(seen)
    edges = falses(n,n)
    for w in targets+1:n, s in 1:targets
        edges[s,w] = edges[w,s] = seen[w,s]
    end
    function connect(a,b)
        edges[a,b] = edges[b,a] = true
        return (a<=targets<b && !seen[b,a]) || (b<=targets<a && !seen[a,b])
    end
    while true
        oldcount = count(edges)
        for u in 1:n-1, v in u+1:n
            edges[u,v] && continue
            if knownpath(signs,edges,u,v,1) && knownpath(signs,edges,u,v,-1)
                connect(u,v) && return true
            end
        end
        for a in 1:n-2, b in a+1:n-1
            edges[a,b] || continue
            for c in b+1:n
                edges[b,c] && edges[a,c] || continue
                members = Int[a,b,c]
                for x in 1:n
                    side = signs[a,b,x]
                    if side != 0 && side == signs[b,c,x] == signs[c,a,x]
                        push!(members,x)
                    end
                end
                for i in eachindex(members), j in i+1:length(members)
                    connect(members[i],members[j]) && return true
                end
            end
        end
        oldcount == count(edges) && return false
    end
end

function check_cuts!(e, path)
    triples = Dict{Int,NTuple{3,Int}}()
    n = size(e.L,1)
    for a in 1:n-2,b in a+1:n-1,c in b+1:n
        var = e.L[a,b,c]
        var > 1 && (triples[var] = (a,b,c))
    end
    for (lineid,line) in enumerate(eachline(path))
        lits = parse.(Int,split(line))
        pop!(lits) == 0 || error("Missing clause terminator")
        required = Dict(abs(l) => -sign(l) for l in lits)
        nodes = collect(1:7)
        for var in keys(required)
            append!(nodes,triples[var])
        end
        sort!(unique!(nodes))
        signs = map(e.L[nodes,nodes,nodes]) do lit
            abs(lit) == 1 && return lit
            return sign(lit) * get(required,abs(lit),0)
        end
        forces_conflict(signs,e.seen[nodes,:]) || error("Unproved geometric cut on line $lineid")
        clause(e,lits)
    end
end
