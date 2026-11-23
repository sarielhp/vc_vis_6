# For a non-visible pair a,b, paths from a to b cannot exist on both sides.
function twohop(e)
    n=size(e.L,1)
    for a in 1:n-1,b in a+1:n
        g=e.edge[a,b]
        g==1 && continue
        side=nv(e)
        for t in 1:n
            t in (a,b) && continue
            for σ in (-1,1)
                clause(e,(g,-σ*side,-σ*e.L[a,b,t],-e.edge[a,t],-e.edge[b,t]))
            end
        end
    end
end
# Choose one disconnected side and a binary vertex coloring separating the endpoints.
function missedpaths(e)
    n=size(e.L,1)
    for w in 8:n,k in 1:7
        e.seen[w,k] && continue
        side=nv(e)
        active=ones(Int,n)
        color=ones(Int,n)
        color[k]=-1
        for t in 1:n
            t in (w,k) && continue
            active[t]=nv(e)
            color[t]=nv(e)
            for σ in (-1,1)
                clause(e,(-σ*side,-σ*e.L[w,k,t],active[t]))
            end
        end
        for a in 1:n-1,b in a+1:n
            equalif(e,color[a],color[b],(-e.edge[a,b],-active[a],-active[b]))
        end
    end
end
function triangles(e;alltri=false)
    n=size(e.L,1)
    for a in 1:n-2,b in a+1:n-1,c in b+1:n
        !alltri && b>7 && continue
        edges=(e.edge[a,b],e.edge[b,c],e.edge[c,a])
        -1 in edges && continue
        tri=nv(e)
        clause(e,((-v for v in edges)...,tri))
        for t in 1:n
            t in (a,b,c) && continue
            for σ in (-1,1)
                inside=(-tri,-σ*e.L[a,b,t],-σ*e.L[b,c,t],-σ*e.L[c,a,t])
                for z in (a,b,c)
                    clause(e,(inside... , e.edge[t,z]))
                end
            end
        end
    end
end
