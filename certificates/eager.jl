# For any candidate visibility graph nonedge, some open side admits no connecting path.
function allpathcuts(e)
    n=size(e.L,1)
    for k in 1:n-1,w in k+1:n
        g=e.edge[k,w]
        g==1 && continue
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
            equalif(e,color[a],color[b],(g,-e.edge[a,b],-active[a],-active[b]))
        end
    end
end
