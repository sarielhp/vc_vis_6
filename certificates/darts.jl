# Sign σ is the orientation of the indicated outer triangle/cycle.
# Each gate is required to hold only when the geometric antecedent is true.
function dart_gate(enc, signs)
    gate = nv(enc)
    clause(enc,((-s for s in signs)...,gate))
    return gate
end

function contains_signs(L,a,b,c,x,σ)
    return (σ*L[a,b,x],σ*L[b,c,x],σ*L[c,a,x])
end

function cut_inside(enc,gate,L,a,b,c,x,σ,extra=())
    tests=contains_signs(L,a,b,c,x,σ)
    clause(enc,(-gate,(-s for s in tests)...,extra...))
end

function explicit_darts(enc)
    L=enc.L
    n=size(L,1)
    for w in 8:n-1, v in w+1:n
        for a in 1:6, b in a+1:7
            all(enc.seen[k,j] for k in (w,v) for j in (a,b)) || continue
            cycle=(w,a,v,b)
            for σ in (-1,1)
                turns=(σ*L[w,a,v],σ*L[a,v,b],σ*L[v,b,w],σ*L[b,w,a])
                convex=dart_gate(enc,turns)
                for x in 8:n
                    enc.seen[x,a] && enc.seen[x,b] && continue
                    cut_inside(enc,convex,L,w,a,v,x,σ)
                    cut_inside(enc,convex,L,w,v,b,x,σ)
                end
                for start in 1:4
                    r,p,q,s = ntuple(i->cycle[mod1(start+i-1,4)],4)
                    reflex=dart_gate(enc,contains_signs(L,p,q,s,r,σ))
                    for x in 8:n
                        enc.seen[x,a] && enc.seen[x,b] && continue
                        if r in (a,b)
                            # r and q are targets. Both see all of the dart.
                            cut_inside(enc,reflex,L,r,p,q,x,σ)
                            cut_inside(enc,reflex,L,r,q,s,x,σ)
                        else
                            if !enc.seen[x,p]
                                cut_inside(enc,reflex,L,p,q,s,x,σ,(-σ*L[r,p,x],))
                            end
                            if !enc.seen[x,s]
                                cut_inside(enc,reflex,L,p,q,s,x,σ,(σ*L[r,s,x],))
                            end
                        end
                    end
                end
            end
        end
    end
end
