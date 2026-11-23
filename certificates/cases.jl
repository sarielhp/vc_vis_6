struct Branch
    stage::Int
    nd::Int
    h::Int
    exits::Tuple
end
branchid(c::Branch) = "s$(c.stage)-d$(c.nd)-h$(c.h)-" * (isempty(c.exits) ? "none" : join(c.exits))
function branches()
    out = [Branch(1,7-h,h,()) for h in 0:5]
    for n in 6:-1:3, h in 0:6-n
        m = 7-n
        edges = 0:(h==0 ? n-1 : n-2)
        reps = Set{Tuple}()
        for seed in Iterators.product(ntuple(_->edges,m)...)
            H, A = collect(seed[1:h]), collect(seed[h+1:end])
            issorted(A) || continue
            orbit = Tuple[]
            for s in (-1,1), shift in 0:n-1
                f(e) = mod(s*e+shift,n)
                (h==0 || f(n-1)==n-1) || continue
                push!(orbit,Tuple(vcat(f.(s==1 ? H : reverse(H)),sort(f.(A)))))
            end
            push!(reps,minimum(orbit))
        end
        append!(out, [Branch(2,n,h,rep) for rep in sort(collect(reps))])
    end
    append!(out,[Branch(2,2,h,()) for h in 1:4])
    @assert length(out)==74 && length(unique(branchid.(out)))==74
    return out
end
maskof(J) = foldl((m,j)->m | (1<<j), J;init=0)
function witnessmasks(c::Branch;augment=true)
    n = c.nd
    d = (1<<n)-1
    masks = Set(m for m in 0:127 if count_ones(m)>=5)
    omit(k) = 127 ⊻ maskof(k)
    if c.stage==1
        push!(masks,d)
        union!(masks,[d⊻(1<<k) for k in 0:n-1])
        if c.h==0
            union!(masks,[omit(mod.(i .+ (0,2,4),7)) for i in 0:6])
        end
    elseif n==6
        union!(masks,omit.([(1,3,5),(0,2,4),(2,4,6),(3,5,6),(2,5,6)]))
    elseif n==5
        union!(masks,[d⊻(1<<k) for k in 0:n-1])
        for (j,e) in enumerate(c.exits)
            push!(masks,omit((mod(e+2,n),mod(e+4,n),n+j-1)))
        end
    else
        union!(masks, [m for m in 0:127 if (m&d)==d])
        union!(masks, [d⊻(1<<k) for k in 0:n-1])
        if n>=3
            for k in 0:n-1
                missed = [n+i-1 for (i,e) in enumerate(c.exits) if k in (e,mod(e+1,n))]
                push!(masks,omit([k;missed]))
            end
        end
        if augment && n==3 && c.h==0 && c.exits==(0,0,1,1)
            union!(masks,[m for m in 0:127 if count_ones(m)==4])
        end
    end
    return sort(collect(masks))
end
