# +1 and -1 denote truth constants; all propositional variables are numbered from 2.
mutable struct Encoding
    io::IOStream
    branch::Branch
    masks::Vector{Int}
    L::Array{Int,3}
    edge::Matrix{Int}
    seen::BitMatrix
    nvar::Int
    nclause::Int
end
nv(e)=e.nvar+=1
function clause(e, lits)
    1 in lits && return
    for l in lits
        @assert l!=0
        l == -1 || print(e.io,l,' ')
    end
    println(e.io,'0')
    e.nclause+=1
end
function equalif(e,a,b,guard=())
    clause(e,(guard...,-a,b))
    clause(e,(guard...,a,-b))
end
function geometry(c,masks,io)
    n=7+length(masks)
    e=Encoding(io,c,masks,zeros(Int,n,n,n),zeros(Int,n,n),falses(n,7),1,0)
    b=c.nd+c.h
    for a in 1:n-2,j in a+1:n-1,k in j+1:n
        # D then H is the cyclic ccw hull order, with H after D's last point.
        l = k<=b ? 1 : nv(e)
        e.L[a,j,k]=e.L[j,k,a]=e.L[k,a,j]=l
        e.L[j,a,k]=e.L[a,k,j]=e.L[k,j,a]=-l
    end
    for w in 8:n,s in 1:7
        e.seen[w,s]=!iszero(masks[w-7]&(1<<(s-1)))
    end
    for a in 1:n,j in a+1:n
        v = a<=7<j ? (e.seen[j,a] ? 1 : -1) : nv(e)
        e.edge[a,j]=e.edge[j,a]=v
    end
    for a in b+1:7,j in 1:b
        clause(e,(e.L[j,mod1(j+1,b),a],))
    end
    return e
end
function ordertype(e)
    L=e.L
    n=size(L,1)
    for a in 1:7,b in a+1:7,c in b+1:7,d in c+1:n-1,z in d+1:n
        five=(a,b,c,d,z)
        for p in five
            h,i,j,k=filter(!=(p),five)
            row=(L[p,h,i],L[p,j,k],L[p,h,j],L[p,i,k],L[p,h,k],L[p,i,j])
            for σ in (-1,1), x in (-1,1), y in (-1,1), z in (-1,1)
                clause(e, row .* (-x,-σ*x,-y,σ*y,-z,-σ*z))
            end
        end
    end
    # Signed-area identity: matching all boundary signs forces the triangle sign.
    for a in 1:n-3,b in a+1:n-2,c in b+1:n-1,z in c+1:n
        for σ in (-1,1)
            clause(e,(-σ*L[a,b,z],-σ*L[b,c,z],-σ*L[c,a,z],σ*L[a,b,c]))
        end
    end
end
function inside!(e,z,a,b,c,guard=())
    L=e.L
    s,t,u,v=L[a,b,z],L[b,c,z],L[c,a,z],L[a,b,c]
    equalif(e,s,t,guard)
    equalif(e,t,u,guard)
    equalif(e,u,v,guard)
end
function wedge!(e,y,a,b)
    L=e.L
    common=[w for w in axes(e.seen,1) if e.seen[w,a] && e.seen[w,b]]
    for w in common
        inside!(e,y,w,a,b)
    end
    yes=filter(w->e.seen[w,y],common)
    no=filter(w->!e.seen[w,y],common)
    for i in eachindex(yes),j in i+1:length(yes),z in no,σ in (-1,1)
        u,v=yes[i],yes[j]
        clause(e,(-σ*L[y,u,v],-σ*L[y,u,z],-σ*L[y,z,v]))
    end
end
function structural(e)
    L=e.L
    c=e.branch
    n=c.nd
    for w in 8:size(L,1), k in 1:n
        e.seen[w,k] && continue
        yes=findall(e.seen[w,:])
        for i in eachindex(yes),j in i+1:length(yes),σ in (-1,1)
            a,b=yes[i],yes[j]
            clause(e,(-σ*L[w,a,k],-σ*L[a,b,k],-σ*L[b,w,k]))
        end
    end
    for (i,k) in enumerate(c.exits)
        wedge!(e,i+n,k+1,mod(k+1,n)+1)
    end
    pocket=[n;collect(n+1:n+c.h);1]
    for idx in 2:length(pocket)-1
        f=pocket[idx]
        wedge!(e,f,n,1)
        wedge!(e,f,pocket[idx-1],pocket[idx+1])
        index=findfirst(==(127⊻(1<<(f-1))),e.masks)
        isnothing(index) && continue
        z=index+7
        for i in eachindex(pocket)
            i==idx && continue
            equalif(e,L[z,f,n],(i<idx ? 1 : -1)*L[z,f,pocket[i]])
        end
        for u in 1:7,v in u+1:7,w in 8:size(L,1)
            (f in (u,v) || !e.seen[w,u] || !e.seen[w,v]) && continue
            for σ in (-1,1)
                inside!(e,f,w,u,v,(-σ*L[z,f,u],σ*L[z,f,v]))
            end
        end
    end
end
function halfplane(e)
    q=findfirst(==(127),e.masks)+7
    L=e.L
    n=size(L,1)
    for v in 8:n
        yes=findall(e.seen[v,:])
        no=findall(.!e.seen[v,:])
        for a in no,c in no,p in yes,σ in (-1,1)
            a==c && continue
            cond=(L[v,q,a],L[v,q,p],L[v,q,c],L[v,a,p],L[v,p,c],L[a,c,v],-L[a,c,p])
            -1 in (σ .* cond) && continue
            base=map(u->-σ*u,cond)
            g=nv(e)
            clause(e,(base...,-e.edge[v,q],g))
            for u in yes
                clause(e,(base...,-σ*L[v,q,u],-σ*L[v,u,a],g))
            end
            for x in 8:n
                e.seen[x,a] && e.seen[x,c] || continue
                clause(e,(-g,-σ*L[v,a,x]))
                clause(e,(-g,-σ*L[v,p,x]))
                e.seen[x,p] || continue
                clause(e,(-g,σ*L[p,x,a]))
                for y in 8:n
                    e.seen[y,a] && e.seen[y,c] && !e.seen[y,p] || continue
                    clause(e,(-g,σ*L[p,x,y]))
                end
            end
        end
    end
end
