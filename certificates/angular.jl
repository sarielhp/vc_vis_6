# All vectors i-p are reflected if necessary into the open half-plane left of pr.
# Their counterclockwise orientations then form an ordinary transitive tournament.
function radialorders(e)
    n=size(e.L,1)
    for p in 1:n
        r=p==1 ? 2 : 1
        points=filter(x->!(x in (p,r)),1:n)
        ord=zeros(Int,n,n)
        for (u,i) in enumerate(points),j in points[u+1:end]
            t=nv(e)
            ord[i,j]=t
            a,b,c=e.L[p,r,i],e.L[p,r,j],e.L[p,i,j]
            for x in (-1,1), y in (-1,1), z in (-1,1)
                clause(e,(-x*a,-y*b,-z*c,x*y*z*t))
            end
        end
        for (u,i) in enumerate(points),v in u+1:length(points),k in points[v+1:end]
            j=points[v]
            clause(e,(-ord[i,j],-ord[j,k],ord[i,k]))
            clause(e,(ord[i,j],ord[j,k],-ord[i,k]))
        end
    end
end
function signedareas(e)
    n=size(e.L,1)
    for a in 1:n-3,b in a+1:n-2,c in b+1:n-1,z in c+1:n, σ in (-1,1)
        clause(e,(-σ*e.L[a,b,z],-σ*e.L[b,c,z],-σ*e.L[c,a,z],σ*e.L[a,b,c]))
    end
end
