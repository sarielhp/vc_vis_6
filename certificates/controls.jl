using QuickEnv # silent
include("cases.jl")
include("encoding.jl")
include("enclosure.jl")
include("eager.jl")
include("angular.jl")

const Point = NTuple{2,Int}
det(a,b,c)=(b[1]-a[1])*(c[2]-a[2])-(b[2]-a[2])*(c[1]-a[1])
opposite(a,b)=(a>0)!=(b>0)
cross(a,b,c,d)=opposite(det(a,b,c),det(a,b,d)) && opposite(det(c,d,a),det(c,d,b))
function visible(poly,a,b)
    !any(cross(a,b,poly[i],poly[mod1(i+1,length(poly))]) for i in eachindex(poly))
end
function general(pos,p,poly)
    all(p!=a for a in pos) || return false
    all(!iszero(det(pos[i],pos[j],p)) for i in eachindex(pos) for j in i+1:length(pos)) || return false
    return all(!iszero(det(a,p,v)) for a in pos for v in poly)
end
insideconv(poly,x)=all(det(poly[i],poly[mod1(i+1,length(poly))],x)>0 for i in eachindex(poly))

function notchcontrol()
    poly=[(-24,-21),(23,-25),(24,22),(3,22),(-1,-3),(-4,22),(-25,22)]
    notch=[(-4,22),(-1,-3),(3,22)]
    s=[(12,0),(8,9),(-5,12),(-12,5),(-11,-6),(-3,-12),(8,-9)]
    @assert all(det(s[i],s[j],v)!=0 for i in 1:7 for j in i+1:7 for v in poly)
    @assert all(det(s[i],s[j],s[k])>0 for i in 1:7 for j in i+1:7 for k in j+1:7)
    ws=Point[]
    masks=Int[]
    for (x,y) in Iterators.product(-11:11,-11:11)
        p=(x,y)
        insideconv(s,p) || continue
        all(det(notch[j],notch[mod1(j+1,3)],p)>=0 for j in 1:3) && continue
        general(vcat(s,ws),p,poly) || continue
        m=maskof(j-1 for j in 1:7 if visible(poly,p,s[j]))
        m in masks && continue
        push!(masks,m)
        push!(ws,p)
    end
    @assert 127 in masks && length(masks)>=5
    return Branch(1,7,0,()),poly,s,ws,masks
end
function checkfixture(c,poly,s,ws,masks,name;strong=false,angular=false)
    points=vcat(s,ws)
    mkpath("controls")
    cnf="controls/$name.cnf"
    open(cnf,"w+") do io
        println(io," "^100)
        e=geometry(c,masks,io)
        structural(e)
        halfplane(e)
        strong ? allpathcuts(e) : twohop(e)
        strong || missedpaths(e)
        triangles(e;alltri=strong)
        ordertype(e)
        angular && radialorders(e)
        for i in eachindex(points),j in i+1:length(points)
            clause(e,((visible(poly,points[i],points[j]) ? 1 : -1)*e.edge[i,j],))
            for k in j+1:length(points)
                σ=sign(det(points[i],points[j],points[k]))
                @assert σ!=0
                clause(e,(σ*e.L[i,j,k],))
            end
        end
        seekstart(io)
        println(io,rpad("p cnf $(e.nvar) $(e.nclause)",100))
    end
    result=run(ignorestatus(`minisat -verb=0 $cnf controls/$name.result`))
    @assert result.exitcode==10
    println((case=name,masks=masks,targets=s,witnesses=ws))
end
checkfixture(notchcontrol()...,"notch")
function certifiedcontrol()
    # A narrow triangular bay enters a large outer rectangle from the right.
    poly=[(-194,-121),(199,-121),(199,51),(-57,55),(199,58),(199,161),(-194,161)]
    s=[(0,0),(103,7),(0,119),(-29,63),(-5,84),(-10,89),(2,94)]
    @assert all(det(s[i],s[j],v)!=0 for i in 1:7 for j in i+1:7 for v in poly)
    @assert all(det(s[i],s[j],s[k])!=0 for i in 1:7 for j in i+1:7 for k in j+1:7)
    @assert all(insideconv(s[1:4],s[i]) for i in 5:7)
    ws=Point[]
    masks=[7,119,127]
    for m in masks
        found=false
        for x in -140:-65,y in -15:75
            p=(x,y)
            general(vcat(s,ws),p,poly) || continue
            actual=maskof(j-1 for j in 1:7 if visible(poly,p,s[j]))
            if actual==m
                push!(ws,p)
                found=true
                break
            end
        end
        @assert found
    end
    exitlabels=Int[]
    for i in 4:7
        options=[j-1 for j in 1:2 if insideconv([ws[1],s[j],s[j+1]],s[i]) || insideconv([ws[1],s[j+1],s[j]],s[i])]
        @assert length(options)==1
        push!(exitlabels,only(options))
    end
    @assert insideconv([ws[2],s[1],s[3]],s[4]) || insideconv([ws[2],s[3],s[1]],s[4])
    return Branch(2,3,1,Tuple(exitlabels)),poly,s,ws,masks
end
checkfixture(certifiedcontrol()...,"certified")
checkfixture(certifiedcontrol()...,"certified-strong";strong=true)
checkfixture(notchcontrol()...,"notch-strong";strong=true)
function halfplanecontrol()
    poly=[(-3,-3),(103,-3),(103,110),(96,107),(95,7),(-3,106),(-3,15),(-105,24),(-105,18),(-3,6)]
    s=[(-100,20),(-2,-1),(20,-2),(102,-1),(102,98),(100,102),(0,100)]
    ws=[(0,0),(100,0)]
    allp=vcat(s,ws)
    @assert all(det(s[i],s[j],s[k])>0 for i in 1:7 for j in i+1:7 for k in j+1:7)
    @assert all(det(allp[i],allp[j],allp[k])!=0 for i in eachindex(allp) for j in i+1:length(allp) for k in j+1:length(allp))
    # Infinite lines passing through a polygon vertex away from the open segment are harmless.
    for i in eachindex(allp),j in i+1:length(allp),t in poly
        if det(allp[i],allp[j],t)==0
            @assert !all(min(allp[i][k],allp[j][k])<=t[k]<=max(allp[i][k],allp[j][k]) for k in 1:2)
        end
    end
    masks=[maskof(j-1 for j in 1:7 if visible(poly,w,s[j])) for w in ws]
    @assert masks[2]==127
    a,p,c=s[6],s[7],s[1]
    v,q=ws
    @assert all(x>0 for x in (det(v,q,a),det(v,q,p),det(v,q,c),det(v,a,p),det(v,p,c),det(a,c,v),-det(a,c,p)))
    @assert visible(poly,v,p) && visible(poly,v,q) && !visible(poly,v,a) && !visible(poly,v,c)
    return Branch(1,7,0,()),poly,s,ws,masks
end
checkfixture(halfplanecontrol()...,"halfplane";strong=true)
checkfixture(certifiedcontrol()...,"radial-certified";strong=true,angular=true)
checkfixture(halfplanecontrol()...,"radial-halfplane";strong=true,angular=true)
