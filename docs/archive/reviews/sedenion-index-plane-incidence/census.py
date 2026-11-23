"""Exact census of the sedenion index planes, written before the Rocq source.

The sign function is the recursion of gororoba-quantum cd_core.cd_sign and of
gororoba-open cd_basis_mul_sign (the two agree line for line). The script
prints one JSON object; it reads no file and takes no argument.

Predictions recorded before the first run, each confirmed by it:
ordered nonassociating basis triples 1848 of 4096; noncommuting ordered
imaginary pairs 210; 35 lines; 15 planes; every pair of planes shares 4
indices and one line; 252 sorted triples fail to associate; 8 planes hold 28
of them and 7 planes hold 4; left alternativity on two-term elements fails in
exactly those 7 planes; 336 ordered signed zero products of 2-blades on 84
unordered assessor pairs; every such pair spans one of the 7 planes, 12 per
plane.
"""
import itertools, json
def sgn(dim,p,q):
    s=1; half=dim>>1
    while half>0:
        ph=p>=half; qh=q>=half
        if not ph and not qh: pass
        elif not ph and qh:
            t=q-half; q=p; p=t
        elif ph and not qh:
            p-=half
            if q!=0: s=-s
        else:
            t=q-half; u=p-half
            if t==0: return -s
            p=t; q=u
        half>>=1
    return s
D=16
S=[[sgn(D,p,q) for q in range(D)] for p in range(D)]
def mul(x,y):
    z=[0]*D
    for i,a in enumerate(x):
        if a:
            for j,b in enumerate(y):
                if b: z[i^j]+=a*b*S[i][j]
    return z
def e(i,c=1):
    v=[0]*D; v[i]=c; return v
def add(x,y): return [a+b for a,b in zip(x,y)]
def nonassoc(a,b,c): return S[a][b]*S[a^b][c]!=S[b][c]*S[a][b^c]
out={}
out['dim8_check']=sum(1 for a in range(8) for b in range(8) for c in range(8) if nonassoc(a,b,c))
out['ordered_nonassoc_4096']=sum(1 for a in range(D) for b in range(D) for c in range(D) if nonassoc(a,b,c))
out['noncommuting_ordered_imag_pairs']=sum(1 for a in range(1,D) for b in range(1,D) if a!=b and S[a][b]!=S[b][a])
lines=[t for t in itertools.combinations(range(1,D),3) if t[0]^t[1]^t[2]==0]
out['lines']=len(lines)
tri=list(itertools.combinations(range(1,D),3))
out['sorted_triples']=len(tri)
out['sorted_nonassoc']=sum(1 for t in tri if nonassoc(*t))
out['sorted_noncollinear_assoc']=sum(1 for t in tri if t not in lines and not nonassoc(*t))
# per unordered triple: how many of 6 orders nonassociate
hist={}
for t in tri:
    n=sum(1 for p in itertools.permutations(t) if nonassoc(*p)); hist[n]=hist.get(n,0)+1
out['orders_nonassoc_hist']=hist
# planes: order-8 subgroups
planes=set()
for g in itertools.combinations(range(1,D),3):
    H={0}
    for x in g: H|={h^x for h in H}
    if len(H)==8: planes.add(tuple(sorted(H)))
planes=sorted(planes)
out['planes']=len(planes)
out['plane_pair_intersections']=sorted({len(set(a)&set(b)) for a,b in itertools.combinations(planes,2)})
out['plane_pairs']=len(list(itertools.combinations(planes,2)))
out['lines_per_plane']=sorted({sum(1 for l in lines if set(l)<=set(P)) for P in planes})
out['planes_per_line']=sorted({sum(1 for P in planes if set(l)<=set(P)) for l in lines})
out['shared_lines_per_plane_pair']=sorted({sum(1 for l in lines if set(l)<=set(a)&set(b)) for a,b in itertools.combinations(planes,2)})
info=[]
for P in planes:
    im=[x for x in P if x]
    t3=[t for t in itertools.combinations(im,3) if t[0]^t[1]^t[2]!=0]
    sn=sum(1 for t in t3 if nonassoc(*t))
    on=sum(1 for p in itertools.permutations(im,3) if nonassoc(*p))
    # alternativity on two-term elements x=e_a+e_b, y=e_c
    lalt=ralt=flex=0
    for a,b in itertools.combinations(im,2):
        x=add(e(a),e(b))
        for c in im:
            y=e(c)
            if mul(x,mul(x,y))!=mul(mul(x,x),y): lalt+=1
            if mul(mul(y,x),x)!=mul(y,mul(x,x)): ralt+=1
            if mul(mul(x,y),x)!=mul(x,mul(y,x)): flex+=1
    info.append({'plane':P,'sorted_nonassoc':sn,'ordered_nonassoc':on,'left_alt_fail':lalt,'right_alt_fail':ralt,'flex_fail':flex})
out['plane_info']=info
# zero products of two-blades
blades=[(i,j,s) for i in range(D) for j in range(i+1,D) for s in (1,-1)]
zp=[]
for (i,j,s),(k,l,t) in itertools.product(blades,blades):
    if not any(mul(add(e(i),e(j,s)),add(e(k),e(l,t)))): zp.append((i,j,s,k,l,t))
out['ordered_signed_zero_products']=len(zp)
def span(g):
    H={0}
    for x in g: H|={h^x for h in H}
    return tuple(sorted(H))
edge={}
for i,j,s,k,l,t in zp:
    edge.setdefault(frozenset([(i,j),(k,l)]),set()).add(span([i,j,k,l]))
out['unordered_assessor_edges']=len(edge)
out['edge_span_sizes']=sorted({len(next(iter(v))) for v in edge.values()})
pt={tuple(d['plane']):(d['sorted_nonassoc']) for d in info}
cnt={}
for v in edge.values():
    P=next(iter(v)); cnt[P]=cnt.get(P,0)+1
out['edges_per_plane']=[{'plane':P,'edges':c,'sorted_nonassoc':pt.get(P)} for P,c in sorted(cnt.items())]
ass=sorted({a for k in edge for a in k})
out['assessors']=len(ass)
out['assessor_xor_keys']=sorted({i^j for i,j in ass})
# kites as components
adj={a:set() for a in ass}
for k in edge:
    a,b=tuple(k); adj[a].add(b); adj[b].add(a)
seen=set(); comps=[]
for a in ass:
    if a in seen: continue
    st=[a]; c=set()
    while st:
        u=st.pop()
        if u in c: continue
        c.add(u); st+=list(adj[u]-c)
    seen|=c; comps.append(sorted(c))
out['kites']=[{'assessors':c,'xor_keys':sorted({i^j for i,j in c}),'planes':sorted({next(iter(edge[k])) for k in edge if set(k)<=set(c)})} for c in comps]
print(json.dumps(out))
