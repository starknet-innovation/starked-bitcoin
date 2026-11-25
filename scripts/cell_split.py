"""Where the proven cells go (GPU-UTIL; docs/design/gpu-util.md).

Reads the per-block needs in data/survey/ (the sample between 493,000 and 935,000 weighted 10) and prints,
under `system.sizesAuto` (tight, early, tiered, uniform): each component's share of the proven cells and of
the cells the blocks need, the shares by layer and by (L, profile), and two what-ifs: components split in
two instances (three quarters of a power of two), and consecutive blocks packed into one proof. No proving.

Usage (from the repo root): python3 scripts/cell_split.py
"""
import json, collections, sys
names="bytes fields msg sha merkle tables walk ctx wmerkle undo b2msg b2s fpwalk urec coin anc".split()
I={n:i for i,n in enumerate(names)}
def ncols(n):
    j=json.load(open(f"airs/block_{n}.json")); return j["n_preprocessed"]+j["n_main"]+4*((len(j.get("lookups",[]))+1)//2)
cols=[ncols(n) for n in names]
FIXED={I["ctx"]:8,I["tables"]:8,I["anc"]:12}
TOP=[I[n] for n in ("sha","msg","bytes","walk")]
TIGHT=dict(msg=1,bytes=1,fpwalk=3,b2s=3,undo=3,b2msg=3,walk=4,fields=7,coin=8,urec=9,merkle=10,wmerkle=10)
EARLY=dict(TIGHT); EARLY["msg"]=0; EARLY["walk"]=2
TIERED=dict(fpwalk=2,b2s=2,undo=2,b2msg=2,fields=5,coin=5,urec=5,merkle=5,wmerkle=5)
P=[("tight",TIGHT),("early",EARLY),("tiered",TIERED)]
cl=lambda n:max(0,(n-1).bit_length())
def logs(nl):
    uL=max(max(nl),8)
    if uL>=12:
        L=max(max(nl[i] for i in TOP),12)
        for pn,off in P:
            lg=[FIXED[i] if i in FIXED else max(L-off.get(n,0),8) for i,n in enumerate(names)]
            if all(a<=b for a,b in zip(nl,lg)): return pn,L,lg
    return "uniform",uL,[uL]*16
files=[("data/survey/needs-0-492992.csv",1),("data/survey/needs-493k-935k-sample.csv",10),("data/survey/needs-r5.csv",1)]
ERA=[(0,200000),(200000,500000),(500000,800000),(800000,972501)]
ex=collections.defaultdict(lambda:[0]*16); pad=collections.defaultdict(lambda:[0]*16); nb=collections.Counter()
byL=collections.Counter(); cellsL=collections.Counter()
cache={}
for f,w in files:
    for line in open(f):
        if "error" in line: continue
        r=list(map(int,line.split(","))); h=r[0]; need=r[1:]
        e=next(i for i,(a,b) in enumerate(ERA) if a<=h<b)
        nl=tuple(cl(x) for x in need)
        if nl not in cache: cache[nl]=logs(nl)
        pn,L,lg=cache[nl]
        nb[e]+=w; byL[(L,pn)]+=w
        c=0
        for i in range(16):
            ex[e][i]+=w*cols[i]*need[i]; pad[e][i]+=w*(cols[i]<<lg[i]); c+=cols[i]<<lg[i]
        cellsL[(L,pn)]+=w*c
tot_p=[sum(pad[e][i] for e in pad) for i in range(16)]; tot_e=[sum(ex[e][i] for e in ex) for i in range(16)]
T=sum(tot_p); TE=sum(tot_e)
print("blocks",sum(nb.values()),"padded cells %.3e exact %.3e ratio %.2f"%(T,TE,T/TE))
print("comp cols  padded%  exact%  pad/exact   per era padded%")
for i,n in sorted(enumerate(names),key=lambda x:-tot_p[x[0]]):
    print(f"{n:8}{cols[i]:4}  {100*tot_p[i]/T:5.1f}  {100*tot_e[i]/TE:5.1f}  {tot_p[i]/max(tot_e[i],1):5.2f}   "+" ".join("%5.1f"%(100*pad[e][i]/sum(pad[e])) for e in range(4)))
print("era cells share:", ["%.1f%%"%(100*sum(pad[e])/T) for e in range(4)], dict(nb))
G={"hash block bytes (bytes,msg,sha,merkle,wmerkle)":"bytes msg sha merkle wmerkle","parse+checks (fields,walk,tables,ctx,anc)":"fields walk tables ctx anc","undo commit (undo,b2msg,b2s,fpwalk)":"undo b2msg b2s fpwalk","coins (urec,coin)":"urec coin"}
for g,ns in G.items():
    print(g,"%.1f%% padded, %.1f%% exact"%(100*sum(tot_p[I[n]] for n in ns.split())/T,100*sum(tot_e[I[n]] for n in ns.split())/TE))
print("cells by L,profile (share of cells, blocks):")
for k in sorted(cellsL): 
    if cellsL[k]/T>0.004: print(k,"%.1f%% cells"%(100*cellsL[k]/T),byL[k],"blocks")

# --- what-ifs ---
print("\n== what-ifs (padded cells, whole chain; baseline %.3e) =="%T)
# (a) split sizes: each of sha,msg,bytes,b2s(+undo,b2msg,fpwalk),walk may be 2^l or 2^(l-1)+2^(l-2)
SPL=[I[n] for n in ("sha","msg","bytes","b2s","walk","undo","b2msg","fpwalk")]
def whatif(split_set):
    tot=0
    for f,w in files:
        for line in open(f):
            if "error" in line: continue
            r=list(map(int,line.split(","))); need=r[1:]
            nl=tuple(cl(x) for x in need); pn,L,lg=cache[nl]
            for i in range(16):
                c=cols[i]<<lg[i]
                if i in split_set and lg[i]>=10 and need[i]<=3<<(lg[i]-2): c=cols[i]*(3<<(lg[i]-2))
                tot+=w*c
    return tot
a=whatif({I["sha"]}); b=whatif(set(SPL))
print("split sizes (3/4 step) on sha only: %.1f%% fewer; on sha,msg,bytes,b2s,walk,undo,b2msg,fpwalk: %.1f%% fewer"%(100*(1-a/T),100*(1-b/T)))
# (b) packing consecutive blocks into bins: one proof per run of blocks, greedy until any component's sum exceeds cap 2^23 (sha) with tight-ish ratios: approximate cells = exact cells summed, padded per bin to powers of two per component
def pack(capL):
    cap=1<<capL; tot=0; bins=0
    for f,w in files:
        acc=[0]*16; 
        def flush():
            nonlocal tot,bins,acc
            if not any(acc): return
            nl=tuple(cl(x) for x in acc); pn,L,lg=logs(nl)
            tot+=w*sum(cols[i]<<lg[i] for i in range(16)); bins+=w; acc=[0]*16
        for line in open(f):
            if "error" in line: continue
            need=list(map(int,line.split(",")))[1:]
            # fixed-size components (tables, ctx, anc) do not add up in this estimate
            if acc[I["sha"]]+need[I["sha"]]>cap and any(acc): flush()
            for i in range(16):
                acc[i]= max(acc[i],need[i]) if i in FIXED else acc[i]+need[i]
        flush()
    return tot,bins
for capL in (22,23,24):
    t,b_=pack(capL); print("packing consecutive blocks to sha<=2^%d: %.3e cells (%.1f%% fewer), %d proofs"%(capL,t,100*(1-t/T),b_))
