"""Size-profile search for TIERS-2 (D-055; docs/reports/2026-11-19-block-cost-split.md, result 4).

Reads the per-block component needs printed by `survey` with STARKED_SURVEY_NEEDS=1 (`height,` then the
16 needs in `system.names` order) and simulates size profiles: a block takes the first profile it fits,
then `tiered`, then `uniform`. Prints the slack of each component below L, the proven cells of a few
hand-picked profiles, and the offsets a coordinate search finds. No proving.

Usage: python3 scripts/tier_search.py needs.csv
Columns per component (preprocessed + main + interaction) are those of docs/design/component-sizes.md;
update `cols` when an AIR changes.
"""
import sys, collections
names="bytes fields msg sha merkle tables walk ctx wmerkle undo b2msg b2s fpwalk urec coin anc".split()
cols=dict(zip(names,[18,264,54,188,67,13,65,96,37,18,33,406,24,63,354,179]))
I={n:i for i,n in enumerate(names)}
rows=[list(map(int,l.split(','))) for l in open(sys.argv[1]) if 'error' not in l]
def cl(n): return max(0,(n-1).bit_length())
def tiered(L):
    o={n:max(L-5,8) for n in names}
    for n in "sha msg bytes walk".split(): o[n]=L
    for n in "fpwalk b2s undo b2msg".split(): o[n]=L-2
    o['ctx']=8;o['tables']=8;o['anc']=12
    return o
def prof(L,off):  # offsets relative to L, floors
    o={}
    for n in names:
        if n in ('ctx','tables'): o[n]=8
        elif n=='anc': o[n]=12
        else: o[n]=max(L-off[n],8)
    return o
def cells(logs): return sum(cols[n]<<logs[n] for n in names)
def fits(need,logs): return all(need[I[n]] <= (1<<logs[n]) for n in names)
def current(need):
    uL=max(cl(max(need)),8)
    if uL<12: return {n:uL for n in names},'uniform'
    L=max(cl(max(need[I[n]] for n in "sha msg bytes walk".split())),12)
    t=tiered(L)
    if fits(need,t): return t,'tiered'
    return {n:uL for n in names},'uniform'
exact=sum(sum(cols[n]*r[1+I[n]] for n in names) for r in rows)
cur=0; d=collections.defaultdict(list); big=0
for r in rows:
    need=r[1:]
    logs,p=current(need); cur+=cells(logs)
    L=max(cl(max(need[I[n]] for n in "sha msg bytes walk".split())),12)
    if L>=22:
        big+=1
        for n in names: d[n].append(L-cl(need[I[n]]))
print(f"blocks {len(rows)}, exact {exact:.3e}, current {cur:.3e} ({cur/exact:.2f}x); blocks with L>=22: {big}")
print("slack below L (log2), blocks with L>=22:  min  p0.1  p1  p5  median")
for n in names:
    v=sorted(d[n]); q=lambda p: v[int(p*(len(v)-1))]
    print(f"  {n:8} {v[0]:3} {q(0.001):3} {q(0.01):3} {q(0.05):3} {q(0.5):3}   current offset {22-tiered(22)[n]}")
def evaluate(label, offs_list):
    # offs_list: profiles tried in order; then current tiered; then uniform
    tot=0; used=collections.Counter()
    for r in rows:
        need=r[1:]
        uL=max(cl(max(need)),8)
        if uL<12: tot+=cells({n:uL for n in names}); used['uniform']+=1; continue
        L=max(cl(max(need[I[n]] for n in "sha msg bytes walk".split())),12)
        done=False
        for k,off in enumerate(offs_list):
            Lk=max(cl(need[I['sha']]),12) if off.get('_sha_only') else L
            lg=prof(Lk,off)
            if fits(need,lg): tot+=cells(lg); used[f'new{k}']+=1; done=True; break
        if done: continue
        logs,p=current(need); tot+=cells(logs); used[p]+=1
    print(f"{label}: {tot:.3e} cells, {tot/exact:.2f}x exact, {100*(1-tot/cur):.1f}% below current; used {dict(used)}")
    return tot
base=dict(sha=0,msg=0,bytes=0,walk=0,fpwalk=2,b2s=2,undo=2,b2msg=2,fields=5,merkle=5,wmerkle=5,urec=5,coin=5)
def off(**kw):
    o=dict(base); o.update(kw); return o
evaluate("A  walk L-2", [off(walk=2)])
evaluate("B  walk L-2, b2s L-3", [off(walk=2,b2s=3)])
evaluate("C  walk L-3, b2s L-3", [off(walk=3,b2s=3)])
evaluate("D  walk L-3, b2s L-4, b2msg L-4, undo L-3", [off(walk=3,b2s=4,b2msg=4,undo=3)])
evaluate("E  D + msg L-1, bytes L-1", [off(walk=3,b2s=4,b2msg=4,undo=3,msg=1,bytes=1)])
evaluate("F  D then A as second profile", [off(walk=3,b2s=4,b2msg=4,undo=3), off(walk=2)])
evaluate("G  E then D then A", [off(walk=3,b2s=4,b2msg=4,undo=3,msg=1,bytes=1), off(walk=3,b2s=4,b2msg=4,undo=3), off(walk=2)])
evaluate("H  p1 offsets everywhere (then D, A)", [off(walk=3,b2s=4,b2msg=5,undo=3,msg=1,bytes=1,fpwalk=3,fields=6,coin=7,urec=8,merkle=9,wmerkle=9), off(walk=3,b2s=4,b2msg=4,undo=3), off(walk=2)])
print("--- search")
import itertools
free="msg bytes walk b2s b2msg undo fpwalk fields coin urec merkle wmerkle".split()
big_rows=[r[1:] for r in rows if max(cl(max(r[1:])),8)>=12]
small_tot=sum(cells({n:max(cl(max(r[1:])),8) for n in names}) for r in rows if max(cl(max(r[1:])),8)<12)
pre=[]
for need in big_rows:
    L=max(cl(max(need[I[n]] for n in "sha msg bytes walk".split())),12)
    slack={n:L-max(cl(need[I[n]]),8) for n in free}
    logs,p=current(need)
    pre.append((L,slack,cells(logs)))
def total(profiles):
    tot=small_tot
    for L,slack,c in pre:
        for off in profiles:
            if all(off[n]<=slack[n] or L-off[n]<8 and slack[n]>=L-8 for n in free):
                tot+=sum(cols[n]<<max(L-off.get(n,0),8) for n in names if n not in('ctx','tables','anc'))+((cols['ctx']+cols['tables'])<<8)+(cols['anc']<<12); break
        else: tot+=c
    return tot
def climb(fixed):
    off={n:base[n] for n in free}
    best=total([off]+fixed)
    improved=True
    while improved:
        improved=False
        for n in free:
            for dlt in (1,-1):
                o=dict(off); o[n]+=dlt
                if o[n]<0: continue
                t=total([o]+fixed)
                if t<best: best=t; off=o; improved=True
    return off,best
tA=off(walk=2); tA={n:tA[n] for n in free}
o1,b1=climb([tA])
print("best first profile (then A, then tiered):", o1, f"{b1:.3e} {100*(1-b1/cur):.1f}% below current")
o2,b2=climb([o1,tA])
print("adding a profile in front:", o2, f"{b2:.3e} {100*(1-b2/cur):.1f}% below current")
o3,b3=climb([])
print("single new profile (then tiered):", o3, f"{b3:.3e} {100*(1-b3/cur):.1f}% below current")
# how many blocks each takes
for label,ps in (("one",[o3]),("two",[o1,tA]),("three",[o2,o1,tA])):
    cnt=collections.Counter()
    for L,slack,c in pre:
        for k,off_ in enumerate(ps):
            if all(off_[n]<=slack[n] or L-off_[n]<8 and slack[n]>=L-8 for n in free): cnt[k]+=1; break
        else: cnt['old']+=1
    print(label, dict(cnt))
