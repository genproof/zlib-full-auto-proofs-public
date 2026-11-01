import sys, heapq, numpy as np
from scipy.optimize import linprog
from dual import XL, XD, st, fib, groups
def zpiece(tau,g):
    if g<=0: return 0
    if g<3: return g*tau[0]
    if g<=10: return tau[17]+3
    return tau[18]+7
def gapcost(tau,g):
    if g<=0: return 0
    k=(g-1)//138
    return k*(tau[18]+7)+zpiece(tau,g-138*k)
def entry(tau,l): return max(tau[l],(tau[16]+4)//3)
GREP_L=[0,1,2,3,11,139,140,141,149,277,278,279]
GREP_D=[0,1,2,3,11]
def huff19(freqs):
    # Huffman lengths for all 19 symbols (zero freq -> tiny), limited to 15 by heuristic
    fr=[max(f,1e-6) for f in freqs]
    h=[(f,i,[i]) for i,f in enumerate(fr)]; heapq.heapify(h); c=100
    L=[0]*19
    while len(h)>1:
        a=heapq.heappop(h); b=heapq.heappop(h)
        for j in a[2]+b[2]: L[j]+=1
        heapq.heappush(h,(a[0]+b[0],c,a[2]+b[2])); c+=1
    while max(L)>15:
        # crude limit: move deepest pair up
        m=max(L); i=L.index(m); L[i]=15
        # fix kraft by lengthening shortest above
        while sum(2.0**-x for x in L)>1:
            j=min(range(19),key=lambda k:(L[k] if L[k]<15 else 99)); L[j]+=1
    return L
OPTS={'tight':False,'opt':[]}
def solve(L,s,taus,DB=100,Hcrude=2283,verbose=False,ret=False):
    def cap(l):
        fb=fib(l+1-s)
        return L-1 if fb==0 else min(L-1,(L+1)//fb)
    G=groups()
    names=[]; idx={}
    def V(k):
        if k not in idx: idx[k]=len(names); names.append(k)
        return idx[k]
    for k in ['lam','mul','mud','eta','kap','nuE','th0','sgl','sgd','nuF']: V(k)
    for t in range(len(taus)): V(('th',t))
    for o in OPTS['opt']: V(('om',o)); V(('omd',o))
    for u in range(1,21): V(('pi',u))
    for v in range(1,29): V(('rho',v))
    for g in G: V(('nu',g))
    nv=len(names)
    A=[];b=[];lab=[]
    def le(d,rhs,lb=None):
        r=np.zeros(nv)
        for k,c in d.items(): r[idx[k]]+=c
        A.append(r); b.append(rhs); lab.append(lb)
    for u in range(1,21):
        for v in range(1,29):
            le({('pi',u):-1,('rho',v):-1},-max(0,u+v-24))
    lens=[l for l in range(1,16) if cap(l)>=1 and (not OPTS['tight'] or fib(l+2-s)<=L+1)]
    def optt(d,f,l,stc,key):
        for o in OPTS['opt']:
            i,j=o
            d[(key,o)]=d.get((key,o),0)-f*max(-i,l-stc-j)
    def hdr(d,l,g,sg):
        for t,tau in enumerate(taus):
            d[('th',t)]=d.get(('th',t),0)+entry(tau,l)+gapcost(tau,g)
        d[sg]=d.get(sg,0)-(g+1)
    for gname,codes in G.items():
        greps=GREP_D if gname[0]=='dist' else GREP_L
        for l in lens:
            for f in sorted(set([1,cap(l)])):
                for g in greps:
                    d={('nu',gname):-1}
                    if gname[0]=='lit':
                        d['lam']=-f*(l-gname[1]); d['eta']=-f; d['mul']=-2.0**-l; hdr(d,l,g,'sgl'); optt(d,f,l,gname[1],'om')
                    elif gname[0]=='len':
                        u=l+gname[2]; d[('pi',u)]=f; d['lam']=-f*(l-gname[1]); d['eta']=-f; d['kap']=f; d['mul']=-2.0**-l; hdr(d,l,g,'sgl'); optt(d,f,l,gname[1],'om')
                    else:
                        v=l+gname[1]; d[('rho',v)]=f; d['lam']=-f*(l-5); d['kap']=-f; d['mud']=-2.0**-l; hdr(d,l,g,'sgd'); optt(d,f,l,5,'omd')
                    le(d,0,('code',gname,l,f,g))
        if gname[0]=='dist':
            for l in range(1,16):
                for g in greps:
                    d={('nu',gname):-1,'nuF':-1,'mud':-2.0**-l}; hdr(d,l,g,'sgd')
                    le(d,0,('forced',gname,l,0,g))
    for l in lens:
        for g in GREP_L:
            d={'nuE':-1,'lam':-(l-7),'eta':-1,'mul':-2.0**-l}; hdr(d,l,g,'sgl'); optt(d,1,l,7,'om')
            le(d,0,('end',l,g))
    c=np.zeros(nv)
    c[idx['lam']]=-1; c[idx['mul']]=1; c[idx['mud']]=1; c[idx['eta']]=L; c[idx['nuE']]=1
    c[idx['th0']]=Hcrude; c[idx['sgl']]=286; c[idx['sgd']]=30; c[idx['nuF']]=2
    for t in range(len(taus)): c[idx[('th',t)]]=71+DB
    for g in G: c[idx[('nu',g)]]=len(G[g])
    Aeq=np.zeros((1,nv)); Aeq[0,idx['lam']]=1; Aeq[0,idx['th0']]=1
    for t in range(len(taus)): Aeq[0,idx[('th',t)]]=1
    beq=[1]
    bounds=[(None,None)]*nv
    for k in ['lam','mud','eta','th0','sgl','sgd','nuF']: bounds[idx[k]]=(0,None)
    for t in range(len(taus)): bounds[idx[('th',t)]]=(0,None)
    for o in OPTS['opt']: bounds[idx[('om',o)]]=(0,None); bounds[idx[('omd',o)]]=(0,None)
    for g in G: bounds[idx[('nu',g)]]=(0,None)
    res=linprog(c,A_ub=np.array(A),b_ub=np.array(b),A_eq=Aeq,b_eq=beq,bounds=bounds,method='highs')
    if res.status!=0: print(res.message); return None
    if ret: return res,names,idx,lab
    return res.fun,res,lab
def iterate(L,s,DB=100,iters=80):
    taus=[[5]*19,[3,3,3,4,4,4,5,5,5,6,6,6,6,6,7,7,5,5,5]]
    taus=[t for t in taus if sum(2.0**-x for x in t)<=1]
    best=None
    for it in range(iters):
        val,res,lab=solve(L,s,taus,DB)
        y=-res.ineqlin.marginals
        bf=[0.0]*19
        for w,lb in zip(y,lab):
            if lb is None or w<1e-9: continue
            if lb[0]=='end': l,g=lb[1],lb[2]
            else: l,g=lb[2],lb[4]
            bf[l]+=w
            if g>=1:
                k=(g-1)//138; r=g-138*k
                bf[18]+=w*k
                if r<3: bf[0]+=w*r
                elif r<=10: bf[17]+=w
                else: bf[18]+=w
        cfg=[]
        for w,lb in zip(y,lab):
            if lb is None or w<1e-9: continue
            if lb[0]=='end': cfg.append((w,lb[1],lb[2]))
            else: cfg.append((w,lb[2],lb[4]))
        from tauopt import improve, tau_obj
        t0=huff19(bf)
        cands=[t0]+taus
        bestt=min(cands,key=lambda t:tau_obj(t,cfg))
        tau,tv=improve(bestt,cfg,rounds=3000,seed=it)
        print('iter',it,'val',round(val,2),'tau',tau,'obj',round(tv,1),'menu-best',round(min(tau_obj(t,cfg) for t in taus),1),flush=True)
        if tau in taus or tv>min(tau_obj(t,cfg) for t in taus)-1e-6: break
        taus.append(tau)
    return val,taus
if __name__=='__main__':
    L=int(sys.argv[1]); s=0
    DB=float(sys.argv[2]) if len(sys.argv)>2 else 100
    if len(sys.argv)>3 and 't' in sys.argv[3]: OPTS['tight']=True
    if len(sys.argv)>3 and 'o' in sys.argv[3]: OPTS['opt']=[(1,1),(2,1),(1,2),(3,1),(2,2),(1,3)]
    val,taus=iterate(L,s,DB)
    print('L',L,'final',val,'budget',8*L-10)
    print('taus',taus)
