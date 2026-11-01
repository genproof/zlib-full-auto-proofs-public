import sys, numpy as np
from scipy.optimize import linprog
from dual import XL, XD, st, fib, groups
UMAX=35; VMAX=43; DMAX=30
def solve(L,Hcrude=2283):
    def cap(l):
        fb=fib(l+1)
        return min(L-1,(L+1)//fb)
    G=groups()
    names=[]; idx={}
    def V(k):
        if k not in idx: idx[k]=len(names); names.append(k)
        return idx[k]
    for k in ['lam','mul','mud','eta','kap','nuE']: V(k)
    for u in range(0,UMAX+1): V(('pi',u))
    for v in range(0,VMAX+1): V(('rho',v))
    for g in G: V(('nu',g))
    nv=len(names); A=[];b=[]
    def le(d,rhs):
        r=np.zeros(nv)
        for k,c in d.items(): r[idx[k]]+=c
        A.append(r); b.append(rhs)
    for u in range(0,UMAX+1):
        for v in range(0,VMAX+1):
            le({('pi',u):-1,('rho',v):-1},-max(0,u+v-24))
    lens=[l for l in range(1,DMAX+1) if cap(l)>=1]
    for g,codes in G.items():
        for l in lens:
            for f in sorted(set([1,cap(l)])):
                d={('nu',g):-1}
                if g[0]=='lit':
                    d['lam']=-f*(l-g[1]); d['eta']=-f; d['mul']=-2.0**-l
                elif g[0]=='len':
                    d[('pi',l+g[2])]=f; d['lam']=-f*(l-g[1]); d['eta']=-f; d['kap']=f; d['mul']=-2.0**-l
                else:
                    d[('rho',l+g[1])]=f; d['lam']=-f*(l-5); d['kap']=-f; d['mud']=-2.0**-l
                le(d,0)
    for l in lens:
        le({'nuE':-1,'lam':-(l-7),'eta':-1,'mul':-2.0**-l},0)
    c=np.zeros(nv)
    c[idx['lam']]=-Hcrude-1; c[idx['mul']]=1; c[idx['mud']]=1; c[idx['eta']]=L; c[idx['nuE']]=1
    for g,codes in G.items(): c[idx[('nu',g)]]=len(codes)
    bounds=[(None,None)]*nv
    bounds[idx['lam']]=(0,1); bounds[idx['mud']]=(0,None); bounds[idx['eta']]=(0,None)
    for g in G: bounds[idx[('nu',g)]]=(0,None)
    res=linprog(c,A_ub=np.array(A),b_ub=np.array(b),bounds=bounds,method='highs')
    return res.fun+Hcrude,res,names,idx,lens
if __name__=='__main__':
    for L in [4096,8192,16384,32768]:
        val,res,names,idx,lens=solve(L)
        print(L,'LMAX',max(lens),'opt',round(val,2),'budget',8*L-10,'slack',round(8*L-10-val,1),flush=True)
