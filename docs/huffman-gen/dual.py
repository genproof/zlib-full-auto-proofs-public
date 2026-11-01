import sys, numpy as np
from scipy.optimize import linprog
XL=[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0]
XD=[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13]
def st(c): return 8 if c<144 else 9 if c<256 else 7 if c<280 else 8
FIB=[0,1]
while len(FIB)<40: FIB.append(FIB[-1]+FIB[-2])
def fib(n): return FIB[n] if n>=0 else 0
def groups():
    G={}
    for c in range(256): G.setdefault(('lit',st(c)),[]).append(c)
    for j in range(257,286): G.setdefault(('len',st(j),XL[j-257]),[]).append(j)
    for d in range(30): G.setdefault(('dist',XD[d]),[]).append(d)
    return G
def solve(L,s,Hcrude=2283,verbose=False):
    def cap(l):
        fb=fib(l+1-s)
        c=L-1 if fb==0 else min(L-1,(L+1)//fb)
        return c
    G=groups()
    names=[]; idx={}
    def V(k):
        if k not in idx: idx[k]=len(names); names.append(k)
        return idx[k]
    for k in ['lam','mul','mud','eta','kap','nuE']: V(k)
    for u in range(1,21): V(('pi',u))
    for v in range(1,29): V(('rho',v))
    for g in G: V(('nu',g))
    nv=len(names)
    A=[];b=[]
    def le(d,rhs):
        r=np.zeros(nv)
        for k,c in d.items(): r[idx[k]]+=c
        A.append(r); b.append(rhs)
    for u in range(1,21):
        for v in range(1,29):
            le({('pi',u):-1,('rho',v):-1},-max(0,u+v-24))
    lens=[l for l in range(1,16) if cap(l)>=1]
    for g,codes in G.items():
        for l in lens:
            for f in sorted(set([1,cap(l)])):
                d={('nu',g):-1}
                if g[0]=='lit':
                    d['lam']=d.get('lam',0)-f*(l-g[1]); d['eta']=d.get('eta',0)-f; d['mul']=-2.0**-l
                elif g[0]=='len':
                    u=l+g[2]; d[('pi',u)]=f; d['lam']=-f*(l-g[1]); d['eta']=-f; d['kap']=f; d['mul']=-2.0**-l
                else:
                    v=l+g[1]; d[('rho',v)]=f; d['lam']=-f*(l-5); d['kap']=-f; d['mud']=-2.0**-l
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
    val=res.fun+Hcrude
    if verbose:
        x=res.x
        for k in names:
            if abs(x[idx[k]])>1e-9: print(k,round(x[idx[k]],5))
    return val,res
if __name__=='__main__':
    for ml in range(1,10):
        L=2**(ml+6); s=0 if L<=2048 else 2
        val,res=solve(L,s)
        print(L,s,'bound',round(val,1),'budget',8*L-10, 'OK' if val<=8*L-10 else 'FAIL')
