import sys, os, math, ast
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dual4
from dual import XL, XD, st, fib
from dual2 import entry, gapcost

def lastlist(fn):
    for line in open(fn):
        if line.startswith('taus '): t=ast.literal_eval(line[5:])
    return t

def make(L, s, taus, DB, D=2**20, verbose=True):
    res,names,idx,lab=dual4.solve(L,s,taus,DB,ret=True)
    x=res.x
    val=lambda k: x[idx[k]]
    lam=round(D*val('lam')); md=max(0,round(D*val('mud')/2**15)); ml=round(D*val('mul')/2**15)
    eta=max(0,round(D*val('eta'))); kap=round(D*val('kap'))
    P=[0]+[math.ceil(D*val(('pi',u))-1e-9) for u in range(1,21)]
    R=[0]+[math.ceil(D*val(('rho',v))-1e-9) for v in range(1,29)]
    # u=0 or v=0 rows: need P[0]+R[v] >= D*max(0,v-24) etc.
    for u in range(0,21):
        for v in range(0,29):
            need=D*max(0,u+v-24)
            if P[u]+R[v]<need:
                if u==0: P[0]+=need-P[0]-R[v]
                else: R[v]+=need-P[u]-R[v]
    # re-check after bumps (bumping R[v] for u keeps earlier ones fine)
    for u in range(0,21):
        for v in range(0,29):
            assert P[u]+R[v]>=D*max(0,u+v-24)
    menu=[]
    for t,tau in enumerate(taus):
        th=round(D*val(('th',t)))
        if th>0: menu.append((tau,th))
    sgl=max(0,round(D*val('sgl'))); sgd=max(0,round(D*val('sgd')))
    thsum=sum(th for _,th in menu)
    th0=D-lam-thsum
    assert th0>=0, (th0,lam,thsum)
    def capz(l):
        fb=fib(l+1-s)
        return L-1 if fb==0 else min(L-1,(L+1)//fb)
    def ment(l): return sum(th*entry(tau,l) for tau,th in menu)
    def mgap(g): return sum(th*gapcost(tau,g) for tau,th in menu)
    bgl=max(mgap(g)-sgl*(g+1) for g in range(286))
    bgd=max(mgap(g)-sgd*(g+1) for g in range(30))
    def xl(c): return XL[c-257] if 0<=c-257<len(XL) else 0
    def al(c,l): return (P[l+xl(c)] if c>=257 else 0)-lam*(l-st(c))-eta+(kap if c>=257 else 0)
    def bl(l): return -ml*2**(15-l)+ment(l)
    def ad(d,l): return R[l+XD[d]]-lam*(l-5)-kap
    def bd(l): return -md*2**(15-l)+ment(l)
    nul=[]
    for c in range(286):
        m=None
        for l in range(1,16):
            cp=capz(l)
            if cp<1: continue
            v=max(al(c,l)+bl(l)+bgl, al(c,l)*cp+bl(l)+bgl)
            m=v if m is None else max(m,v)
        if m is None: m=0
        if c!=256: m=max(m,0)
        nul.append(m)
    nud=[]
    for d in range(30):
        m=0
        for l in range(1,16):
            cp=capz(l)
            if cp<1: continue
            m=max(m,ad(d,l)+bd(l)+bgd, ad(d,l)*cp+bd(l)+bgd)
        nud.append(m)
    nuF=max([0]+[bd(l)+bgd-nud[d] for d in range(30) for l in range(1,16)])
    final=th0*2283+thsum*(71+DB)-lam+2**15*(ml+md)+eta*L+sum(nul)+sum(nud)+2*nuF+286*sgl+30*sgd
    budget=D*(8*L-10)
    if verbose: print('L',L,'s',s,'menu',len(menu),'LPval',round(res.fun,2),'final/D',final/D,'budget',8*L-10,'OK' if final<=budget else 'FAIL',flush=True)
    return dict(L=L,s=s,D=D,lam=lam,ml=ml,md=md,eta=eta,kap=kap,P=P,R=R,nul=nul,nud=nud,nuF=nuF,th0=th0,menu=menu,
                dbl=DB,sgl=sgl,sgd=sgd,bgl=bgl,bgd=bgd,final=final,budget=budget)

def zn(v): return '(%d)'%v if v<0 else str(v)
def zl(l): return '[' + '; '.join(zn(v) for v in l) + ']'
def coq(name, c):
    menu='[' + '; '.join('(%s, %s)'%(zl(t),zn(th)) for t,th in c['menu']) + ']'
    vals=[c['L'],c['s'],c['D'],c['lam'],c['ml'],c['md'],c['eta'],c['kap']]
    return ('Definition %s : cert := mkCert %s\n  %s\n  %s\n  %s\n  %s\n  %s %s\n  %s\n  %s.\n'
            % (name,' '.join(zn(v) for v in vals),zl(c['P']),zl(c['R']),zl(c['nul']),zl(c['nud']),
               zn(c['nuF']),zn(c['th0']),menu,' '.join(zn(v) for v in [c['dbl'],c['sgl'],c['sgd'],c['bgl'],c['bgd']])))

if __name__=='__main__':
    which=sys.argv[1:]
    out=[]
    for ml in range(1,10):
        L=2**(ml+6)
        if which and str(L) not in which: continue
        s=0 if L<=2048 else 2
        if L==128: taus=lastlist(os.path.join(HERE,'taus_128.txt')); DB=75
        elif L==256: taus=lastlist(os.path.join(HERE,'taus_256.txt')); DB=100
        else: taus=[]; DB=100
        c=make(L,s,taus,DB)
        out.append(coq('cert%d'%L,c))
        print(coq('cert%d'%L,c))
