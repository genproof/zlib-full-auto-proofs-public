import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dualD
from dual import XL, XD, st, fib
UMAX=35; VMAX=43; DMAX=30
SLACK={4096:15360, 8192:32768, 16384:67584, 32768:139264}
def zn(v): return '(%d)'%v if v<0 else str(v)
def zl(l): return '[' + '; '.join(zn(v) for v in l) + ']'
def make(L, D=2**34):
    val,res,names,idx,lens=dualD.solve(L)
    x=res.x; g=lambda k: x[idx[k]]
    lam=min(D,max(0,round(D*g('lam')))); ml=round(D*g('mul')/2**30); md=max(0,round(D*g('mud')/2**30))
    eta=max(0,round(D*g('eta'))); kap=round(D*g('kap'))
    P=[math.ceil(D*g(('pi',u))-1e-6) for u in range(UMAX+1)]
    R=[math.ceil(D*g(('rho',v))-1e-6) for v in range(VMAX+1)]
    for u in range(UMAX+1):
        for v in range(VMAX+1):
            need=D*max(0,u+v-24)
            if P[u]+R[v]<need: R[v]+=need-P[u]-R[v]
    for u in range(UMAX+1):
        for v in range(VMAX+1): assert P[u]+R[v]>=D*max(0,u+v-24)
    def capz(l): return min(L-1,(L+1)//fib(l+1))
    def xl(c): return XL[c-257] if c>=257 else 0
    def al(c,l): return (P[l+xl(c)] if c>=257 else 0)-lam*(l-st(c))-eta+(kap if c>=257 else 0)
    def bl(l): return -ml*2**(30-l)
    def ad(d,l): return R[l+XD[d]]-lam*(l-5)-kap
    def bd(l): return -md*2**(30-l)
    nul=[]
    for c in range(286):
        m=0 if c!=256 else None
        for l in range(1,DMAX+1):
            cp=capz(l)
            if cp<1: continue
            v=max(al(c,l)+bl(l), al(c,l)*cp+bl(l))
            m=v if m is None else max(m,v)
        nul.append(m)
    nud=[]
    for d in range(30):
        m=0
        for l in range(1,DMAX+1):
            cp=capz(l)
            if cp>=1: m=max(m,ad(d,l)+bd(l),ad(d,l)*cp+bd(l))
            m=max(m,bd(l))
        nud.append(m)
    th0=D-lam
    final=th0*2283-lam+2**30*(ml+md)+eta*L+sum(nul)+sum(nud)
    sl=SLACK[L]
    print('L',L,'LP',round(val,2),'final/D',round(final/D,3),'budget-slack',8*L-10-sl,'OK' if final<=D*(8*L-10-sl) else 'FAIL',
          'maxint',max(abs(v) for v in P+R+nul+nud+[lam,ml,md,eta,kap]),flush=True)
    vals=[L,D,lam,ml,md,eta,kap]
    return ('Definition certd%d : certd := mkCertD %s\n  %s\n  %s\n  %s\n  %s.\n'
            % (L,' '.join(zn(v) for v in vals),zl(P),zl(R),zl(nul),zl(nud)))
if __name__=='__main__':
    out=''
    for L in [4096,8192,16384,32768]: out+=make(L)+'\n'
    print(out)
