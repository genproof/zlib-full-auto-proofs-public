"""The certificates of src/proof/huffman/Repair.v (cert_table): exact rational linear-programming certificates
for the bit-length repair bound (gen_bitlen with max_length M = 7, the bit-length tree: n <= NMAX leaves, total
weight W <= 316, target T).  For each depth profile d whose repair the per-position caps do not bound by T, a
dual solution of the linear program (scipy.optimize.linprog, HiGHS) gives the support of a certificate, which is
then solved exactly over the rationals and scaled to integers; a profile that cannot occur gets a Farkas
certificate.  docs/huffman-gen/certs.py formats them as Repair.v's cert_table (T = 75, NMAX = 15).

Usage:  python3 docs/huffman-gen/repair_cert.py T NMAX   (prints the certificates as JSON)"""
import sys, json, math
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog
F=[0,1,1]
while len(F)<40: F.append(F[-1]+F[-2])


def certs(T, NMAX):
    M=7; W=316
    def repl(d):
        c=[0]*16
        for x in d: c[min(x,M)]+=1
        I=sum(c[l]*2**(M-l) for l in range(1,M+1))-2**M
        for _ in range(I):
            b=M-1
            while c[b]==0: b-=1
            c[b]-=1; c[b+1]+=2; c[M]-=1
        L=[]
        for l in range(M,0,-1): L+=[l]*c[l]
        return L
    allp={}
    def gen(l, rem, nl, acc):
        if l>12:
            if rem==0: allp.setdefault(len(acc),[]).append(acc)
            return
        unit=1<<(12-l)
        if rem>nl*unit: return
        for x in range(min(rem//unit,nl)+1):
            gen(l+1, rem-x*unit, nl-x, [l]*x+acc)
    gen(1,4096,NMAX,[])
    def simple(d,L): return sum((Lk-dk)*(W//F[dk+1]) if Lk>dk else (Lk-dk) for Lk,dk in zip(L,d))
    def solve_exact(rows, rhs_vec, support):
        # solve sum_{i in S} y_i rows[i] = rhs_vec exactly (rows: list of int lists), return dict or None
        S=list(support); n=len(rhs_vec)
        # augmented matrix n x (|S|+1)
        Mx=[[Fr(rows[i][k]) for i in S]+[Fr(rhs_vec[k])] for k in range(n)]
        m=len(S); r=0; piv=[]
        for col in range(m):
            p=None
            for i in range(r,n):
                if Mx[i][col]!=0: p=i; break
            if p is None: continue
            Mx[r],Mx[p]=Mx[p],Mx[r]
            pv=Mx[r][col]; Mx[r]=[x/pv for x in Mx[r]]
            for i in range(n):
                if i!=r and Mx[i][col]!=0:
                    fct=Mx[i][col]; Mx[i]=[a-fct*b for a,b in zip(Mx[i],Mx[r])]
            piv.append(col); r+=1
            if r==n: break
        for i in range(r,n):
            if Mx[i][m]!=0: return None
        y={S[c]:Fr(0) for c in range(m)}
        for i,col in enumerate(piv): y[S[col]]=Mx[i][m]
        return y
    out=[]; worst=Fr(0); nsimple=0
    for n in sorted(allp):
        for d in allp[n]:
            L=repl(d)
            if L==d or simple(d,L)<=T: nsimple+=1; continue
            a=[Lk-dk for Lk,dk in zip(L,d)]
            rows=[];rhs=[];kind=[]
            for k in range(n):
                r=[0]*n; r[k]=F[d[k]+1]; rows.append(r); rhs.append(W); kind.append(('cap',k))
            for k in range(n):
                r=[0]*n; r[k]=-1; rows.append(r); rhs.append(-1); kind.append(('low',k))
            for k in range(n-1):
                r=[0]*n; r[k]=1; r[k+1]=-1; rows.append(r); rhs.append(0); kind.append(('mono',k))
            rows.append([1]*n); rhs.append(W); kind.append(('sum',0))
            for e in allp[n]:
                r=[dk-ek for dk,ek in zip(d,e)]
                if any(r): rows.append(r); rhs.append(0); kind.append(('opt',e))
            A=np.array(rows,dtype=float); b=np.array(rhs,dtype=float)
            res=linprog(-np.array(a,dtype=float),A_ub=A,b_ub=b,bounds=[(None,None)]*n,method='highs')
            if res.status==0:
                yf=-res.ineqlin.marginals
                S=[i for i in range(len(rows)) if yf[i]>1e-9]
                y=solve_exact(rows,a,S)
                assert y is not None and all(v>=0 for v in y.values()), ('exact dual failed',d)
            else:
                # Farkas: y>=0, y A = 0, y b = -1
                m=len(rows)
                r2=linprog(np.zeros(m),A_eq=np.vstack([A.T,b[None,:]]),b_eq=np.concatenate([np.zeros(n),[-1.0]]),
                           bounds=[(0,None)]*m,method='highs')
                assert r2.status==0, ('no farkas',d)
                S=[i for i in range(m) if r2.x[i]>1e-9]
                rowsb=[rows[i]+[rhs[i]] for i in range(m)]
                yfk=solve_exact(rowsb,[0]*n+[-1],S)
                assert yfk is not None and all(v>=0 for v in yfk.values()), ('exact farkas failed',d)
                # combine with box certificate: caps cover positive a
                y={}
                for k in range(n):
                    if a[k]>0: y[k]=Fr(math.ceil(a[k]/F[d[k]+1]))
                box=sum(v*rhs[i] for i,v in y.items())
                t=max(Fr(0),(box-T)/1)+1   # y_f b = -1 per unit of t
                for i,v in yfk.items(): y[i]=y.get(i,Fr(0))+t*v
            # exact verification
            coef=[sum(y.get(i,0)*rows[i][k] for i in range(len(rows))) for k in range(n)]
            assert all(coef[k]>=a[k] for k in range(n)), ('coef',d)
            bound=sum(v*rhs[i] for i,v in y.items())
            assert bound<=T, ('bound',d,bound)
            worst=max(worst,bound)
            Q=1
            for v in y.values(): Q=Q*v.denominator//math.gcd(Q,v.denominator)
            yi={i:int(v*Q) for i,v in y.items() if v!=0}
            cert=dict(d=d,Q=Q,alpha=[yi.get(k,0) for k in range(n)],beta=[yi.get(n+k,0) for k in range(n)],
                      gamma=[yi.get(2*n+k,0) for k in range(n-1)],sigma=yi.get(3*n-1,0),
                      alts=[(yi[i],kind[i][1]) for i in sorted(yi) if kind[i][0]=='opt'],bound=float(bound))
            out.append(cert)
    print('simple',nsimple,'certs',len(out),'worst',float(worst),'maxQ',max(c['Q'] for c in out),
          'maxval',max(max(c['alpha']+c['beta']+c['gamma']+[c['sigma']]+[v for v,_ in c['alts']]) for c in out), file=sys.stderr)
    return out


if __name__ == '__main__':
    json.dump(certs(int(sys.argv[1]), int(sys.argv[2])), sys.stdout)
