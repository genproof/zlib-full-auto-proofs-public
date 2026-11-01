import random
from dual2 import entry, gapcost
def tau_obj(tau, cfg):
    # cfg: list of (w, l, g)
    return sum(w*(entry(tau,l)+gapcost(tau,g)) for w,l,g in cfg)
def kraft_ok(t): return all(1<=x<=15 for x in t) and sum(2.0**-x for x in t)<=1+1e-12
def improve(tau, cfg, rounds=4000, seed=0):
    rnd=random.Random(seed)
    best=list(tau); bv=tau_obj(best,cfg)
    for r in range(rounds):
        t=list(best)
        k=rnd.choice([1,1,2,2,3])
        for _ in range(k):
            i=rnd.randrange(19); t[i]=max(1,min(15,t[i]+rnd.choice([-2,-1,1,2])))
        # repair kraft by lengthening the cheapest-to-lengthen symbols
        tries=0
        while sum(2.0**-x for x in t)>1+1e-12 and tries<100:
            j=rnd.randrange(19)
            if t[j]<15: t[j]+=1
            tries+=1
        if not kraft_ok(t): continue
        v=tau_obj(t,cfg)
        if v<bv-1e-9: best,bv=t,v
    return best,bv
