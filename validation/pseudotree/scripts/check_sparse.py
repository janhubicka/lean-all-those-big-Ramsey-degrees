"""Independent finite audit of the sparse coding construction and diary extraction.

Checks every chain of size at most four among the first 50 coding points.
These finite checks do not establish the infinite Ramsey statements."""

from functools import lru_cache
from itertools import combinations

@lru_cache(None)
def F(i,m,k):
    if m==k==0:return 1
    if m<k or k==0:return 0
    if i==0:return k*F(0,m,k+1)+k*F(0,m-1,k-1)
    return 2*k*F(1,m,k+1)+F(0,m-1,k-1)+2*(k-1)*F(1,m-1,k-1)+F(1,m-1,k)

def make_P(N):
    W=['']; P=[]; crit={}
    for s in range(N):
        u=W[0]; curr=list(W)
        for j,v in enumerate((u,u+'0',u+'02')):
            crit[3*s+j]=v
            nxt=[]
            for w in curr:
                if w==v:
                    nxt.extend([w+'0',w+'2'] if j<2 else [w+'1'])
                else:nxt.append(w+('0' if w<v else '2'))
            curr=nxt
        rem=[]
        for w in W[1:]: rem.append(next(z for z in curr if z.startswith(w)))
        W=rem+[u+'000',u+'021',u+'222'];P.append(u+'02')
    return P,crit

def bkey(s):return tuple({'2':0,'*':1,'0':2}[x] for x in s+'*')
def leq(s,t):
    ss=s.split('1');tt=t.split('1');k=len(ss)-1;l=len(tt)-1
    return k<=l and ss[:k]==tt[:k] and bkey(ss[k])<=bkey(tt[k])
def lcp(s,t):
    i=0
    while i<min(len(s),len(t)) and s[i]==t[i]:i+=1
    return s[:i]
def extract(C):
    M={lcp(x,y) for x in C for y in C}; ps=sorted(map(len,M)); assert len(ps)==len(set(ps))
    vmax=next(x for x in C if all(leq(y,x) for y in C))
    K=set(ps)
    for p,q in zip(ps,ps[1:]):
        if q<=len(vmax) and vmax[p]!='1':
            ks=[k for k in range(p+1,q) if vmax[k]=='1']
            if ks: K.add(ks[0])
    K=sorted(K)
    U={''.join(x[k] for k in K if k<len(x)) for x in C}; D={x[:i] for x in U for i in range(len(x)+1)}
    types=[]
    for j in range(len(K)):
        lev={x for x in D if len(x)==j};crit=[]
        for x in lev:
            sons={i for i in '012' if x+i in D}
            if x in U:
                assert sons in (set(),{'1'}),(C,U,D,x,sons)
                typ='b' if not sons else 'c';crit.append((x,typ))
            elif sons=={'0','2'}:crit.append((x,'a'))
            elif sons=={'1'}:crit.append((x,'d'))
            else:assert len(sons)==1 and sons<={'0','2'}
        assert len(crit)==1,(C,U,D,j,crit)
        x,typ=crit[0]
        if typ in 'cd': assert '2' not in x
        if typ=='d': assert j>0 and types[-1] not in 'cd'
        for y in lev-{x}:assert y+('0' if y<x else '2') in D
        types.append(typ)
    # Check strong/ray-preserving all edges using source representatives.
    e={x[:j]:w[:K[j]] for w,x in ((w,''.join(w[k] for k in K if k<len(w))) for w in C) for j in range(len(x)+1)}
    for x in D:
        if x:
            assert e[x].startswith(e[x[:-1]]+x[-1])
            if x[-1] in '02':assert '1' not in e[x][len(e[x[:-1]])+1:]
    return tuple(sorted(U)),types

if __name__ == "__main__":
    print('recurrence', [F(1,n,1) for n in range(1,8)])
    P,crit=make_P(50)
    print('first code nodes',P[:4])
    for n in (1,2,3,4):
        diaries=set();chains=0
        for C in combinations(P,n):
            if all(leq(x,y) or leq(y,x) for x,y in combinations(C,2)):
                chains+=1; key,types=extract(C); diaries.add(key)
        print(n,'chains',chains,'different diaries',len(diaries),'total expected',F(1,n,1))
