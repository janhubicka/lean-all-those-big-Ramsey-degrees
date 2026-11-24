"""Independent literal enumeration of the four diary event types, sizes 1--4.

This enumerates coding sets directly and checks for duplicate executions.
It is separate from the Lean recurrence and is not an infinite Ramsey proof."""

from collections import Counter

def generate(n):
    seen={}; count=Counter()
    def rec(active,U,m,allow_d,events):
        k=len(active)
        if not k:
            if m==0:
                key=tuple(sorted(U));assert key not in seen
                seen[key]=events;count[len(events)]+=1
            return
        if m<k:return
        for d in active:
            opts=[]
            if k+1<=m:opts.append('a')
            if m:opts.append('b')
            if '2' not in d:
                if m>k:opts.append('c')
                if allow_d:opts.append('d')
            for e in opts:
                nextactive=[]
                for u in active:
                    if u!=d:nextactive.append(u+('0' if u<d else '2'))
                    else:nextactive+=([u+'0',u+'2'] if e=='a' else [u+'1'] if e in 'cd' else [])
                rec(nextactive,U+([d] if e in 'bc' else []),m-(e in 'bc'),e in 'ab',events+e)
    rec([''],[],n,False,'')
    return seen,count
if __name__ == "__main__":
    for n in range(1,5):
        seen,count=generate(n)
        print(n,len(seen),'maxheight',max(count),'height counts',dict(sorted(count.items())))
