#!/usr/bin/env python3
"""nd-sym search generator (stdlib only). No checker code is imported.
Run: bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym/gen_sym.py --help'
The supply is an untrusted optimization; check_sym.py recomputes all arithmetic.
"""
import sys
sys.dont_write_bytecode=True
import argparse
import collections
import itertools
import json
import math
import pathlib
import time

HERE = pathlib.Path(__file__).resolve().parent

def valuation(x, p):
    v = 0
    while x and x % p == 0:
        x //= p
        v += 1
    return v

class Budget(Exception):
    pass

class Generator:
    def __init__(self, coefs, K, qmin, supply=None, seconds=60, lifts=10000000,
                 nodes=500000, mcap=10**24, depth=100, sumsets=True, pin2=True, pin_digits=3):
        self.coefs = tuple(sorted(coefs))
        self.groups = tuple(sorted(collections.Counter(self.coefs).items()))
        self.K, self.qmin, self.t0 = K, qmin, valuation(K, 2)
        assert K > 0 and K % 5 and qmin > self.t0
        assert all(c > 0 and c % 10 for c in coefs)
        self.dim = len(coefs) + 1
        self.pin2 = bool(pin2 and qmin >= self.t0+3)
        parity_map={1:(0,0),3:(1,0),7:(0,1),5:(1,1)}
        self.parities=parity_map[(K >> self.t0)%8] if self.pin2 else None
        self.pin_digits=min(pin_digits,qmin)
        self.pin_pairs=[]
        self.cosets={}
        if self.pin_digits:
            mod=5**self.pin_digits*2**max(0,self.pin_digits-self.t0)
            def period(b):
                value=b%mod; n=1
                while value!=1:
                    value=value*b%mod;n+=1
                return n
            self.pin_periods=(period(3),period(7))
            p3,p7=self.pin_periods
            residues7=collections.defaultdict(list)
            for w in range(p7): residues7[pow(7,w,mod)].append(w)
            unit=K//2**self.t0%mod
            for a in range(p3):
                for w in residues7[unit*pow(3,-a,mod)%mod]:
                    if not self.pin2 or (a%2,w%2)==self.parities:
                        self.pin_pairs.append((a,w))
        self.supply = supply if supply is not None else json.loads((HERE/'supply.json').read_text())
        self.byperiod = collections.defaultdict(list)
        for p, d, a, w in self.supply:
            self.byperiod[d].append((p, d, a, w, math.lcm(a, w)))
        self.deadline = time.monotonic() + seconds
        self.liftcap, self.nodecap, self.mcap, self.depthcap = lifts, nodes, mcap, depth
        self.sumsets = sumsets
        self.lifts = 0
        self.nodes = []
        self.trace = []
        self.at = None
        self.tables, self.alcache, self.inv, self.sumcache = {}, {}, {}, {}
        self.kills = collections.Counter()

    def check_budget(self):
        if self.lifts > self.liftcap: raise Budget('lifts')
        if len(self.nodes) > self.nodecap: raise Budget('nodes')
        if time.monotonic() > self.deadline: raise Budget('time')

    def zero(self):
        return (0,) + (0,) * len(self.coefs)

    def nested(self, r):
        out = [r[0]]
        i = 1
        for c, n in self.groups:
            out.append(list(r[i:i+n]))
            i += n
        return out

    def key(self, pt, M):
        out = [pt[0] % M]
        i = 1
        for c, n in self.groups:
            out.extend(sorted(q % M for q in pt[i:i+n]))
            i += n
        return tuple(out)

    def xm(self, r, m, period):
        key = (m, period)
        if period <= 20000:
            if key not in self.tables:
                t = [1]
                for _ in range(1, period): t.append(t[-1]*10 % m)
                self.tables[key] = t
            t = self.tables[key]
            return (t[r[0] % period] + self.K + sum(c*t[e % period] for c,e in zip(self.coefs,r[1:]))) % m
        return (pow(10,r[0],m) + self.K + sum(c*pow(10,e,m) for c,e in zip(self.coefs,r[1:]))) % m

    def sig(self, r, M):
        j = valuation(M,3)
        x = self.xm(r,3**(j+2),3**j)
        a = (j+2,None) if not x else (valuation(x,3),)*2
        if M % 6: return a,(0,None)
        i = valuation(M,7)
        x = self.xm(r,7**(i+1),6*7**i)
        return a, ((i+1,None) if not x else (valuation(x,7),)*2)

    def aligned(self, M, a, w):
        kind = (a[1] is None,w[1] is None)
        key = (M,kind)
        if key not in self.alcache:
            es = [e for d,ee in self.byperiod.items() if M % d == 0 for e in ee]
            def strength(e):
                o3,o7=e[2],e[3]
                if self.pin2:
                    o3//=math.gcd(o3,2);o7//=math.gcd(o7,2)
                h = math.lcm(o3 if kind[0] else 1,o7 if kind[1] else 1)
                return ((e[0]-1)//h, -e[0])
            self.alcache[key] = sorted((e for e in es if not all(kind) or self.pin2 or (e[0]-1)//e[4]>1 or e[0]<=10000),key=strength,reverse=True)
        return self.alcache[key]

    def forbidden(self, T, e, a, w):
        p,d,o3,o7,H = e
        if T == 0: return True
        if self.pin_digits:
            # Unknown exponents range through their decimal residue classes plus
            # independent multiples of the decimal periods. Lower bounds do not
            # shrink the image of these rays in a finite multiplicative group.
            cache=(p,a[1],w[1])
            if cache not in self.cosets:
                p3,p7=self.pin_periods
                h=math.lcm(o3//math.gcd(o3,p3) if a[1] is None else 1,
                           o7//math.gcd(o7,p7) if w[1] is None else 1)
                allowed=set()
                for ar,wr in self.pin_pairs:
                    if a[1] is not None and a[0]%p3!=ar: continue
                    if w[1] is not None and w[0]%p7!=wr: continue
                    aa=ar if a[1] is None else a[0]
                    ww=wr if w[1] is None else w[0]
                    allowed.add(pow(pow(3,aa,p)*pow(7,ww,p)%p,h,p))
                self.cosets[cache]=(h,allowed,pow(2,-self.t0,p))
            h,allowed,inverse2=self.cosets[cache]
            return pow(T*inverse2%p,h,p) not in allowed
        alo,wlo=a[0],w[0]
        if self.pin2:
            pa,pw=self.parities
            if (a[1] is not None and alo%2!=pa) or (w[1] is not None and wlo%2!=pw): return True
            if a[1] is None: alo += (pa-alo)%2
            if w[1] is None: wlo += (pw-wlo)%2
            o3//=math.gcd(o3,2); o7//=math.gcd(o7,2); H=math.lcm(o3,o7)
        key=(p,alo,wlo)
        if key not in self.inv:
            self.inv[key]=pow(2,-self.t0,p)*pow(3,-alo,p)*pow(7,-wlo,p)%p
        z=T*self.inv[key]%p
        h = H if a[1] is None and w[1] is None else o3 if a[1] is None else o7 if w[1] is None else 1
        return (z != 1) if h==1 else pow(z,h,p)!=1

    def test(self, e, r, a, w):
        return self.forbidden(self.xm(r,e[0],e[1]),e,a,w)

    def kill(self, r, M, a, w, preferred=()):
        for e in preferred:
            if self.test(e,r,a,w): return e
        for e in self.aligned(M,a,w):
            if self.test(e,r,a,w): return e
        return None

    def sumkill(self, r, M, a, w):
        if not self.sumsets: return None
        candidates=[]
        for d,ee in self.byperiod.items():
            f=d//math.gcd(M,d)
            if 1<f<=7:
                candidates.extend(e for e in ee if ((e[0]-1)//e[4]>1 or self.pin2 or self.pin_digits) and e[0] <= 10**12)
        def strength(e):
            if self.pin_digits:
                self.forbidden(1,e,a,w)
                h,images,_=self.cosets[(e[0],a[1],w[1])]
                return ((e[0]-1)//(h*max(1,len(images))),-e[1])
            return ((e[0]-1)//e[4],-e[1])
        candidates.sort(key=strength,reverse=True)
        for e in candidates[:16]:
            self.check_budget()
            p,d,_,_,_=e
            if self.pin_digits and not self.cosets[(p,a[1],w[1])][1]:
                self.kills['empty_decimal_target']+=1
                return e
            g=math.gcd(M,d)
            vals={self.K % p}
            for c,q in zip((1,)+self.coefs,r):
                key=(p,g,c,q%g)
                if key not in self.sumcache:
                    self.sumcache[key] = {c*pow(10,q%g+j*g,p)%p for j in range(d//g)}
                term=self.sumcache[key]
                if len(vals)*len(term)>20000: break
                vals={(u+v)%p for u in vals for v in term}
            else:
                if all(self.forbidden(t,e,a,w) for t in vals):
                    self.kills['sumset']+=1
                    return e
        return None

    def lifts_of(self, r, M, f):
        """Split each repeated parent residue into an unordered multiset of its f lifts."""
        axes=[[(r[0]+M*t,) for t in range(f)]]
        i=1
        for c,n in self.groups:
            buckets=[]
            for b,m in sorted(collections.Counter(r[i:i+n]).items()):
                buckets.append(list(itertools.combinations_with_replacement([b+M*t for t in range(f)],m)))
            axes.append([tuple(sorted(itertools.chain.from_iterable(z))) for z in itertools.product(*buckets)])
            i+=n
        for z in itertools.product(*axes):
            yield tuple(itertools.chain.from_iterable(z))

    def lift_count(self, r, f):
        ans=f
        i=1
        for c,n in self.groups:
            for m in collections.Counter(r[i:i+n]).values(): ans*=math.comb(f+m-1,m)
            i+=n
        return ans

    def expand(self, r, M, f):
        self.at={'M':M,'factor':f,'predicted_lifts':self.lift_count(r,f),'r':self.nested(r)}
        if M*f>self.mcap: raise Budget('modulus')
        if self.lifts+self.at['predicted_lifts']>self.liftcap: raise Budget('lifts forecast')
        alive=[]
        used=[]
        M2=M*f
        parent_a,parent_w=self.sig(r,M)
        for rr in self.lifts_of(r,M,f):
            self.lifts+=1
            if self.lifts % 1024==0: self.check_budget()
            if f%3==0:
                j=valuation(M2,3); x=self.xm(rr,3**(j+2),3**j)
                a=(j+2,None) if not x else (valuation(x,3),)*2
            else: a=parent_a
            if M2%6==0 and (M%6!=0 or f%7==0):
                j=valuation(M2,7); x=self.xm(rr,7**(j+1),6*7**j)
                w=(j+1,None) if not x else (valuation(x,7),)*2
            else: w=parent_w
            e=self.kill(rr,M2,a,w,used)
            if e is None: alive.append((rr,a,w))
            elif e not in used: used.append(e)
        return alive,used

    def exact(self, N, r, M):
        """Generator-side exhaustive recursive subtraction with monotone equal positions.
        L is bounded solely by 10^L <= N-K; do not assume no decimal carries.
        """
        R=N-self.K
        if R<=0: return []
        out=[]
        for L in range(self.qmin,len(str(R))):
            rem=R-10**L
            def dfs(i,left,qs):
                if i==len(self.coefs):
                    pt=(L,)+tuple(qs)
                    if left==0 and self.key(pt,M)==r: out.append(list(pt))
                    return
                if left<=0: return
                low=self.qmin
                if i and self.coefs[i]==self.coefs[i-1]: low=qs[-1]+1
                for q in range(low,L):
                    if q in qs: continue
                    term=self.coefs[i]*10**q
                    if term>left: break
                    dfs(i+1,left-term,qs+[q])
            dfs(0,rem,[])
        return sorted(out)

    def new(self, r, M, parent):
        self.check_budget()
        i=len(self.nodes)
        self.nodes.append({'id':i,'p':parent,'m':M,'r':self.nested(r)})
        return i

    def leaf(self, i, r, M, a, w, known_alive=False):
        e=None if known_alive else self.kill(r,M,a,w)
        if e:
            self.nodes[i].update(k='l',x={'prime':e[0]})
            return True
        if a[1] is not None and w[1] is not None:
            N=(2**self.t0)*(3**a[0])*(7**w[0])
            self.nodes[i].update(k='l',x={'sz':[a[0],w[0]],'sol':self.exact(N,r,M)})
            self.kills['size']+=1
            return True
        return False

    def run(self, schedule=(2,3,7,3,2,2,2,3), root=None):
        r,M=root if root is not None else (self.zero(),1)
        i=self.new(r,M,-1)
        if self.leaf(i,r,M,*self.sig(r,M)): return self.nodes
        frontier=[(i,r,M,0)]
        for f in schedule:
            if not frontier: break
            nf=[]
            for i,r,M,dep in frontier:
                if f>3 and self.lift_count(r,f)>1000:
                    e=self.sumkill(r,M,*self.sig(r,M))
                    if e:
                        self.nodes[i].update(k='l',x={'prime':e[0]})
                        continue
                alive,used=self.expand(r,M,f)
                self.nodes[i].update(k='i',m2=M*f,c=[],rest=[e[0] for e in used])
                for rr,a,w in alive:
                    j=self.new(rr,M*f,i)
                    self.nodes[i]['c'].append(j)
                    if not self.leaf(j,rr,M*f,a,w,known_alive=True): nf.append((j,rr,M*f,dep))
            frontier=nf
            self.trace.append({'M':M*f,'frontier':len(nf),'nodes':len(self.nodes),'lifts':self.lifts})
        stack=frontier
        while stack:
            self.check_budget()
            i,r,M,dep=stack.pop()
            if dep>=self.depthcap: raise Budget('depth')
            a,w=self.sig(r,M)
            e=self.sumkill(r,M,a,w)
            if e:
                self.nodes[i].update(k='l',x={'prime':e[0]})
                continue
            if M%6:
                f=6//math.gcd(M,6)
            elif a[1] is None and w[1] is not None: f=3
            elif w[1] is None and a[1] is not None: f=7
            else:
                # Keep richness growing before choosing the expensive factor seven.
                rich=(2,3,2,3,2,2,3,7)
                f=rich[dep%len(rich)]
            alive,used=self.expand(r,M,f)
            self.nodes[i].update(k='i',m2=M*f,c=[],rest=[e[0] for e in used])
            for rr,aa,ww in alive:
                j=self.new(rr,M*f,i)
                self.nodes[i]['c'].append(j)
                if not self.leaf(j,rr,M*f,aa,ww,known_alive=True): stack.append((j,rr,M*f,dep+1))
        return self.nodes

    def write(self, path, scope='full', extra=None):
        assert all(n.get('k') in ('i','l') for n in self.nodes)
        meta={'k':'meta','format':'nd-sym','version':1,'domain':'unordered',
              'scope':scope,'groups':[list(x) for x in self.groups], 'K':self.K,
              'qmin':self.qmin,'dim':self.dim,'pin2':self.pin2,'pin_digits':self.pin_digits,
              'root':{'r':self.nodes[0]['r'],'m':self.nodes[0]['m']},'extra':extra or {}}
        path=pathlib.Path(path)
        path.parent.mkdir(parents=True,exist_ok=True)
        tmp=path.with_suffix(path.suffix+'.tmp')
        with tmp.open('w') as f:
            for rec in [meta]+self.nodes: f.write(json.dumps(rec,separators=(',',':'))+'\n')
        tmp.replace(path)

    def solutions(self):
        return sorted({tuple(s) for nd in self.nodes if nd.get('k')=='l' for s in nd['x'].get('sol',[])})


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--coefs',required=True,help='comma-separated coefficients; empty for dim 1')
    ap.add_argument('--K',type=int,required=True)
    ap.add_argument('--qmin',type=int,required=True)
    ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=float,default=60)
    ap.add_argument('--lifts',type=int,default=10000000)
    ap.add_argument('--nodes',type=int,default=500000)
    ap.add_argument('--schedule',default='2,3,7,3,2,2,2,3')
    ap.add_argument('--no-sumsets',action='store_true')
    ap.add_argument('--no-pin2',action='store_true')
    ap.add_argument('--pin-digits',type=int,choices=(0,1,2,3),default=3)
    args=ap.parse_args()
    g=Generator([int(x) for x in args.coefs.split(',') if x],args.K,args.qmin,
                seconds=args.seconds,lifts=args.lifts,nodes=args.nodes,sumsets=not args.no_sumsets,pin2=not args.no_pin2,pin_digits=args.pin_digits)
    start=time.monotonic()
    try:
        g.run([int(x) for x in args.schedule.split(',') if x]); g.write(args.out)
        status='GENERATED'
    except Budget as e: status='BUDGET: '+str(e)
    print(json.dumps({'label':'COMPUTED','status':status,'seconds':time.monotonic()-start,
                      'nodes':len(g.nodes),'lifts':g.lifts,'trace':g.trace,'at':g.at,
                      'solutions':g.solutions() if status=='GENERATED' else []}))
    return 0 if status=='GENERATED' else 2

if __name__=='__main__': sys.exit(main())
