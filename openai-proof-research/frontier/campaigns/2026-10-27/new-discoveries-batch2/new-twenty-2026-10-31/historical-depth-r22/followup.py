import resource,os,itertools,collections,json,sys
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(45,45));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
# Import only definitions; avoid repeating first sweep.
s=open(__file__.replace('followup.py','attempts.py')).read();exec(s[s.index('def sc'):s.index('for n in range(2,9)')])
for p in itertools.permutations(range(1,6)):
 if p[0]==5 and sc(p)!=block(p):print('failed_block_witness',p,'actual',sc(p),'block_prediction',block(p));break
# Alternative induction by deleting the second input. For a fixed output, inspect how
# many possible reduced outputs appear; naive two-fiber recurrence would need <=2.
for n in range(4,9):
 fibers=collections.defaultdict(list)
 for tail in itertools.permutations(range(1,n)):
  p=(n,)+tail;q=sc(p);a=p[1];red=tuple(x-(x>a) for x in p if x!=a);qr=sc(red);fibers[q].append((a,qr))
 most=max((len(set(vals)),q) for q,vals in fibers.items());print('delete_second',n,'max_distinct_reduced_pairs',most,flush=True)
 # distinct reduced outputs alone may be small, but deletion value multiplicity obstructs injection.
 print('max_distinct_reduced_outputs',n,max(len(set(qr for a,qr in vals)) for vals in fibers.values()),flush=True)
