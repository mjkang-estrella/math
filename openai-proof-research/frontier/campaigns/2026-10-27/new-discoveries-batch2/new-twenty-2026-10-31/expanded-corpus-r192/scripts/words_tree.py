import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];s=(D/'scripts/word_sam.py').read_text();ns={'__file__':str(D/'scripts/word_sam.py')};exec(s[:s.index('rng=random.Random')],ns);close=ns['close'];comp=ns['complexity'];depth=int(sys.argv[1]);count=0;best=(0,None);fail=[]
def visit(w,dirs):
 global count,best
 if len(dirs)==depth:
  count+=1;z=comp(w)
  if z[0]>best[0]:best=(z[0],{'n':z[1],'factor_count':z[2],'directive':dirs,'prefix_length':len(w)})
  if z[0]>=6:fail.append(best[1])
  if count%1000==0:(D/f'outputs/word-tree-{depth}.json').write_text(json.dumps({'completed_leaves':count,'depth':depth,'best':best,'counterexamples':fail,'finished':False},indent=2))
  return
 for b in '01':
  for e in (0,1):visit(close(w+b,e),dirs+[(b,e)])
for e in (0,1):visit(close('0',e),[('0',e)])
(D/f'outputs/word-tree-{depth}.json').write_text(json.dumps({'completed_leaves':count,'depth':depth,'best':best,'counterexamples':fail,'finished':True,'scope':'All binary directives of fixed depth with first letter 0, either first antimorphism. Complements cover first letter 1. Finite prefix factor lower bounds for all lengths.'},indent=2));print(count,best)
