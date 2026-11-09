from generate_reduced import *
import re
# Postprocess generated checks into larger scalar batches and weighted merge batches.
def rebatch(a,b,e):
 mods=generate(a,b,e);ns=f'R{a}_{b}_{e}';data=(L/'formal'/(ns+'Bounds.lean')).read_text();N=int(re.search(r'∀ m : Fin (\d+)',data)[1]);out=[]
 # Keep existing non-check modules and regenerate check modules from their aggregate declaration.
 for stage,var,size in [('Bounds','m',256),('Base','m',64),('Edge','m',32),('Merge','u',0)]:
  mod=ns+stage;src=(L/'formal'/(mod+'.lean')).read_text();beg=src.index('theorem ');end=src.index(' := by',beg);decl=src[beg:end];name=decl.split()[1]
  # original dependencies for check bodies
  head='import '+ns+('Edges' if stage=='Edge' else 'Data')+'\n'+src[src.index('set_option'):beg]
  ranges=[];extras=[]
  if stage!='Merge':ranges=[(st,min(st+size,N)) for st in range(0,N,size)]
  else:
   st=0;weight=0
   for u in range(N):
    w=1<<u.bit_count()
    if weight and weight+w>512:ranges.append((st,u));st=u;weight=0
    weight+=w
    if w>512:ranges.append((u,u+1));st=u+1;weight=0
   if st<N:ranges.append((st,N))
  bs=[]
  for bi,(st,en) in enumerate(ranges):
   bm=mod+f'B{bi}';bs.append(bm)
   text=decl.replace('theorem '+name+' :','theorem '+name+f'B{bi} :').replace(f'{var} : Fin {N}',f'{var} : Fin {en-st}').replace(var+'.val',f'({var}.val+{st})')
   imports=[];proof='by decide'
   if stage=='Merge' and (1<<st.bit_count())>512:
    n=int(re.search(r'unionCheck \d+ (\d+)',decl)[1]);k=(N.bit_length()-1);cnt=1<<st.bit_count();chunks=(cnt+255)//256;ss=[]
    pred=f'(fun a => if a = 0 ∨ a = {st} then true else bitCheck {n} (table a) (table ({st} ^^^ a)) (table {st}))'
    for j in range(chunks):
     sm=mod+f'U{st}S{j}';ss.append(sm);lst=f'((submasks {k} {st}).drop {j*256})'
     if j+1<chunks:lst=f'({lst}.take 256)'
     body=f'theorem slice{st}_{j} : {lst}.all {pred} = true := by decide\n'
     for d in ['dev','formal']:(L/d/(sm+'.lean')).write_text(head+body+'end '+ns+'\n')
    extras+=ss;imports=ss
    proof=f'by\n  intro u\n  have he : u.val+{st} = {st} := by omega\n  rw [he]\n  change (submasks {k} {st}).all {pred} = true\n'
    for j in range(chunks-1):
     proof+='  '+('  '*j)+'apply all_split _ _ 256\n'
     proof+='  '+('  '*j)+f'· exact slice{st}_{j}\n'
     proof+='  '+('  '*j)+'·\n'
     if j:proof+='    '+('  '*j)+'simp only [List.drop_drop]\n'
    proof+='  '+('  '*(chunks-1))+f'exact slice{st}_{chunks-1}'
   hd=''.join('import '+x+'\n' for x in imports)+head
   for d in ['formal','dev']:(L/d/(bm+'.lean')).write_text(hd+text+' := '+proof+'\nend '+ns+'\n')
  def dispatch(lo,hi,ind):
   if hi-lo==1:
    st,en=ranges[lo]
    return ind+f'have hb : {var}.val-{st} < {en-st} := by omega\n'+ind+f'have he : {var}.val-{st}+{st} = {var}.val := by omega\n'+ind+f'have hp := {name}B{lo} ⟨{var}.val-{st},hb⟩\n'+ind+'simpa only [he] using hp\n'
   mid=(lo+hi)//2
   return ind+f'by_cases h{mid} : {var}.val < {ranges[mid][0]}\n'+ind+'·\n'+dispatch(lo,mid,ind+'  ')+ind+'·\n'+dispatch(mid,hi,ind+'  ')
  agg=''.join('import '+x+'\n' for x in bs)+src[src.index('set_option'):beg]+decl+' := by\n  intro '+var+'\n'+dispatch(0,len(bs),'  ')+'end '+ns+'\n'
  for d in ['dev','formal']:(L/d/(mod+'.lean')).write_text(agg)
  # Replace original stage dependency block in topological plan.
  old=[x for x in mods if re.fullmatch(mod+r'\d*',x)]
  idx=min(mods.index(x) for x in old);mods=[x for x in mods if x not in old];mods[idx:idx]=extras+bs+[mod]
 return mods
if __name__=='__main__':
 import sys
 print(json.dumps(rebatch(*map(int,sys.argv[1:4]))))
