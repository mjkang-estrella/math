import pathlib,json,re,hashlib,collections
S=pathlib.Path('frontier/sources/i103_algebraic_complexity_discovery')
D=json.load(open('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'))
T=json.load(open('sources/preprints-tree.json'))['tree']; blobs={x['path']:x for x in T if x['type']=='blob'}
queries={
 'rational':r'(?i)noncommutative.{0,50}(?:rational|hitting)|rational.{0,40}(?:formula|identit)|pencil.{0,50}hitting',
 'expansion':r'(?i)folded.{0,20}(?:Wronskian|Reed)|Casoratian|Newton.{0,30}(?:basis|bases|flag)|(?:small.subspace|lossless|dimension).{0,20}expan',
 'fields':r'(?i)positive.characteristic.{0,60}(?:formula|pencil|tensor)|every.field.{0,60}(?:rank|matrix|hitting)|simultaneous.{0,30}(?:domain|invertib)',
 'tensor':r'(?i)9/4|nine.fourths|2\.258|staggered.extraction|finite.win|exact.discrete.Fourier',
 'models':r'(?i)shared.{0,25}(?:circuit|subcomputation)|border.determinantal|homogeneous.depth.five'
}
(S/'queries.json').write_text(json.dumps(queries,indent=2)+'\n')
counts=collections.Counter();summary=[]
with open(S/'lexical-hits.jsonl','w') as out:
 for d in D:
  p=pathlib.Path(d['local']);b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==d['sha256'],p
  orig=pathlib.Path(d['original_local']).read_bytes();assert hashlib.sha256(orig).hexdigest()==d['original_sha256'],d['path']
  git=hashlib.sha1(b'blob '+str(len(orig)).encode()+b'\0'+orig).hexdigest();assert git==blobs[d['path']]['sha']==d['git_sha']
  txt=b.decode('utf-8',errors='replace')
  for i,line in enumerate(txt.splitlines(),1):
   for key,expr in queries.items():
    for m in re.finditer(expr,line):
     counts[key]+=1;out.write(json.dumps({'query':key,'path':d['path'],'local':d['local'],'line_splitlines':i,'start':m.start(),'end':m.end(),'match':m.group(),'line':line},ensure_ascii=False)+'\n')
(S/'search-domain.json').write_text(json.dumps(D,indent=2)+'\n')
summary={'entries':len(T),'manuscripts':len({x['path'].split('/')[1] for x in T}),'original_positions':len(blobs),'domain':len(D),'counts':dict(counts),'search_kind':'full-domain lexical only; NOT full semantic reading','line_convention':'decode UTF-8 replace, str.splitlines(), 1-based; start/end 0-based Python character indexes; all matches retained as multiset','pdf_reextractions':0}
(S/'search-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
# Prior ledger screen preserves every exact relevant paragraph, but does not claim a semantic read of all historical text.
with open(S/'ledger-relevant-passages.txt','w') as f:
 for path in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']:
  t=(S/'snapshots'/path).read_text();f.write('\nFILE '+path+'\n')
  for para in t.split('\n\n'):
   if re.search(r'(?i)algebraic|complexity|hitting|tensor|matrix.multiplication|R00[689]|R01[01234]|I10[0123]|I100|eight|two remain',para):f.write(para+'\n\n')
