import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
vs=json.loads((D/'outputs/versions.json').read_text());out={}
for a,versions in vs.items():
 out[a]=[]
 for v in versions:
  p=D/'sources'/f'{a}v{v}.txt';lines=p.read_text().splitlines();hits=[i for i,l in enumerate(lines) if re.search(r'^Conjecture|^Conjectured|^Theorem 1.3',l)]
  out[a].append({'version':v,'pdf_sha256':H(p.with_suffix('.pdf').read_bytes()),'text_sha256':H(p.read_bytes()),'anchors':[{'line_1based':i+1,'text':'\n'.join(lines[max(0,i-2):i+15])} for i in hits]})
(D/'outputs/version-anchors.json').write_text(json.dumps(out,ensure_ascii=False,indent=2))
for name in ['omega-D5','omega-Problems','openai-preprints']:
 x=json.loads((D/f'sources/{name}.json').read_text());assert not x.get('truncated')
 hits=[p['path'] for p in x['tree'] if re.search('spectral.*cycle|rose.window|erdos.deep|separable.*record|steiner.*hyper|hilton.milner|neutral.*renewal|neural.*ideal|rational.*catalan|discus|descendent.*matroid|censored.*spik|refined.bps|pseudocircle|gamma.vector',p['path'],re.I)]
 (D/f'outputs/{name}-target-screen.json').write_text(json.dumps({'truncated':False,'count':len(x['tree']),'matched_paths':hits},indent=2))
print('versions',sum(map(len,vs.values())))
print('hashes and complete registry scope flags recorded')
