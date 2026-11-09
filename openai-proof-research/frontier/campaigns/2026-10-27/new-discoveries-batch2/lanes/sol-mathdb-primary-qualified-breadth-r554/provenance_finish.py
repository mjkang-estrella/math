import pathlib,json,re
P=pathlib.Path(__file__).parent
out=json.loads((P/'retrieval-bindings.json').read_text())
for e in out:
 if 'path' not in e:continue
 s=(P/(e['name']+'.txt')).read_text()
 e['version_markers']=list(dict.fromkeys(re.findall(r'arXiv:\s*[\d.]+v\d+[^\n]{0,80}',s)))[:3]
 e['body_coverage']='selected passages only; whole-body and dependency audit false'
print([(e['name'],e.get('version_markers')) for e in out])
(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
# retain already-read precise local Postnikov passages, without claiming whole proof clearance
s=(P/'postnikov.txt').read_text();out=json.loads((P/'selected-passages.json').read_text())
for a,b in [('Theorem 3.3.','Theorem 3.4.'),('Theorem 4.1.','5. Pattern avoidance'),('Theorem 6.3.','Corollary 6.4.')]:
 start=s.index(a);end=s.find(b,start+len(a));end=end if end>=0 else start+3300
 out.append({'file':'postnikov.txt','start':start,'passage':s[start:end]})
(P/'selected-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
