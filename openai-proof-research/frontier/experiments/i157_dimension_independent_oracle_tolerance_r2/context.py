"""Preserve exact decoded occurrences, independently of semantic-read credit."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i157_dimension_independent_oracle_tolerance_r2'
assert not (S/'seal.json').exists()
def sha(b): return hashlib.sha256(b).hexdigest()
pieces=[]; indices={}; occurrences=[]; roots=[]
def put(root,path,value):
    text=value if isinstance(value,str) else json.dumps(value,ensure_ascii=False)
    key=(type(value).__name__,text)
    if key not in indices:
        indices[key]=len(pieces);pieces.append({'type':key[0],'text':text,'sha256':sha(text.encode())})
    occurrences.append({'root':root,'path':path,'piece':indices[key]})
def walk(root,value,path):
    if isinstance(value,dict):
        for key,child in value.items():walk(root,child,path+[{'key':key}])
    elif isinstance(value,list):
        for i,child in enumerate(value):walk(root,child,path+[{'index':i}])
    elif isinstance(value,str):
        pos=start=0;decoder=json.JSONDecoder()
        while pos<len(value):
            match=re.search(r'[\[{]',value[pos:])
            if not match:break
            k=pos+match.start()
            try: obj,n=decoder.raw_decode(value[k:])
            except ValueError:pos=k+1;continue
            if not isinstance(obj,(dict,list)):pos=k+1;continue
            if k>start:put(root,path+[{'slice':[start,k]}],value[start:k])
            walk(root,obj,path+[{'embedded':k,'length':n}]);pos=start=k+n
        if start<len(value) or not value:put(root,path+[{'slice':[start,len(value)]}],value[start:])
    else:put(root,path,value)
for p in ['frontier/iterations/iteration154-dimension-independent-oracle-tolerance-task.json','frontier/iterations/iteration152-algorithmic-sampling-reconstruction-discovery-task.json','frontier/experiments/i154-parent-verification.json']:
    b=(R/p).read_bytes();roots.append({'path':p,'sha256':sha(b)});walk(p,json.loads(b),[])
old='frontier/sources/i152_algorithmic_sampling_reconstruction_discovery/'
inherited=[old+x for x in ['context-unique.json','context-unique.txt','context-decoding-coverage.json','context-paragraphs.json','context-paragraph-coverage.json']]
inherited+=['frontier/sources/i136_birational_positivity_discovery/'+x for x in ['context-reading.txt','context-coverage.json','input-freeze.json']]
result={'roots':roots,'pieces':pieces,'occurrences':occurrences,'inherited_occurrence_records':[{'path':p,'sha256':sha((R/p).read_bytes())} for p in inherited],'semantic_read_complete':False,'scope':'Exact structured occurrence inventory. Inherited records retained by immutable flat reference; no new semantic-read claim follows from this operation.'}
(S/'decoded-occurrences.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'pieces':len(pieces),'occurrences':len(occurrences),'inherited_maps':len(inherited)}))
