import json, re, sys
P='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/rcs128-manuscript-r1/'
aux=open('build-1/article.aux').read()
labels={}
for m in re.finditer(r'\\newlabel\{([^}]*)\}\{\{([^}]*)\}\{([^}]*)\}',aux):
    labels[m.group(1)]=(m.group(2),m.group(3))
import glob,os
texlabels={}
for f in sorted(glob.glob(P+'public/sections/*.tex')):
    for m in re.finditer(r'\\label\{([^}]*)\}',open(f).read()):
        texlabels.setdefault(m.group(1),[]).append(os.path.relpath(f,P))
bad=[];n=0
def walk(o):
    global n
    if isinstance(o,dict):
        if 'label' in o and 'page' in o:
            n+=1
            L=o['label']
            got=labels.get(L)
            ok = got is not None and got[0]==o['number'] and int(got[1])==o['page'] and texlabels.get(L)==[o['file']]
            if not ok: bad.append((L,o,got,texlabels.get(L)))
        for v in o.values(): walk(v)
    elif isinstance(o,list):
        for v in o: walk(v)
for f in ['response-to-findings.json','proof-scope-crosswalk.json']:
    walk(json.load(open(P+f)))
dups=[k for k,v in texlabels.items() if len(v)>1]
print(json.dumps({'locations_checked':n,'mismatches':bad,'aux_labels':len(labels),'tex_labels':len(texlabels),'dup_labels':dups}))
