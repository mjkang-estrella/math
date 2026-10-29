exec((__import__('pathlib').Path(__file__).parent/'audit.py').read_text().split("if sys.argv[1] in")[0])
h=json.loads((b/'sources/omega-head.json').read_text())['sha'];o=json.loads((b/'sources/openai-head.json').read_text())['sha'];c=json.loads((b/'sources/count-head.json').read_text())['sha']
paths=['Problems/bhatia-jain-2016-stolarsky-mean-matrices-class-a.md','D5/S3/Quantum/Matrix/StolarskyMean/Defs.lean','D5/S3/Quantum/Matrix/StolarskyMean/Result.lean','D5/S0/Rewriting/CascadeContinuation.lean','D5/S3/ObserverMemory/Refinement/CascadeCompletion.lean','D5/S3/Weil/Scattering/FiniteScatteringCascade.lean','Problems/grunwald-pales-2024-gini-mean-comparison.md','D5/S3/Constants/PowerMeanKernel.lean','D5/S3/Divergence/MeanKernels/LogarithmicMeanSandwich.lean']
tasks=[('omega-body-'+str(i)+'.txt','https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+p) for i,p in enumerate(paths)]
tasks += [('openai-CONTENTS.md','https://raw.githubusercontent.com/openai/math/'+o+'/CONTENTS.md'),('count-registry.json','https://raw.githubusercontent.com/suvrit/count-ex-machina/'+c+'/registry.json')]
(b/'body-map.json').write_text(json.dumps(paths,indent=2))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:r=list(ex.map(lambda x:get(*x),tasks))
(b/'http-bodies.json').write_text(json.dumps(r,indent=2));print([(x['name'],x.get('status',x.get('error')),x.get('bytes')) for x in r])
