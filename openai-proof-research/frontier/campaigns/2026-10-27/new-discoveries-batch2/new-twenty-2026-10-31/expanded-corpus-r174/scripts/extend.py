import pathlib,json,importlib.util,sys,time
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
s=importlib.util.spec_from_file_location('seq',L/'scripts/sequence_search.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
pat=sys.argv[1];N=int(sys.argv[2]);t=time.monotonic();lens,w=m.produce(tuple(ord(a)-97 for a in pat),N)
d={'pattern':pat,'through_n':N,'lengths':lens,'final_word':w,'seconds':time.monotonic()-t}
with (L/'outputs/sequence-extended.jsonl').open('a') as f:f.write(json.dumps(d)+'\n')
print(d)
