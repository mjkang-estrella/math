from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];r=json.load(open(D/'outputs/comb.json'))[-1];cs=[c for _,c in reversed(r['counterexample_centers'])]
def route(a,b):
 x,y=a;u,v=b;out=[]
 if x==u:
  for z in range(y+1,v+1) if y<=v else range(y-1,v-1,-1):out.append((x,z))
 else:
  out.extend((x,z) for z in range(y-1,-1,-1))
  out.extend((z,0) for z in (range(x+1,u+1) if x<=u else range(x-1,u-1,-1)))
  out.extend((u,z) for z in range(1,v+1))
 return out
def vstr(v):return '('+str(v[0])+','+str(v[1])+')'
cert=[]
for x in range(3):
 for y in range(36):
  t,p=min(((t,route(c,(x,y))) for t,c in enumerate(cs) if len(route(c,(x,y)))<=9-t),key=lambda tp:len(tp[1]))
  cert.append((t,p))
s='\ndef centers : Fin 10 → Vertex 3 36 := !['+','.join(map(vstr,cs))+']\n'
s+='def certificates : Fin 108 → Fin 10 × List (Vertex 3 36) := ![\n'+',\n'.join('('+str(t)+',['+','.join(map(vstr,p))+'])' for t,p in cert)+']\n'
s+='''def cert (v : Vertex 3 36) := certificates ⟨v.1.val*36+v.2.val, by omega⟩
theorem certificates_valid : ∀ v : Vertex 3 36,
 checkPath (centers (cert v).1) (cert v).2 v = true ∧
 (cert v).2.length ≤ 9-(cert v).1.val := by decide
 theorem burnable_ten : Burnable 3 36 10 := by
 refine ⟨centers, fun v => ?_⟩
 obtain ⟨p,hp⟩ := path_sound _ _ _ (certificates_valid v).1
 exact ⟨(cert v).1,p,by simpa [hp] using (certificates_valid v).2⟩
theorem greedy_fails_through_ten : ∀ S : Fin 3, ∀ t : Fin 11,
 ¬ GreedySuccess 3 36 t.val S.val := by decide
theorem source_refutation : ¬ SourceClaim := by
 intro h
 obtain ⟨S,hS,t,ht,hg⟩ := h 3 36 (by decide) (by decide) 10 burnable_ten
 exact greedy_fails_through_ten ⟨S,hS⟩ ⟨t,by omega⟩ hg
end Comb373367
#print axioms Comb373367.source_refutation
'''
(D/'formal/Certificate.lean.fragment').write_text(s)
p=D/'formal/Comb.lean';base=p.read_text().split('\ndef centers')[0];p.write_text(base+s)
(D/'outputs/comb-witness.json').write_text(json.dumps({'centers':cs,'certificates':cert},indent=2))
