import pathlib,re,json
D=pathlib.Path(__file__).resolve().parents[1];txt=(D/'sources/trure-conjectures.body').read_text()
keys=['2207.03425','2207.04150','2207.11596','2207.14495','2208.05137','2208.07229','2208.08809','2208.11181','2208.12803','2208.13683','2209.03436','2209.05940','2209.05949','2209.12182','2209.14198','2210.00669','2210.03336','2210.05915','2210.09547','2211.04640','Hurlbert','Hackenbush','quasipolar','MSTD','Macchia']
rows=[]
for k in keys:
 for m in re.finditer(re.escape(k),txt,re.I):rows.append({'query':k,'context':txt[max(0,m.start()-350):m.end()+500]})
(D/'notes/registry-matches.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2)[:10000])
