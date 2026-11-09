import json,pathlib,subprocess,sys,re,hashlib,collections
p=pathlib.Path.cwd()
def save(f,d):
 text=d if isinstance(d,str) else json.dumps(d,indent=2)
 subprocess.run([sys.executable,"-I","-B",str(p/"write_lane.py"),f],input=text,text=True,check=True)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
rows=json.loads((p/"results/COVERAGE-PLAN-PAID.json").read_text())
order=json.loads((p/"SOURCE-ORDER.json").read_text());assert {r["module"] for r in rows}==set(order)
meta=json.loads((p/"audit/TOOL-METADATA.json").read_text())
prod={n["name"]:n for n in meta["nodes"] if n["scope"]=="production"}
aux={n["name"]:n for n in meta["nodes"] if n["scope"]=="auxiliary"}
allnodes={**aux,**prod}
cl=set(json.loads((p/"audit/VERIFIED-EVIDENCE.json").read_text())["new_endpoint_nodes"])
cons=collections.defaultdict(set)
for name,n in allnodes.items():
 for dep in n["deps"]:cons[dep].add(name)
for row in rows:
 names=sorted(n for scope in ["production","auxiliary"] for n in meta["roots"][scope] if allnodes[n]["origin"]==row["module"])
 row["actual_declarations"]=[dict(allnodes[n],universal_consumed=n in cl,immediate_consumers=sorted(cons[n])) for n in names]
 row["source_sha256"]=sha(p/"src"/(row["module"]+".lean"))
 row["explicit_authored_declaration_tokens"]=re.findall(r"(?m)^\s*(?:noncomputable )?(?:def|theorem|abbrev|structure)\s+([^\s{(:]+)",(p/"src"/(row["module"]+".lean")).read_text())
save("results/SOURCE-BODY-COVERAGE.json",rows)
old=json.loads((p/"inputs/independent-review-r5/audit/RECOMPUTED-DAG.json").read_text())
fresh=(p/"logs/1794124502924129072_lean_CMDRRAuditFinal.log").read_text()
closures={}
for m in re.finditer(r"ENDPOINT_CLOSURE (\S+)\s+\[(.*?)\]",fresh,re.S):
 closures[m[1]]=[x.strip() for x in m[2].split(",") if x.strip()]
assert len(closures)==15,len(closures)
for root,names in closures.items():assert set(names)==set(old["closures"][root]),root
save("audit/FRESH-CLOSURES-CROSSCHECK.json",{"all15_exact_sets_equal_r5":True,"counts":{k:len(v) for k,v in closures.items()},"added_structural_nodes":sorted(cl-set(old["closures"]["CMDRR.universalExistsFiveThree_negation"]))})
table="| Module | Critical declarations inspected | Semantic invariant | Consumption edge / gap |\n|---|---|---|---|\n"
for r in rows:table+="| "+r["module"]+" | "+r["critical"]+" | "+r["invariant"]+" | "+r["consumption"]+"; no unpaid body gap |\n"
body=(p/"results/REPORT-BODY.txt").read_text().replace("COVERAGE_TABLE",table)
body += "\nA first final-report assembly failed before report creation because its closure regex was over-escaped (zero matches). The changed v2 parser corrects that documentary error; both attempts are retained.\n"
save("FINAL-REVIEW.md",body)
summary=json.loads((p/"audit/TOOL-METADATA-SUMMARY.json").read_text())
gates={"ordinary_correctness":"PASS","literal_source_provenance":"PASS","source_to_body":"PASS","fresh39strict39checkers":"PASS","metadata_axiom_origin":"PASS","retained15closures_and_controls":"PASS_WITHIN_SCOPE","manuscript":"PASS_ARCHIVAL_RECORD","family94":"PASS_SUPPLIED_SCOPES","prior":"BOUNDED_NO_MATCH_ACCESS_LIMIT","significance":"PROSPECTIVE_PASS_ROOT_ADJUDICATION_PENDING","historical_process":"HOLD_ROOT_ADJUDICATION","acceptance":"PENDING_ROOT"}
save("review.json",{"326555":{"reviewer":"GPT-6.1 Sol high/default personally; no children/fallback","credit":0,"campaign":55,"target":60,"prior":39,"recommendation":"TECHNICAL_PASS_ROOT_ADJUDICATION_PENDING","remaining_review_completed":True,"gates":gates,"source_body_table":rows,"metadata":summary,"metadata_files":["audit/METADATA.json","audit/TOOL-METADATA.json","audit/METADATA-SUMMARY.json","audit/TOOL-METADATA-SUMMARY.json"],"fresh_replay":"results/FRESH-REPLAY.json","retained_evidence":"audit/VERIFIED-EVIDENCE.json","fresh_closures":"audit/FRESH-CLOSURES-CROSSCHECK.json","provenance":"results/TARGET-PROVENANCE.json","paper_pages_actually_viewed":[1,2,3,4,5,6],"source_final_pages_actually_viewed":[1,2,3,4,5,10,11,12,13,14,15,16,20,21,22],"mathematical_gap":None,"routine_subsuming_bridge_identified":False,"worldwide_novelty":False,"access_limit":"Berman-Smith2013 companion403, no new retrieval; cached registry heads not live/delta proof clearance","root_only_pending":["Scientific acceptance and adoption of bounded significance/prior qualification","Historical and current process adjudication"],"current_incidents":"audit/CURRENT-INCIDENTS.json","report":"FINAL-REVIEW.md","frozen_after":"frozen-after.json","terminal_manifest":"SHA256-MANIFEST.json"}})
save("audit/ALL-PAGE-QA.json",{"paper_pages":[1,2,3,4,5,6],"status":"PASS","method":"Own capped pdftoppm1600 render then actual original-detail view_image; page2 equation close but separate from footer","math_text_unchanged":True,"original_to_root_diff":"logs/1794124586395239762_pdf_skill_and_context.log","root_reporting_repairs_verified":True,"native_image_group_telemetry":None,"source_final_pages":[1,2,3,4,5,10,11,12,13,14,15,16,20,21,22]})
print("REPORTS_WRITTEN","39 rows",sum(len(r["actual_declarations"]) for r in rows),"actual roots", "fresh15 equal", "added_structural",sorted(cl-set(old["closures"]["CMDRR.universalExistsFiveThree_negation"])))

