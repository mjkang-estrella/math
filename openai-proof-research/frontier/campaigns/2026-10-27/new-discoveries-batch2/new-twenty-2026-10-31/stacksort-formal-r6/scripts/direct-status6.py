import json,pathlib
p=pathlib.Path(__file__).resolve().parent.parent
f=p/'results.json'; d=json.loads(f.read_text())
d['validation']['literal_P5_P6_direct_kernel_decide']={'status':'NOT_COMPLETED_WITHIN_RESOURCE_LIMITS','P5':'plain decide and decide +kernel hit Lean interpreter memory limit (-M3500), exit 134','P6':'plain decide stopped by the 6 GiB RSS watchdog, exit 137','proof_equalities':'Both literal P equalities follow unconditionally from exactSeeds20_proved; separate direct enumeration is not claimed.'}
d['validation']['rss_watchdog_kills']=sum('RSS CAP EXCEEDED' in f.read_text() for f in (p/'logs').glob('*.log') if f.name[0].isdigit())
f.write_text(json.dumps(d,indent=2)+'\n')
