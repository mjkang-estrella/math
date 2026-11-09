from pathlib import Path
r=Path(__file__).resolve().parent;p=r/'packet/src/RUP.lean';s=p.read_text();a=s.index('def rup ');b=s.index('\ntheorem remaining_sound',a)
s=s[:a]+'''def rup (f : NClause) (hs : List NClause) : Bool :=
  List.rec (motive := fun _ => NClause → Bool) (fun _ => false)
    (fun c _ prev fs => match remaining fs c with
      | [] => true
      | [z] => prev ((z.1, !z.2) :: fs)
      | _ => false) hs f
'''+s[b:];p.write_text(s)
for name in ['RUP','Pilot500','Pilot2000','ReplayEndpoint','AuditR3']:
 for phase in ['build','check']:
  for ext in ['log','receipt.json']:
   p=r/'logs'/f'{phase}-{name}.{ext}'
   if p.exists():p.rename(r/'logs'/f'{phase}-{name}.before-recursor.{ext}')
(r/'recursor-order.txt').write_text('RUP\nPilot500\nPilot2000\nReplayEndpoint\nAuditR3\n')
