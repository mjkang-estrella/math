from pathlib import Path
p=Path('formal/OriginAudit.lean');s=p.read_text()
s=s.replace('import Result\nimport Lean','module\npublic import Result\nimport Lean\npublic section')
s=s.replace('#[`Source, `Boundary, `Gadget, `Edges, `Degrees, `Local, `Lower, `Charges, `Transport, `Refutation, `UpperWitness, `UpperDegrees, `Upper, `Result]', '#[`Pointwise, `Majorant, `Tail, `Density, `LogConcavity, `InputMoment, `Profile, `Result]')
p.write_text(s)
