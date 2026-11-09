from pathlib import Path
p=Path('Audit.lean');s=p.read_text();s=s.replace('    if name.toString.startsWith "IR350452." then','''    let localModule := match env.getModuleIdxFor? name with
      | some idx => #[`General, `GData, `Four, `Three, `Finite, `Endpoint, `Control].contains
          env.header.moduleNames[idx]!
      | none => false
    if localModule then''');p.write_text(s)
