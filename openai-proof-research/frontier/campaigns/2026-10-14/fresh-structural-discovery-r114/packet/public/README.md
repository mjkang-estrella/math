# r114 packet

Start with [public/report.md](report.md), then the screen and reading records. This is a no-target/no-nominee discovery archive.

Public prose is original research documentation, offered under CC BY 4.0. Public Python code is original, offered under the MIT License; copyright 2026 the authors of this research record. Permission is granted, free of charge, to any person obtaining a copy of the code and associated documentation to deal in the code without restriction, including use, copy, modification, merging, publication, distribution, sublicensing and sale, subject to inclusion of this copyright and permission notice. THE CODE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY ARISING FROM THE CODE OR ITS USE.

Private upstream, third-party, and prior-project copies are evidence, not relicensed public content. Their original rights remain with their respective holders. A raw URL receipt is an identity record, not permission to republish. No upload or publication is performed by this packet.

From a trusted Python installation, use a separately trusted copy of the verifier when checking an untrusted packet:

    python -B /trusted/verify.py /path/to/packet --expected-manifest-sha256 EXTERNALLY_SUPPLIED_FINAL_HASH

The external handoff provides the verifier hash as well as the detached manifest and report hashes. Directories use zero logical payload bytes in the inventory; exact children are separately enumerated. The manifest excludes only itself, whose exact bytes are authenticated by the external hash. Special files, symlinks, hardlinks, extra empty directories, missing files and self-resealed mutations are rejected. This is a static integrity check, not protection against a concurrent hostile filesystem mutation or mathematical validation.

To reproduce controls, create a work directory outside the packet and run:

    python -B /trusted/run_controls.py /path/to/packet --expected-manifest-sha256 EXTERNALLY_SUPPLIED_FINAL_HASH --work-directory /path/outside/packet

All mutations occur in disposable copies. The original is checked before and after. Do not write control output or Python caches inside the sealed packet.
