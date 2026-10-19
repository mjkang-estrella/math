# Local evidence integrity only

`verify.py` requires three explicit inputs: the packet directory, the exact complete external `sources/preprints-tree.json`, and `--expected-manifest-sha256` supplied from a trusted detached parent receipt. It does not discover or trust a hash from inside the packet. The outer handoff records the final hash.

The manifest seals exact file and directory inventories. Verification rejects extra, absent, changed, symlink and special-file payloads. It checks the complete tree's exact SHA256, 13,223 entries and nontruncation; all canonical source bytes against Git blobs and pinned raw URLs; and retained primary PDF/text hashes. It performs no network request and writes no file. It does not authenticate a claimed theorem, prove originality, assign a gate, or establish that a retained body was semantically read.

Run the original verifier with Python `-B` to suppress bytecode side effects. `integrity_controls.py` is a separate copy-mutating harness: supply an owned `--work-parent` for its temporary directories. Its twelve cases include clean extraction-equivalent copying, missing/wrong detached hash, payload change/removal, added file/directory, symlink, manifest change, payload plus self-resealed manifest, and wrong/missing complete tree. The self-resealed case retains the original trusted detached anchor. It also compares file contents, size and modification times before and after every verifier invocation. Filesystem access-time changes are outside that check.

All copied controls are destroyed after use. Their final JSON receipt belongs outside the sealed packet. Neither integrity controls nor finite diagnostics are mathematical gates. No public release or upload is authorized by this archive.
