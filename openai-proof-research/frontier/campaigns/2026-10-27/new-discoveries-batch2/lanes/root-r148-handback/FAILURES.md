# Root verification correction

The first guarded verify.py run failed with KeyError: 'files' at the manifest read (exit 1, sampled peak group RSS 30,253,056 bytes). This lane uses the `entries` schema, unlike recent lanes using `files`. Corrected the root reader to the actual schema. No candidate file or resource cap changed; the failed run performed no replay or receipt write.
