# Verification parser failures

The Lean audit itself completed all22 partitions successfully. Its first guarded
Python reader rejected universe-qualified axiom display names such as
`Classical.choice.{u}` and `Quot.sound.{u}`. The reader now strips only universe
suffixes before comparing the actual axiom names against the three-name allowlist.

The next reader run correctly refused incomplete type-report coverage:
35,654 declarations/safety/axiom reports but34,733 recognized type headers. The
921 remaining headers print the declaration name alone, followed by multiline
binders/type; they were present in the full Lean logs. Recognizing that exact
current declaration-name line repairs coverage without excluding any name.
The corrected run reports35,654 for all four coverage sets.

These were verification-reader failures, not formal proof failures or successful
audit receipts. Their diagnostics appeared in the session transcript; this note
preserves the exact causes/counts. The final verifier streams the unchanged full
logs and still requires complete agreement of declaration, type, safety and axiom
coverage. No mathematical source or resource cap changed for either correction.

The first final integrity run rejected archive order because the writer sorts
pathlib Paths by components, whereas the reader demanded raw string order.
Both are deterministic but differ for a directory and a similarly prefixed
filename. The reader now validates the writer's exact component ordering.
`attempts/final-verification01` preserves the failed reader, manifest and error
record. The archive and all mathematical sources remain unchanged. The final
manifest is regenerated, followed by another separate guarded verifier run.
