# Public research repository

Public destination: https://github.com/mjkang-estrella/math

On 2026-10-09 the user authorized committing and pushing verified research, and explicitly selected publication of **only `openai-proof-research`**. The public history retains this directory and its separate research commits. The other local project, `dlp-research`, and untracked files are excluded. The original local checkout and commit identifiers are unchanged.

The authoritative count is [four accepted substantial findings out of ten](frontier/TEN-FINDINGS.md). Each accepted result has a complete written proof, independent AI proof and significance reviews, and parent verification under the stipulated OpenAI corpus. This is not formal certification, human peer review, or a worldwide-priority claim. Working proposals, failed approaches and review records are published as explicitly labeled research history; their presence is not acceptance.

Filtering unrelated history changes Git commit identifiers. Historical reports retain their original local identifiers. These are the public equivalents for the accepted results:

| Finding | Original mathematical commit | Public mathematical commit | Original final acceptance | Public final acceptance |
|---|---|---|---|---|
| R006 | `4e09ab8` | [63bd303](https://github.com/mjkang-estrella/math/commit/63bd3035ecd3d25b9ca169cb5a683dce4d6a70d6) | `d950f93` | [d17bb43](https://github.com/mjkang-estrella/math/commit/d17bb431238805ebb3e163838e8fd1f6d3c3d7f2) |
| R008 | `e651d0e` | [1b43169](https://github.com/mjkang-estrella/math/commit/1b43169f645c11cc2e1cb17d743819a8ad381dd0) | `8155129` | [f12c4ee](https://github.com/mjkang-estrella/math/commit/f12c4ee380be6642183ad4c879e4ad7bc00a49f2) |
| R009 | `4afc0cf` | [88442fa](https://github.com/mjkang-estrella/math/commit/88442fac766130626c07b04fa9f6e16cd646f52c) | `1bf8898` | [5df2f03](https://github.com/mjkang-estrella/math/commit/5df2f03bd2baddf62ff4e05e3bc3cc02583e002c) |
| R010 | `1b384f1` | [aac800a](https://github.com/mjkang-estrella/math/commit/aac800a611e71921d2d254845e2d860ccb876306) | `f034e3d` | [16c7edb](https://github.com/mjkang-estrella/math/commit/16c7edbcdd02a50fe0fc3f31387968429f09b9d7) |

`tools/publish_public.py` exports committed history into a temporary bare repository, checks every exported commit for paths outside the authorized directory, verifies the final project tree is byte-identical, checks object integrity and GitHub file-size limits, and optionally pushes without force. It stores the full original/public commit mapping and the verified remote head in the source checkout's Git metadata. Future pushes must use this filtered workflow, not `git push origin main` from the shared checkout.

Statements in earlier sealed reports that no external publication occurred describe their original review date. The public release does not alter the reviewed proof bytes or their validation scope. Some downloaded raw source files are intentionally ignored by Git; source manifests retain pinned URLs and hashes for retrieval.
