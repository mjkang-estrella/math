# 소인수분해 연구 인계

작성: 2026-10-09 UTC / 2026-10-08 America/Los_Angeles.
**사용자 지시에 따른 결과 회수·인계 완료. 신규 연구·실험·하위 작업·재시작은 금지한다.**
남은 리뷰는 모두 회수했고, 기존 goal의 실제 도구 응답은 **paused**이다.
응답 원문은 [lifecycle 기록](findings/closure-lifecycle.json)에 보존했다. 성과 달성
`complete`가 아니다. 사용자가 명시적으로 재개하기 전에는 아래 다음 단계를 실행하지 않는다.
ECDLP는 별도 [인계 문서](../../dlp-research/research/HANDOVER.md)를 참조한다.
`Find New Low-Hanging Mathematical Proofs`는 중단 대상이 아니며 변경하지 않는다.

## 1. 목적, 전제, 현재 결론

목표는 입력 정수 N의 **비트 길이 n**에 대한 고전적 소인수분해의 완전한
시간 복잡도를 낮추는 것이다. 생성, 전처리, 실패, 재시작, 메모리/피연산자
폭, gcd 및 실제 인수 복구를 모두 비용에 포함한다. 최초 동기는
[Hotz의 글](https://geohot.github.io/blog/jekyll/update/2026/03/16/polynomial-time-factoring.html)이지만,
그 글은 실행 가능한 다항시간 알고리즘의 증명이 아니다.

**검증된 새로운 end-to-end 소인수분해 복잡도 개선: NONE.**
다항시간에 처리 가능한 특수 후보 집합과 여러 정확한 항등식은 얻었지만,
그 집합에 유용한 인수가 반드시 또는 충분한 확률로 존재한다는 정리가 없다.
작은 실험의 인수 발견, 후보 집합 압축, AI 리뷰 통과, Lean 빌드는 서로
다른 증거이며 일반 소인수분해 시간의 개선을 뜻하지 않는다.

정확한 계약은 [SPECIFICATION](../docs/SPECIFICATION.md), 실행 환경은
[README](../README.md), 기존 연구 이력은 [STATE](STATE.md)의 보존된 본문과
[W001 기준선 검토](hypotheses/W001-baselines.md)에 있다. 일반/특수 입력,
증명된/휴리스틱 보장, 고전/양자 알고리즘을 섞지 않는다.

## 2. 채택한 결과와 정확한 범위

아래 최근 수학 결과는 서면 유도 및 독립 AI 리뷰 수준이다. 별도 표시가
없으면 Lean 정리가 아니고 구현의 점근적 성능을 측정한 결과도 아니다.

| 결과 | 채택 범위 | 남은 제한 |
|---|---|---|
| [정확한 carry quotient](findings/W032-exact-carry-quotient.md), [리뷰](findings/W032-carry-quotient-review.md) | 전체 분모/unit 검사를 통과한 실제 정수 등차수열에서 c=Δ^(2R+1)r/N^(2R) 정수, \|c\|<4^R, 원래 digit filter와 gcd 동일. 계수 점화식·monic 다점 평가·부호 있는 정수 convolution. 한 stencil 획득 soft O(R² logN). | 정확한 정수 나눗셈, 충분한 정밀도와 실제 unwrapped 입력이 필수. 성공 확률은 미증명. |
| [N개 공통 lift sweep](findings/W032-lift-breakpoint-sweep.md), [리뷰](findings/W032-lift-sweep-review.md) | a0=1에서 O(R²) threshold record로 모든 실제 carry 값을 소비, soft O(R²(logN+R)). tie는 원자적으로 처리. | 무익한 가족도 빠르게 소진할 수 있다. 이벤트 수는 독립 시행 수나 gcd 수의 하한이 아니다. |
| [큰 시작점의 arrangement cover](findings/W032-lift-arrangement-cover.md), [리뷰](findings/W032-arrangement-cover-review.md) | 큰 a0에 비례한 loop를 제거. 합리수 slab 방식 soft O(R⁷(logN+R)). 수평선의 경계 겹침/0으로 나누기 예외를 명시해 수정. | 실제 lift 값을 포함하는 상위 집합이다. 추가 값에 실제 lift witness나 균등 lift 확률을 붙이지 않는다. |
| [두 매개변수 affine lift](findings/W032-affine-lift-family.md), [리뷰](findings/W032-affine-lift-review.md) | 시작점·step을 함께 변화시켜 N² residue vector를 생성. 항등식·부호·완전한 chamber cover·soft O(R¹⁰(logN+R)) slab 상계를 리뷰가 인정. 부모가 500행 전부 읽고 봉인 파일 확인. | 지지집합의 엄격한 증가와 유용한 인수 공급은 미증명. pairwise phase independence는 mutual independence가 아니다. 정확한 2차 모멘트는 균등 sampler의 상계만 준다. |
| [가중 edge walk](findings/W032-weighted-edge-walk.md), [최종 리뷰](findings/W032-edge-walk-review.md) | 같은 floor cover를 line별 초기화와 원자적 가중 교차 업데이트로 소비한다. 기존 큰 시작점 cover는 soft O(R⁴(n+R)), 공급된 affine 식은 soft O(R⁶(n+R)); 보수적 streaming 공간 상계 포함. | 교차점 중복 제거 시 incidence 보존, tie 전체 갱신 후 sampling, 경계 안쪽 처리 규약이 필수. 구현·Lean·속도 실험 없음. 작은 시작점의 1차원 sweep보다 항상 유리한 것이 아니다. 인수 공급 정리는 없음. |
| [W034 입력 의존 지수](hypotheses/W034.md), [리뷰](findings/W034-input-annihilator-review.md) | E=∏(N^j−1), 원래 균등 unit base의 전체 2-adic chain에 대해 정확한 semiprime 성공식과 획득/거듭제곱 비용. 한 component의 uncovered index가 작으면 조건부 성공 보장. | 일반 입력에서 그 index가 작다는 정리 없음. generalized p−1 및 RSA cycling 선행 연구와 가깝다. 신규성 확정 아님. |
| [W033 primitive ratio 공유](findings/W033-primitive-ratio-sharing.md), [리뷰](findings/W033-ratio-sharing-review.md) | no-alias 범위의 정확한 unit-slope 성공식, multiplicity 제거, full-gcd 복구 및 raw/accepted sampling 비용 구분. | 여전히 Θ(H²) 서로 다른 ratio와 지정된 소비자의 square-root 규모 비용. 일반 하한 아님. |

최신 인계 때 회수한 리뷰의 원본 동일성은
[closure-intake.json](findings/closure-intake.json), 이전 것은
[quotient-transition-intake](findings/W032-quotient-transition-intake.json)에 기록했다.
해시는 전달 파일의 동일성만 확인하며 수학적 참을 증명하지 않는다.

## 3. 실험과 실제 검증

**완료된 Lean 범위:** [Factoring/](../Factoring), [Factoring.lean](../Factoring.lean),
[Audit.lean](../Audit.lean). 인수 witness 계약, cofactor 감소, 완전 탐색 splitter의
soundness/completeness, 특정 algebraic residual/conic/chart 항등식 등이다.
[Goals.lean](../Factoring/Goals.lean)의 다항시간 목표는 abstract-machine 명세이며
그런 알고리즘의 존재 증명이 아니다. W032/W034 전체 알고리즘의 Lean 증명은 없다.

**Python 환경:** [factoring_lab/](../factoring_lab), [tests/](../tests),
[configs/smoke.json](../configs/smoke.json). stdlib 기반이며 실제 알고리즘의
입력은 N, 난수 seed, meter이다. 인수는 검증 단계에서만 사용한다.
기본 harness는 신뢰한 코드를 검사하는 장치이며 OS 보안 격리가 아니다.

**이전 W032 scalar assay:** 155 case, 131 unit, 항등식과 다섯 matrix control이
통과했다. 19,964/20,000 events. [부모 판정](findings/W032-assay-parent-disposition.md).
이는 고정된 작은 입력 증거이며 재실행하지 않는다.

**최신 frozen lift assay:** [프로토콜](findings/W032-lift-sweep-protocol.md),
[결과](findings/W032-lift-sweep-assay.md), [독립 감사](findings/W032-sweep-assay-audit.md),
[원본 패키지](findings/W032-lift-sweep-assay-evidence/).

- b=9: N=281861, R=5, 79 intervals/75 distinct carries, 모두 gcd=1.
- b=13: N=68027983, R=7, 137 intervals/130 distinct carries, 모두 gcd=1.
- b=17: 입력 소수 생성 중 전체 event cap 도달. N/R/candidate/control은
  미시작. 실패한 가족으로 세지 않으며 성공 확률은 알 수 없다.
- 하나의 실행만 수행: **전체 20,000 events / 60초** 예산에 setup, 정렬,
  참조 계산, 기록 포함. 관측 시간 0.238444초(올림). cap을 늘리지 않았다.
- 두 완료 case의 네 직접 control씩 및 첫 case의 원래 scalar control 통과.
  다중 tie와 zero-net tie 경로는 source review만 수행했고 실험에서 발생하지 않았다.
- 감사에서 terminal record의 **outer group tag 오류** 발견: b=9/13 최종
  envelope가 group=17로 기록됐다. `result.b`와 nested result는 status.json 및
  앞선 완료 기록과 일치한다. 원본 수정/repair-run 없이 이 한계를 보존한다.
  상세 위치는 [terminal-attribution](findings/W032-sweep-assay-audit-evidence/terminal-attribution.json).
- 감사는 전체 코드 읽기, 파일 해시·구조·기록 연결 확인이며 수치 재계산은 아니다.
  arithmetic undercount나 수학 구현 오류는 발견하지 못했다. events는 bit 연산이 아니다.

마지막 프로젝트 검증 기록:
[closure-project-checks.txt](findings/closure-project-checks.txt), 종료 정리 시 exit 0.
12 Python tests, source screen, pinned Lean build, axiom audit가 통과했다.
이 검증은 해당 standalone assay를 실행하지 않으며 W032 정리를 증명하지 않는다.
이전 검증도 [W032-lift-sweep-project-checks.txt](findings/W032-lift-sweep-project-checks.txt)에 보존했다.

## 4. 폐기·보류한 가지

보존된 탐색 경로는 W001의 baseline/관계식/결정론적 cover/군 동역학/
lifting/order/algebra 비교, W002–W007의 norm·field·계수 구성,
W008–W014의 collision·dynamics·interval/exponent 표현,
W015–W020의 factorial·progression·character·class-order 소비자,
W021–W030의 root chart·coefficient product·carry 비용,
W031–W034의 정규화 scalar·lift·divisibility/order 가지로 묶어 읽을 수 있다.
이것은 역사 안내이며 각 세부 정리의 범위는 원래 report/disposition이 기준이다.

- 초기 broad ideation과 H001–H031/W001–W031의 세부 기록은
  [hypotheses](hypotheses/), [findings](findings/), `tasks-H*.json`/`tasks-W*.json`에
  남아 있다. 각 disposition의 제한된 범위를 유지한다. 전체 factoring 하한으로
  일반화하지 않는다.
- [small-tail filter](findings/W032-small-tail-depth-bound.md): 정확한 tail guard가
  R=O(logN/loglogN)을 강제해 큰 소인수에 닿는 carry 크기를 얻지 못한다.
  D를 곱해도 D는 gcd-unit이라 지원 범위를 늘리지 못한다.
- [label-period 압축](findings/W032-label-period-lower-bound.md): 증명된 period
  하계와 stencil 폭 조건이 해당 균형 입력에서 증폭을 막는다. 임의 carry
  소비자를 배제하는 정리가 아니다.
- [W031 정규화 계수 screen](findings/W031-screen-parent-disposition.md): 특정
  coefficient는 새 소수를 노출하지만 public coefficient 전체 높이/coverage가
  비용을 되돌린다. 입력 의존 조합 전체를 배제하지 않는다.
- relation/norm 제안들은 생성·smoothness·rank·root recovery·유용한 확률 중
  빠진 비용/정리 때문에 완전한 개선으로 채택되지 않았다. 관련 초기 기준선은
  [W001-relations](hypotheses/W001-relations.md).
- [integral annihilator compiler](findings/W032-annihilator-image.md): 부모의
  서면 유도만 있고 독립 리뷰/Lean/실험 없음. 모든 정수 필터의 image ideal을
  계산하는 방식과 무제한 target programming은 곧바로 factoring 이득이 아니다.
- [W034 exponent compression](findings/W034-exponent-compression.md): 중단 전에
  작성한 부모 유도. LCM/cyclotomic 비용과 국소 모델을 다루지만 별도 검증 없음.
- `x_(j+1)=x_j^N modN`로 여러 개별 지수 검사를 공유하는 생각은 중단 직전
  대화에서 나온 미검증 아이디어이며 구현/실험/후속 작업을 시작하지 않았다.
  회수된 W034 리뷰는 generalized RSA cycling이라는 선행 기법을 지적한다.

## 5. 최신 작업 종료 상태와 태스크 위치

완전한 prompt, provider 오류, taskId/childThreadId, 최종 summary는
[tasks-W032.json](tasks-W032.json), [tasks-W034.json](tasks-W034.json)에 있다.
태스크 ID 공통 prefix:

```text
node:delegated-task:command%3Amcp%3A662deaf0-7cd2-44c1-ba36-11987049a724%3Adelegate-task%3A
```

| suffix | 상태/범위 |
|---|---|
| factoring-w032-lift-sweep-review-r1 | 완료, algebra/coverage/cost 채택 |
| factoring-w032-lift-sweep-assay-r1 | 완료, 한 실행은 2 완료/1 setup-stop |
| factoring-w032-arrangement-cover-review-r1 | 완료, 수평 경계 수정 후 채택 |
| factoring-w032-sweep-assay-audit-r1 | 완료, 기록 태그 결함을 명시하고 유한 결과 채택 |
| factoring-w032-affine-lift-review-r1 | 완료, algebra/cover/cost·pairwise moment 검토, yield 미증명 |
| factoring-w034-input-annihilator-opus-r1 | API 반복 오류로 실패, 수학 결과 없음 |
| factoring-w034-input-annihilator-codex-r2 | 완료·봉인·종료, 정확한 조건부 성공식 인정 |
| factoring-w032-edge-walk-review-r1 | 완료·봉인·회수. 502행 리뷰 전부 읽음, 외부 anchor와 31개 payload SHA256 일치. 명시한 규약을 포함한 geometric compiler 채택 |

Edge 리뷰는 공급된 floor 식의 geometry/cost만 다루고 affine 항등식 자체는
조건부로 남겼다. 별도 affine 리뷰가 그 항등식을 인정했다는 사실과 구분한다.
둘을 조합해도 유용한 인수 존재·확률 정리는 생기지 않는다. 기존 부모 노트의
`Unreviewed` 표제는 당시 작성 상태이며 최신 판정은 이 문서와
[closure-disposition](findings/closure-disposition.md)이 기준이다.
종료 중 새 검토 라운드, 실패 리뷰 재시작, 새 연구 실험은 없었다.

Git 루트는 상위 math이며 다른 연구도 같은 저장소를 사용한다.
**factoring-research는 인계 작성 시 untracked이며 관련 커밋은 없다.**
자동 commit/push를 하지 않는다. 형제 프로젝트의 커밋이나 파일을 이 연구의
성과로 간주하지 않는다. 원본 run/review payload는 수정하지 않는다.
ECDLP 인계 커밋은 `8ffd4016ba033f124da6ff3547e5cc113cc9f713`이며,
별도 코디네이터가 기존 권한으로 만들었다. 이 스레드는 ECDLP 파일을 수정하지 않았다.

## 6. 재현과 보존 절차

다음은 인계 받은 사람이 검증 범위를 알기 위한 명령이다. 새로운 연구 실험을
허용하는 지시가 아니다. 기존 frozen assay의 `run_once.py`를 재실행하지 않는다.

```bash
cd /home/mj-kang/Documents/Dev/math/factoring-research
./scripts/check.sh
# 기존 일반 harness run에 대해서만 저장된 결과의 무결성/검증 확인:
.venv/bin/python -m factoring_lab verify-run research/runs/<existing-directory>
```

Standalone W032 증거는 `research/findings/*-evidence/`의 manifest에 기록된
파일 크기/SHA256을 외부 terminal anchor와 비교한다. manifest 자체 해시 및
포함 파일 모두를 확인해야 한다. `closure-intake.json` 등에 이미 확인한
anchor가 있다. 이것은 candidate 실행이 아니다.

명시적 재개 후 새로운 실험을 선택한다면 [RESEARCH_LOOP](../RESEARCH_LOOP.md)의
원본 동결·실패/미시작 보존 규칙을 적용한다. smoke 기본값은 20,000 events,
4096 operand bits, worker 1초, 전체 60초지만, 최신 lift assay는 모든 그룹을
합친 **global 20,000/60초**로 더 엄격하다. 소진한 run을 새 budget으로
대체하거나 재실행해 성공률 분모를 바꾸지 않는다. 타이밍·event vector와
완전한 bit complexity 증명은 구분한다.

## 7. 명시적 재개 때만 할 일

핵심 병목은 candidate acquisition 자체가 아니라 **유용한 인수 공급과 전체
비용 대비 성공 확률**이다. 후보 집합의 크기나 carry의 크기는 그 정리가 아니다.

재개가 명시되면 먼저 최신 봉인 리뷰와 이 문서의 최종 상태를 읽고, 기존 run을
반복하지 말고, 검토된 primitive 중 하나를 고른다. affine family의 적절한
인수 존재/확률, 짧은 annihilator 선택의 실제 이득, 또는 W034의 작은 uncovered
index를 보장하는 입력 의존 지수를 모두 실패/준비 비용까지 포함해 검토할 수
있다. 그때도 비교 대상과 보장 범위를 맞춰야 한다. 현재는 이를 실행하지 않는다.

## 최종 종료 확인

2026-10-09 UTC 결과 회수 완료. [lifecycle 기록](findings/closure-lifecycle.json)에
T3 상태, task 응답, scheduler 및 ECDLP 종료 통보를 보존했다.

- 소인수분해의 마지막 edge 리뷰 `completed`, `hasPendingChildRuns=false`.
  전체 `tasks-*.json`에서 비종료 태스크 0건.
- T3 project live inventory는 마지막 회수 이후 소인수분해/ECDLP 하위 작업 0건,
  페이지 잔여 없음. 현재 종료 정리 중인 부모와 중단 제외 연구만 실행 중이었다.
- Native inventory는 이 부모만 표시했다. 소인수분해 native live child 0건.
- Project scheduled tasks 0건. 관련 연구 실행 프로세스 검사에서도 0건.
  자동 연구 루프의 연속 실행 권한은 철회됐고 아래 goal 일시정지로 종료한다.
- ECDLP 코디네이터가 인계 완료, native/T3 live child 및 pending run 0건,
  실제 goal `paused` 반환을 통보했다. 작업트리 clean과 위 커밋도 읽기 전용으로 확인했다.
- 소인수분해 기존 goal `01a119f0-41d7-7811-af5c-769e0c698d7e`는
  `update_goal(status="paused")` 실제 응답 **paused** 확인. `complete`가 아니다.

`Find New Low-Hanging Mathematical Proofs`와 그 하위 작업은 변경하거나 중단하지 않았다.
사용자가 명시적으로 재개하기 전에는 과거 본문의 next action을 실행하지 않는다.
