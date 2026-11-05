# Conformalized quantile regression

Yaniv Romano, Evan Patterson and Emmanuel J. Candès (2019). [Conformalized Quantile Regression](https://proceedings.neurips.cc/paper/2019/hash/5103c3584b063c431bd1268e9b5e76fb-Abstract.html). *Advances in Neural Information Processing Systems, 32 (NeurIPS 2019)*. Archived preprint: [arXiv:1905.03222v1](https://arxiv.org/abs/1905.03222v1).

Selected result: Theorem 1 lower-coverage core and five supporting statements.

This is a structural formalization under explicit score-exchangeability and empirical-quantile-count hypotheses. The observation-level training argument and the upper-coverage clause are outside this result. The checked target has no nonstandard axioms.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 6 |
| Physical Lean lines | 394 |
| Passed / tasks (main + supporting) | 6/6 (1+5) |
| Used external references (main results) | 0 |
| Cached Statlib modules | 5 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1: finite-sample lower-coverage core | `cqr_006_romano_patterson_candes_cqr_finite_sample_miscoverage_bound` | [Main.lean:12](proof/src/ProverJobs/cqr_006_romano_patterson_candes_cqr_finite_sample_miscoverage_bound/Main.lean#L12) |

The linked declarations are the public proof entry points. Fully qualified declaration names and checked modules are listed in [proof/build.json](proof/build.json).

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Miscoverage is contained in a strict lower-rank event | `cqr_001_split_miscoverage_subset_strict_lower_rank_event` | [Main.lean:8](proof/src/ProverJobs/cqr_001_split_miscoverage_subset_strict_lower_rank_event/Main.lean#L8) |
| Strict lower-rank event cardinality bound | `cqr_002_strict_lower_rank_event_cardinality_bound` | [Main.lean:8](proof/src/ProverJobs/cqr_002_strict_lower_rank_event_cardinality_bound/Main.lean#L8) |
| Rank-event probability bound under equiprobability | `cqr_003_rank_event_measure_bound_of_equiprobable` | [Main.lean:9](proof/src/ProverJobs/cqr_003_rank_event_measure_bound_of_equiprobable/Main.lean#L9) |
| Score exchangeability implies rank-event equiprobability | `cqr_004_rank_events_equiprobable_of_score_exchangeable` | [Main.lean:9](proof/src/ProverJobs/cqr_004_rank_events_equiprobable_of_score_exchangeable/Main.lean#L9) |
| Split-conformal score miscoverage bound | `cqr_005_split_conformal_score_miscoverage_bound_of_exchangeable` | [Main.lean:14](proof/src/ProverJobs/cqr_005_split_conformal_score_miscoverage_bound_of_exchangeable/Main.lean#L14) |

## External references used by the main results

No explicit external citation axioms are retained in this source package.

## License and permitted use

The original Lean formalization contributions in [proof/src/](proof/src/) are [MIT-licensed](../../LICENSES/MIT.txt), including commercial reuse subject to the MIT notice requirements. Imported dependencies are separately licensed.

The supplied Statlib `.olean` library caches are separate from the paper inputs and proof-source grant. They are limited to noncommercial reproduction and verification of this archive: no commercial use, extraction for other projects, or reverse engineering to recover or reconstruct library content, subject to independent upstream rights and applicable law. See the [cache license](../../LICENSES/CACHE-VERIFICATION.txt). Source reuse does not authorize commercial use of Statlib.

The cited paper and input materials retain their original rights; this repository does not grant permission to commercially exploit or relicense them. See [license scope and upstream notices](../../LICENSE).
