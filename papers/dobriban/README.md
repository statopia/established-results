# Dobriban — BH/FDR counterexample

Edgar Dobriban (2026). [The Benjamini–Hochberg Procedure Can Fail to Control the FDR for Correlated Two-Sided Gaussian Tests](https://arxiv.org/abs/2607.12208v1). *arXiv preprint, 2607.12208v1*.

Selected result: Theorem 1 certificate endpoint.

This development uses fixed Appendix B certificates and explicit input hypotheses; it does not claim to formalize every analytic part of the paper. The checked certificate endpoint has no nonstandard axioms.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 6 |
| Physical Lean lines | 1,789 |
| Passed / tasks (main + supporting) | 1/1 (1+0) |
| Used external references (main results) | 0 |
| Cached Statlib modules | 1 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1: BH/FDR counterexample certificate | `app_dobriban_theorem1_counterexample_certificate` | [Main.lean:11](proof/src/ProverJobs/app_dobriban_theorem1_counterexample_certificate/Main.lean#L11) |

The linked declarations are the public proof entry points. Fully qualified declaration names and checked modules are listed in [proof/build.json](proof/build.json).

## Supporting tasks

No separate supporting paper tasks are selected for this package.

## External references used by the main results

No explicit external citation axioms are retained in this source package.

## License and permitted use

The original Lean formalization contributions in [proof/src/](proof/src/) are [MIT-licensed](../../LICENSES/MIT.txt), including commercial reuse subject to the MIT notice requirements. Imported dependencies are separately licensed.

The supplied Statlib `.olean` library caches are separate from the paper inputs and proof-source grant. They are limited to noncommercial reproduction and verification of this archive: no commercial use, extraction for other projects, or reverse engineering to recover or reconstruct library content, subject to independent upstream rights and applicable law. See the [cache license](../../LICENSES/CACHE-VERIFICATION.txt). Source reuse does not authorize commercial use of Statlib.

The cited paper and input materials retain their original rights; this repository does not grant permission to commercially exploit or relicense them. See [license scope and upstream notices](../../LICENSE).
