# Data thinning — Theorem 1

Ameer Dharamshi, Anna Neufeld, Keshav Motwani, Lucy L. Gao, Daniela Witten and Jacob Bien (2025). [Generalized Data Thinning Using Sufficient Statistics](https://doi.org/10.1080/01621459.2024.2353948). *Journal of the American Statistical Association, 120(549), 511–523*. Archived preprint: [arXiv:2303.12931v3](https://arxiv.org/abs/2303.12931v3).

Selected result: Theorem 1 (generalized thinning).

The final theorem has no nonstandard axioms. The exact modeling hypotheses remain in the Lean declaration.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 5 |
| Physical Lean lines | 125 |
| Passed / tasks (main + supporting) | 1/1 (1+0) |
| Used external references (main results) | 0 |
| Cached Statlib modules | 0 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1: generalized thinning | `Theorem_1_Main_theorem_thm_generalized_thinning` | [Result_r1_4ef57bb18b204c33b27dd76a319b4312.lean:11](proof/src/ProverJobs/paper_fresh_20261028t224543381z_data_thinning/PaperProofInterfaces/Result_r1_4ef57bb18b204c33b27dd76a319b4312.lean#L11) |

The linked declarations are the public proof entry points. Fully qualified declaration names and checked modules are listed in [proof/build.json](proof/build.json).

`Base.lean` contains definitions and helper proofs; the selected public theorem statements are in the linked `PaperProofInterfaces` files.

## Supporting tasks

No separate supporting paper tasks are selected for this package.

## External references used by the main results

No explicit external citation axioms are retained in this source package.

## License and permitted use

The original Lean formalization contributions in [proof/src/](proof/src/) are [MIT-licensed](../../LICENSES/MIT.txt), including commercial reuse subject to the MIT notice requirements. Imported dependencies are separately licensed.

The supplied Statlib `.olean` library caches are separate from the paper inputs and proof-source grant. They are limited to noncommercial reproduction and verification of this archive: no commercial use, extraction for other projects, or reverse engineering to recover or reconstruct library content, subject to independent upstream rights and applicable law. See the [cache license](../../LICENSES/CACHE-VERIFICATION.txt). Source reuse does not authorize commercial use of Statlib.

The cited paper and input materials retain their original rights; this repository does not grant permission to commercially exploit or relicense them. See [license scope and upstream notices](../../LICENSE).
