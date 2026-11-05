# Dynamic Matrix Recovery — Theorem 1

Ziyuan Chen, Ying Yang and Fang Yao (2024). [Dynamic Matrix Recovery](https://doi.org/10.1080/01621459.2023.2297468). *Journal of the American Statistical Association, 119(548), 2996–3007*. Related preprint: [arXiv:2305.10524](https://arxiv.org/abs/2305.10524). This selection formalizes Theorem 1 and Lemma 1 from the supplied corrected general positive-definite design version.

The main theorem bounds the Frobenius error of the local nuclear-norm penalized estimator. For `lambda >= 2 WDelta`, the bound is `kappa * bias + min {sqrt ((kappa * bias)^2 + (2 lambda / mu) * nuclearNorm M0), ((1 + sqrt 2) / 2) * (lambda / mu) * sqrt (rank M0)}`. It also proves the sharper displayed square-root bound for the data-dependent choice `lambda = 2 WDelta`. Here `mu` is the minimum eigenvalue of the design second-moment matrix and `kappa` is its condition number.

The common design second-moment matrix `Sigma` is positive definite; the smoothing weights are nonnegative and sum to one. The feasible set is nonempty, closed and convex and contains the true matrix at the selected time. The formal statement includes the observation model, measurability and integrability assumptions, zero noise/design cross-moments, a common design second-moment form and the estimator's minimization property. Lemma 1 gives a condition-number bound for a positive-definite bilinear form.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 28 |
| Physical Lean lines | 4,827 |
| Passed / tasks (main + supporting) | 2/2 (1+1) |
| Used external references (main result) | 0 |
| Cached Statlib modules | 307 |

[Input paper](input/main.tex) · [Supplement](input/supp.tex) · [Main theorem specification](input/theorems.yaml) · [Lemma 1 specification](input/supporting/lemma-1.yaml) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1: general positive-definite design error bound | `PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported.Theorem_1_thm_error_bound_corrected_general_positive_definite_design_error_bound_with_explicit_kappa_Sigma_smoothing_bia` | [Result_r2_b4a74728d408437a9ead7cf6927ddd55.lean:15](proof/src/ProverJobs/paper_fresh_20261102t124951011390z_dynamic_matrix/PaperProofInterfaces/Result_r2_b4a74728d408437a9ead7cf6927ddd55.lean#L15) |

## Supporting task

| Task | Lean declaration | Source |
| --- | --- | --- |
| Lemma 1: positive-definite quadratic-form bound | `PaperProofTasks.job_paper_c8b26067279b40ecab829c145c82445e.Statlib.Imported.paper_c8b26067279b40ecab829c145c82445e` | [Result_r1_1b9b6482bf2841008c3df5c888f9d375.lean:13](proof/src/ProverJobs/paper_fresh_20261102t124951011390z_dynamic_matrix/PaperProofInterfaces/Result_r1_1b9b6482bf2841008c3df5c888f9d375.lean#L13) |

## External references and use locations

The main theorem has no external citation axiom in its recursive proof dependencies. Lemma 1 uses the following two spectral bounds.

| Reference used by Lemma 1 | Axiom declaration | Use location |
| --- | --- | --- |
| Minimum-eigenvalue quadratic-form lower bound | [ext_model_1:11](proof/src/ProverJobs/job_paper_c8b26067279b40ecab829c145c82445e/ExternalNodes/Node_6515c10a3b2a6920f75d.lean#L11) | [Lemma 1:23](proof/src/ProverJobs/paper_fresh_20261102t124951011390z_dynamic_matrix/PaperProofInterfaces/Result_r1_1b9b6482bf2841008c3df5c888f9d375.lean#L23) |
| Maximum-eigenvalue bilinear-form bound and condition-number identity | [ext_model_2:16](proof/src/ProverJobs/job_paper_c8b26067279b40ecab829c145c82445e/ExternalNodes/Node_4e38c0b212aeaf238af1.lean#L16) | [Lemma 1:26](proof/src/ProverJobs/paper_fresh_20261102t124951011390z_dynamic_matrix/PaperProofInterfaces/Result_r1_1b9b6482bf2841008c3df5c888f9d375.lean#L26) |

The build configuration checks both exact theorem declarations and their permitted axiom dependencies. The cache contains the recursive public Statlib module dependencies of the source imports.

## License and permitted use

The original Lean formalization contributions in [proof/src/](proof/src/) are [MIT-licensed](../../LICENSES/MIT.txt), including commercial reuse subject to the MIT notice requirements. Imported dependencies are separately licensed.

The supplied Statlib `.olean` library caches are separate from the paper inputs and proof-source grant. They are limited to noncommercial reproduction and verification of this archive: no commercial use, extraction for other projects, or reverse engineering to recover or reconstruct library content, subject to independent upstream rights and applicable law. See the [cache license](../../LICENSES/CACHE-VERIFICATION.txt). Source reuse does not authorize commercial use of Statlib.

The cited paper and input materials retain their original rights; this repository does not grant permission to commercially exploit or relicense them. See [license scope and upstream notices](../../LICENSE).
