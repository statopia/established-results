# ProTrans — Theorem 1

Ziyuan Chen, Yifan Jiang, Jingyuan Liu and Fang Yao (2026). [Deconfounding via Profiled Transfer Learning](https://doi.org/10.1080/01621459.2026.2686441). *Journal of the American Statistical Association*. Related preprint: [arXiv:2508.11622](https://arxiv.org/abs/2508.11622). This selection formalizes the supplied corrected model-shift Lasso theorem and nine supporting results.

For a desired exponent `c > 0`, the theorem chooses strictly positive constants `N0`, `C1` and `C2` before the dimension, sample sizes and data distribution. With the stated sample-size and regularization bounds, it constructs a measurable event of probability at least `1 - p^(-c)`. On this event, whenever the restricted-eigenvalue and initial-estimator bounds hold, every profiling/Lasso minimizer satisfies the stated l1, l2 and prediction-error bounds. It also gives the probability bound after subtracting the probabilities of failure of those two conditions.

The assumptions include independent sample rows, a common joint law for the residual/confounder pairs, centered sub-Gaussian coordinates and noise, noise independence from its corresponding residual/confounder pair, residual/confounder orthogonality, model-shift sparsity, bounded source-coefficient spread, weighted-average confounding similarity and uniformly bounded source heterogeneity. The constants have the dependency order stated in the corrected input theorem; the confounding map may be nonlinear.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 88 |
| Physical Lean lines | 11,643 |
| Passed / tasks (main + supporting) | 10/10 (1+9) |
| Used external references (main result) | 0 |
| Cached Statlib modules | 44 |

[Input paper](input/main.tex) · [Supplement](input/supp.tex) · [Main theorem specification](input/theorems.yaml) · [Supporting specifications](input/supporting/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1 | `PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer.ModelShiftLasso.thm_upper_bound_of_eta` | [Result_r2_6a9795530ac2493ab2d5d2297abd9bfa.lean:13](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r2_6a9795530ac2493ab2d5d2297abd9bfa.lean#L13) |

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| lem:high_probability_set | `PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.paper_106ef041a01147028d56a10b8f69010e` | [Result_r1_4c20b7b98d8b4deb93037d3bf57b6612.lean:22](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r1_4c20b7b98d8b4deb93037d3bf57b6612.lean#L22) |
| lem:error_sample_covariance_sparse | `PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf.Statlib.Imported.paper_8d45c5e7199146b78778677b2fbc23cf` | [Result_r2_6e79449348904d3687f01470dc38e7b3.lean:16](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r2_6e79449348904d3687f01470dc38e7b3.lean#L16) |
| lem:weighted_confounding_transfer | `PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.paper_110bb96e917848c19df0625891303d5c` | [Result_r2_f910a4d0bb8b49d3886c7ed362a9f427.lean:17](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r2_f910a4d0bb8b49d3886c7ed362a9f427.lean#L17) |
| lem:error_sample_covariance2 | `PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.paper_6ff987a9c5974b249aed2ac5c2c60b28` | [Result_r3_638efc8243244a249ba3f08616b7e29f.lean:18](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r3_638efc8243244a249ba3f08616b7e29f.lean#L18) |
| lem:error_noise | `PaperProofTasks.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Statlib.Imported.paper_5bfd1842871e4bc6b291fb4a9624d4b1` | [Result_r2_6defa74e9c844ff68b638ec8be62ff62.lean:18](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r2_6defa74e9c844ff68b638ec8be62ff62.lean#L18) |
| Scalar Bernstein bound | `PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa.Statlib.Imported.paper_ebad183ded244602a77f3710a9957efa` | [Result_r1_c78ef2b1a7b04addb1235360efc87b12.lean:17](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r1_c78ef2b1a7b04addb1235360efc87b12.lean#L17) |
| Uniform concentration argument (common moment bound for centered products) | `PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported.paper_6881610d85e44b6089ed4cd810570574` | [Result_r2_e24c3cb04d32496a93b7f37153f2a690.lean:16](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r2_e24c3cb04d32496a93b7f37153f2a690.lean#L16) |
| lem:error_sample_covariance1 | `PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported.paper_4a6904a098fa4fcebf3058bbb4e15c0e` | [Result_r1_b605a65c1a4f4314bf24e76c176cb5f5.lean:15](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r1_b605a65c1a4f4314bf24e76c176cb5f5.lean#L15) |
| Union-bound consequence over at most \(p^2\) or \(pq\) coordinates | `PaperProofTasks.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Statlib.Imported.paper_8ff73b3c73e04139840b7ba5205a04c8` | [Result_r1_06560c0791fe45d694620add3dcdf414.lean:16](proof/src/ProverJobs/paper_fresh_20261102t180245072z_profiled_transfer/PaperProofInterfaces/Result_r1_06560c0791fe45d694620add3dcdf414.lean#L16) |

## External references and use locations

None of the ten selected declarations depends on an external citation axiom.

The build checks every configured source module and each selected theorem's recursive axiom dependencies. The cache contains the recursive public Statlib dependencies of the source imports.
