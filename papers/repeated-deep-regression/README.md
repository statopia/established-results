# Deep Regression for Repeated Measurements — Theorem 2.1

Shunxing Yan, Fang Yao and Hang Zhou (2025). [Deep Regression for Repeated Measurements](https://doi.org/10.1080/01621459.2025.2458344). *Journal of the American Statistical Association, 120(552), 2461–2472*. Archived preprint: [arXiv:2302.13908v2](https://arxiv.org/abs/2302.13908v2). This selection proves a formalized instance of Theorem 2.1 and Lemmas S.2, S.3 and S.8.

The main result gives a positive universal constant bounding the expected integrated squared prediction error by the approximation term, `(B1^2 + B2^2) / n`, and the localized-complexity term `(rstar + 1/(n*m)) * (B1^2 + B2^2 * log(n)^2 + B3^2 * log(n*m)^2)`.

The selected statement assumes `B1 >= 1`, positive `B2` and `B3`, the displayed exponential-moment conditions `E exp(|U_i(X_ij)| / B2) <= 1` and `E exp(|eps_ij| / B3) <= 1`, independent design samples and subject processes, centered independent measurement errors, and a positive subroot-complexity fixed point. It also includes the stated boundedness, continuity, measurability and integrability conditions. The candidate class is star-convex about its mean `f0`, which agrees with the regression function `fcirc` almost everywhere, and admits a countable pointwise approximation. For a nonempty candidate class these conditions include the mean in the class, so the approximation term vanishes. These are the assumptions of this selected formalized instance.

Lemma S.2 assumes a countable pointwise approximating subclass and the explicit localization-regime inequality in its Lean contract; its concentration event uses `t+1` confidence slack. Lemma S.8 applies to bounded centered processes whose absolute normalized-average supremum is controlled pointwise by a countable subclass. The countable Massart tail uses a strict bad event, so the resulting good event has the displayed non-strict bound, including zero envelopes. The main theorem supplies the pointwise separability required by Lemma S.2.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 44 |
| Physical Lean lines | 8,774 |
| Passed / tasks (main + supporting) | 4/4 (1+3) |
| Used external references (main result) | 2 |
| Cached Statlib modules | 17 |

[Input paper](input/main.pdf) · [Supplement](input/supp.pdf) · [Main theorem specification](input/theorems.yaml) · [Supporting specifications](input/supporting/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 2.1 | `PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression.Statlib.Imported.Theorem_2_1_first_main_theorem_thm_thm1_non_asymptotic_prediction_error_bound_for_repeated_measurements_regression` | [Result_r7_27863536a81849878cf4d6dc79d21dbe.lean:20](proof/src/ProverJobs/paper_fresh_20261030t103504286z_deep_regression/PaperProofInterfaces/Result_r7_27863536a81849878cf4d6dc79d21dbe.lean#L20) |

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Lemma S.2 | `PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.paper_8d614b8e54384bdaa316eb81207fecf6` | [Result_r8_e343c8253c2e4ab7a3769d098ab27284.lean:17](proof/src/ProverJobs/paper_fresh_20261030t103504286z_deep_regression/PaperProofInterfaces/Result_r8_e343c8253c2e4ab7a3769d098ab27284.lean#L17) |
| Lemma S.3 | `PaperProofTasks.job_paper_1574fdcfec814d558ee3dee791a61f4b.Statlib.Imported.paper_1574fdcfec814d558ee3dee791a61f4b` | [Result_r1_8e140b0ad7e34b6cbff6d58f43cd4e1d.lean:15](proof/src/ProverJobs/paper_fresh_20261030t103504286z_deep_regression/PaperProofInterfaces/Result_r1_8e140b0ad7e34b6cbff6d58f43cd4e1d.lean#L15) |
| Lemma S.8 | `PaperProofTasks.job_paper_383d12cb48d74c8f98648c6beef78bb3.Statlib.Imported.paper_383d12cb48d74c8f98648c6beef78bb3` | [Result_r4_ca83ae08893c497f9e70940ee4dba991.lean:16](proof/src/ProverJobs/paper_fresh_20261030t103504286z_deep_regression/PaperProofInterfaces/Result_r4_ca83ae08893c497f9e70940ee4dba991.lean#L16) |

## External references and use locations

The main theorem uses the following two retained citation interfaces through its supporting results. The exact interfaces and their proof use locations are linked below.

| Reference | Axiom declaration | Use location |
| --- | --- | --- |
| Ledoux and Talagrand (1991), Theorem 4.12: Rademacher contraction | [ext_model_1:18](proof/src/ProverJobs/job_paper_8d614b8e54384bdaa316eb81207fecf6/ExternalNodes/Node_6515c10a3b2a6920f75d.lean#L18) | [Lemma S.2:308](proof/src/ProverJobs/job_paper_8d614b8e54384bdaa316eb81207fecf6/ProvedNodes/Node_1156518618_e13ca37b_de059a44.lean#L308) |
| Massart (2000), Theorem 4: countable-index bounded-process concentration | [massart_countable_average_tail:10](proof/src/ProverJobs/job_paper_383d12cb48d74c8f98648c6beef78bb3/ExternalNodes/Node_94432b52633046d7cf21.lean#L10) | [Lemma S.8:61](proof/src/ProverJobs/paper_fresh_20261030t103504286z_deep_regression/PaperProofInterfaces/Result_r4_ca83ae08893c497f9e70940ee4dba991.lean#L61) |

The build checks every configured source module and each selected theorem's recursive axiom dependencies. The cache contains the recursive public Statlib dependencies of the source imports.
