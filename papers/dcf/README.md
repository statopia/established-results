# DCF — Theorem 1

Kaijie Xue and Fang Yao (2020). [*Distribution and correlation-free two-sample test of high-dimensional means*](https://doi.org/10.1214/19-AOS1848). *The Annals of Statistics, 48(3), 1304–1328*. Related preprint: [arXiv:1904.07416v1](https://arxiv.org/abs/1904.07416v1).

The retained [main paper](input/main.pdf) and [supplement](input/supp.pdf) supply Theorem 1 and Lemmas 1–4. The result bounds the two-sample Gaussian approximation error over all hyperrectangles by

`ρ** ≤ K₃ [(B² log⁷(p n)/n)^(1/6) + (B² log⁷(p m)/m)^(1/6)]`.

The assumptions include independent observations in both samples, independent Gaussian arrays with matching means and covariances, the stated third-moment and exponential-tail bounds, and the two rate-smallness conditions. The formalization covers positive sample sizes and `p ≥ 2`. For every fixed `δ₁ > δ₂ > 0` and every prescribed variance lower bound `b > 0`, the constants `K₃ > 0` and `c₁ > 0` are selected before the sequence `δ`, sample sizes, dimension, distributions and data; they may depend on those fixed bounds. The combined coordinate variances must be at least `b`. The main declaration is the uniform-variance version; the original declaration is retained as its `b = 1` corollary.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 164 |
| Physical Lean lines | 41,336 |
| Passed / tasks (main + supporting) | 5/5 (1+4) |
| Used external references (main results) | 1 |
| Cached Statlib modules | 91 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1 | `PaperProofTasks.paper_fresh_20261101t120354916065z_dcf.Statlib.Imported.Theorem_1_two_sample_Gaussian_approximation_over_rectangles_rho_n_m_double_star_bound_uniform_variance` | [Main.lean:24](proof/src/ProverJobs/paper_fresh_20261101t120354916065z_dcf/Main.lean#L24) |

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Lemma 1 | `PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported.paper_370f7a68a9a1447a9d903f9a55f08bd5` | [Main.lean:18](proof/src/ProverJobs/job_paper_370f7a68a9a1447a9d903f9a55f08bd5/Main.lean#L18) |
| Lemma 2 | `PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.paper_ed515f3f70ec457d86e430f1b91735bf` | [GaussianComparisonLemma2.lean:24](proof/src/ProverJobs/job_paper_ed515f3f70ec457d86e430f1b91735bf/ProofSupport/GaussianComparisonLemma2.lean#L24) |
| Lemma 3 | `PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported.paper_c88218b13cf249bdb98064482dead315` | [Main.lean:20](proof/src/ProverJobs/job_paper_c88218b13cf249bdb98064482dead315/Main.lean#L20) |
| Lemma 4 | `PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.paper_2d165b9668ee43088292ee6f2129e2cd` | [Main.lean:22](proof/src/ProverJobs/job_paper_2d165b9668ee43088292ee6f2129e2cd/Main.lean#L22) |

Lemma 1 constructs the smooth derivative majorant. Lemma 2 proves the two-sample interpolation comparison, including the zero-scale case. Lemma 3 gives the recursive Gaussian approximation bound, and Lemma 4 selects the smoothing parameters and absorbs the recursion. These are actual proofs in the retained package; their interface modules import the corresponding proofs.

## External references used by the main result

The count is the number of distinct external citation axioms in the actual recursive proof dependencies of the selected main theorem. Standard Lean axioms, ordinary library imports, explicit hypotheses and unused declarations are excluded. The retained external result remains an assumption.

| Reference | Declaration and source | Direct proof uses |
| --- | --- | --- |
| Chernozhukov–Chetverikov–Kato (2017), Lemma C.1: exponential tails to truncated third moments | `PaperProofTasks.paper_fresh_20261101t120354916065z_dcf.ext_model_4` — [Node_103826e30030eda123b2.lean:16](proof/src/ProverJobs/paper_fresh_20261101t120354916065z_dcf/ExternalNodes/Node_103826e30030eda123b2.lean#L16) | [Node_708476089_d6dcc332_8100d91f.lean:229](proof/src/ProverJobs/paper_fresh_20261101t120354916065z_dcf/ProvedNodes/Node_708476089_d6dcc332_8100d91f.lean#L229), [Node_708476089_d6dcc332_8100d91f.lean:316](proof/src/ProverJobs/paper_fresh_20261101t120354916065z_dcf/ProvedNodes/Node_708476089_d6dcc332_8100d91f.lean#L316) |

Victor Chernozhukov, Denis Chetverikov and Kengo Kato (2017). [*Central limit theorems and bootstrap in high dimensions*](https://arxiv.org/abs/1412.3661v4). *The Annals of Probability, 45(4), 2309–2352*, Lemma C.1. The retained nonnegative-variable form bounds the truncated third moment by `6 A (t+B)³ exp(−t/B)` under the exponential tail bound `P(ξ>x) ≤ A exp(−x/B)`.

Nazarov's Gaussian rectangle increment bound is supplied by the existing proved library theorem through [Node_2490289310_a8cb3761_ef64bef0.lean:26](proof/src/ProverJobs/job_paper_ed515f3f70ec457d86e430f1b91735bf/ProvedNodes/Node_2490289310_a8cb3761_ef64bef0.lean#L26); it is not a retained citation axiom.

## Verification

From `proof/`:

```sh
lake update
lake exe cache get
python3 verify.py
```

The build compiles the complete retained source package against pinned Lean/Mathlib versions and the checked Statlib cache, then checks the five selected targets against their external-axiom allowlists. Task counts refer to these Lean targets under the hypotheses and citation stated here.

## License and permitted use

The original Lean formalization contributions in [proof/src/](proof/src/) are [MIT-licensed](../../LICENSES/MIT.txt), including commercial reuse subject to the MIT notice requirements. Imported dependencies are separately licensed.

The supplied Statlib `.olean` library caches are separate from the paper inputs and proof-source grant. They are limited to noncommercial reproduction and verification of this archive: no commercial use, extraction for other projects, or reverse engineering to recover or reconstruct library content, subject to independent upstream rights and applicable law. See the [cache license](../../LICENSES/CACHE-VERIFICATION.txt). Source reuse does not authorize commercial use of Statlib.

The cited paper and input materials retain their original rights; this repository does not grant permission to commercially exploit or relicense them. See [license scope and upstream notices](../../LICENSE).
