# Residual spectral matching — first main theorem (Theorem 4.1)

Ziyuan Chen and Fang Yao. *Residual spectral matching: a new perspective for matrix completion*. Supplied revised manuscript and supplement (version date unspecified). Related public preprint: [*Matrix Completion via Residual Spectral Matching* (2024), arXiv:2412.10005v2](https://arxiv.org/abs/2412.10005v2).

The retained [main manuscript](input/main.tex) and [supplement](input/supp.tex) are the supplied revised texts. The selected first main theorem is numbered **Theorem 4.1** in that manuscript, with label `thm:upper_bound_for_rankr`.

The result bounds the Frobenius recovery error by `C σ sqrt(m r / p)` with probability at least `1 − c n⁻³`. One common event controls every finite-loss incoherent rank-`r` candidate satisfying `L(M) ≤ C_L ω₁`, including any global minimizer when one exists. The assumptions include independent Bernoulli sampling, centered independent subexponential noise, an independent same-mask Gaussian reference, the stated rank/incoherence and sampling bounds, fixed `α₀ > 15`, and the asymptotic first-weight condition. Constants are chosen before the dimensions and data, after the fixed parameters and weight family.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 329 |
| Physical Lean lines | 71,973 |
| Passed / tasks (main + supporting) | 5/5 (1+4) |
| Used external references (main results) | 5 |
| Cached Statlib modules | 348 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| First main theorem (Theorem 4.1): uniform rank-r recovery | `PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported.Theorem_4_1_first_main_theorem_thm_upper_bound_for_rankr_rank_r_matrix_recovery_bound_including_the_uniform_low_loss_can` | [M_3c654cddf6e1fcc0a7f3.lean:26](proof/src/ProverJobs/ResidualE2EAssembly20261106/M_3c654cddf6e1fcc0a7f3.lean#L26) |

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Mask geometry: uniform Bernoulli sampling bounds | `PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.paper_45fc93d926fd4099b9973daee59eb529` | [M_67d6ea704d6a7d52908a.lean:20](proof/src/ProverJobs/ResidualE2EAssembly20261106/M_67d6ea704d6a7d52908a.lean#L20) |
| Same-mask spectral and scale calibration | `PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.paper_951aae9227d84800bf9113306ae458aa` | [M_6b0a59abdf3a33a0a258.lean:22](proof/src/ProverJobs/ResidualE2EAssembly20261106/M_6b0a59abdf3a33a0a258.lean#L22) |
| Relative sampling for incoherent candidates | `PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.paper_165f462a7e494b7a9c0f4fb377733656` | [M_4dcb7f0571ad1487c5f6.lean:18](proof/src/ProverJobs/ResidualE2EAssembly20261106/M_4dcb7f0571ad1487c5f6.lean#L18) |
| Sparse coarse rigidity: sufficient-exponent formulation | `PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.Completed.sparse_coarse_rigidity` | [M_0be00d53e6a63ca31006.lean:255](proof/src/ProverJobs/ResidualE2ESupport20261106/M_0be00d53e6a63ca31006.lean#L255) |

The sparse coarse-rigidity entry has the selected sufficient-exponent contract `∀ D > 0, ∃ α₁ > 15, ∀ α₀ ≥ α₁, …`; this is a different exponent quantifier order from the supplied supplement. The main proof's calibration uses the stronger [all-`α₀ > 15` helper](proof/src/ProverJobs/ResidualE2ESupport20261106/M_fa8bbc31a4e4e2df874d.lean#L261) instead. Its constants may depend on `α₀`; it does not require `α₀ ≥ 16`. The separate helper is an internal proof component, not an additional counted task.

## External references used by the main result

The count is the number of distinct external citation axioms in the actual recursive proof dependencies of the selected main theorem. It counts five retained results, including three results from the same Brailovskaya–van Handel paper. Standard Lean axioms, ordinary library imports, unused declarations and explicit theorem hypotheses are excluded. These citations remain assumptions in the formal development.

| Reference | Axiom declaration and source | Direct proof uses |
| --- | --- | --- |
| Brailovskaya–van Handel, *Universality and Sharp Matrix Concentration Inequalities*, Remark 6.13: resolvent trace comparison | `PaperProofTasks.ResidualE2ESupport20261106.ext_model_1` — [Node_4e757cd702eee1ecc4cb.lean:44](proof/src/ProverJobs/ResidualE2ESupport20261106/ExternalNodes/Node_4e757cd702eee1ecc4cb.lean#L44) | [M_6a5763320d58217f30a5.lean:68](proof/src/ProverJobs/ResidualE2ESupport20261106/M_6a5763320d58217f30a5.lean#L68) |
| Brailovskaya–van Handel, Corollary 2.7: upper norm concentration | `PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.bvh_upper_concentration` — [Node_556e505598fbe6bfd0d0.lean:33](proof/src/ProverJobs/ResidualE2ESupport20261106/ExternalNodes/Node_556e505598fbe6bfd0d0.lean#L33) | [M_02fc9694186f0fd2900a.lean:49](proof/src/ProverJobs/ResidualE2ESupport20261106/M_02fc9694186f0fd2900a.lean#L49), [M_fcdbf385f97b07d4c7eb.lean:79](proof/src/ProverJobs/ResidualE2ESupport20261106/M_fcdbf385f97b07d4c7eb.lean#L79) |
| Brailovskaya–van Handel, Theorem 3.16 and §9.2: lower singular-value edge | `PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.bvh_lower_edge` — [Node_3965994620e137a49900.lean:12](proof/src/ProverJobs/ResidualE2ESupport20261106/ExternalNodes/Node_3965994620e137a49900.lean#L12) | [M_d004fbb4a25718027e28.lean:40](proof/src/ProverJobs/ResidualE2ESupport20261106/M_d004fbb4a25718027e28.lean#L40) |
| Bai–Silverstein (2010), Theorem B.14: smoothing inequality | `PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.bai_smoothing_modulus` — [Node_610ef984489599a94e55.lean:18](proof/src/ProverJobs/ResidualE2ESupport20261106/ExternalNodes/Node_610ef984489599a94e55.lean#L18) | [M_72c3ed5da738fdd670a7.lean:34](proof/src/ProverJobs/ResidualE2ESupport20261106/M_72c3ed5da738fdd670a7.lean#L34) |
| Tu et al. (2016), Lemma 5.4: Procrustes distance bound | `PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.ext_model_2` — [M_84b6b31a8725c0394946.lean:19](proof/src/ProverJobs/ResidualE2EAssembly20261106/M_84b6b31a8725c0394946.lean#L19) | [M_5d1852be792d69517477.lean:63](proof/src/ProverJobs/ResidualE2EAssembly20261106/M_5d1852be792d69517477.lean#L63) |

Reference sources:

- Tatiana Brailovskaya and Ramon van Handel, [*Universality and Sharp Matrix Concentration Inequalities*](https://web.math.princeton.edu/~rvan/tuniv240625.pdf), retained resolvent-comparison, concentration and lower-edge results.
- Zhidong Bai and Jack W. Silverstein (2010), *Spectral Analysis of Large Dimensional Random Matrices*, second edition, Theorem B.14; [publisher appendix](https://link.springer.com/content/pdf/bbm:978-1-4419-0661-8/1).
- Stephen Tu, Ross Boczar, Max Simchowitz, Mahdi Soltanolkotabi and Benjamin Recht (2016), [*Low-rank Solutions of Linear Matrix Equations via Procrustes Flow*](https://arxiv.org/abs/1507.03566v2), Lemma 5.4. The citation explicitly requires a strictly positive smallest singular value, which is proved at its application site.

## Verification

From `proof/`:

```sh
lake update
lake exe cache get
python3 verify.py
```

The build compiles the complete retained source package against pinned Lean/Mathlib versions and the checked Statlib cache, then checks the five selected targets against their external-axiom allowlists. Task counts refer to these Lean targets under the hypotheses and citations stated here.

## License and permitted use

The original Lean formalization contributions in [proof/src/](proof/src/) are [MIT-licensed](../../LICENSES/MIT.txt), including commercial reuse subject to the MIT notice requirements. Imported dependencies are separately licensed.

The supplied Statlib `.olean` library caches are separate from the paper inputs and proof-source grant. They are limited to noncommercial reproduction and verification of this archive: no commercial use, extraction for other projects, or reverse engineering to recover or reconstruct library content, subject to independent upstream rights and applicable law. See the [cache license](../../LICENSES/CACHE-VERIFICATION.txt). Source reuse does not authorize commercial use of Statlib.

The cited paper and input materials retain their original rights; this repository does not grant permission to commercially exploit or relicense them. See [license scope and upstream notices](../../LICENSE).
