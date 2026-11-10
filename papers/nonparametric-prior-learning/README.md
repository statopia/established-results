# Nonparametric Prior Learning — Theorems 2.4 and 3.3

Junxiong Jia, Deyu Meng, Zongben Xu and Fang Yao (2026). [Nonparametric Prior Learning in Differential Equation Modeling](https://doi.org/10.1080/01621459.2026.2625449). *Journal of the American Statistical Association*. Archived preprint: [arXiv:2310.12436v2](https://arxiv.org/abs/2310.12436v2). The input includes the supplementary material.

Theorem 2.4 is retained in an integrable formulation of Theorem 2.4, the PAC-Bayes transfer bound. With probability at least `1-delta`, one common event bounds the transfer error for every hyper-posterior by the empirical multi-task error, `(1/lambda+1/gamma)*KL(Q||HP)`, the unnormalized base-KL sum multiplied by `1/gamma`, the joint log-MGF term, and `log(1/delta)/sqrt(n)`. The task distributions and positive sample sizes are sampled independently from the environment; each task's observations follow its conditional product law. KL terms can equal positive infinity.

The statement uses separable real Banach spaces, a fixed hyper-prior, normalized Gibbs base posteriors, positive `lambda`, `gamma` and `n`, and `delta` in `(0,1]`. It explicitly assumes joint measurability and integrability of the indicated kernels, losses and exponential moments. In particular, the loss for each parameter must be integrable under **every data probability law**, and transfer/empirical loss integrands must be integrable under **every hyper-posterior**. These global integrability requirements are stronger than finite moments under the sampled task laws and exclude general squared losses on unbounded data spaces. They are the scope of this selected formalized result.

## Theorem 3.3: spectral/domain formulation

For a fixed hyperparameter, a positive sample size and a positive tempering parameter, the additional result proves that the generalized posterior is absolutely continuous with respect to its data-dependent Gaussian prior, has the stated exponential Radon–Nikodym density with a positive finite normalizer, and varies continuously in Hellinger distance as the finite dataset varies. The normalizer and posterior are the actual integral and normalized likelihood tilt, respectively.

The statement uses separable real Hilbert spaces, spectral covariance operators, positive eigenvalues with the stated summability conditions, and the learned Gaussian prior family. It assumes the displayed measurability and inverse-domain conditions, a finite exponential moment of `M₁(‖u‖_{U^{1−s̃}})²` near zero, and the stated growth and continuity of the prior mean in `U^{1+s̃}`. Data converge in the `X` topology and the `H^{α−s}` norm. The exponential-moment assumption is retained in both the finite- and infinite-dimensional cases.

This is the **spectral/domain formulation** given by the linked Lean declaration. Its explicit hypotheses specify its scope:

- Observations are elements of the ambient space `H`, with `H^{α−s} ⊆ range Γ^{1/2}`. The relevant forward-map values must also lie in `range Γ^{1/2}`, where `Γ⁻¹ᐟ²` is defined. The result does not claim to cover general data in negative-order completions or an almost-sure set of generalized-noise observations.
- The inverse and forward estimates in `hA1`–`hA4` use the spectral exponent `s̃`. In particular, `hA1` bounds `‖Γ⁻¹ᐟ²w‖_{H^{−s̃}}` by a constant times `‖w‖_{H^{α−s}}`, and bounds `‖Γ¹ᐟ²w‖_{H^{s̃}}` by a constant times `‖w‖_{H^{ρ−α}}` over its stated `ρ` interval. The corresponding estimates in the paper's Assumption 3.2 use `s` and, for the second output norm, `ρ`. The archived declaration therefore carries different explicit spectral compatibility conditions; full equivalence to every case of the paper is not asserted.

[Theorem 3.3 paper](input/theorem-3-3/main.pdf) · [Supplement](input/theorem-3-3/supp.pdf) · [Theorem 3.3 specification](input/theorem-3-3/theorems.yaml)

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 154 |
| Physical Lean lines | 34,200 |
| Passed / selected tasks (main + supporting) | 2/2 (2+0) |
| Internal supporting lemma modules | 145 |
| Used external references (main results) | 1 |
| Cached Statlib modules | 31 |

[Paper and supplement](input/main.pdf) · [Selected theorem specification](input/theorems.yaml) · [Lean sources](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorems and supporting entries

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 2.4 | `Statlib.Imported.theorem_2_4` | [Main.lean:14](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/Main.lean#L14) |
| Theorem 3.3 (spectral/domain formulation) | `PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported.Theorem_3_3_Bayesian_Well_Posedness_of_Inverse_Problems_posterior_density_positive_finite_normalizer_and_Hellinger_conti` | [Main.lean:19](proof/src/ProverJobs/paper_fresh_20261108t120211266248z_prior_learning33/Main.lean#L19) |
| Statistical objects and loss definitions | `Statlib.Imported.T24` | [Base.lean](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/Base.lean) |
| Internal supporting lemmas | `Statlib.Imported.statopia_math_node_*` | [ProvedNodes.lean](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/ProvedNodes.lean), [lemma modules](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/ProvedNodes/) |

The two selected tasks are the main Theorems 2.4 and 3.3, with no separately selected supporting tasks. The 38 internal lemma modules for Theorem 2.4 provide change of measure, approximation of test functions, product/conditional KL chain rules and exponential-Markov estimates. Theorem 3.3 has 107 internal lemma modules for Gaussian measures, spectral norms, prior-density comparison, normalization and Hellinger continuity; their entry is [ProvedNodes.lean](proof/src/ProverJobs/paper_fresh_20261108t120211266248z_prior_learning33/ProvedNodes.lean), with definitions in [Base.lean](proof/src/ProverJobs/paper_fresh_20261108t120211266248z_prior_learning33/Base.lean). All internal modules are included in source counts.

## External references used and use location

| Reference | Axiom declaration | Use location |
| --- | --- | --- |
| Pinski, Simpson, Stuart and Weber (2015), [formula (A.1)](https://doi.org/10.1137/140962802): Donsker-Varadhan variational formula | [citation:11](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/ExternalNodes/Node_a26b2b509ee15a62f52b.lean#L11) | [bounded-test-function bridge:57](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/ProvedNodes/Node_35798353_6c7e7779_b4361b5f.lean#L57) |

Only Theorem 2.4 uses this citation; Theorem 3.3 has no external citation axiom in its recursive proof dependencies. Standard Lean axioms and ordinary library imports are excluded from the count.

The citation states the variational formula for bounded continuous test functions on a Polish probability space. The Lean lemmas extend it to the measurable/integrable functions used by the proof. The build checks all configured source modules and the selected main theorem's recursive axiom dependencies.

## Verification

From `proof/`:

```sh
lake update
lake exe cache get
python3 verify.py
```

The build configuration lists the two selected main targets and their separate axiom allowlists. Verification compiles all retained sources against pinned Lean/Mathlib dependencies and the checked Statlib cache, then checks each target's recursive axiom dependencies.

## License and permitted use

The original Lean formalization contributions in [proof/src/](proof/src/) are [MIT-licensed](../../LICENSES/MIT.txt), including commercial reuse subject to the MIT notice requirements. Imported dependencies are separately licensed.

The supplied Statlib `.olean` library caches are separate from the paper inputs and proof-source grant. They are limited to noncommercial reproduction and verification of this archive: no commercial use, extraction for other projects, or reverse engineering to recover or reconstruct library content, subject to independent upstream rights and applicable law. See the [cache license](../../LICENSES/CACHE-VERIFICATION.txt). Source reuse does not authorize commercial use of Statlib.

The cited paper and input materials retain their original rights; this repository does not grant permission to commercially exploit or relicense them. See [license scope and upstream notices](../../LICENSE).
