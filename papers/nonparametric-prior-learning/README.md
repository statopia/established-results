# Nonparametric Prior Learning — Theorem 2.4

Junxiong Jia, Deyu Meng, Zongben Xu and Fang Yao (2026). [Nonparametric Prior Learning in Differential Equation Modeling](https://doi.org/10.1080/01621459.2026.2625449). *Journal of the American Statistical Association*. Archived preprint: [arXiv:2310.12436v2](https://arxiv.org/abs/2310.12436v2). The input includes the supplementary material.

This selection proves an integrable formulation of Theorem 2.4, the PAC-Bayes transfer bound. With probability at least `1-delta`, one common event bounds the transfer error for every hyper-posterior by the empirical multi-task error, `(1/lambda+1/gamma)*KL(Q||HP)`, the unnormalized base-KL sum multiplied by `1/gamma`, the joint log-MGF term, and `log(1/delta)/sqrt(n)`. The task distributions and positive sample sizes are sampled independently from the environment; each task's observations follow its conditional product law. KL terms can equal positive infinity.

The statement uses separable real Banach spaces, a fixed hyper-prior, normalized Gibbs base posteriors, positive `lambda`, `gamma` and `n`, and `delta` in `(0,1]`. It explicitly assumes joint measurability and integrability of the indicated kernels, losses and exponential moments. In particular, the loss for each parameter must be integrable under **every data probability law**, and transfer/empirical loss integrands must be integrable under **every hyper-posterior**. These global integrability requirements are stronger than finite moments under the sampled task laws and exclude general squared losses on unbounded data spaces. They are the scope of this selected formalized result.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 43 |
| Physical Lean lines | 8,159 |
| Passed / selected tasks (main + supporting) | 1/1 (1+0) |
| Internal supporting lemma modules | 38 |
| Used external references (main result) | 1 |
| Cached Statlib modules | 1 |

[Paper and supplement](input/main.pdf) · [Selected theorem specification](input/theorems.yaml) · [Lean sources](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem and supporting entries

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 2.4 | `Statlib.Imported.theorem_2_4` | [Main.lean:14](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/Main.lean#L14) |
| Statistical objects and loss definitions | `Statlib.Imported.T24` | [Base.lean](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/Base.lean) |
| Internal supporting lemmas | `Statlib.Imported.statopia_math_node_*` | [ProvedNodes.lean](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/ProvedNodes.lean), [lemma modules](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/ProvedNodes/) |

The selected task is Theorem 2.4. Its 38 internal lemma modules provide change of measure, approximation of test functions, product/conditional KL chain rules and exponential-Markov estimates; they are included in source counts.

## External reference and use location

| Reference | Axiom declaration | Use location |
| --- | --- | --- |
| Pinski, Simpson, Stuart and Weber (2015), [formula (A.1)](https://doi.org/10.1137/140962802): Donsker-Varadhan variational formula | [citation:11](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/ExternalNodes/Node_a26b2b509ee15a62f52b.lean#L11) | [bounded-test-function bridge:57](proof/src/ProverJobs/jobea4701a9720de21f681f2da3/ProvedNodes/Node_35798353_6c7e7779_b4361b5f.lean#L57) |

The citation states the variational formula for bounded continuous test functions on a Polish probability space. The Lean lemmas extend it to the measurable/integrable functions used by the proof. The build checks all configured source modules and the selected main theorem's recursive axiom dependencies.
