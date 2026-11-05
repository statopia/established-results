# Some Established Results for Statistical Problems via Statopia Prover

Some selected Lean 4 formalization results verified using [Statopia Prover](https://prover.statopia.ai/).

- [Statopia Prover](https://prover.statopia.ai/)
- [Statlib](https://statlib.statopia.ai/)

The collection contains 83 statistics problems, six guided IMO results, fourteen papers (15 main developments and 52 supporting tasks), and a neural-network approximation component.

- [Paper results](papers/README.md)
- [Statistics benchmark](statistics-benchmark/README.md)
- [IMO results](imo-2026/README.md)
- [Neural-network approximation](statlib-contributions/neural-network-approximation/SUMMARY.md)

Every paper, benchmark task and IMO task has `input/`, `proof/` and a result summary. `proof/` contains Lean sources, the required Statlib cache, exact targets and pinned build configuration. Source line counts include supporting modules. Results are checked under their stated hypotheses and the external citations actually used by their proofs.

| Paper | Lean files | Lean lines | Cached modules | Used external references | Passed / tasks (main + supporting) |
| --- | ---: | ---: | ---: | ---: | ---: |
| [CCK — Theorem 2 (covariance-only bound)](papers/cck/README.md) | 78 | 12,223 | 122 | 1 | 6/6 (1+5) |
| [Gaussian approximation — Theorem 3.1](papers/gaussian/README.md) | 88 | 15,047 | 90 | 3 | 6/6 (1+5) |
| [DP clustering — Theorem 1](papers/dp-clustering/README.md) | 218 | 34,932 | 4 | 0 | 16/16 (1+15) |
| [Dynamic Matrix Recovery — Theorem 1](papers/dynamic-matrix/README.md) | 28 | 4,827 | 307 | 0 | 2/2 (1+1) |
| [ProTrans — Theorem 1 (corrected model-shift bound)](papers/protrans/README.md) | 88 | 11,643 | 44 | 0 | 10/10 (1+9) |
| [Deep Regression for Repeated Measurements — Theorem 2.1](papers/repeated-deep-regression/README.md) | 44 | 8,774 | 17 | 2 | 4/4 (1+3) |
| [Nonparametric Prior Learning — Theorem 2.4 (integrable formulation)](papers/nonparametric-prior-learning/README.md) | 43 | 8,159 | 1 | 1 | 1/1 (1+0) |
| [HulC — Theorem 1](papers/hulc/README.md) | 15 | 1,397 | 1 | 0 | 2/2 (1+1) |
| [HMC — Theorems 2.2 (i–ii) and 5.14](papers/hmc/README.md) | 73 | 7,214 | 2 | 1 | 8/8 (2+6) |
| [Data thinning — Theorem 1](papers/data-thinning/README.md) | 5 | 125 | 0 | 0 | 1/1 (1+0) |
| [EILLS — Theorem 4.2](papers/eills/README.md) | 11 | 2,079 | 0 | 0 | 1/1 (1+0) |
| [CQR — Theorem 1 (lower-coverage core)](papers/cqr/README.md) | 6 | 394 | 5 | 0 | 6/6 (1+5) |
| [Dobriban — Theorem 1 (certificate)](papers/dobriban/README.md) | 6 | 1,789 | 1 | 0 | 1/1 (1+0) |
| [Lei — Theorem 3.1 (interfaces)](papers/lei/README.md) | 17 | 2,786 | 1 | 0 | 3/3 (1+2) |

Used external references count distinct citation axioms in the actual recursive proof dependencies of the selected main theorem(s), counted once per paper. Citations used only by independent supporting tasks, unused declarations, library imports and explicit theorem hypotheses are excluded. Passed/tasks gives the total with its main/supporting split.

## Paper references

- **CCK** — Victor Chernozhukov, Denis Chetverikov and Kengo Kato (2015). [Comparison and anti-concentration bounds for maxima of Gaussian random vectors](https://doi.org/10.1007/s00440-014-0565-9). *Probability Theory and Related Fields, 162, 47–70*. Archived preprint: [arXiv:1301.4807v4](https://arxiv.org/abs/1301.4807v4). [Archived result](papers/cck/README.md).
- **Gaussian approximation** — Miles E. Lopes, Zhenhua Lin and Hans-Georg Müller (2020). [Bootstrapping Max Statistics in High Dimensions: Near-Parametric Rates Under Weak Variance Decay and Application to Functional and Multinomial Data](https://doi.org/10.1214/19-AOS1844). *The Annals of Statistics, 48(2), 1214–1229*. Archived preprint: [arXiv:1807.04429v2](https://arxiv.org/abs/1807.04429v2). [Archived result](papers/gaussian/README.md).
- **DP clustering** — Filippo Ascolani, Antonio Lijoi, Giovanni Rebaudo and Giacomo Zanella (2023). [Clustering consistency with Dirichlet process mixtures](https://doi.org/10.1093/biomet/asac051). *Biometrika, 110(2), 551–558*. Archived preprint: [arXiv:2205.12924v1](https://arxiv.org/abs/2205.12924v1). [Archived result](papers/dp-clustering/README.md).
- **Dynamic Matrix Recovery** — Ziyuan Chen, Ying Yang and Fang Yao (2024). [Dynamic Matrix Recovery](https://doi.org/10.1080/01621459.2023.2297468). *Journal of the American Statistical Association, 119(548), 2996–3007*. Related preprint: [arXiv:2305.10524](https://arxiv.org/abs/2305.10524). [Archived result](papers/dynamic-matrix/README.md).
- **ProTrans** — Ziyuan Chen, Yifan Jiang, Jingyuan Liu and Fang Yao (2026). [Deconfounding via Profiled Transfer Learning](https://doi.org/10.1080/01621459.2026.2686441). *Journal of the American Statistical Association*. Related preprint: [arXiv:2508.11622](https://arxiv.org/abs/2508.11622). [Archived result](papers/protrans/README.md).
- **Deep regression** — Shunxing Yan, Fang Yao and Hang Zhou (2025). [Deep Regression for Repeated Measurements](https://doi.org/10.1080/01621459.2025.2458344). *Journal of the American Statistical Association, 120(552), 2461–2472*. Archived preprint: [arXiv:2302.13908v2](https://arxiv.org/abs/2302.13908v2). [Archived result](papers/repeated-deep-regression/README.md).
- **Nonparametric prior learning** — Junxiong Jia, Deyu Meng, Zongben Xu and Fang Yao (2026). [Nonparametric Prior Learning in Differential Equation Modeling](https://doi.org/10.1080/01621459.2026.2625449). *Journal of the American Statistical Association*. Archived preprint: [arXiv:2310.12436v2](https://arxiv.org/abs/2310.12436v2). [Archived result](papers/nonparametric-prior-learning/README.md).
- **HulC** — Arun Kumar Kuchibhotla, Sivaraman Balakrishnan and Larry Wasserman (2024). [The HulC: Confidence Regions from Convex Hulls](https://doi.org/10.1093/jrsssb/qkad134). *Journal of the Royal Statistical Society Series B: Statistical Methodology, 86(3), 586–622*. Archived preprint: [arXiv:2105.14577v2](https://arxiv.org/abs/2105.14577v2). [Archived result](papers/hulc/README.md).
- **HMC** — Samuel Livingstone, Michael Betancourt, Simon Byrne and Mark Girolami (2019). [On the Geometric Ergodicity of Hamiltonian Monte Carlo](https://doi.org/10.3150/18-BEJ1083). *Bernoulli, 25(4A), 3109–3138*. Archived preprint: [arXiv:1601.08057v5](https://arxiv.org/abs/1601.08057v5). The archived v5 includes the corrigendum. [Archived result](papers/hmc/README.md).
- **Data thinning** — Ameer Dharamshi, Anna Neufeld, Keshav Motwani, Lucy L. Gao, Daniela Witten and Jacob Bien (2025). [Generalized Data Thinning Using Sufficient Statistics](https://doi.org/10.1080/01621459.2024.2353948). *Journal of the American Statistical Association, 120(549), 511–523*. Archived preprint: [arXiv:2303.12931v3](https://arxiv.org/abs/2303.12931v3). [Archived result](papers/data-thinning/README.md).
- **EILLS** — Jianqing Fan, Cong Fang, Yihong Gu and Tong Zhang (2024). [Environment Invariant Linear Least Squares](https://doi.org/10.1214/24-AOS2435). *The Annals of Statistics, 52(5), 2268–2292*. Archived preprint: [arXiv:2303.03092v3](https://arxiv.org/abs/2303.03092v3). [Archived result](papers/eills/README.md).
- **Conformalized quantile regression** — Yaniv Romano, Evan Patterson and Emmanuel J. Candès (2019). [Conformalized Quantile Regression](https://proceedings.neurips.cc/paper/2019/hash/5103c3584b063c431bd1268e9b5e76fb-Abstract.html). *Advances in Neural Information Processing Systems, 32 (NeurIPS 2019)*. Archived preprint: [arXiv:1905.03222v1](https://arxiv.org/abs/1905.03222v1). [Archived result](papers/cqr/README.md).
- **Dobriban** — Edgar Dobriban (2026). [The Benjamini–Hochberg Procedure Can Fail to Control the FDR for Correlated Two-Sided Gaussian Tests](https://arxiv.org/abs/2607.12208v1). *arXiv preprint, 2607.12208v1*. [Archived result](papers/dobriban/README.md).
- **Lei** — Lihua Lei (2026). [No Universal Multiplicative FDR Bound for the Benjamini–Hochberg Procedure with Correlated Two-Sided Gaussian Tests](https://arxiv.org/abs/2607.14812v1). *arXiv preprint, 2607.14812v1*. [Archived result](papers/lei/README.md).

To build a single task, enter its `proof/` directory:

```sh
lake update
lake exe cache get
python3 verify.py
```

At the collection root, `make setup` installs public dependencies, `make check` checks file/cache hashes, and `make verify` compiles every configured result and checks target axioms. Lean and Mathlib versions are pinned. The neural wrapper uses the root build entry and cache under `verification/`; its implementation sources and scope are described in its summary.
