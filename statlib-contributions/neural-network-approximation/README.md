# Neural-network approximation

Reference: Michael Kohler and Sophie Langer, *On the rate of convergence of fully connected deep neural network regression estimates*, Annals of Statistics 49(4), 2231–2249 (2021). The reference PDF and available author source are in [materials/](materials/).

[AtResolution.lean](AtResolution.lean) exposes positive architecture constants and, for every sufficiently large resolution `M`, a network with explicit depth proportional to `M^d`, bounded width, a parameter budget and approximation error proportional to `M^(-2(r+beta))`. This is an approximation component, not the entire statistical regression-risk theorem. Its explicit quantified assumptions remain in the Lean statement.

The seven implementation modules are published under [Statlib/](Statlib/). Root `make verify` checks the existing compiled library interface through the `AtResolution` wrapper using the pinned dependency cache. This command does not rebuild all seven implementation modules from source.

| Source | Physical lines |
| --- | ---: |
| [Statlib/Nonparametric/Approximation/NeuralNetwork.lean](Statlib/Nonparametric/Approximation/NeuralNetwork.lean) | 107 |
| [Statlib/Nonparametric/Approximation/NeuralNetworkAlgebra.lean](Statlib/Nonparametric/Approximation/NeuralNetworkAlgebra.lean) | 35,028 |
| [Statlib/Nonparametric/Approximation/ReLUNetworkConstruction.lean](Statlib/Nonparametric/Approximation/ReLUNetworkConstruction.lean) | 7,713 |
| [Statlib/Nonparametric/Approximation/ReLUStateMachine.lean](Statlib/Nonparametric/Approximation/ReLUStateMachine.lean) | 8,466 |
| [Statlib/Nonparametric/Approximation/ShallowReLUApproximation.lean](Statlib/Nonparametric/Approximation/ShallowReLUApproximation.lean) | 380 |
| [Statlib/Nonparametric/Approximation/ShallowReLUApproximationGeometry.lean](Statlib/Nonparametric/Approximation/ShallowReLUApproximationGeometry.lean) | 3,781 |
| [Statlib/Nonparametric/Vocabulary/NeuralNetwork.lean](Statlib/Nonparametric/Vocabulary/NeuralNetwork.lean) | 447 |

Total: 7 implementation source modules / 55,922 physical lines.

## License scope

The Statlib implementation modules and their compiled dependency caches are excluded from the paper-proof MIT grant. The implementation sources retain the license applicable to their upstream version; see the included [Statlib license](../../LICENSES/Statlib.txt). The supplied Statlib caches are limited to noncommercial verification of this archive under the [cache license](../../LICENSES/CACHE-VERIFICATION.txt), including its prohibition on reverse engineering to recover library content, subject to independent upstream rights and applicable law. The reference PDF and author TeX retain their original rights. See [repository license scope](../../LICENSE).
