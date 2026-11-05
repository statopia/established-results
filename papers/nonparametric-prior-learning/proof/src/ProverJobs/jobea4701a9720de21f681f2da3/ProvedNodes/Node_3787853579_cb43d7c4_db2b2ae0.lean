import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_2355383860_a99655fa_e6455cc0
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_3787853579_cb43d7c4 : ∀ {Theta U : Type*} [MeasurableSpace Theta] [MeasurableSpace U]
    [MeasurableSpace.CountableOrCountablyGenerated Theta U]
    (Q HP : ProbabilityMeasure Theta) (K L : Kernel Theta U)
    [IsMarkovKernel K] [IsMarkovKernel L]
    (hac : (Q : Measure Theta) ⊗ₘ K ≪ (HP : Measure Theta) ⊗ₘ L),
    ((Q : Measure Theta) ≪ (HP : Measure Theta)) ∧
    (∀ᵐ theta ∂(Q : Measure Theta),
      (K theta : Measure U) ≪ (L theta : Measure U)) := by
  /- @proof-region region.target-node.session.73f4172c18bfcb7d begin -/
  intro Theta U _ _ _ Q HP K L _ _ hac
  refine ⟨?_, ?_⟩
  · have hmap : ((Q : Measure Theta) ⊗ₘ K).fst ≪ ((HP : Measure Theta) ⊗ₘ L).fst :=
      hac.map measurable_fst
    rwa [Measure.fst_compProd, Measure.fst_compProd] at hmap
  · exact statopia_math_node_2355383860_a99655fa Q K L
      (Measure.absolutelyContinuous_compProd_of_compProd hac)
  /- @proof-region region.target-node.session.73f4172c18bfcb7d end -/

end
end Statlib.Imported
