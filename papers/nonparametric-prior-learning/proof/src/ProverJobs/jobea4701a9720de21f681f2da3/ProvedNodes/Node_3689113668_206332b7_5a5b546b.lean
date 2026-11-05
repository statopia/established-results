import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base

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
theorem statopia_math_node_3689113668_206332b7 : ∀ {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    [MeasurableSpace.CountableOrCountablyGenerated alpha beta]
    (mu : Measure alpha) [SFinite mu]
    (kappa eta : Kernel alpha beta) [IsFiniteKernel kappa] [IsFiniteKernel eta]
    (h_ac : ∀ᵐ a ∂mu, kappa a ≪ eta a),
    Measure.compProd mu kappa
        = (Measure.compProd mu eta).withDensity
            (fun p : alpha × beta => Kernel.rnDeriv kappa eta p.1 p.2) ∧
      Measure.compProd mu kappa ≪ Measure.compProd mu eta := by
  /- @proof-region region.target-node.session.3d30015889176bf0 begin -/
  intro alpha beta _ _ _ mu _ kappa eta _ _ h_ac
  classical
  have hg_meas : Measurable (Function.uncurry (fun a b => Kernel.rnDeriv kappa eta a b)) :=
    Kernel.measurable_rnDeriv kappa eta
  have hae : Kernel.withDensity eta (fun a b => Kernel.rnDeriv kappa eta a b) =ᵐ[mu] kappa := by
    filter_upwards [h_ac] with a ha
    exact Kernel.withDensity_rnDeriv_eq ha
  have hcongr : Measure.compProd mu kappa
      = Measure.compProd mu (Kernel.withDensity eta (fun a b => Kernel.rnDeriv kappa eta a b)) :=
    (Measure.compProd_congr hae).symm
  have hwd : Measure.compProd mu (Kernel.withDensity eta (fun a b => Kernel.rnDeriv kappa eta a b))
      = (Measure.compProd mu eta).withDensity
          (fun p : alpha × beta => Kernel.rnDeriv kappa eta p.1 p.2) :=
    Measure.compProd_withDensity hg_meas
  constructor
  · exact hcongr.trans hwd
  · rw [hcongr, hwd]
    exact withDensity_absolutelyContinuous (Measure.compProd mu eta) _
  /- @proof-region region.target-node.session.3d30015889176bf0 end -/

end
end Statlib.Imported
