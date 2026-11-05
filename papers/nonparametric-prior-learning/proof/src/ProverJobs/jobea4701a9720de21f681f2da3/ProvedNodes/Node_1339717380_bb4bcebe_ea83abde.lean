import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_2532196350_d96cfaed_5069ee04
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_3061690113_f8874630_7f6128e7


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
theorem statopia_math_node_1339717380_bb4bcebe : ∀ {Theta U : Type*} [MeasurableSpace Theta] [MeasurableSpace U]
    (n : ℕ) (hn : 0 < n)
    [MeasurableSpace.CountableOrCountablyGenerated Theta (Fin n → U)]
    (Qpost HP : ProbabilityMeasure Theta)
    (kap lam : Fin n → Theta → Measure U)
    (hkap_prob : ∀ (i : Fin n) (theta : Theta), IsProbabilityMeasure (kap i theta))
    (hlam_prob : ∀ (i : Fin n) (theta : Theta), IsProbabilityMeasure (lam i theta))
    (hkap_meas : ∀ i : Fin n, Measurable fun theta : Theta => kap i theta)
    (hlam_meas : ∀ i : Fin n, Measurable fun theta : Theta => lam i theta)
    (hKL_meas : ∀ i : Fin n, Measurable fun theta : Theta =>
      InformationTheory.klDiv (kap i theta) (lam i theta)),
    InformationTheory.klDiv
        ((Qpost : Measure Theta).bind fun theta =>
          Measure.map (fun u : Fin n → U => (theta, u))
            (Measure.pi fun i : Fin n => kap i theta))
        ((HP : Measure Theta).bind fun theta =>
          Measure.map (fun u : Fin n → U => (theta, u))
            (Measure.pi fun i : Fin n => lam i theta))
      = InformationTheory.klDiv (Qpost : Measure Theta) (HP : Measure Theta)
        + ∫⁻ theta, ∑ i : Fin n, InformationTheory.klDiv (kap i theta) (lam i theta)
            ∂(Qpost : Measure Theta) := by
  /- @proof-region region.target-node.session.1255368ea21ef1b6 begin -/
  intro Θ U _ _ n hn _ Qpost HP kap lam hkap_prob hlam_prob hkap_meas hlam_meas hKL_meas
  have hchain : InformationTheory.klDiv
      ((Qpost : Measure Θ).bind fun θ =>
        Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n => kap i θ))
      ((HP : Measure Θ).bind fun θ =>
        Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n => lam i θ))
      = InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ)
        + ∫⁻ θ, InformationTheory.klDiv (Measure.pi fun i : Fin n => kap i θ)
            (Measure.pi fun i : Fin n => lam i θ) ∂(Qpost : Measure Θ) := by
    exact statopia_math_node_2532196350_d96cfaed n hn Qpost HP kap lam hkap_prob hlam_prob
      hkap_meas hlam_meas hKL_meas
  have htensor : ∀ θ : Θ, InformationTheory.klDiv (Measure.pi fun i : Fin n => kap i θ)
      (Measure.pi fun i : Fin n => lam i θ)
      = ∑ i : Fin n, InformationTheory.klDiv (kap i θ) (lam i θ) := by
    intro θ
    exact statopia_math_node_3061690113_f8874630 n (fun i => kap i θ) (fun i => lam i θ)
      (fun i => hkap_prob i θ) (fun i => hlam_prob i θ)
  rw [hchain]
  simp only [htensor]
  /- @proof-region region.target-node.session.1255368ea21ef1b6 end -/

end
end Statlib.Imported
