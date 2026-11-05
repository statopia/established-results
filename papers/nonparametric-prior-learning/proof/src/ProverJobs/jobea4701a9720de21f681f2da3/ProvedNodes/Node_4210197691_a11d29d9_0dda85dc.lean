import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_79440718_8647c8d9_38e2d9f6

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
theorem statopia_math_node_4210197691_a11d29d9 : ∀ {Theta U : Type*} [MeasurableSpace Theta] [MeasurableSpace U]
    (n : ℕ) (kap : Fin n → Theta → Measure U)
    (hprob : ∀ (i : Fin n) (theta : Theta), IsProbabilityMeasure (kap i theta))
    (hmeas : ∀ i : Fin n, Measurable fun theta : Theta => kap i theta),
    Measurable fun theta : Theta =>
      Measure.map (fun u : Fin n → U => (theta, u)) (Measure.pi fun i : Fin n => kap i theta) := by
  /- @proof-region region.target-node.session.3b05a7a7a145520a begin -/
  intro Theta U _ _ n kap hprob hmeas
  have hπ : Measurable fun θ : Theta => Measure.pi fun i : Fin n => kap i θ :=
    statopia_math_node_79440718_8647c8d9 n kap hprob hmeas
  have hfin : ∀ θ : Theta, IsFiniteMeasure (Measure.pi fun i : Fin n => kap i θ) := by
    intro θ
    haveI : ∀ i : Fin n, IsProbabilityMeasure (kap i θ) := fun i => hprob i θ
    exact inferInstance
  rw [Measure.measurable_measure]
  intro s hs
  have hker : Measurable fun θ : Theta =>
      (Measure.pi fun i : Fin n => kap i θ) (Prod.mk θ ⁻¹' s) :=
    ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite
      (κ := ⟨fun θ => Measure.pi fun i : Fin n => kap i θ, hπ⟩) hs hfin
  have hmk : ∀ θ : Theta, Measurable fun u : Fin n → U => (θ, u) := fun θ => by measurability
  have hval : ∀ θ : Theta,
      (Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n => kap i θ)) s
        = (Measure.pi fun i : Fin n => kap i θ) (Prod.mk θ ⁻¹' s) := by
    intro θ
    simp [Measure.map_apply, hs, hmk θ]
  rw [show (fun b : Theta => (Measure.map (fun u : Fin n → U => (b, u))
        (Measure.pi fun i : Fin n => kap i b)) s)
      = fun b : Theta => (Measure.pi fun i : Fin n => kap i b) (Prod.mk b ⁻¹' s) from
    funext hval]
  exact hker
  /- @proof-region region.target-node.session.3b05a7a7a145520a end -/

end
end Statlib.Imported
