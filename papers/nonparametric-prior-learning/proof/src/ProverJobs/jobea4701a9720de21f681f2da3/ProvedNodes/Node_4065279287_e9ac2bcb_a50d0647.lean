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
theorem statopia_math_node_4065279287_e9ac2bcb : ∀ {X Y U Θ V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
    [TopologicalSpace.SeparableSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V] [MeasurableSpace V] [BorelSpace V]
    (M : Model X Y U Θ V)
    (hloss : Measurable (Function.uncurry M.ℓ))
    (n : ℕ) (hn : 0 < n)
    (ω : Fin n → Block (X × Y))
    (hPost_meas : ∀ k : ℕ, Measurable fun q : (Fin k → X × Y) × Θ => basePost M k q.1 q.2)
    (hLoss_int : ∀ (u : U) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun z : X × Y => M.ℓ u z) (D : Measure (X × Y)))
    (hLemp_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ),
      Integrable (fun u : U => Lemp M.ℓ u S) (basePost M k S θ : Measure U)),
    Measurable (fun θ : Θ => (1 / (n : ℝ)) * ∑ i : Fin n,
      LgibbsEmp M.ℓ (basePost M (mOf ω i : ℕ) (SOF ω i) θ : Measure U) (SOF ω i)) := by
  /- @proof-region region.target-node.session.1a36540f01b354b1 begin -/
  intro X Y U Θ V
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro M hloss n hn ω hPost_meas hLoss_int hLemp_int
  have hInt_meas : ∀ i : Fin n, Measurable (fun θ : Θ => LgibbsEmp M.ℓ (basePost M (mOf ω i : ℕ) (SOF ω i) θ : Measure U) (SOF ω i)) := by
    intro i
    have hLemp_meas : Measurable fun u : U => Lemp M.ℓ u (SOF ω i) := by
      have hterm : ∀ j : Fin (mOf ω i : ℕ), Measurable fun u : U => M.ℓ u (SOF ω i j) := by
        intro j
        exact hloss.comp (measurable_id.prodMk measurable_const)
      have hsum : Measurable fun u : U => ∑ j : Fin (mOf ω i : ℕ), M.ℓ u (SOF ω i j) :=
        Finset.measurable_sum Finset.univ (fun j _ => hterm j)
      simpa only [Lemp] using measurable_const.mul hsum
    have hκ_meas : Measurable fun θ : Θ => (basePost M (mOf ω i : ℕ) (SOF ω i) θ : Measure U) := by
      have h1 : Measurable fun θ : Θ => (basePost M (mOf ω i : ℕ) (SOF ω i) θ : ProbabilityMeasure U) :=
        (hPost_meas (mOf ω i : ℕ)).comp (measurable_const.prodMk measurable_id)
      exact measurable_subtype_coe.comp h1
    let κ : Kernel Θ U := ⟨fun θ => (basePost M (mOf ω i : ℕ) (SOF ω i) θ : Measure U), hκ_meas⟩
    have hpos : Measurable fun θ : Θ => ∫⁻ u, ENNReal.ofReal (Lemp M.ℓ u (SOF ω i)) ∂κ θ :=
      Measurable.lintegral_kernel (f := fun u => ENNReal.ofReal (Lemp M.ℓ u (SOF ω i))) hLemp_meas.ennreal_ofReal
    have hneg : Measurable fun θ : Θ => ∫⁻ u, ENNReal.ofReal (-(Lemp M.ℓ u (SOF ω i))) ∂κ θ :=
      Measurable.lintegral_kernel (f := fun u => ENNReal.ofReal (-(Lemp M.ℓ u (SOF ω i)))) hLemp_meas.neg.ennreal_ofReal
    have hsub : Measurable fun θ : Θ =>
        (∫⁻ u, ENNReal.ofReal (Lemp M.ℓ u (SOF ω i)) ∂κ θ).toReal -
        (∫⁻ u, ENNReal.ofReal (-(Lemp M.ℓ u (SOF ω i))) ∂κ θ).toReal :=
      hpos.ennreal_toReal.sub hneg.ennreal_toReal
    have hEq : (fun θ : Θ => LgibbsEmp M.ℓ (basePost M (mOf ω i : ℕ) (SOF ω i) θ : Measure U) (SOF ω i)) =
        (fun θ : Θ =>
          (∫⁻ u, ENNReal.ofReal (Lemp M.ℓ u (SOF ω i)) ∂κ θ).toReal -
          (∫⁻ u, ENNReal.ofReal (-(Lemp M.ℓ u (SOF ω i))) ∂κ θ).toReal) := by
      funext θ
      simp only [LgibbsEmp]
      exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hLemp_int (mOf ω i : ℕ) (SOF ω i) θ)
    rw [hEq]
    exact hsub
  exact measurable_const.mul (Finset.measurable_sum Finset.univ (fun i _ => hInt_meas i))
  /- @proof-region region.target-node.session.1a36540f01b354b1 end -/

end
end Statlib.Imported
