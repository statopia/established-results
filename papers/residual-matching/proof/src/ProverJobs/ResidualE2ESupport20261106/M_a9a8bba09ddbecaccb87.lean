import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_8d431690763c512aee9c

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1043732631_ea2639e2 : ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
    let ν : MeasureTheory.Measure (ι → ℝ) :=
      MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)
    (∀ k : ι, MeasureTheory.Integrable (fun g : ι → ℝ => g k) ν) ∧
    (∀ k : ι, ∫ g : ι → ℝ, g k ∂ν = 0) ∧
    (∀ k l : ι, MeasureTheory.Integrable (fun g : ι → ℝ => g k * g l) ν) ∧
    (∀ k l : ι, ∫ g : ι → ℝ, g k * g l ∂ν = if k = l then (1 : ℝ) else 0) ∧
    (∀ k : ι, ∫ g : ι → ℝ, (g k) ^ 2 ∂ν = 1) ∧
    MeasureTheory.IsProbabilityMeasure ν := by
  /- @proof-region region.target-node.session.9697179ed60100f0 begin -/
  intro ι _ _
  dsimp only
  have hmap : ∀ k : ι, Measure.map (fun g : ι → ℝ => g k)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) = gaussianReal 0 1 := by
    intro k
    have h := Measure.pi_map_eval (μ := fun _ : ι => gaussianReal 0 1) k
    simpa using h
  have hprob : IsProbabilityMeasure (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    Measure.pi.instIsProbabilityMeasure _
  have hsqint : ∀ k : ι, Integrable (fun g : ι → ℝ => (g k) ^ 2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    intro k
    have hmem : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 1) := by
      simpa using Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
        (μ₀ := (0 : ℝ)) (v := (1 : NNReal)) 1 2 (by simp)
    have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := hmem.integrable_sq
    have hφ : AEMeasurable (fun g : ι → ℝ => g k)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) := (measurable_pi_apply k).aemeasurable
    have h : Integrable (fun x : ℝ => x ^ 2) (Measure.map (fun g : ι → ℝ => g k)
        (Measure.pi (fun _ : ι => gaussianReal 0 1))) := by
      rw [hmap k]
      exact hsq
    simpa using MeasureTheory.Integrable.comp_aemeasurable h hφ
  have hmean : ∀ k : ι, ∫ g : ι → ℝ, g k ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
    intro k
    have hφ : AEMeasurable (fun g : ι → ℝ => g k) (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
      exact (measurable_pi_apply k).aemeasurable
    have hid0 : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := IsGaussian.integrable_fun_id
    have hsm : AEStronglyMeasurable (fun x : ℝ => x)
        (Measure.map (fun g : ι → ℝ => g k) (Measure.pi (fun _ : ι => gaussianReal 0 1))) := by
      rw [hmap k]
      exact hid0.aestronglyMeasurable
    have key : ∫ y : ℝ, y ∂(Measure.map (fun g : ι → ℝ => g k)
          (Measure.pi (fun _ : ι => gaussianReal 0 1)))
        = ∫ g : ι → ℝ, g k ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
      simpa using MeasureTheory.integral_map (μ := Measure.pi (fun _ : ι => gaussianReal 0 1))
        (φ := fun g : ι → ℝ => g k) hφ (f := fun x : ℝ => x) hsm
    rw [hmap k] at key
    have hzero : ∫ y : ℝ, y ∂(gaussianReal (0 : ℝ) 1) = 0 := by
      simpa using ProbabilityTheory.integral_linearMap_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
        (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
    rw [hzero] at key
    exact key.symm
  have hmom2 : ∀ k : ι, ∫ g : ι → ℝ, (g k) ^ 2 ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) = 1 := by
    intro k
    have hφ : AEMeasurable (fun g : ι → ℝ => g k) (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
      (measurable_pi_apply k).aemeasurable
    have hmem : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 1) := by
      simpa using Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
        (μ₀ := (0 : ℝ)) (v := (1 : NNReal)) 1 2 (by simp)
    have hsm : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        (Measure.map (fun g : ι → ℝ => g k) (Measure.pi (fun _ : ι => gaussianReal 0 1))) := by
      rw [hmap k]
      exact hmem.integrable_sq.aestronglyMeasurable
    have key : ∫ y : ℝ, y ^ 2 ∂(Measure.map (fun g : ι → ℝ => g k)
          (Measure.pi (fun _ : ι => gaussianReal 0 1)))
        = ∫ g : ι → ℝ, (g k) ^ 2 ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
      simpa using MeasureTheory.integral_map (μ := Measure.pi (fun _ : ι => gaussianReal 0 1))
        (φ := fun g : ι → ℝ => g k) hφ (f := fun x : ℝ => x ^ 2) hsm
    rw [hmap k] at key
    exact key.symm.trans statopia_math_node_2245285305_8fe98c79
  refine ⟨?_, ?_, ?_, ?_, ?_, hprob⟩
  · intro k
    have hφ : AEMeasurable (fun g : ι → ℝ => g k) (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
      (measurable_pi_apply k).aemeasurable
    have hid : Integrable (fun x : ℝ => x) (Measure.map (fun g : ι → ℝ => g k)
        (Measure.pi (fun _ : ι => gaussianReal 0 1))) := by
      rw [hmap k]
      exact IsGaussian.integrable_fun_id
    simpa using MeasureTheory.Integrable.comp_aemeasurable hid hφ
  · intro k
    exact hmean k
  · intro k l
    have hsum : Integrable (fun g : ι → ℝ => g k ^ 2 + g l ^ 2)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) := (hsqint k).add (hsqint l)
    refine MeasureTheory.integrable_of_le_of_le ?_ ?_ ?_ hsum.neg hsum
    · exact ((measurable_pi_apply k).mul (measurable_pi_apply l)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun g => by
        show -(g k ^ 2 + g l ^ 2) ≤ g k * g l
        nlinarith [sq_nonneg (g k + g l), sq_nonneg (g k), sq_nonneg (g l)])
    · exact Filter.Eventually.of_forall (fun g => by
        show g k * g l ≤ g k ^ 2 + g l ^ 2
        nlinarith [sq_nonneg (g k - g l), sq_nonneg (g k), sq_nonneg (g l)])
  · intro k l
    by_cases hkl : k = l
    · rw [hkl]
      simpa [pow_two] using hmom2 l
    · have hX : ∀ i : ι, Measurable (fun x : ℝ => if i = l then -x else x) := by
        intro i
        by_cases hi : i = l
        · subst hi
          simpa using measurable_neg
        · simpa [hi] using measurable_id
      have hindep : iIndepFun (fun (i : ι) (g : ι → ℝ) => g i)
          (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
        have h := ProbabilityTheory.iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1)
          (X := fun _ (x : ℝ) => x) (fun _ => measurable_id.aemeasurable)
        simpa using h
      have hpair : (fun g : ι → ℝ => g k) ⟂ᵢ[Measure.pi (fun _ : ι => gaussianReal 0 1)]
          (fun g : ι → ℝ => g l) := by
        have h2 := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul).1 hindep
          ({k, l} : Finset ι)
          (sets := fun i => if i = k then (Set.univ : Set ℝ) else Set.univ)
          (by intro i _; by_cases hik : i = k <;> simp [hik])
        have h3 := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul).1 hindep
          ({k, l} : Finset ι)
          (sets := fun i => Set.univ)
          (by intro i _; exact MeasurableSet.univ)
        rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
        intro s t hs ht
        have h4 := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul).1 hindep
          ({k, l} : Finset ι)
          (sets := fun i => if i = k then s else if i = l then t else Set.univ)
          (by
            intro i _
            by_cases hik : i = k
            · subst hik; simpa using hs
            · by_cases hil : i = l
              · subst hil; simpa [hik] using ht
              · simp [hik, hil])
        have h5 := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul).1 hindep
          ({k, l} : Finset ι)
          (sets := fun i => if i = k then s else if i = l then t else Set.univ)
          (by
            intro i _
            by_cases hik : i = k
            · subst hik; simpa using hs
            · by_cases hil : i = l
              · subst hil; simpa [hik] using ht
              · simp [hik, hil])
        simpa [hkl, Ne.symm hkl] using h4
      have hfac := ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hpair
        (((measurable_pi_apply k)).aestronglyMeasurable)
        (((measurable_pi_apply l)).aestronglyMeasurable)
      rw [hmean k, hmean l, mul_zero] at hfac
      rw [if_neg hkl]
      exact hfac
  · intro k
    exact hmom2 k
  /- @proof-region region.target-node.session.9697179ed60100f0 end -/

end Statlib.Imported

