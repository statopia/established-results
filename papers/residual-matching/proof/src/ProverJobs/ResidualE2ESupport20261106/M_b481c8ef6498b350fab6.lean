import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_1096857301_d7b64af8 : ∀ (m n : ℕ) (i i' : Fin m) (j j' : Fin n),
    (Integrable (fun z : Fin m → Fin n → ℝ => z i j * z i' j')
        (stdNormalMatrixMeasure m n)) ∧
      (∫ z : Fin m → Fin n → ℝ, z i j * z i' j' ∂(stdNormalMatrixMeasure m n)
        = if (i, j) = (i', j') then (1 : ℝ) else 0) := by
  /- @proof-region region.target-node.session.9190a91582f41851 begin -/
  intro m n i i' j j'
  let ρ : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let M : Measure (Fin n → ℝ) := MeasureTheory.Measure.pi (fun _ : Fin n => ρ)
  let ν : Measure (Fin m → Fin n → ℝ) := MeasureTheory.Measure.pi (fun _ : Fin m => M)
  change (Integrable (fun z : Fin m → Fin n → ℝ => z i j * z i' j') ν) ∧
      (∫ z : Fin m → Fin n → ℝ, z i j * z i' j' ∂ν
        = if (i, j) = (i', j') then (1 : ℝ) else 0)
  have hmpOut : ∀ a : Fin m, MeasurePreserving (Function.eval a) ν M :=
    fun a => measurePreserving_eval (fun _ : Fin m => M) a
  have hmpIn : ∀ b : Fin n, MeasurePreserving (Function.eval b) M ρ :=
    fun b => measurePreserving_eval (fun _ : Fin n => ρ) b
  have hmp : ∀ (a : Fin m) (b : Fin n),
      MeasurePreserving (fun z : Fin m → Fin n → ℝ => z a b) ν ρ := by
    intro a b
    exact (hmpIn b).comp (hmpOut a)
  have hSecond : ∫ x : ℝ, x ^ 2 ∂ρ = 1 := by
    have hvar := ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x) (μ := ρ)
      (measurable_id.aemeasurable)
    have hmean : ∫ x : ℝ, x ∂ρ = 0 := by
      simpa [ρ] using ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
    have hVarVal : ProbabilityTheory.variance (fun x : ℝ => x) ρ = 1 := by
      have h := ProbabilityTheory.variance_fun_id_gaussianReal (μ := 0) (v := 1)
      simpa [ρ] using h
    rw [hVarVal] at hvar
    simp only [hmean, sub_zero] at hvar
    exact hvar.symm
  have hIntSq : Integrable (fun x : ℝ => x ^ 2) ρ := by
    have h : MemLp (fun x : ℝ => x ^ 2) 1 ρ :=
      Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal (μ₀ := 0) (v := 1) 2 1 (by simp)
    exact MemLp.integrable (le_refl (1 : ENNReal)) h
  have hSq : ∀ (a : Fin m) (b : Fin n), Integrable (fun z : Fin m → Fin n → ℝ => (z a b) ^ 2) ν := by
    intro a b
    have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ρ :=
      (continuous_id.pow 2).aestronglyMeasurable
    have := ((hmp a b).integrable_comp hmeas).mpr hIntSq
    simpa only [Function.comp_apply] using this
  have hZero : ∀ (a : Fin m) (b : Fin n), ∫ z : Fin m → Fin n → ℝ, z a b ∂ν = 0 := by
    intro a b
    have hfm : AEMeasurable (fun z : Fin m → Fin n → ℝ => z a b) ν :=
      (hmp a b).measurable.aemeasurable
    have hmeas : AEStronglyMeasurable (fun x : ℝ => x) ρ := measurable_id.aestronglyMeasurable
    have hmeas' : AEStronglyMeasurable (fun x : ℝ => x)
        (Measure.map (fun z : Fin m → Fin n → ℝ => z a b) ν) := by
      rw [(hmp a b).map_eq]; exact hmeas
    have him := MeasureTheory.integral_map hfm hmeas'
    rw [(hmp a b).map_eq] at him
    rw [← him]
    simpa [ρ] using ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
  have hInt : Integrable (fun z : Fin m → Fin n → ℝ => z i j * z i' j') ν := by
    have hsum : Integrable (fun z : Fin m → Fin n → ℝ => (z i j) ^ 2 + (z i' j') ^ 2) ν :=
      (hSq i j).add (hSq i' j')
    have hfm : AEStronglyMeasurable (fun z : Fin m → Fin n → ℝ => z i j * z i' j') ν :=
      (((hmp i j).measurable).mul ((hmp i' j').measurable)).aestronglyMeasurable
    refine hsum.mono' hfm ?_
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (z i j), sq_abs (z i' j'), sq_nonneg (|z i j| - |z i' j'|)]
  refine ⟨hInt, ?_⟩
  by_cases hcase : (i, j) = (i', j')
  · have hii := (Prod.mk.injEq i j i' j').mp hcase
    obtain ⟨rfl, rfl⟩ := hii
    rw [if_pos rfl]
    have hsqfun : (fun z : Fin m → Fin n → ℝ => z i j * z i j) = (fun z => (z i j) ^ 2) := by
      funext z; ring
    rw [hsqfun]
    have hfm : AEMeasurable (fun z : Fin m → Fin n → ℝ => z i j) ν :=
      (hmp i j).measurable.aemeasurable
    have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ρ :=
      (continuous_id.pow 2).aestronglyMeasurable
    have hmeas' : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        (Measure.map (fun z : Fin m → Fin n → ℝ => z i j) ν) := by
      rw [(hmp i j).map_eq]; exact hmeas
    have him := MeasureTheory.integral_map hfm hmeas'
    rw [(hmp i j).map_eq] at him
    rw [← him]
    exact hSecond
  · rw [if_neg hcase]
    have hZeroM : ∀ b : Fin n, ∫ y : Fin n → ℝ, y b ∂M = 0 := by
      intro b
      have hfm : AEMeasurable (Function.eval b) M := (hmpIn b).measurable.aemeasurable
      have hmeas : AEStronglyMeasurable (fun x : ℝ => x) (Measure.map (Function.eval b) M) := by
        rw [(hmpIn b).map_eq]; exact measurable_id.aestronglyMeasurable
      have him := MeasureTheory.integral_map hfm hmeas
      rw [(hmpIn b).map_eq] at him
      rw [← him]
      simpa [ρ] using ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
    by_cases hii : i = i'
    · rw [hii]
      have hjj : j ≠ j' := by
        intro h; exact hcase (by rw [hii, h])
      have hmapI : Measure.map (fun z : Fin m → Fin n → ℝ => z i') ν = M := (hmpOut i').map_eq
      have hfm : AEMeasurable (fun z : Fin m → Fin n → ℝ => z i') ν := (hmpOut i').measurable.aemeasurable
      have hmeas : AEStronglyMeasurable (fun y : Fin n → ℝ => y j * y j')
          (Measure.map (fun z : Fin m → Fin n → ℝ => z i') ν) := by
        rw [hmapI]
        exact (((hmpIn j).measurable).mul ((hmpIn j').measurable)).aestronglyMeasurable
      have him := MeasureTheory.integral_map hfm hmeas
      rw [hmapI] at him
      rw [← him]
      have hIn : iIndepFun (fun (k : Fin n) (y : Fin n → ℝ) => y k) M := by
        have h := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin n => ρ)
          (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
        simpa using h
      have hIndep : IndepFun (fun y : Fin n → ℝ => y j) (fun y => y j') M := hIn.indepFun hjj
      have hprod := ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hIndep
        (hmpIn j).measurable.aestronglyMeasurable (hmpIn j').measurable.aestronglyMeasurable
      have hprod' : ∫ y : Fin n → ℝ, y j * y j' ∂M
          = (∫ y : Fin n → ℝ, y j ∂M) * (∫ y : Fin n → ℝ, y j' ∂M) := by simpa using hprod
      rw [hprod', hZeroM j, hZeroM j']
      simp
    · have hOut : iIndepFun (fun (k : Fin m) (z : Fin m → Fin n → ℝ) => z k) ν := by
        have h := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin m => M)
          (X := fun _ : Fin m => (id : (Fin n → ℝ) → (Fin n → ℝ))) (fun _ => measurable_id.aemeasurable)
        simpa using h
      have hIndep : IndepFun (fun z : Fin m → Fin n → ℝ => z i) (fun z => z i') ν := hOut.indepFun hii
      have hmapI : Measure.map (fun z : Fin m → Fin n → ℝ => z i) ν = M := (hmpOut i).map_eq
      have hmapI' : Measure.map (fun z : Fin m → Fin n → ℝ => z i') ν = M := (hmpOut i').map_eq
      have hX : AEMeasurable (fun z : Fin m → Fin n → ℝ => z i) ν := (hmpOut i).measurable.aemeasurable
      have hY : AEMeasurable (fun z : Fin m → Fin n → ℝ => z i') ν := (hmpOut i').measurable.aemeasurable
      have hf : AEStronglyMeasurable (fun y : Fin n → ℝ => y j)
          (Measure.map (fun z : Fin m → Fin n → ℝ => z i) ν) := by
        rw [hmapI]; exact (hmpIn j).measurable.aestronglyMeasurable
      have hg : AEStronglyMeasurable (fun y : Fin n → ℝ => y j')
          (Measure.map (fun z : Fin m → Fin n → ℝ => z i') ν) := by
        rw [hmapI']; exact (hmpIn j').measurable.aestronglyMeasurable
      have hprod := ProbabilityTheory.IndepFun.integral_fun_comp_mul_comp hIndep hX hY hf hg
      have hprod' : ∫ z : Fin m → Fin n → ℝ, z i j * z i' j' ∂ν
          = (∫ z : Fin m → Fin n → ℝ, z i j ∂ν) * (∫ z : Fin m → Fin n → ℝ, z i' j' ∂ν) := by
        simpa using hprod
      rw [hprod', hZero i j, hZero i' j']
      simp
  /- @proof-region region.target-node.session.9190a91582f41851 end -/

end Statlib.Imported

