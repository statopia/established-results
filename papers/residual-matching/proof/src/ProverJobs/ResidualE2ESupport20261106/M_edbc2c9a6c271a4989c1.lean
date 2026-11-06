import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_35fba7b58e1fa3f7fe12

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
theorem statopia_math_node_930997348_7feb7b3b : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (p Kt : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) (hKt : 0 < Kt)
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hXi_mean : ∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0)
    (hXi_var : ∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hXi_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
      μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
    (let e1 : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
     let e2 : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
     let F : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin m) (Fin n) ℝ :=
       fun k x i j => if (i, j) = e2.symm k then maskedScaled p (Xi x.1) (Mask x.1) i j else 0
     let Z : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) →
         Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
       fun k x u v =>
         ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (F k x)
             (Matrix.transpose (F k x)) (0 : Matrix (Fin n) (Fin n) ℝ)).map
           Complex.ofReal) (e1.symm u) (e1.symm v)
     let G : (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
       fun x u v =>
         ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
             (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ)))
             (Matrix.transpose (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ))))
             (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) (e1.symm u) (e1.symm v)
     iIndepFun (fun (k : Fin (m * n)) (x : Ω × (Fin m → Fin n → ℝ)) => Z k x)
         (μ.prod (stdNormalMatrixMeasure m n)) ∧
       IndepFun (fun (x : Ω × (Fin m → Fin n → ℝ)) (k : Fin (m * n)) => Z k x)
         (fun x => G x) (μ.prod (stdNormalMatrixMeasure m n))) := by
  /- @proof-region region.target-node.session.ea479616a8733765 begin -/
  intro Ω _ μ _ m n hm hn p Kt hp_pos hp_le hKt Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep
    hXi_mean hXi_var hXi_tail hMask_meas hMask_val hMask_law hMask_indep hIndep
  let e1 : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  let e2 : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  let F : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin m) (Fin n) ℝ :=
    fun k x i j => if (i, j) = e2.symm k then maskedScaled p (Xi x.1) (Mask x.1) i j else 0
  let Z : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) →
      Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun k x u v =>
      ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (F k x)
          (Matrix.transpose (F k x)) (0 : Matrix (Fin n) (Fin n) ℝ)).map
        Complex.ofReal) (e1.symm u) (e1.symm v)
  let G : (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun x u v =>
      ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
          (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ)))
          (Matrix.transpose (Matrix.of fun i j => x.2 i j / Real.sqrt ((m : ℝ))))
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) (e1.symm u) (e1.symm v)
  let ν : Measure (Fin m → Fin n → ℝ) := stdNormalMatrixMeasure m n
  let μ' : Measure (Ω × (Fin m → Fin n → ℝ)) := μ.prod ν
  change iIndepFun (fun (k : Fin (m * n)) (x : Ω × (Fin m → Fin n → ℝ)) => Z k x) μ' ∧
    IndepFun (fun (x : Ω × (Fin m → Fin n → ℝ)) (k : Fin (m * n)) => Z k x) (fun x => G x) μ'
  refine ⟨?_, ?_⟩
  · exact statopia_math_node_2677770135_08a2ad00 μ m n hm p hp_pos Xi Mask
      hXi_meas hMask_meas hXi_indep hMask_indep hIndep
  · let x0 : Fin m → Fin n → ℝ := fun _ _ => 0
    let Ψ : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun M u v =>
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) M (Matrix.transpose M)
            (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal) (e1.symm u) (e1.symm v)
    let X : Ω → (Fin (m * n) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ) :=
      fun y k => Ψ (F k (y, x0))
    let Y : (Fin m → Fin n → ℝ) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun w => Ψ (fun i j => w i j / Real.sqrt ((m : ℝ)))
    have hXeq : (fun (x : Ω × (Fin m → Fin n → ℝ)) (k : Fin (m * n)) => Z k x)
        = fun x => X x.1 := rfl
    have hYeq : (fun x : Ω × (Fin m → Fin n → ℝ) => G x) = fun x => Y x.2 := rfl
    rw [hXeq, hYeq]
    haveI hν : IsProbabilityMeasure ν := by
      change IsProbabilityMeasure
        (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
      infer_instance
    have hΨ : Measurable Ψ := by
      rw [measurable_pi_iff]
      intro u
      rw [measurable_pi_iff]
      intro v
      dsimp only [Ψ]
      rcases e1.symm u with a | a <;> rcases e1.symm v with b | b <;>
        simp only [Matrix.map_apply, Matrix.fromBlocks, Matrix.of_apply,
          Matrix.transpose_apply, Sum.elim_inl, Sum.elim_inr] <;>
        measurability
    have hXm : Measurable X := by
      rw [measurable_pi_iff]
      intro k
      have hFk : Measurable (fun y => F k (y, x0)) := by
        rw [measurable_pi_iff]
        intro i
        rw [measurable_pi_iff]
        intro j
        dsimp only [F, maskedScaled]
        by_cases hc : (i, j) = e2.symm k
        · simp only [if_pos hc]
          have hXt : Measurable fun y => Xi y i j := hXi_meas i j
          have hMt : Measurable fun y => Mask y i j := hMask_meas i j
          measurability
        · simp only [if_neg hc]
          measurability
      exact hΨ.comp hFk
    have hYm : Measurable Y := by
      have hscaled : Measurable
          (fun w : (Fin m → Fin n → ℝ) => fun i j => w i j / Real.sqrt ((m : ℝ))) := by
        rw [measurable_pi_iff]
        intro i
        rw [measurable_pi_iff]
        intro j
        measurability
      exact hΨ.comp hscaled
    exact indepFun_prod hXm hYm
  /- @proof-region region.target-node.session.ea479616a8733765 end -/

end Statlib.Imported

