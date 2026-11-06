import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_011f1c57bd28401e02c9
import ProverJobs.ResidualE2ESupport20261106.M_dc0b202a876ee2da78b2

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
theorem statopia_math_node_2593933868_24c165f4 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n)
    (U W : Ω → Fin n → ℝ)
    (hU_meas : ∀ k : Fin n, Measurable fun ω => U ω k)
    (hW_meas : ∀ k : Fin n, Measurable fun ω => W ω k)
    (hU_gauss : ∀ a : Fin n → ℝ, ∃ v : NNReal,
      Measure.map (fun ω => ∑ k : Fin n, a k * U ω k) μ = ProbabilityTheory.gaussianReal 0 v)
    (hIndep : ProbabilityTheory.IndepFun U W μ)
    (Phi : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hPhi_meas : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => Phi p.1 p.2)
    (hPhi_bdd : ∃ C : ℝ, ∀ x y : Fin n → ℝ, |Phi x y| ≤ C)
    (hPhi_diff : ∀ y : Fin n → ℝ, ContDiff ℝ 1 fun x : Fin n → ℝ => Phi x y)
    (hPhi_int : ∀ k : Fin n, Integrable (fun ω => U ω k * Phi (U ω) (W ω)) μ)
    (hPhi_deriv_int : ∀ k l : Fin n,
      Integrable (fun ω => deriv (fun s : ℝ => Phi (Function.update (U ω) l s) (W ω)) (U ω l)) μ),
    ∀ k : Fin n, ∫ ω, U ω k * Phi (U ω) (W ω) ∂μ
      = ∑ l : Fin n, (∫ ω, U ω k * U ω l ∂μ)
          * ∫ ω, deriv (fun s : ℝ => Phi (Function.update (U ω) l s) (W ω)) (U ω l) ∂μ := by
  /- @proof-region region.target-node.session.d1ad1c304a698060 begin -/
  intro Ω _instΩ μ _instμ n hn U W hU_meas hW_meas hU_gauss hIndep Phi hPhi_meas hPhi_bdd hPhi_diff hPhi_int hPhi_deriv_int
  intro k
  set Sigma : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => ∫ ω, U ω i * U ω j ∂μ) with hSigma
  have hMemLp : ∀ i : Fin n, MemLp (fun ω => U ω i) 2 μ := by
    intro i
    obtain ⟨v, hv⟩ := hU_gauss (fun k : Fin n => if k = i then (1 : ℝ) else 0)
    have hv' : Measure.map (fun ω => ∑ k, (if k = i then (1 : ℝ) else 0) * U ω k) μ
        = ProbabilityTheory.gaussianReal 0 v := by simpa using hv
    have hfun : (fun ω => ∑ k, (if k = i then (1 : ℝ) else 0) * U ω k) = fun ω => U ω i := by
      funext ω
      have h1 : (fun k : Fin n => (if k = i then (1 : ℝ) else 0) * U ω k)
          = (fun k => if k = i then U ω k else 0) := by
        funext k
        by_cases hk : k = i
        · simp [hk]
        · simp [hk]
      rw [h1]
      simp
    have hmap : Measure.map (fun ω => U ω i) μ = ProbabilityTheory.gaussianReal 0 v := by
      rw [← hfun]
      exact hv'
    have h2 : MemLp id 2 (Measure.map (fun ω => U ω i) μ) := by
      rw [hmap]
      simpa using ProbabilityTheory.memLp_id_gaussianReal (2 : NNReal)
    exact MeasureTheory.MemLp.comp_of_map h2 (hU_meas i).aemeasurable
  have hFrozen : ∀ᵐ y ∂(Measure.map W μ), ∫ x, x k * Phi x y ∂(Measure.map U μ)
      = ∑ l : Fin n, Sigma k l * ∫ x, deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l) ∂(Measure.map U μ) := by
    have hUmeas : Measurable U := measurable_pi_iff.mpr hU_meas
    have hWmeas : Measurable W := measurable_pi_iff.mpr hW_meas
    have hpair : Measure.map (fun ω => (U ω, W ω)) μ
        = (Measure.map U μ).prod (Measure.map W μ) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hUmeas.aemeasurable hWmeas.aemeasurable).mp hIndep
    have hJoint : ∀ l : Fin n, Integrable
        (Function.uncurry (fun x y => deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l)))
        ((Measure.map U μ).prod (Measure.map W μ)) := by
      intro l
      exact (statopia_math_node_3574194610_c2928622 n l Phi hPhi_meas hPhi_diff).2 μ U W hUmeas hWmeas
        (hPhi_deriv_int l l) hpair |>.1
    haveI hprobW : IsProbabilityMeasure (Measure.map W μ) :=
      ⟨by rw [MeasureTheory.Measure.map_apply hWmeas MeasurableSet.univ]; simp⟩
    have hchild := statopia_math_node_187531984_414bbd93 n hn μ U hU_meas hU_gauss
      (Measure.map W μ) Phi hPhi_meas hPhi_bdd hPhi_diff hJoint k
    simpa using hchild
  have hMain : ∫ ω, U ω k * Phi (U ω) (W ω) ∂μ
      = ∫ y, ∫ x, x k * Phi x y ∂(Measure.map U μ) ∂(Measure.map W μ) := by
    have hUmeas : Measurable U := measurable_pi_iff.mpr hU_meas
    have hWmeas : Measurable W := measurable_pi_iff.mpr hW_meas
    have hpair : Measure.map (fun ω => (U ω, W ω)) μ
        = (Measure.map U μ).prod (Measure.map W μ) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hUmeas.aemeasurable hWmeas.aemeasurable).mp hIndep
    have hFmeas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 k * Phi p.1 p.2) :=
      ((measurable_pi_apply k).comp measurable_fst).mul hPhi_meas
    have hpairaem : AEMeasurable (fun ω => (U ω, W ω)) μ :=
      (Measurable.prodMk hUmeas hWmeas).aemeasurable
    have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 k * Phi p.1 p.2)
        ((Measure.map U μ).prod (Measure.map W μ)) := by
      rw [← hpair]
      exact (MeasureTheory.integrable_map_measure hFmeas.aestronglyMeasurable hpairaem).mpr (hPhi_int k)
    have key : ∫ ω, U ω k * Phi (U ω) (W ω) ∂μ
        = ∫ p : (Fin n → ℝ) × (Fin n → ℝ), p.1 k * Phi p.1 p.2
            ∂(Measure.map (fun ω => (U ω, W ω)) μ) :=
      (MeasureTheory.integral_map hpairaem hFmeas.aestronglyMeasurable).symm
    rw [key, hpair]
    exact MeasureTheory.integral_prod_symm
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 k * Phi p.1 p.2) hint
  have hstep1 : ∫ y, ∫ x, x k * Phi x y ∂(Measure.map U μ) ∂(Measure.map W μ)
      = ∑ l : Fin n, Sigma k l * ∫ y, ∫ x, deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l) ∂(Measure.map U μ) ∂(Measure.map W μ) := by
    have hUmeas : Measurable U := measurable_pi_iff.mpr hU_meas
    have hWmeas : Measurable W := measurable_pi_iff.mpr hW_meas
    have hpair : Measure.map (fun ω => (U ω, W ω)) μ
        = (Measure.map U μ).prod (Measure.map W μ) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hUmeas.aemeasurable hWmeas.aemeasurable).mp hIndep
    have hintOf : ∀ l : Fin n, Integrable
        (Function.uncurry (fun x y => deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l)))
        ((Measure.map U μ).prod (Measure.map W μ)) := by
      intro l
      exact (statopia_math_node_3574194610_c2928622 n l Phi hPhi_meas hPhi_diff).2 μ U W hUmeas hWmeas
        (hPhi_deriv_int l l) hpair |>.1
    have hInt : ∀ l : Fin n, Integrable
        (fun y => Sigma k l * ∫ x, deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l) ∂(Measure.map U μ))
        (Measure.map W μ) := by
      intro l
      exact (MeasureTheory.Integrable.integral_prod_right (hintOf l)).const_mul (Sigma k l)
    have hcongr : ∫ y, ∫ x, x k * Phi x y ∂(Measure.map U μ) ∂(Measure.map W μ)
        = ∫ y, ∑ l : Fin n, Sigma k l * ∫ x, deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l) ∂(Measure.map U μ) ∂(Measure.map W μ) :=
      MeasureTheory.integral_congr_ae hFrozen
    rw [hcongr]
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun l _ => hInt l)]
    exact Finset.sum_congr rfl (fun l _ => MeasureTheory.integral_const_mul (Sigma k l) _)
  have hstep2 : ∀ l : Fin n, ∫ y, ∫ x, deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l) ∂(Measure.map U μ) ∂(Measure.map W μ)
      = ∫ ω, deriv (fun s : ℝ => Phi (Function.update (U ω) l s) (W ω)) (U ω l) ∂μ := by
    intro l
    have hUmeas : Measurable U := measurable_pi_iff.mpr hU_meas
    have hWmeas : Measurable W := measurable_pi_iff.mpr hW_meas
    have hpair : Measure.map (fun ω => (U ω, W ω)) μ
        = (Measure.map U μ).prod (Measure.map W μ) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hUmeas.aemeasurable hWmeas.aemeasurable).mp hIndep
    obtain ⟨hint, hAESM⟩ :=
      (statopia_math_node_3574194610_c2928622 n l Phi hPhi_meas hPhi_diff).2 μ U W hUmeas hWmeas (hPhi_deriv_int l l) hpair
    have hAESM' : AEStronglyMeasurable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => deriv (fun s : ℝ => Phi (Function.update p.1 l s) p.2) (p.1 l))
        (Measure.map (fun ω => (U ω, W ω)) μ) := by
      rw [hpair]
      exact hAESM
    have key : ∫ p : (Fin n → ℝ) × (Fin n → ℝ), deriv (fun s : ℝ => Phi (Function.update p.1 l s) p.2) (p.1 l) ∂(Measure.map (fun ω => (U ω, W ω)) μ)
        = ∫ ω, deriv (fun s : ℝ => Phi (Function.update (U ω) l s) (W ω)) (U ω l) ∂μ :=
      MeasureTheory.integral_map (Measurable.prodMk hUmeas hWmeas).aemeasurable hAESM'
    rw [← key, hpair]
    exact (MeasureTheory.integral_prod_symm
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => deriv (fun s : ℝ => Phi (Function.update p.1 l s) p.2) (p.1 l)) hint).symm
  calc ∫ ω, U ω k * Phi (U ω) (W ω) ∂μ
      = ∫ y, ∫ x, x k * Phi x y ∂(Measure.map U μ) ∂(Measure.map W μ) := hMain
    _ = ∑ l : Fin n, Sigma k l * ∫ y, ∫ x, deriv (fun s : ℝ => Phi (Function.update x l s) y) (x l) ∂(Measure.map U μ) ∂(Measure.map W μ) := hstep1
    _ = ∑ l : Fin n, (∫ ω, U ω k * U ω l ∂μ) * ∫ ω, deriv (fun s : ℝ => Phi (Function.update (U ω) l s) (W ω)) (U ω l) ∂μ := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hstep2 l, hSigma]
          rfl
  /- @proof-region region.target-node.session.d1ad1c304a698060 end -/

end Statlib.Imported

