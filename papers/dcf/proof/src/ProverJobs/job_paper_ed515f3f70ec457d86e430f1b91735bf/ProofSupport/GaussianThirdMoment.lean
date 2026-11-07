import Statlib.StatFoundation.Convergence.AnalysisTools.CharacteristicFunction
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_even_moment_le
import Lean
import Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_even_moment_le
import Statlib.StatFoundation.Convergence.AnalysisTools.CharacteristicFunction
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace DCFGaussianThirdReview
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `DCFGaussianThirdReview then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.DCFGaussianThirdReview))

lemma abs_third_le_eight_of_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y W : Ω → ℝ) (hY : Measurable Y) (hW : Measurable W)
    (hYmean : ∫ ω, Y ω ∂P = 0) (hY3 : Integrable (fun ω => |Y ω| ^ 3) P)
    (hsg : HasSubgaussianMGF W ⟨∫ ω, Y ω ^ 2 ∂P, integral_nonneg (fun _ => sq_nonneg _)⟩ P) :
    ∫ ω, |W ω| ^ 3 ∂P ≤ 8 * ∫ ω, |Y ω| ^ 3 ∂P := by
  let V : ℝ := ∫ ω, Y ω ^ 2 ∂P
  have hV : 0 ≤ V := integral_nonneg (fun _ => sq_nonneg _)
  have hY3Lp : MemLp Y 3 P := by
    apply (integrable_norm_rpow_iff hY.aestronglyMeasurable (by norm_num : (3 : ENNReal) ≠ 0)
      (by norm_num : (3 : ENNReal) ≠ ⊤)).mp
    simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_ofNat] using hY3
  by_cases hzero : V = 0
  · have hsg0 : HasSubgaussianMGF W 0 P := by
      have hz : (⟨∫ ω, Y ω ^ 2 ∂P, integral_nonneg (fun _ => sq_nonneg _)⟩ : NNReal) = 0 := by
        ext; exact hzero
      exact hz ▸ hsg
    have hae := hsg0.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hi : (∫ ω, |W ω| ^ 3 ∂P) = 0 := by
      calc
        (∫ ω, |W ω| ^ 3 ∂P) = ∫ _, (0 : ℝ) ∂P := integral_congr_ae (hae.mono (fun ω h => by simp [h]))
        _ = 0 := by simp
    rw [hi]
    exact mul_nonneg (by norm_num) (integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) 3))
  · have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hzero)
    let σ := Real.sqrt V
    have hσ : 0 < σ := Real.sqrt_pos.mpr hVp
    have hσ2 : σ ^ 2 = V := Real.sq_sqrt hV
    have h2 := Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_even_moment_le
      P W hW σ hσ ⟨V, hV⟩ hσ2.symm hsg 1 (by norm_num)
    have h4 := Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_even_moment_le
      P W hW σ hσ ⟨V, hV⟩ hσ2.symm hsg 2 (by norm_num)
    norm_num at h2 h4
    have hWi2 : Integrable (fun ω => W ω ^ 2) P := (hsg.memLp 2).integrable_sq
    have hWi4 : Integrable (fun ω => W ω ^ 4) P := by
      exact ProbabilityTheory.integrable_pow_of_integrable_exp_mul one_ne_zero
        (hsg.integrable_exp_mul 1) (by simpa using hsg.integrable_exp_mul (-1)) 4
    have hWi3 : Integrable (fun ω => |W ω| ^ 3) P := by
      simpa only [Real.norm_eq_abs] using (hsg.memLp 3).integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
    have hpt : ∀ ω, 4 * σ * |W ω| ^ 3 ≤ W ω ^ 4 + 4 * σ ^ 2 * W ω ^ 2 := by
      intro ω
      have hs := sq_nonneg (|W ω| ^ 2 - 2 * σ * |W ω|)
      have ha2 : |W ω| ^ 2 = W ω ^ 2 := sq_abs _
      have ha4 : |W ω| ^ 4 = W ω ^ 4 := by
        calc
          |W ω| ^ 4 = (|W ω| ^ 2) ^ 2 := by ring
          _ = (W ω ^ 2) ^ 2 := by rw [sq_abs]
          _ = W ω ^ 4 := by ring
      nlinarith
    have hi := integral_mono (hWi3.const_mul (4 * σ)) (hWi4.add (hWi2.const_mul (4 * σ ^ 2))) hpt
    change (∫ ω, 4 * σ * |W ω| ^ 3 ∂P) ≤ ∫ ω, W ω ^ 4 + 4 * σ ^ 2 * W ω ^ 2 ∂P at hi
    rw [integral_const_mul, integral_add hWi4 (hWi2.const_mul (4 * σ ^ 2)), integral_const_mul] at hi
    have hthirdW : (∫ ω, |W ω| ^ 3 ∂P) ≤ 8 * σ ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 4 * σ ^ 2)
      have hfactor : 0 ≤ 4 * σ * (8 * σ ^ 3 - ∫ ω, |W ω| ^ 3 ∂P) := by nlinarith [h4]
      exact le_of_sub_nonneg ((mul_nonneg_iff_of_pos_left (by positivity : 0 < 4 * σ)).mp hfactor)
    have hthirdY : σ ^ 3 ≤ ∫ ω, |Y ω| ^ 3 ∂P :=
      Statlib.StatFoundation.Convergence.BerryEsseen.lyapunov_third_moment hσ hY hYmean
        hσ2.symm rfl hY3Lp
    exact hthirdW.trans (mul_le_mul_of_nonneg_left hthirdY (by norm_num))

open Statlib.StatFoundation.RandomVariable.Gaussian
lemma gaussian_coordinate_third_le_eight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℕ} (W : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hW : IsCenteredGaussianVector P W Sigma)
    (j : Fin p) (Y : Ω → ℝ) (hY : Measurable Y)
    (hYmean : ∫ ω, Y ω ∂P = 0) (hY3 : Integrable (fun ω => |Y ω| ^ 3) P)
    (hvar : Sigma j j = ∫ ω, Y ω ^ 2 ∂P) :
    ∫ ω, |W ω j| ^ 3 ∂P ≤ 8 * ∫ ω, |Y ω| ^ 3 ∂P := by
  have hexp : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * W ω j)) P := by
    intro t
    simpa [Pi.single_apply] using hW.integrable_exp (Pi.single j t)
  have hmgf : ∀ t : ℝ, (∫ ω, Real.exp (t * W ω j) ∂P) =
      Real.exp ((∫ ω, Y ω ^ 2 ∂P) * t ^ 2 / 2) := by
    intro t
    have h := hW.mgf_eq (Pi.single j t)
    simpa [Pi.single_apply, hvar, mul_pow, mul_assoc, mul_comm, mul_left_comm, pow_two] using h
  have hsg : HasSubgaussianMGF (fun ω => W ω j)
      ⟨∫ ω, Y ω ^ 2 ∂P, integral_nonneg (fun _ => sq_nonneg _)⟩ P :=
    ⟨hexp, fun t => by simpa only [mgf, NNReal.coe_mk] using (hmgf t).le⟩
  exact abs_third_le_eight_of_subgaussian P Y (fun ω => W ω j) hY
    ((measurable_pi_apply j).comp hW.measurable) hYmean hY3 hsg

lemma gaussian_coordinate_centered_third_le_eight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℕ} (W : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hW : IsCenteredGaussianVector P W Sigma)
    (j : Fin p) (Y : Ω → ℝ) (μ : ℝ) (hY : Measurable Y) (hY2 : MemLp Y 2 P)
    (hYmean : ∫ ω, Y ω ∂P = μ)
    (hY3 : Integrable (fun ω => |Y ω - μ| ^ 3) P)
    (hvar : Sigma j j = ∫ ω, (Y ω - μ) ^ 2 ∂P) :
    ∫ ω, |W ω j| ^ 3 ∂P ≤ 8 * ∫ ω, |Y ω - μ| ^ 3 ∂P := by
  have hYi : Integrable Y P := memLp_one_iff_integrable.mp
    (hY2.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2))
  have hm : (∫ ω, Y ω - μ ∂P) = 0 := by
    rw [integral_sub hYi (integrable_const μ), hYmean]
    simp
  exact gaussian_coordinate_third_le_eight P W Sigma hW j (fun ω => Y ω - μ)
    (hY.sub measurable_const) hm hY3 hvar

end DCFGaussianThirdReview

