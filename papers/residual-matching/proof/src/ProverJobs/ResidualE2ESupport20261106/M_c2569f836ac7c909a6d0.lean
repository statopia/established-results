import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_8fca21b6c1dec9760fbf
import ProverJobs.ResidualE2ESupport20261106.M_a672c9317c853e441ad0

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

theorem reference_monte_carlo (rhoMin : ℝ) (hrhoMin : 0 < rhoMin) :
(∀ D : ℝ, 0 < D →
        ∃ alpha1 : ℝ, 15 < alpha1 ∧
          ∀ (alpha0 : ℝ), alpha1 ≤ alpha0 → 15 < alpha0 →
            ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ m0 : ℕ,
              ∀ (m n : ℕ) (p : ℝ) (T : ℕ)
                {Ωs : Type*} [MeasurableSpace Ωs] (μΩ : Measure Ωs)
                [IsProbabilityMeasure μΩ]
                (Om : Ωs → Matrix (Fin m) (Fin n) ℝ)
                (μG : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure μG]
                (γ : Fin n → ℝ)
                (hm : m0 ≤ m) (hn : 2 ≤ n) (hnm : n ≤ m)

                (hp0 : 0 < p) (hp1 : p ≤ 1)
                (hrho_lo : rhoMin ≤ rho m n) (hrho_hi : rho m n ≤ 1)
                (hT : 1 ≤ T)
                (hmp : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
                (hγ : ∀ i : Fin n,
                  (∫ x, nuRho (rho m n) x
                      ∂(volume.restrict (Set.Icc (γ i) (lambdaPlus (rho m n)))))
                    = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ))
                (hmask : IsBernoulliMask μΩ Om p)
                (hgauss : IsStdGaussianMatrixLaw μG)
                (hint : ∀ (s : Ωs) (i : Fin n),
                  Integrable (fun G : Matrix (Fin m) (Fin n) ℝ =>
                    sv hnm (maskOp (Om s) ((Real.sqrt (m : ℝ))⁻¹ • G)) i) μG),
                  (μΩ {s : Ωs | ∀ i : Fin n,
                        |lambdaCirc hnm μG (Om s) i - Real.sqrt p * γ i|
                          ≤ C * Real.sqrt p * deltaM m}
                      ≥ ENNReal.ofReal (1 - c * Real.rpow (n : ℝ) (-D))) ∧
                  (∀ (OmF : Matrix (Fin m) (Fin n) ℝ),
                    (∀ i : Fin n,
                      |lambdaCirc hnm μG OmF i - Real.sqrt p * γ i|
                        ≤ C * Real.sqrt p * deltaM m) →
                    (∀ i : Fin n,
                      Integrable (fun G : Matrix (Fin m) (Fin n) ℝ =>
                        sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • G)) i) μG) →
                    (∀ i j, OmF i j = 0 ∨ OmF i j = 1) →
                    ∀ {Ωg : Type*} [MeasurableSpace Ωg] (μg : Measure Ωg)
                      [IsProbabilityMeasure μg]
                      (G : Ωg → Fin T → Matrix (Fin m) (Fin n) ℝ),
                      IsGaussianDrawsLaw μg G →
                        μg {s : Ωg | ∀ i : Fin n,
                            |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|
                              ≤ C * Real.sqrt (Real.log (n : ℝ) / ((m : ℝ) * (T : ℝ)))}
                          ≥ ENNReal.ofReal (1 - c * Real.rpow (n : ℝ) (-D)))) := by
  intro D hD
  refine ⟨16, by norm_num, ?_⟩
  intro alpha0 halpha1le halpha0
  obtain ⟨cR, CR, hcR, hCR, m0R, hRef⟩ := reference_all_alpha D rhoMin hD hrhoMin alpha0 halpha0
  obtain ⟨cM, CM, hcM, hCM, hMC⟩ :=
    statopia_math_node_1891546014_cda991f2 D hD
  refine ⟨max cR cM, CR + CM, lt_of_lt_of_le hcR (le_max_left cR cM), add_pos hCR hCM,
    m0R, ?_⟩
  intro m n p T Ωs _ μΩ _ Om μG _ γ hm hn hnm hp0 hp1 hrho_lo hrho_hi hT hmp hγ hmask
    hgauss hint
  have hx : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-D) := Real.rpow_nonneg (Nat.cast_nonneg n) (-D)
  constructor
  · have hR := hRef m n p μΩ Om μG γ hm hn hnm hp0 hp1 hrho_lo hrho_hi hmp hγ hmask
      hgauss
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans hn hnm
    have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
    have hδ : (0 : ℝ) ≤ deltaM m := by
      unfold deltaM
      exact le_of_lt (inv_pos.mpr hlog)
    refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hR) (measure_mono ?_)
    · have h1 : cR * Real.rpow (n : ℝ) (-D) ≤ max cR cM * Real.rpow (n : ℝ) (-D) :=
        mul_le_mul_of_nonneg_right (le_max_left cR cM) hx
      exact sub_le_sub_left h1 1
    · intro s hs i
      exact le_trans (hs i) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (le_of_lt hCM))
          (Real.sqrt_nonneg p)) hδ)
  · intro OmF hlam hInt hbin Ωg _ μg _ G hdraws
    have hM := hMC m n T hn hnm hT OmF hbin μG hgauss hInt μg G hdraws
    refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hM) (measure_mono ?_)
    · have h1 : cM * Real.rpow (n : ℝ) (-D) ≤ max cR cM * Real.rpow (n : ℝ) (-D) :=
        mul_le_mul_of_nonneg_right (le_max_right cR cM) hx
      exact sub_le_sub_left h1 1
    · intro s hs i
      exact le_trans (hs i) (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (le_of_lt hCR)) (Real.sqrt_nonneg _))

end
end Statlib.Imported


#print axioms ResidualLoss20261106.Statlib.Imported.reference_monte_carlo

