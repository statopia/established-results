import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_a4ce435c878395fb1023
import ProverJobs.ResidualE2EAssembly20261106.M_399dab5851d6e971fa0b

import ProverJobs.ResidualE2EAssembly20261106.M_3faa623820844d0d053c

namespace PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

theorem paper_951aae9227d84800bf9113306ae458aa
    (K rhoMin : ℝ) (hK : 0 < K) (hrhoMin : 0 < rhoMin) :
    (∀ (alpha0 : ℝ), 15 < alpha0 →
          ∃ c c1 C C0 : ℝ, 0 < c ∧ 0 < c1 ∧ 0 < C ∧ 0 < C0 ∧ ∃ m0 : ℕ,
          ∀ (m n : ℕ) (p : ℝ) (T r : ℕ) (sigma : ℝ)
            {Ωs : Type*} [MeasurableSpace Ωs] (μ : Measure Ωs) [IsProbabilityMeasure μ]
            (Om Hm : Ωs → Matrix (Fin m) (Fin n) ℝ)
            (G : Ωs → Fin T → Matrix (Fin m) (Fin n) ℝ)
            (M0 : Matrix (Fin m) (Fin n) ℝ) (w : Fin n → ℝ)
            (U0 : Matrix (Fin m) (Fin r) ℝ) (d0 : Fin r → ℝ)
            (V0 : Matrix (Fin n) (Fin r) ℝ) (mu0 : ℝ)
            (hsigma : 0 < sigma)
            (hm : m0 ≤ m) (hn : 2 ≤ n) (hnm : n ≤ m)
            (hp0 : 0 < p) (hp1 : p ≤ 1)
            (hrho_lo : rhoMin ≤ rho m n) (hrho_hi : rho m n ≤ 1)
            (hT : 1 ≤ T)
            (hmp : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
            (hw_nn : ∀ i : Fin n, 0 ≤ w i) (hw_sum : (∑ i : Fin n, w i) = 1)
            (hM0 : IsIncoherentSVD M0 U0 d0 V0 mu0)
            (hlaw : IsSamplingLaw μ Om Hm G p sigma K),
              ∃ E : Set Ωs, MeasurableSet E ∧
                ENNReal.ofReal (1 - c1 * ((n : ℝ) ^ 3)⁻¹) ≤ μ E ∧
                ∀ s ∈ E,
                  (Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om s))
                      ≤ C * Real.sqrt ((m : ℝ) / p)) ∧
                  (∀ A B : Matrix (Fin m) (Fin n) ℝ,
                    inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                      |matInner (TOmega (Om s) U0 V0 A) B - p * matInner A B|
                        ≤ C * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B) ∧
                  (∀ i : Fin n,
                    |sv hnm (maskOp (Om s) (Hm s)) i / (sigma * Real.sqrt (m : ℝ))
                      - lambdaHat hnm (Om s) (G s) i|
                      ≤ C * Real.sqrt p * deltaM m) ∧
                  (max (Statlib.HighDim.MatrixAnalysis.opNorm (maskOp (Om s) (Hm s))
                        / (sigma * Real.sqrt (m : ℝ)))
                      (lambdaHat hnm (Om s) (G s)
                        ⟨0, Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn⟩)
                    ≤ Real.sqrt p * (1 + Real.sqrt (rho m n) + C * deltaM m)) ∧
                  (c * (n : ℝ) * Real.sqrt p
                    ≤ ∑ i ∈ indexSet n, lambdaHat hnm (Om s) (G s) i) ∧
                  (|sigmaHat hnm (indexSet n) (lambdaHat hnm (Om s) (G s))
                        (Yobs (Om s) M0 (Hm s)) (Om s) M0
                      / sigma - 1| ≤ C * deltaM m) ∧
                  (loss hnm (indexSet n) p w (lambdaHat hnm (Om s) (G s))
                      (Yobs (Om s) M0 (Hm s)) (Om s) M0
                    ≤ ENNReal.ofReal (C0 * deltaM m ^ 2)) ∧
                  (∀ M : Matrix (Fin m) (Fin n) ℝ,
                    |sigmaHat hnm (indexSet n) (lambdaHat hnm (Om s) (G s))
                          (Yobs (Om s) M0 (Hm s)) (Om s) M
                        / sigma - 1|
                      ≤ C * deltaM m
                        + C * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp (Om s) (M - M0))
                            / (sigma * Real.sqrt ((m : ℝ) * (n : ℝ) * p))))

    ∧ (∀ D : ℝ, 0 < D →
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
                          ≥ ENNReal.ofReal (1 - c * Real.rpow (n : ℝ) (-D))))
:= by
  /- @proof-region region.root.4444a4590e30 begin -/
  exact PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported.paper_951aae9227d84800bf9113306ae458aa K rhoMin hK hrhoMin
  /- @proof-region region.root.4444a4590e30 end -/

end Statlib.Imported

end

-- Paper root revision 3f57f9ee-70df-4acc-8c5d-b6bdab1799c4

