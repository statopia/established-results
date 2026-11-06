import Lean
import ProverJobs.ResidualE2ESupport20261106.M_cc93c829671a6c60a1f1
import ProverJobs.ResidualE2ESupport20261106.M_6009dc3183eb479769aa

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ResidualLoss20261106.Statlib.Imported
universe u

theorem noise_calibration (K rhoMin : ℝ) (hK : 0 < K) (hrhoMin : 0 < rhoMin)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ m0att : ℕ,
      ∀ (p sigma : ℝ) (n m : ℕ) (γ : Fin n → ℝ)
        {Ωs : Type u} [MeasurableSpace Ωs] (μ : Measure Ωs) [IsProbabilityMeasure μ]
        (Om Hm : Ωs → Matrix (Fin m) (Fin n) ℝ)
        (hm : m0att ≤ m) (hn : 2 ≤ n) (hnm : n ≤ m) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hrho_lo : rhoMin ≤ (rho m n)) (hrho_hi : (rho m n) ≤ 1) (hsigma : 0 < sigma)
        (hmp : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (hgamma : ∀ i : Fin n,
          (∫ x, nuRho (rho m n) x ∂(volume.restrict (Set.Icc (γ i) (lambdaPlus (rho m n)))))
            = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ))
        (hOm_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Om s i j)
        (hOm_bin : ∀ (s : Ωs) (i : Fin m) (j : Fin n), Om s i j = 0 ∨ Om s i j = 1)
        (hOm_prob : ∀ (i : Fin m) (j : Fin n), μ {s : Ωs | Om s i j = 1} = ENNReal.ofReal p)
        (hHm_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Hm s i j)
        (hHm_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => Hm s i j) μ)
        (hHm_mean : ∀ (i : Fin m) (j : Fin n), (∫ s, Hm s i j ∂μ) = 0)
        (hHm_int2 : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => (Hm s i j) ^ 2) μ)
        (hHm_var : ∀ (i : Fin m) (j : Fin n), (∫ s, (Hm s i j) ^ 2 ∂μ) = sigma ^ 2)
        (hHm_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
          μ {s : Ωs | t * sigma < |Hm s i j|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / K))))
        (hindep : iIndepFun (fun (x : (Fin m × Fin n) ⊕ (Fin m × Fin n)) => fun s : Ωs =>
          match x with
          | Sum.inl q => Om s q.1 q.2
          | Sum.inr q => Hm s q.1 q.2) μ),
        μ {s : Ωs |
              (∀ i : Fin n,
                |sv hnm (maskOp (Om s) (Hm s)) i / (sigma * Real.sqrt (m : ℝ))
                    - Real.sqrt p * γ i|
                  ≤ C * Real.sqrt p * deltaM m) ∧
              sv hnm (maskOp (Om s) (Hm s)) ⟨0, Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn⟩
                  / (sigma * Real.sqrt (m : ℝ))
                ≤ Real.sqrt p * (1 + Real.sqrt (rho m n) + C * deltaM m)}
          ≥ ENNReal.ofReal (1 - c * Real.rpow (n : ℝ) (-4 : ℝ)) := by
  obtain ⟨CR, cR, hCR, hcR, m0att, hRig⟩ :=
    sparse_rigidity_loss_vocabulary.{u} K rhoMin hK hrhoMin alpha0 halpha0
  obtain ⟨C, c, hC, hc, h⟩ := ideal_noise_from_actual_rigidity.{u}
    K rhoMin hK hrhoMin alpha0 halpha0 CR cR hCR hcR m0att hRig
  exact ⟨C, c, hC, hc, m0att, h⟩

end ResidualLoss20261106.Statlib.Imported
#print axioms ResidualLoss20261106.Statlib.Imported.noise_calibration

