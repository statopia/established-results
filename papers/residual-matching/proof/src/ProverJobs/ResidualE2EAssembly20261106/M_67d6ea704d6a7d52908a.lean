import Lean
import ProverJobs.ResidualE2ESupport20261106.M_5cf4bd571fbd2d512273
import ProverJobs.ResidualE2EAssembly20261106.M_2899ebcb4b6cf51030cf

import ProverJobs.ResidualE2EAssembly20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

theorem paper_45fc93d926fd4099b9973daee59eb529 :
    ∀ rho : ℝ, 0 < rho → ∀ alpha0 : ℝ, 15 < alpha0 →
    ∃ N0 : ℕ, ∃ Cs CL Cth c : ℝ,
      0 < Cs ∧ 0 < CL ∧ 0 < Cth ∧ 0 < c ∧
      ∀ (m n r : ℕ) (p mu0 sigma : ℝ),
        0 < m → 0 < n → N0 ≤ m → n ≤ m →
        0 ≤ p → p ≤ 1 →
        rho ≤ (n : ℝ) / (m : ℝ) → (n : ℝ) / (m : ℝ) ≤ 1 →
        0 < sigma → 12 * r ≤ n →
        (m : ℝ) * p ≥ Real.rpow (Real.log (m : ℝ)) alpha0 →
        (n : ℝ) * p ≥ Cs * mu0 * (r : ℝ) * Real.log (m : ℝ) →
        ∀ (M0 : Matrix (Fin m) (Fin n) ℝ) (U0 : Matrix (Fin m) (Fin r) ℝ)
          (V0 : Matrix (Fin n) (Fin r) ℝ) (s0 : Fin r → ℝ),
          M0.rank = r →
          U0.transpose * U0 = 1 →
          V0.transpose * V0 = 1 →
          (∀ i, 0 < s0 i) →
          M0 = U0 * Matrix.diagonal s0 * V0.transpose →
          rowNorm U0 ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) →
          rowNorm V0 ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) →
          ∀ {Ωm : Type*} [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
            (H : Fin m → Fin n → Ωm → ℝ) (Om : Fin m → Fin n → Ωm → ℝ),
            (∀ i j, Measurable (H i j)) →
            (∀ i j, Integrable (H i j) P) →
            iIndepFun (fun (ij : Fin m × Fin n) => H ij.1 ij.2) P →
            (∀ i j, ∫ omega, H i j omega ∂P = 0) →
            (∀ i j, ∫ omega, (H i j omega) ^ 2 ∂P = sigma ^ 2) →
            (∃ KH : ℝ, 0 < KH ∧ ∀ i j (t : ℝ), 0 ≤ t →
              P {omega | t ≤ |H i j omega|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / KH)))) →
            (∀ i j, Measurable (Om i j)) →
            iIndepFun (fun (ij : Fin m × Fin n) => Om ij.1 ij.2) P →
            (∀ i j, ∀ᵐ omega ∂P, Om i j omega = 0 ∨ Om i j omega = 1) →
            (∀ i j, P {omega | Om i j omega = 1} = ENNReal.ofReal p) →
            (∀ i j, Integrable (Om i j) P) →
            (∀ i j, ∫ omega, Om i j omega ∂P = p) →
            IndepFun (fun omega (ij : Fin m × Fin n) => Om ij.1 ij.2 omega)
              (fun omega (ij : Fin m × Fin n) => H ij.1 ij.2 omega) P →
            1 - ENNReal.ofReal (c / (n : ℝ) ^ 4) ≤
              P {omega |
                
                specNorm (Wmask p (fun i j => Om i j omega))
                    ≤ CL * Real.sqrt ((m : ℝ) / p) ∧
                
                (∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
                  specNorm (Tmask p (fun i j => Om i j omega) (L * R.transpose))
                    ≤ CL * Real.sqrt ((m : ℝ) / p) * rowNorm L * rowNorm R) ∧
                
                (∀ A B : Matrix (Fin m) (Fin n) ℝ,
                  MemTangentRect U0 V0 A → MemTangentRect U0 V0 B →
                  |frobInner (Tmask p (fun i j => Om i j omega) A) B|
                    ≤ Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                      * frobNorm A * frobNorm B) ∧
                
                (∀ (k l : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
                    (C1 : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
                  |frobInner (Tmask p (fun i j => Om i j omega) (A * B.transpose))
                      (C1 * D.transpose)|
                    ≤ CL * Real.sqrt ((m : ℝ) / p) * bFactor A C1 * bFactor B D)}
:= by
  /- @proof-region region.root.a0d40265c1f0 begin -/
  exact PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.completed_mask_geometry_e2e
  /- @proof-region region.root.a0d40265c1f0 end -/

end

end Statlib.Imported

-- Paper root revision 4a664b26-ec41-4554-b0df-a7811701a889

