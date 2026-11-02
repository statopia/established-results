import ProverJobs.job_paper_c8b26067279b40ecab829c145c82445e.ExternalNodes.Node_4e38c0b212aeaf238af1
import ProverJobs.job_paper_c8b26067279b40ecab829c145c82445e.ExternalNodes.Node_6515c10a3b2a6920f75d
import ProverJobs.job_paper_c8b26067279b40ecab829c145c82445e.Vocabulary
import ProverJobs.job_paper_c8b26067279b40ecab829c145c82445e.ProvedNodes
import ProverJobs.job_paper_c8b26067279b40ecab829c145c82445e.Base

namespace PaperProofTasks.job_paper_c8b26067279b40ecab829c145c82445e

open Matrix
namespace Statlib.Imported


theorem paper_c8b26067279b40ecab829c145c82445e (d : ℕ) (hd : 0 < d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hSsymm : S.IsSymm) (hSpd : S.PosDef) :
    ∀ a b : EuclideanSpace ℝ (Fin d),
      a.ofLp ⬝ᵥ (S *ᵥ (a + b).ofLp) ≥
        lambdaMin d hd S hSpd.isHermitian *
          (‖a‖ ^ 2 - kappaSigma d hd S hSpd.isHermitian * ‖a‖ * ‖b‖)
:= by
  /- @proof-region region.root.b21bfa7690ff begin -/
  intro a b
  have h1 : a.ofLp ⬝ᵥ (S *ᵥ a.ofLp) ≥ lambdaMin d hd S hSpd.isHermitian * ‖a‖ ^ 2 :=
    ext_model_1 d hd S hSsymm hSpd a
  have h2 : -(kappaSigma d hd S hSpd.isHermitian * lambdaMin d hd S hSpd.isHermitian *
        ‖a‖ * ‖b‖) ≤ a.ofLp ⬝ᵥ (S *ᵥ b.ofLp) :=
    (abs_le.mp (ext_model_2 d hd S hSsymm hSpd a b).2.2).1
  have hexp : a.ofLp ⬝ᵥ (S *ᵥ (a + b).ofLp)
      = a.ofLp ⬝ᵥ (S *ᵥ a.ofLp) + a.ofLp ⬝ᵥ (S *ᵥ b.ofLp) := by
    simp [Matrix.mulVec_add, dotProduct_add]
  rw [hexp]
  have h3 : lambdaMin d hd S hSpd.isHermitian * ‖a‖ ^ 2 +
      -(kappaSigma d hd S hSpd.isHermitian * lambdaMin d hd S hSpd.isHermitian * ‖a‖ * ‖b‖)
      = lambdaMin d hd S hSpd.isHermitian *
        (‖a‖ ^ 2 - kappaSigma d hd S hSpd.isHermitian * ‖a‖ * ‖b‖) := by
    ring
  linarith [h1, h2, h3]
  /- @proof-region region.root.b21bfa7690ff end -/

end Statlib.Imported

