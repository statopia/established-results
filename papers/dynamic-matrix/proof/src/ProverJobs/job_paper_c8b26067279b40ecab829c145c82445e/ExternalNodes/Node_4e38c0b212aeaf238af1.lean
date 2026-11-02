import ProverJobs.job_paper_c8b26067279b40ecab829c145c82445e.Base

namespace PaperProofTasks.job_paper_c8b26067279b40ecab829c145c82445e

-- External DAG node: ext_model_2 (AXIOM)
example : Prop := (open Matrix in (open Statlib.Imported in (∀ (d : ℕ) (hd : 0 < d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hSsymm : S.IsSymm) (hSpd : S.PosDef)
    (a b : EuclideanSpace ℝ (Fin d)),
    lambdaMax d hd S hSpd.isHermitian =
        kappaSigma d hd S hSpd.isHermitian * lambdaMin d hd S hSpd.isHermitian ∧
    |a.ofLp ⬝ᵥ (S *ᵥ b.ofLp)| ≤
      lambdaMax d hd S hSpd.isHermitian * ‖a‖ * ‖b‖ ∧
    |a.ofLp ⬝ᵥ (S *ᵥ b.ofLp)| ≤
      kappaSigma d hd S hSpd.isHermitian * lambdaMin d hd S hSpd.isHermitian *
        ‖a‖ * ‖b‖)))
axiom ext_model_2 : (open Matrix in (open Statlib.Imported in (∀ (d : ℕ) (hd : 0 < d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hSsymm : S.IsSymm) (hSpd : S.PosDef)
    (a b : EuclideanSpace ℝ (Fin d)),
    lambdaMax d hd S hSpd.isHermitian =
        kappaSigma d hd S hSpd.isHermitian * lambdaMin d hd S hSpd.isHermitian ∧
    |a.ofLp ⬝ᵥ (S *ᵥ b.ofLp)| ≤
      lambdaMax d hd S hSpd.isHermitian * ‖a‖ * ‖b‖ ∧
    |a.ofLp ⬝ᵥ (S *ᵥ b.ofLp)| ≤
      kappaSigma d hd S hSpd.isHermitian * lambdaMin d hd S hSpd.isHermitian *
        ‖a‖ * ‖b‖)))

