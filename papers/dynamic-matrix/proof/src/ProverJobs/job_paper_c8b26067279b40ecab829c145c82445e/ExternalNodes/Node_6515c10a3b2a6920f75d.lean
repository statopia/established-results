import ProverJobs.job_paper_c8b26067279b40ecab829c145c82445e.Base

namespace PaperProofTasks.job_paper_c8b26067279b40ecab829c145c82445e

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (∀ (d : ℕ) (hd : 0 < d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hSsymm : S.IsSymm) (hSpd : S.PosDef),
    ∀ a : EuclideanSpace ℝ (Fin d),
      a.ofLp ⬝ᵥ (S.mulVec a.ofLp) ≥
        Statlib.Imported.lambdaMin d hd S hSpd.isHermitian * ‖a‖ ^ 2)
axiom ext_model_1 : (∀ (d : ℕ) (hd : 0 < d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hSsymm : S.IsSymm) (hSpd : S.PosDef),
    ∀ a : EuclideanSpace ℝ (Fin d),
      a.ofLp ⬝ᵥ (S.mulVec a.ofLp) ≥
        Statlib.Imported.lambdaMin d hd S hSpd.isHermitian * ‖a‖ ^ 2)

