import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

-- External DAG node: ext_model_3 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (∀ (Ω : Type*) [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (xi1 xi2 : Ω → ℝ)
    (hxi1 : Measurable xi1) (hxi2 : Measurable xi2)
    (hIndep : IndepFun xi1 xi2 mu)
    (phi1 phi2 : ℝ → ℝ)
    (hphi1_nonneg : ∀ x, 0 ≤ phi1 x) (hphi2_nonneg : ∀ x, 0 ≤ phi2 x)
    (hphi1_mono : Monotone phi1) (hphi2_mono : Monotone phi2)
    (hE11 : Integrable (fun ω => phi1 (xi1 ω)) mu)
    (hE21 : Integrable (fun ω => phi2 (xi1 ω)) mu)
    (hE12 : Integrable (fun ω => phi1 (xi2 ω)) mu)
    (hE22 : Integrable (fun ω => phi2 (xi2 ω)) mu)
    (hE1211 : Integrable (fun ω => phi1 (xi1 ω) * phi2 (xi1 ω)) mu)
    (hE1222 : Integrable (fun ω => phi1 (xi2 ω) * phi2 (xi2 ω)) mu)
    (hE1221 : Integrable (fun ω => phi1 (xi1 ω) * phi2 (xi2 ω)) mu),
    ((∫ ω, phi1 (xi1 ω) ∂mu) * (∫ ω, phi2 (xi1 ω) ∂mu) ≤
        ∫ ω, phi1 (xi1 ω) * phi2 (xi1 ω) ∂mu) ∧
      ((∫ ω, phi1 (xi1 ω) ∂mu) * (∫ ω, phi2 (xi2 ω) ∂mu) ≤
        (∫ ω, phi1 (xi1 ω) * phi2 (xi1 ω) ∂mu) +
          (∫ ω, phi1 (xi2 ω) * phi2 (xi2 ω) ∂mu)) ∧
      ((∫ ω, phi1 (xi1 ω) * phi2 (xi2 ω) ∂mu) ≤
        (∫ ω, phi1 (xi1 ω) * phi2 (xi1 ω) ∂mu) +
          (∫ ω, phi1 (xi2 ω) * phi2 (xi2 ω) ∂mu))))
axiom ext_model_3 : (open MeasureTheory ProbabilityTheory in (∀ (Ω : Type*) [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (xi1 xi2 : Ω → ℝ)
    (hxi1 : Measurable xi1) (hxi2 : Measurable xi2)
    (hIndep : IndepFun xi1 xi2 mu)
    (phi1 phi2 : ℝ → ℝ)
    (hphi1_nonneg : ∀ x, 0 ≤ phi1 x) (hphi2_nonneg : ∀ x, 0 ≤ phi2 x)
    (hphi1_mono : Monotone phi1) (hphi2_mono : Monotone phi2)
    (hE11 : Integrable (fun ω => phi1 (xi1 ω)) mu)
    (hE21 : Integrable (fun ω => phi2 (xi1 ω)) mu)
    (hE12 : Integrable (fun ω => phi1 (xi2 ω)) mu)
    (hE22 : Integrable (fun ω => phi2 (xi2 ω)) mu)
    (hE1211 : Integrable (fun ω => phi1 (xi1 ω) * phi2 (xi1 ω)) mu)
    (hE1222 : Integrable (fun ω => phi1 (xi2 ω) * phi2 (xi2 ω)) mu)
    (hE1221 : Integrable (fun ω => phi1 (xi1 ω) * phi2 (xi2 ω)) mu),
    ((∫ ω, phi1 (xi1 ω) ∂mu) * (∫ ω, phi2 (xi1 ω) ∂mu) ≤
        ∫ ω, phi1 (xi1 ω) * phi2 (xi1 ω) ∂mu) ∧
      ((∫ ω, phi1 (xi1 ω) ∂mu) * (∫ ω, phi2 (xi2 ω) ∂mu) ≤
        (∫ ω, phi1 (xi1 ω) * phi2 (xi1 ω) ∂mu) +
          (∫ ω, phi1 (xi2 ω) * phi2 (xi2 ω) ∂mu)) ∧
      ((∫ ω, phi1 (xi1 ω) * phi2 (xi2 ω) ∂mu) ≤
        (∫ ω, phi1 (xi1 ω) * phi2 (xi1 ω) ∂mu) +
          (∫ ω, phi1 (xi2 ω) * phi2 (xi2 ω) ∂mu))))

