import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (∀ (n : ℕ) (hn : 0 < n) (b1 : ℝ) (hb1 : 0 ≤ b1)
    (Phi : Fin n → ℝ → ℝ) (Omega' : Set (Fin n → ℝ))
    (hLip : ∀ i : Fin n, LipschitzWith ⟨b1, hb1⟩ (Phi i))
    (hzero : ∀ i : Fin n, Phi i 0 = 0)
    (hbdd : Bornology.IsBounded Omega')
    (P : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsProbabilityMeasure P]
    (hRadem : P = MeasureTheory.Measure.pi (fun _ : Fin n => Statlib.Imported.rademacherLaw)),
    ∫ sigma, sSup ((fun t : Fin n → ℝ =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n, sigma i * Phi i (t i)|) '' Omega') ∂P ≤
      2 * b1 * ∫ sigma, sSup ((fun t : Fin n → ℝ =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n, sigma i * t i|) '' Omega') ∂P)
axiom ext_model_1 : (∀ (n : ℕ) (hn : 0 < n) (b1 : ℝ) (hb1 : 0 ≤ b1)
    (Phi : Fin n → ℝ → ℝ) (Omega' : Set (Fin n → ℝ))
    (hLip : ∀ i : Fin n, LipschitzWith ⟨b1, hb1⟩ (Phi i))
    (hzero : ∀ i : Fin n, Phi i 0 = 0)
    (hbdd : Bornology.IsBounded Omega')
    (P : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsProbabilityMeasure P]
    (hRadem : P = MeasureTheory.Measure.pi (fun _ : Fin n => Statlib.Imported.rademacherLaw)),
    ∫ sigma, sSup ((fun t : Fin n → ℝ =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n, sigma i * Phi i (t i)|) '' Omega') ∂P ≤
      2 * b1 * ∫ sigma, sSup ((fun t : Fin n → ℝ =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n, sigma i * t i|) '' Omega') ∂P)

