import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1115460558_7c8fc3cc_766cf58f
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_981266013_fb7e4a2e_b561f1f3

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2978248555_2b2dc1fc : ∀ (b : ℝ) (hb : 0 < b)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi1 phi2 : ℝ) (y : Fin p → ℝ) (v : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
    (hdeltane : delta n m ≠ 0)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hX2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hY2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
    (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1),
    (let phi : ℝ := min phi1 phi2
     let beta : ℝ := phi * Real.log (p : ℝ)
     let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (n : ℝ))⁻¹ *
         (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
           + Real.sqrt (1 - t) * (F i x.2 j - muX j))
     let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
           + Real.sqrt (1 - t) * (G i x.2 j - muY j))
     let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
       (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
     let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (n : ℝ))⁻¹ *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
           - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
     let Zdot : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
           - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
     let kappa : (Fin p → ℝ) → ℝ := fun w =>
       phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
     let Istar : Ω × Ω → ℝ := fun x =>
       ∫ t in (0 : ℝ)..1,
         ∑ j : Fin p, ∑ i : Fin n,
           (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j
     let Istarstar : Ω × Ω → ℝ := fun x =>
       ∫ t in (0 : ℝ)..1,
         ∑ j : Fin p, ∑ i : Fin m,
           (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j
     Integrable Istar (P.prod P) ∧ Integrable Istarstar (P.prod P) ∧
       ∫ x, (kappa (Z 1 x) - kappa (Z 0 x)) ∂(P.prod P) =
         (∫ x, Istar x ∂(P.prod P)) + ∫ x, Istarstar x ∂(P.prod P)) := by
  /- @proof-region region.target-node.session.80fa1df230f2bc56 begin -/
  intro b hb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range Ω hΩ P hP n m p delta muX muY X Y F G phi1 phi2 y v hn hm hp hlogp hdeltane hXm hYm hFm hGm hX2 hY2 hX3 hY3 hF3 hG3 hphi1 hphi2 hv0 hv1
  let phi : ℝ := min phi1 phi2
  let beta : ℝ := phi * Real.log (p : ℝ)
  let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
        + Real.sqrt (1 - t) * (F i x.2 j - muX j))
  let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        + Real.sqrt (1 - t) * (G i x.2 j - muY j))
  let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
    (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
  let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
        - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
  let Zdot : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
  let kappa : (Fin p → ℝ) → ℝ := fun w =>
    phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
  let Istar : Ω × Ω → ℝ := fun x =>
    ∫ t in (0 : ℝ)..1,
      ∑ j : Fin p, ∑ i : Fin n,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j
  let Istarstar : Ω × Ω → ℝ := fun x =>
    ∫ t in (0 : ℝ)..1,
      ∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j
  have hpt : ∀ x : Ω × Ω, kappa (Z 1 x) - kappa (Z 0 x) = Istar x + Istarstar x :=
    @statopia_math_node_1115460558_7c8fc3cc phi0 hphi0_cont Ω hΩ n m p delta muX muY X Y F G phi1 phi2 y v hp hphi1 hphi2 hv0 hv1
  have hIS := @statopia_math_node_981266013_fb7e4a2e phi0 hphi0_cont hphi0_left hphi0_right Ω hΩ P hP n m p delta muX muY X Y F G phi1 phi2 y v hp hphi1 hphi2 hv0 hv1 hXm hYm hFm hGm hX2 hY2 hX3 hY3 hF3 hG3
  have hI1 : Integrable Istar (P.prod P) := hIS.1
  have hI2 : Integrable Istarstar (P.prod P) := hIS.2
  show Integrable Istar (P.prod P) ∧ Integrable Istarstar (P.prod P) ∧
    ∫ x, (kappa (Z 1 x) - kappa (Z 0 x)) ∂(P.prod P) =
      (∫ x, Istar x ∂(P.prod P)) + ∫ x, Istarstar x ∂(P.prod P)
  refine ⟨hI1, hI2, ?_⟩
  calc ∫ x, (kappa (Z 1 x) - kappa (Z 0 x)) ∂(P.prod P)
      = ∫ x, (Istar x + Istarstar x) ∂(P.prod P) := by simp only [hpt]
    _ = (∫ x, Istar x ∂(P.prod P)) + ∫ x, Istarstar x ∂(P.prod P) := integral_add hI1 hI2
  /- @proof-region region.target-node.session.80fa1df230f2bc56 end -/

end

end Statlib.Imported

