import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_4002104850_4380db1f_47e2833e
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_955888345_2e654e22_4674fdd3

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
theorem statopia_math_node_2984263438_339ceff3 : ∀ (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi1 phi2 : ℝ) (y : Fin p → ℝ) (v t : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlog : 0 < Real.log (p : ℝ))
    (hdelta : delta n m ≠ 0)
    (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hX2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hY2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hXint : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYint : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hFgauss : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGgauss : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i)),
    ∀ z : Fin p → ℝ,
      |((P.prod P) {x : Ω × Ω | ∀ j : Fin p,
          (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
              (Real.sqrt t * (Real.sqrt v * (X i (Prod.fst x) j - muX j) +
                Real.sqrt (1 - v) * (F i (Prod.fst x) j - muX j)) +
              Real.sqrt (1 - t) * (F i (Prod.snd x) j - muX j))) +
          (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
              (Real.sqrt t * (Real.sqrt v * (Y i (Prod.fst x) j - muY j) +
                Real.sqrt (1 - v) * (G i (Prod.fst x) j - muY j)) +
              Real.sqrt (1 - t) * (G i (Prod.snd x) j - muY j))) ≤ z j}).toReal
        - (P {ω : Ω | ∀ j : Fin p,
            combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ z j}).toReal|
      ≤ rho P n m p (delta n m) muX muY X Y F G := by
  /- @proof-region region.target-node.session.0a5bd00b46920d01 begin -/
  intro Ω _ P _ n m p delta muX muY X Y F G phi1 phi2 y v t hn hm hp hlog hdelta
    hphi1 hphi2 hv0 hv1 ht hXm hYm hFm hGm hindep hX2 hY2 hXint hYint hFgauss hGgauss z
  exact statopia_math_node_955888345_2e654e22 Ω P n m p hn hm hp hlog delta hdelta muX muY
    X Y F G hXm hYm hFm hGm hindep hX2 hY2 hXint hYint hFgauss hGgauss phi1 phi2 hphi1 hphi2
    y v hv0 hv1 t ht.1 ht.2 z
  /- @proof-region region.target-node.session.0a5bd00b46920d01 end -/

end

end Statlib.Imported

