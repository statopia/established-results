import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2370750926_4f6d6a8f_59de9429
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3349189165_a90ed3a5_871f2f1e

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
theorem statopia_math_node_792479139_d2da39bf : ∀ (b : ℝ) (hb : 0 < b),
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
        (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
        (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
        (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
        (hX : ∀ i : Fin n, Measurable (X i)) (hY : ∀ i : Fin m, Measurable (Y i))
        (hF : ∀ i : Fin n, Measurable (F i)) (hG : ∀ i : Fin m, Measurable (G i))
        (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
        (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
        (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
        (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
        (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
        (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
        (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
        (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
        (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
        (hFcov : ∀ i : Fin n, IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
        (hGcov : ∀ i : Fin m, IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
        (hbvar : ∀ (j : Fin p), b ≤ ∫ (ω : Ω), combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j ^ 2 ∂P)
        (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
        (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (y : Fin p → ℝ),
        let phi : ℝ := min phi1 phi2
        let beta : ℝ := phi * Real.log (p : ℝ)
        let kappa0 : ℝ := phi⁻¹ + 2 * beta⁻¹
        let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
          (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
              (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
                Real.sqrt (1 - t) * (F i x.2 j - muX j)))
            + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
              (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
                Real.sqrt (1 - t) * (G i x.2 j - muY j)))
        ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          (∫ x : Ω × Ω,
            Set.indicator
              {x : Ω × Ω |
                -(kappa0 + 2 * beta⁻¹) < (⨆ j : Fin p, (Z t x j - y j)) ∧
                (⨆ j : Fin p, (Z t x j - y j)) ≤ kappa0 + 2 * beta⁻¹}
              (fun _ => (1 : ℝ)) x ∂(P.prod P))
          ≤ 2 * rho P n m p (delta n m) muX muY X Y F G
              + Cb * kappa0 * (Real.sqrt (Real.log (p : ℝ)) + 1) := by
  /- @proof-region region.target-node.session.985b2ed73805c398 begin -/
  intro b hb
  obtain ⟨CB, hCBpos, hCB⟩ := statopia_math_node_3349189165_a90ed3a5 b hb
  refine ⟨2 * CB, by linarith, ?_⟩
  intro Ω _ P _ n m p delta muX muY X Y F G hn hm hp hlogp hX hY hF hG hindep
    hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov hbvar phi1 phi2 hphi1 hphi2 v hv0 hv1 y
  dsimp only
  intro t ht
  set k0 : ℝ := (min phi1 phi2)⁻¹ + 2 * (min phi1 phi2 * Real.log (p : ℝ))⁻¹ with hk0def
  set W : ℝ := k0 + 2 * (min phi1 phi2 * Real.log (p : ℝ))⁻¹ with hWdef
  have hphi_pos : (0 : ℝ) < min phi1 phi2 := lt_min (by linarith) (by linarith)
  have hinv_phi : (0 : ℝ) ≤ (min phi1 phi2)⁻¹ := inv_nonneg.2 (le_of_lt hphi_pos)
  have hbinv_nonneg : (0 : ℝ) ≤ (min phi1 phi2 * Real.log (p : ℝ))⁻¹ :=
    inv_nonneg.2 (le_of_lt (mul_pos hphi_pos hlogp))
  have hk0_nonneg : (0 : ℝ) ≤ k0 := by
    rw [hk0def]
    linarith
  have hW_nonneg : (0 : ℝ) ≤ W := by
    rw [hWdef]
    linarith
  have hWle : W ≤ 2 * k0 := by
    rw [hWdef, hk0def]
    nlinarith [hinv_phi, hbinv_nonneg]
  have hS : (0 : ℝ) ≤ Real.sqrt (Real.log (p : ℝ)) + 1 := by
    have h := Real.sqrt_nonneg (Real.log (p : ℝ))
    linarith
  have hred' := statopia_math_node_2370750926_4f6d6a8f (Ω := Ω) (P := P) n m p delta muX muY
    X Y F G hn hm hp hX hY hF hG hindep hFcov hGcov v hv0 hv1 y W hW_nonneg t ht
  have hB := hCB (Ω := Ω) (P := P) n m p delta muX muY X Y F G hn hm hp hX hY hF hG hindep
    hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov hbvar y W hW_nonneg
  have hCBW : CB * W * (Real.sqrt (Real.log (p : ℝ)) + 1)
      ≤ (2 * CB) * k0 * (Real.sqrt (Real.log (p : ℝ)) + 1) := by
    have h2 : (0 : ℝ) ≤ CB * (Real.sqrt (Real.log (p : ℝ)) + 1) :=
      mul_nonneg (le_of_lt hCBpos) hS
    calc CB * W * (Real.sqrt (Real.log (p : ℝ)) + 1)
        = (CB * (Real.sqrt (Real.log (p : ℝ)) + 1)) * W := by ring
      _ ≤ (CB * (Real.sqrt (Real.log (p : ℝ)) + 1)) * (2 * k0) :=
          mul_le_mul_of_nonneg_left hWle h2
      _ = (2 * CB) * k0 * (Real.sqrt (Real.log (p : ℝ)) + 1) := by ring
  exact le_trans hred' (by linarith [hB, hCBW])
  /- @proof-region region.target-node.session.985b2ed73805c398 end -/

end

end Statlib.Imported

