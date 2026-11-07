import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3349189165_a90ed3a5_871f2f1e
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_691214651_0da9ee85_9672f420

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
theorem statopia_math_node_3058846527_46c4d95c : ∀ (b : ℝ) (hb : 0 < b),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
        (hlogp : 0 < Real.log (p : ℝ))
        (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
        (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
        (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ),
        (∀ i : Fin n, Measurable (X i)) →
        (∀ i : Fin m, Measurable (Y i)) →
        (∀ i : Fin n, Measurable (F i)) →
        (∀ i : Fin m, Measurable (G i)) →
        iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P →
        (∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P) →
        (∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P) →
        (∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P) →
        (∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P) →
        (∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P) →
        (∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P) →
        (∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j) →
        (∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j) →
        (∀ i : Fin n,
          IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i)) →
        (∀ i : Fin m,
          IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i)) →
        (∀ j : Fin p, Integrable (fun ω =>
          (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2) P) →
        (∀ j : Fin p, b ≤ ∫ ω,
          (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P) →
        ∀ (phi1 phi2 : ℝ), 1 ≤ phi1 → 1 ≤ phi2 →
          ∀ (v : ℝ), 0 ≤ v → v ≤ 1 → ∀ y : Fin p → ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
            (∫ x, Set.indicator
                {u : Fin p → ℝ |
                  -((min phi1 phi2))⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
                    (⨆ j : Fin p, (u j - y j)) ∧
                  (⨆ j : Fin p, (u j - y j)) ≤
                    ((min phi1 phi2))⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹}
                (fun _ : Fin p → ℝ => (1 : ℝ))
                (fun j : Fin p =>
                  (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
                    (Real.sqrt t *
                        (Real.sqrt v * (X i x.1 j - muX j) +
                          Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
                      Real.sqrt (1 - t) * (F i x.2 j - muX j))) +
                  (∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
                    (Real.sqrt t *
                        (Real.sqrt v * (Y i' x.1 j - muY j) +
                          Real.sqrt (1 - v) * (G i' x.1 j - muY j)) +
                      Real.sqrt (1 - t) * (G i' x.2 j - muY j))))
                ∂(P.prod P)) ≤
              2 * rho P n m p (delta n m) muX muY X Y F G +
                C * (((min phi1 phi2))⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹) *
                  Real.sqrt (Real.log (p : ℝ)) := by
  /- @proof-region region.target-node.session.73e62c5485ea38b2 begin -/
  intro b hb
  obtain ⟨Cb, hCb, hD⟩ := statopia_math_node_3349189165_a90ed3a5 b hb
  set Ctop : ℝ := Cb * (1 + 1 / Real.sqrt (Real.log 2)) with hCtop
  refine ⟨Ctop, ?_, ?_⟩
  · have hl2 : 0 < Real.log 2 := by
      have h := Real.log_lt_log (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)
      simpa using h
    have hs2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hl2
    have hpos : 0 < Ctop := by
      rw [hCtop]
      positivity
    exact le_of_lt hpos
  intro Ω _ P _ n m p hn hm hp hlogp delta muX muY X Y F G
    hXm hYm hFm hGm hindep hXL2 hYL2 hX3 hY3 hF3 hG3 hXmean hYmean hFcov hGcov hcomb2 hbvar
  intro phi1 phi2 hphi1 hphi2 v hv0 hv1 y t ht
  set K : ℝ := ((min phi1 phi2))⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ with hK
  set Gp : ℝ := (P {ω : Ω | -K < (⨆ j : Fin p,
        (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ∧
      (⨆ j : Fin p,
        (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ≤ K}).toReal
    with hGp
  have hKnn : 0 ≤ K := by
    rw [hK]
    have hmin : (0 : ℝ) < min phi1 phi2 := by
      have h := le_min hphi1 hphi2
      linarith
    positivity
  have h2 : Gp ≤ Ctop * K * Real.sqrt (Real.log (p : ℝ)) := by
    rw [hGp]
    have hbound := hD (Ω := Ω) (P := P) (n := n) (m := m) (p := p) (delta := delta)
      (muX := muX) (muY := muY) (X := X) (Y := Y) (F := F) (G := G)
      hn hm hp hXm hYm hFm hGm hindep hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3
      hFcov hGcov hbvar y K hKnn
    refine le_trans hbound ?_
    have hl2 : 0 < Real.log 2 := by
      have h := Real.log_lt_log (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)
      simpa using h
    have hp2 : 2 ≤ p := by
      have h0 : p ≠ 0 := by rintro rfl; simp at hlogp
      have h1 : p ≠ 1 := by rintro rfl; simp at hlogp
      omega
    have hlog2 : Real.log 2 ≤ Real.log (p : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hp2
    have hs2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hl2
    have hsle : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log (p : ℝ)) := Real.sqrt_le_sqrt hlog2
    have hle : Real.sqrt (Real.log (p : ℝ)) + 1 ≤
        (1 + 1 / Real.sqrt (Real.log 2)) * Real.sqrt (Real.log (p : ℝ)) := by
      have h1 : (1 : ℝ) ≤ Real.sqrt (Real.log (p : ℝ)) / Real.sqrt (Real.log 2) := by
        rw [div_eq_mul_inv]
        have h0 : Real.sqrt (Real.log 2) * (Real.sqrt (Real.log 2))⁻¹ ≤
            Real.sqrt (Real.log (p : ℝ)) * (Real.sqrt (Real.log 2))⁻¹ :=
          mul_le_mul_of_nonneg_right hsle (by positivity)
        rwa [mul_inv_cancel₀ (ne_of_gt hs2)] at h0
      have hexp : (1 + 1 / Real.sqrt (Real.log 2)) * Real.sqrt (Real.log (p : ℝ))
          = Real.sqrt (Real.log (p : ℝ)) + Real.sqrt (Real.log (p : ℝ)) / Real.sqrt (Real.log 2) := by
        rw [div_eq_mul_inv]
        ring
      rw [hexp]
      linarith
    calc Cb * K * (Real.sqrt (Real.log (p : ℝ)) + 1)
        ≤ Cb * K * ((1 + 1 / Real.sqrt (Real.log 2)) * Real.sqrt (Real.log (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hle (mul_nonneg (le_of_lt hCb) hKnn)
      _ = Ctop * K * Real.sqrt (Real.log (p : ℝ)) := by
          rw [hCtop]
          ring
  refine le_trans (b := 2 * rho P n m p (delta n m) muX muY X Y F G + Gp) ?_ ?_
  · have hset : {u : Fin p → ℝ |
        -((min phi1 phi2))⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
          (⨆ j : Fin p, (u j - y j)) ∧
        (⨆ j : Fin p, (u j - y j)) ≤
          ((min phi1 phi2))⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹}
        = {u : Fin p → ℝ | -K < (⨆ j : Fin p, (u j - y j)) ∧
            (⨆ j : Fin p, (u j - y j)) ≤ K} := by
      rw [hK]
      ext u
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, h2⟩
    rw [hset, hGp]
    exact statopia_math_node_691214651_0da9ee85 b hb (Ω := Ω) (P := P) (n := n) (m := m) (p := p)
      (delta := delta) (muX := muX) (muY := muY) (X := X) (Y := Y) (F := F) (G := G)
      hn hm hp hlogp hXm hYm hFm hGm hindep hXL2 hYL2 hX3 hY3 hF3 hG3 hXmean hYmean
      hFcov hGcov hcomb2 hbvar phi1 phi2 hphi1 hphi2 v hv0 hv1 y t ht K hKnn
  · linarith
  /- @proof-region region.target-node.session.73e62c5485ea38b2 end -/

end

end Statlib.Imported

