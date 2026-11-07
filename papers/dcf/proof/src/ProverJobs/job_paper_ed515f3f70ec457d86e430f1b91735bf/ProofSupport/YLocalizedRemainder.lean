import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.RemainderBudget
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.YLeaveOneOut
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.GaussianThirdMoment
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.DirectionalTaylor
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_944887933_296b41c2_3665ec26
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.QRegularization
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.RemainderLocalization
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.RemainderCoordinateMoments
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1649031325_12d7295c_13e7bff5
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1910587795_b1904894_9a3b27fc
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_204015260_c65710ba_ef38b55c
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2105095423_f9567069_cacdc142
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_287517620_f22d7735_a6b10e08
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2945293653_548ae0bd_878bb98d
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3276301073_1a4e82d2_4c88bb73
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3406556126_a8c6e89f_7455c3d4
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3973197367_b91ba50f_1e5affbb
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_4002104850_4380db1f_47e2833e
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_4050339779_734b360b_cdfed423
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_4252936244_9b4dbd57_d6240c58
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_911816952_4086d22b_a7efc4ca
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ExternalNodes.Node_db4d645b77957b8d955d

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported
universe u

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
set_option maxHeartbeats 4000000

set_option autoImplicit false in
theorem statopia_math_node_1559958170_cd7bf946 : ∀ (b : ℝ) (hb : 0 < b)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (Ckappa C1 C2 C3 Cb : ℝ)
    (hCkappa : 0 ≤ Ckappa) (hC1 : 1 ≤ C1) (hC3 : 1 ≤ C3) (hCb : 0 < Cb)
    (hG : ∀ (p : ℕ), 2 ≤ p → ∀ (phi : ℝ), 1 ≤ phi →
      ∀ (y w : Fin p → ℝ) (j : Fin p),
        |(fderiv ℝ (fun w' : Fin p → ℝ =>
            phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
              Real.log (∑ k : Fin p, Real.exp (phi * Real.log (p : ℝ) * (w' k - y k)))))) w)
          (Pi.single j (1 : ℝ))| ≤ Ckappa * phi)
    (hQ : ∀ (p : ℕ), 0 < p → 0 < Real.log (p : ℝ) → ∀ (phi : ℝ), 1 ≤ phi →
      ∀ y : Fin p → ℝ,
        ∃ Q : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ,
          (∀ (j k l : Fin p) (w : Fin p → ℝ), 0 ≤ Q j k l w) ∧
          (∀ (j k l : Fin p) (w : Fin p → ℝ),
            |(iteratedFDeriv ℝ 3 (fun w' : Fin p → ℝ =>
                phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
                  Real.log (∑ i : Fin p, Real.exp (phi * Real.log (p : ℝ) * (w' i - y i)))))) w)
              (fun t : Fin 3 => Pi.single ((![j, k, l] : Fin 3 → Fin p) t) (1 : ℝ))| ≤
              Q j k l w) ∧
          (∀ w : Fin p → ℝ,
            (∑ a : Fin p, ∑ bb : Fin p, ∑ c : Fin p, Q a bb c w) ≤
              C1 * C2 * phi * (phi * Real.log (p : ℝ)) ^ 2) ∧
          (∀ (j k l : Fin p) (w w' : Fin p → ℝ),
            (∀ r : Fin p, |w' r| * (phi * Real.log (p : ℝ)) ≤ 1) →
              Q j k l (w + w') ≤ C3 * Q j k l w))
    (hL : ∀ (ΩL : Type u) [MeasurableSpace ΩL] (PL : Measure ΩL) [IsProbabilityMeasure PL]
      (nL mL pL : ℕ) (deltaL : ℕ → ℕ → ℝ) (muXL muYL : Fin pL → ℝ)
      (XL : Fin nL → ΩL → Fin pL → ℝ) (YL : Fin mL → ΩL → Fin pL → ℝ)
      (FL : Fin nL → ΩL → Fin pL → ℝ) (GG : Fin mL → ΩL → Fin pL → ℝ)
      (phi1L phi2L : ℝ) (yL : Fin pL → ℝ) (vL : ℝ)
      (hnL : 0 < nL) (hmL : 0 < mL) (hpL : 0 < pL) (hlogpL : 0 < Real.log (pL : ℝ))
      (hdL : deltaL nL mL ≠ 0)
      (hXLm : ∀ i : Fin nL, Measurable (XL i))
      (hYLm : ∀ i : Fin mL, Measurable (YL i))
      (hFLm : ∀ i : Fin nL, Measurable (FL i))
      (hGLm : ∀ i : Fin mL, Measurable (GG i))
      (hindepL : iIndepFun (β := fun _ => Fin pL → ℝ) (jointFam XL YL FL GG) PL)
      (hXL2L : ∀ (i : Fin nL) (j : Fin pL), MemLp (fun ω => XL i ω j) 2 PL)
      (hYL2L : ∀ (i : Fin mL) (j : Fin pL), MemLp (fun ω => YL i ω j) 2 PL)
      (hXL3L : ∀ (i : Fin nL) (j : Fin pL), Integrable (fun ω => |XL i ω j - muXL j| ^ 3) PL)
      (hYL3L : ∀ (i : Fin mL) (j : Fin pL), Integrable (fun ω => |YL i ω j - muYL j| ^ 3) PL)
      (hFL3L : ∀ (i : Fin nL) (j : Fin pL), Integrable (fun ω => |FL i ω j - muXL j| ^ 3) PL)
      (hGL3L : ∀ (i : Fin mL) (j : Fin pL), Integrable (fun ω => |GG i ω j - muYL j| ^ 3) PL)
      (hXLmeanL : ∀ (i : Fin nL) (j : Fin pL), ∫ ω, XL i ω j ∂PL = muXL j)
      (hYLmeanL : ∀ (i : Fin mL) (j : Fin pL), ∫ ω, YL i ω j ∂PL = muYL j)
      (hFLcovL : ∀ i : Fin nL,
        IsCenteredGaussianVector PL (fun ω j => FL i ω j - muXL j) (covX PL muXL XL i))
      (hGLcovL : ∀ i : Fin mL,
        IsCenteredGaussianVector PL (fun ω j => GG i ω j - muYL j) (covY PL muYL YL i))
      (hcombL : ∀ j : Fin pL, Integrable (fun ω =>
        (combVec nL mL (deltaL nL mL) muXL muYL (fun i => XL i ω) (fun i => YL i ω) j) ^ 2) PL)
      (hboundL : ∀ j : Fin pL, b ≤ ∫ ω,
        (combVec nL mL (deltaL nL mL) muXL muYL (fun i => XL i ω) (fun i => YL i ω) j) ^ 2 ∂PL)
      (hphi1L : 1 ≤ phi1L) (hphi2L : 1 ≤ phi2L) (hvL0 : 0 ≤ vL) (hvL1 : vL ≤ 1),
      let ZSTL : ℝ → ΩL × ΩL → Fin nL → Fin pL → ℝ := fun t x i j =>
        (Real.sqrt (nL : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt vL * (XL i x.1 j - muXL j) +
              Real.sqrt (1 - vL) * (FL i x.1 j - muXL j)) +
            Real.sqrt (1 - t) * (FL i x.2 j - muXL j))
      let ZSSL : ℝ → ΩL × ΩL → Fin mL → Fin pL → ℝ := fun t x i j =>
        (Real.sqrt (mL : ℝ))⁻¹ * deltaL nL mL *
          (Real.sqrt t * (Real.sqrt vL * (YL i x.1 j - muYL j) +
              Real.sqrt (1 - vL) * (GG i x.1 j - muYL j)) +
            Real.sqrt (1 - t) * (GG i x.2 j - muYL j))

      let ZL : ℝ → ΩL × ΩL → Fin pL → ℝ := fun t x j =>
        (∑ i : Fin nL, ZSTL t x i j) + (∑ i : Fin mL, ZSSL t x i j)
      let rhoL : ℝ := rho PL nL mL pL (deltaL nL mL) muXL muYL XL YL FL GG
      let hlocL : (Fin pL → ℝ) → ℝ := fun w =>
        Set.indicator {w : Fin pL → ℝ |
            -(min phi1L phi2L)⁻¹ - 2 * ((min phi1L phi2L) * Real.log (pL : ℝ))⁻¹ <
                (⨆ j : Fin pL, (w j - yL j)) ∧
              (⨆ j : Fin pL, (w j - yL j)) ≤
                (min phi1L phi2L)⁻¹ + 2 * ((min phi1L phi2L) * Real.log (pL : ℝ))⁻¹}
          (fun _ => 1) w
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        ∫ x, hlocL (ZL t x) ∂(PL.prod PL) ≤ 2 * rhoL +
          Cb * ((min phi1L phi2L)⁻¹ + 2 * ((min phi1L phi2L) * Real.log (pL : ℝ))⁻¹) *
            Real.sqrt (Real.log (pL : ℝ)))
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi1 phi2 : ℝ) (y : Fin p → ℝ) (v : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
    (hd : delta n m ≠ 0)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
    (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hFcov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (hcomb : ∀ j : Fin p, Integrable (fun ω =>
      (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2) P)
    (hbound : ∀ j : Fin p, b ≤ ∫ ω,
      (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P)
    (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hp2 : 2 ≤ p) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
    let KAP : (Fin p → ℝ) → ℝ := fun w =>
      phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
        Real.log (∑ r : Fin p, Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w r - y r)))))
    let ZST : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
            Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - t) * (F i x.2 j - muX j))
    let ZSS : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i x.2 j - muY j))
    let ZC : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
      (∑ i : Fin n, ZST t x i j) + (∑ i : Fin m, ZSS t x i j)
    let ZD : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
    |∫ x : Ω × Ω, (∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j) ∂(P.prod P)|
      ≤ 1000000 * ((C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4 * (Real.sqrt (m : ℝ))⁻¹ *
          |delta n m| ^ 3 * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
          ((min phi1 phi2) ^ 2 * (Real.log (p : ℝ)) ^ 2 *
            (phi2 * (LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G) +
              LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
              min phi1 phi2 * Mstar P m (delta n m) muY Y G phi2)) := by
  /- @proof-region region.target-node.session.d04636c4d0dc09e5 begin -/
  classical
  intro b hb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
    Ckappa C1 C2 C3 Cb hCkappa hC1 hC3 hCb hG hQ hL
  intro Ω instΩ P instP n m p delta muX muY X Y F G phi1 phi2 y v
  intro hn hm hp hlogp hd hXm hYm hFm hGm hindep hXL2 hYL2 hX3 hY3 hF3 hG3
    hXmean hYmean hFcov hGcov hcomb hbound hphi1 hphi2 hv0 hv1 hp2 t ht0 ht1
  let KAP : (Fin p → ℝ) → ℝ := fun w =>
    phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
      Real.log (∑ r : Fin p, Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w r - y r)))))
  let ZST : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
          Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
        Real.sqrt (1 - t) * (F i x.2 j - muX j))
  let ZSS : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
          Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
        Real.sqrt (1 - t) * (G i x.2 j - muY j))
  let ZC : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
    (∑ i : Fin n, ZST t x i j) + (∑ i : Fin m, ZSS t x i j)
  let ZD : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
          Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))

  have hphi : 1 ≤ min phi1 phi2 := by
    rcases le_total phi1 phi2 with hle | hle
    · rwa [min_eq_left hle]
    · rwa [min_eq_right hle]
  obtain ⟨Q, hQnn, hQmaj, hQmass, hQbox⟩ := hQ p hp hlogp (min phi1 phi2) hphi y
  have hgrad : ∀ (w : Fin p → ℝ) (j : Fin p),
      |(fderiv ℝ (fun w' : Fin p → ℝ =>
          phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
            Real.log (∑ k : Fin p,
              Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w' k - y k)))))) w)
        (Pi.single j (1 : ℝ))| ≤ Ckappa * (min phi1 phi2) :=
    fun w j => hG p hp2 (min phi1 phi2) hphi y w j
  have hGcoord : ∀ (i : Fin m) (k : Fin p), Measurable (fun ω => G i ω k) :=
    fun i k => (measurable_pi_apply k).comp (hGm i)
  have hGzero : ∀ (i : Fin m) (j : Fin p), ∫ ω, (G i ω j - muY j) ∂P = 0 := by
    intro i j
    exact (statopia_math_node_204015260_c65710ba P p hp (fun ω k => G i ω k - muY k)
      (fun k => (hGcoord i k).sub measurable_const) (covY P muY Y i) (hGcov i) j).1
  have hGmint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j - muY j) P := by
    intro i j
    exact (statopia_math_node_204015260_c65710ba P p hp (fun ω k => G i ω k - muY k)
      (fun k => (hGcoord i k).sub measurable_const) (covY P muY Y i) (hGcov i) j).2.2
  have hGint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j) P := by
    intro i j
    have h2 : Integrable (fun ω => (G i ω j - muY j) + muY j) P :=
      (hGmint i j).add (integrable_const (muY j))
    simpa using h2
  have hGmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, G i ω j ∂P = muY j := by
    intro i j
    have hsplit : ∫ ω, G i ω j ∂P = (∫ ω, (G i ω j - muY j) ∂P) + (∫ ω, (muY j) ∂P) := by
      conv_lhs => rw [show (fun ω => G i ω j) = fun ω => (G i ω j - muY j) + muY j from by
        funext ω; ring]
      exact integral_add (hGmint i j) (integrable_const (muY j))
    have hc : (∫ ω, (muY j) ∂P) = muY j := by
      rw [integral_const]
      have h1 : P.real Set.univ = 1 := by simp
      rw [h1, one_smul]
    rw [hsplit, hGzero i j, hc, zero_add]
  have hYint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => Y i ω j) P := by
    intro i j
    exact (hYL2 i j).integrable (by norm_num)
  have hMstarmono : Mstar P m (delta n m) muY Y G (min phi1 phi2) ≤
      Mstar P m (delta n m) muY Y G phi2 :=
    statopia_math_node_3973197367_b91ba50f Ω P m p hlogp (delta n m) hd muY Y G hYm hGm hY3 hG3
      (min phi1 phi2) phi2 hphi (min_le_right phi1 phi2)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hminv : (0 : ℝ) ≤ (m : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hmR)
  have hphipos : (0 : ℝ) < min phi1 phi2 := lt_of_lt_of_le zero_lt_one hphi
  have hbetapos : 0 < min phi1 phi2 * Real.log (p : ℝ) := mul_pos hphipos hlogp
  have hLYnn : 0 ≤ LY P m muY Y := by
    unfold LY
    exact Real.iSup_nonneg (fun j =>
      mul_nonneg hminv (Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => by positivity))))
  have hrhonn : 0 ≤ rho P n m p (delta n m) muX muY X Y F G := by
    unfold rho
    exact Real.iSup_nonneg (fun v => Real.iSup_nonneg (fun y => abs_nonneg _))
  have hint_nn : ∀ (s : Set Ω) (g : Ω → ℝ) (ω : Ω), 0 ≤ g ω → 0 ≤ s.indicator g ω := by
    intro s g ω hg
    by_cases h : ω ∈ s
    · simpa [Set.indicator, h] using hg
    · simp [Set.indicator, h]
  have hmax3 : ∀ (f : Fin p → ℝ), (0 : ℝ) ≤ (maxAbs f) ^ 3 := by
    intro f
    unfold maxAbs
    exact pow_nonneg (Real.iSup_nonneg (fun j : Fin p => abs_nonneg (f j))) 3
  have hMYnn : 0 ≤ MY P m (delta n m) muY Y phi2 := by
    unfold MY
    rw [if_neg hd]
    refine mul_nonneg hminv (Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => ?_)))
    exact hint_nn _ (fun ω' => (maxAbs (fun j : Fin p => Y i ω' j - muY j)) ^ 3) ω
      (hmax3 _)
  have hMGnn : 0 ≤ MG P m (delta n m) muY G phi2 := by
    unfold MG
    rw [if_neg hd]
    refine mul_nonneg hminv (Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => ?_)))
    exact hint_nn _ (fun ω' => (maxAbs (fun j : Fin p => G i ω' j - muY j)) ^ 3) ω
      (hmax3 _)
  have hMstarnn : 0 ≤ Mstar P m (delta n m) muY Y G phi2 := by
    unfold Mstar
    exact add_nonneg hMYnn hMGnn
  have hAm : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω =>
      Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) := by
    intro i j
    have hY1 : Measurable (fun x : Ω × Ω => Y i x.1 j) :=
      ((measurable_pi_apply j).comp (hYm i)).comp measurable_fst
    have hG1 : Measurable (fun x : Ω × Ω => G i x.1 j) :=
      ((measurable_pi_apply j).comp (hGm i)).comp measurable_fst
    exact (measurable_const.mul (hY1.sub measurable_const)).add
      (measurable_const.mul (hG1.sub measurable_const))
  have hBm : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => G i x.2 j - muY j) := by
    intro i j
    exact (((measurable_pi_apply j).comp (hGm i)).comp measurable_snd).sub measurable_const
  have hZSSm : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i x.2 j - muY j))) := by
    intro i j
    exact measurable_const.mul
      ((measurable_const.mul (hAm i j)).add (measurable_const.mul (hBm i j)))
  have hZDm : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))) := by
    intro i j
    exact measurable_const.mul
      ((measurable_const.mul (hAm i j)).sub (measurable_const.mul (hBm i j)))
  have hphi_le_phi2 : min phi1 phi2 ≤ phi2 := min_le_right phi1 phi2
  have hbracket : 0 ≤ phi2 * (LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G) +
      LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
      min phi1 phi2 * Mstar P m (delta n m) muY Y G phi2 := by
    have h1 : 0 ≤ phi2 * (LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G) :=
      mul_nonneg (le_trans zero_le_one hphi2) (mul_nonneg hLYnn hrhonn)
    have h2 : 0 ≤ LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) :=
      mul_nonneg hLYnn (Real.sqrt_nonneg _)
    have h3 : 0 ≤ min phi1 phi2 * Mstar P m (delta n m) muY Y G phi2 :=
      mul_nonneg hphipos.le hMstarnn
    exact add_nonneg (add_nonneg h1 h2) h3

  have hE1 : ∀ (i : Fin m) (j k : Fin p),
      Integrable (fun x : Ω × Ω =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ)))
            (fun k' => ZC t x k' - ZSS t x i k')) (Pi.single k (1 : ℝ)) *
          ZSS t x i k * ZD t x i j) (P.prod P) ∧
        ∫ x, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ)))
            (fun k' => ZC t x k' - ZSS t x i k')) (Pi.single k (1 : ℝ)) *
          ZSS t x i k * ZD t x i j ∂(P.prod P) = 0 :=
    fun i j k =>
      statopia_math_node_3406556126_a8c6e89f Ω P n m p delta muX muY X Y F G phi1 phi2
        hphi1 hphi2 phi0 hphi0_cont hphi0_left hphi0_right hphi0_range y v hv0 hv1
        hn hm hp hlogp hXm hYm hFm hGm hindep hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3
        hFcov hGcov t ht0 ht1 i j k
  have hZrest_eq : ∀ (i : Fin m) (x : Ω × Ω),
      (fun k => ZC t x k - ZSS t x i k)
        = fun k => (∑ i' : Fin n, ZST t x i' k) +
            (∑ i' : Fin m, (if i' = i then (0 : ℝ) else ZSS t x i' k)) := by
    intro i x
    funext k
    have hT : (∑ i' : Fin m, ZSS t x i' k) - ZSS t x i k
        = ∑ i' : Fin m, (if i' = i then (0 : ℝ) else ZSS t x i' k) := by
      have h2 : ∀ i' : Fin m, (if i' = i then (0 : ℝ) else ZSS t x i' k)
          = ZSS t x i' k - (if i' = i then ZSS t x i' k else 0) := by
        intro i'
        by_cases h : i' = i <;> simp [h]
      have h3 : (∑ i' : Fin m, if i' = i then ZSS t x i' k else 0) = ZSS t x i k := by
        simp
      rw [Finset.sum_congr rfl (fun i' _ => h2 i'), Finset.sum_sub_distrib, h3]
    linarith [hT]
  have hE0 : ∀ (i : Fin m) (j : Fin p),
      (∫ x : Ω × Ω, (fderiv ℝ KAP (fun k => ZC t x k - ZSS t x i k))
          (Pi.single j (1 : ℝ)) * ZD t x i j ∂(P.prod P)) = 0 := by
    intro i j
    have h := statopia_math_node_4252936244_9b4dbd57 Ω P n m p delta muX muY X Y F G
      hn hm hp hlogp hd hXm hYm hFm hGm hindep hYmean hGmean hXL2 hYL2 hX3 hY3 hF3 hG3
      hFcov hGcov v hv0 hv1 phi1 phi2 hphi1 hphi2 y phi0 hphi0_cont hphi0_left
      hphi0_right hphi0_range t ht0 ht1 i j
    refine Eq.trans ?_ h.2.2.2
    apply integral_congr_ae
    filter_upwards with x
    simp only [hZrest_eq i x]
    rfl
  have hYdiffInt : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => Y i ω j - muY j) P :=
    fun i j => (hYint i j).sub (integrable_const (muY j))
  have hGdiffInt : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j - muY j) P :=
    fun i j => (hGint i j).sub (integrable_const (muY j))
  let ell : ℝ := Real.sqrt (m : ℝ) / (4 * |delta n m| * (min phi1 phi2 * Real.log (p : ℝ)))
  have hZSSβ : ∀ (i : Fin m) (x : Ω × Ω),
      (∀ r : Fin p, |Y i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.2 r - muY r| ≤ ell) →
      ∀ r : Fin p,
        |ZSS t x i r| * (min phi1 phi2 * Real.log (p : ℝ)) ≤ 3 / 4 := by
    intro i x h1 h2 h3 r
    have hA : |Y i x.1 r - muY r| ≤ ell := h1 r
    have hA' : |G i x.1 r - muY r| ≤ ell := h2 r
    have hB : |G i x.2 r - muY r| ≤ ell := h3 r
    have hsv : Real.sqrt v ≤ 1 := by simpa using Real.sqrt_le_sqrt hv1
    have hsv0 : (0 : ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
    have hsv' : Real.sqrt (1 - v) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) - v ≤ 1 by linarith)
    have hsv0' : (0 : ℝ) ≤ Real.sqrt (1 - v) := Real.sqrt_nonneg _
    have hst : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt (le_of_lt ht1)
    have hst0 : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    have hst' : Real.sqrt (1 - t) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) - t ≤ 1 by linarith)
    have hst0' : (0 : ℝ) ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
    have hX : |Real.sqrt v * (Y i x.1 r - muY r) +
        Real.sqrt (1 - v) * (G i x.1 r - muY r)| ≤ 2 * ell := by
      calc |Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)|
          ≤ |Real.sqrt v * (Y i x.1 r - muY r)| +
            |Real.sqrt (1 - v) * (G i x.1 r - muY r)| := abs_add_le _ _
        _ = Real.sqrt v * |Y i x.1 r - muY r| + Real.sqrt (1 - v) * |G i x.1 r - muY r| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hsv0']
        _ ≤ 1 * ell + 1 * ell :=
            add_le_add (mul_le_mul hsv hA (abs_nonneg _) zero_le_one)
              (mul_le_mul hsv' hA' (abs_nonneg _) zero_le_one)
        _ = 2 * ell := by ring
    have hinner : |Real.sqrt t *
          (Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)) +
          Real.sqrt (1 - t) * (G i x.2 r - muY r)| ≤ 3 * ell := by
      calc |Real.sqrt t *
            (Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)) +
            Real.sqrt (1 - t) * (G i x.2 r - muY r)|
          ≤ |Real.sqrt t *
              (Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r))| +
              |Real.sqrt (1 - t) * (G i x.2 r - muY r)| := abs_add_le _ _
        _ = Real.sqrt t *
              |Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)| +
              Real.sqrt (1 - t) * |G i x.2 r - muY r| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hst0, abs_of_nonneg hst0']
        _ ≤ 1 * (2 * ell) + 1 * ell :=
            add_le_add (mul_le_mul hst hX (abs_nonneg _) zero_le_one)
              (mul_le_mul hst' hB (abs_nonneg _) zero_le_one)
        _ = 3 * ell := by ring
    have hem0 : (0 : ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ :=
      le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hmR))
    have hellpos : 0 < ell := by
      have h1 : (0 : ℝ) < |delta n m| := abs_pos.mpr hd
      have h2 : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
      have h3 : (0 : ℝ) < 4 * |delta n m| * (min phi1 phi2 * Real.log (p : ℝ)) :=
        mul_pos (mul_pos (by norm_num) h1) hbetapos
      exact div_pos h2 h3
    have hZSSabs : |ZSS t x i r| ≤ (Real.sqrt (m : ℝ))⁻¹ * |delta n m| * (3 * ell) := by
      have hb : ZSS t x i r = (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 r - muY r) +
              Real.sqrt (1 - v) * (G i x.1 r - muY r)) +
            Real.sqrt (1 - t) * (G i x.2 r - muY r)) := rfl
      rw [hb, abs_mul, abs_mul, abs_of_nonneg hem0]
      exact mul_le_mul (le_refl _) hinner (abs_nonneg _) (mul_nonneg hem0 (abs_nonneg _))
    have hEq : (Real.sqrt (m : ℝ))⁻¹ * |delta n m| * (3 * ell) *
        (min phi1 phi2 * Real.log (p : ℝ)) = 3 / 4 := by
      have hem : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hmR)
      have hdabs : |delta n m| ≠ 0 := abs_ne_zero.mpr hd
      have hβ : (min phi1 phi2 * Real.log (p : ℝ)) ≠ 0 := ne_of_gt hbetapos
      have h4 : (4 : ℝ) * |delta n m| * (min phi1 phi2 * Real.log (p : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hdabs) hβ
      simp only [ell]
      field_simp [hem, hdabs, hβ, h4]
    calc |ZSS t x i r| * (min phi1 phi2 * Real.log (p : ℝ))
        ≤ ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| * (3 * ell)) *
            (min phi1 phi2 * Real.log (p : ℝ)) :=
          mul_le_mul hZSSabs (le_refl _) (le_of_lt hbetapos)
            (mul_nonneg (mul_nonneg hem0 (abs_nonneg _)) (by linarith [hellpos]))
      _ = 3 / 4 := hEq
  have hLoc : (∫ x : Ω × Ω, Set.indicator
        {w : Fin p → ℝ |
          -(min phi1 phi2)⁻¹ - 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹ <
              (⨆ j : Fin p, (w j - y j)) ∧
            (⨆ j : Fin p, (w j - y j)) ≤
              (min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹}
        (fun _ => (1 : ℝ)) (ZC t x) ∂(P.prod P)) ≤
      2 * rho P n m p (delta n m) muX muY X Y F G +
        Cb * ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹) *
          Real.sqrt (Real.log (p : ℝ)) :=
    hL Ω P n m p delta muX muY X Y F G phi1 phi2 y v hn hm hp hlogp hd hXm hYm hFm hGm
      hindep hXL2 hYL2 hX3 hY3 hF3 hG3 hXmean hYmean hFcov hGcov hcomb hbound
      hphi1 hphi2 hv0 hv1 t ⟨le_of_lt ht0, le_of_lt ht1⟩
  have hboxQ : ∀ (i : Fin m) (x : Ω × Ω),
      (∀ r : Fin p, |Y i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.2 r - muY r| ≤ ell) →
      ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ l k j : Fin p,
        Q l k j ((fun k' => ZC t x k' - ZSS t x i k') +
            (fun k' => s * ZSS t x i k')) ≤
          C3 * Q l k j (fun k' => ZC t x k' - ZSS t x i k') := by
    intro i x h1 h2 h3 s hs l k j
    refine hQbox l k j _ _ ?_
    intro r
    have hU : |ZSS t x i r| * (min phi1 phi2 * Real.log (p : ℝ)) ≤ 3 / 4 :=
      hZSSβ i x h1 h2 h3 r
    have hsabs : |s| ≤ 1 := by
      rw [abs_of_nonneg hs.1]
      exact hs.2
    have hprod : (|s| * |ZSS t x i r|) * (min phi1 phi2 * Real.log (p : ℝ)) ≤ 1 * (3 / 4) := by
      calc (|s| * |ZSS t x i r|) * (min phi1 phi2 * Real.log (p : ℝ))
          = |s| * (|ZSS t x i r| * (min phi1 phi2 * Real.log (p : ℝ))) := by ring
        _ ≤ 1 * (3 / 4) :=
            mul_le_mul hsabs hU (by positivity) zero_le_one
    rw [abs_mul]
    linarith
  have hboxQ2 : ∀ (i : Fin m) (x : Ω × Ω),
      (∀ r : Fin p, |Y i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.2 r - muY r| ≤ ell) →
      ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ l k j : Fin p,
        Q l k j ((fun k' => ZC t x k' - ZSS t x i k') +
            (fun k' => s * ZSS t x i k')) ≤
          C3 ^ 2 * Q l k j (ZC t x) := by
    intro i x h1 h2 h3 s hs l k j
    have hA := hboxQ i x h1 h2 h3 s hs l k j
    have hB : Q l k j (fun k' => ZC t x k' - ZSS t x i k') ≤ C3 * Q l k j (ZC t x) := by
      have hside : ∀ r : Fin p,
          |(fun k' => -ZSS t x i k') r| * (min phi1 phi2 * Real.log (p : ℝ)) ≤ 1 := by
        intro r
        have hU : |ZSS t x i r| * (min phi1 phi2 * Real.log (p : ℝ)) ≤ 3 / 4 :=
          hZSSβ i x h1 h2 h3 r
        have h2' : |(fun k' => -ZSS t x i k') r| = |ZSS t x i r| := by
          show |-ZSS t x i r| = |ZSS t x i r|
          exact abs_neg _
        rw [h2']
        linarith
      have hbb := hQbox l k j (ZC t x) (fun k' => -ZSS t x i k') hside
      simpa using hbb
    calc Q l k j ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => s * ZSS t x i k'))
        ≤ C3 * Q l k j (fun k' => ZC t x k' - ZSS t x i k') := hA
      _ ≤ C3 * (C3 * Q l k j (ZC t x)) :=
          mul_le_mul_of_nonneg_left hB (le_trans zero_le_one hC3)
      _ = C3 ^ 2 * Q l k j (ZC t x) := by ring
  have hAmX : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω =>
      Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) := by
    intro i j
    have hX1 : Measurable (fun x : Ω × Ω => X i x.1 j) :=
      ((measurable_pi_apply j).comp (hXm i)).comp measurable_fst
    have hF1 : Measurable (fun x : Ω × Ω => F i x.1 j) :=
      ((measurable_pi_apply j).comp (hFm i)).comp measurable_fst
    exact (measurable_const.mul (hX1.sub measurable_const)).add
      (measurable_const.mul (hF1.sub measurable_const))
  have hBmX : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => F i x.2 j - muX j) := by
    intro i j
    exact (((measurable_pi_apply j).comp (hFm i)).comp measurable_snd).sub measurable_const
  have hZSTm : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
            Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - t) * (F i x.2 j - muX j))) := by
    intro i j
    exact measurable_const.mul
      ((measurable_const.mul (hAmX i j)).add (measurable_const.mul (hBmX i j)))
  have hZCm : ∀ j : Fin p, Measurable (fun x : Ω × Ω => ZC t x j) := by
    intro j
    have h1 : Measurable (fun x : Ω × Ω => ∑ i : Fin n, ZST t x i j) :=
      Finset.measurable_sum Finset.univ (fun i _ => hZSTm i j)
    have h2 : Measurable (fun x : Ω × Ω => ∑ i : Fin m, ZSS t x i j) :=
      Finset.measurable_sum Finset.univ (fun i _ => hZSSm i j)
    exact h1.add h2
  have hUm : ∀ (i : Fin m) (j : Fin p),
      Measurable (fun x : Ω × Ω => (fun k => ZC t x k - ZSS t x i k) j) :=
    fun i j => (hZCm j).sub (hZSSm i j)
  have hZDcoorm : ∀ (i : Fin m) (j : Fin p),
      Measurable (fun x : Ω × Ω => ZD t x i j) :=
    fun i j => hZDm i j
  have hgoodmass : ∀ (i : Fin m) (x : Ω × Ω),
      (∀ r : Fin p, |Y i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.2 r - muY r| ≤ ell) →
      ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ j : Fin p,
        (∑ l : Fin p, ∑ k : Fin p,
            Q l k j ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => s * ZSS t x i k'))) ≤
          C3 ^ 2 * (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) := by
    intro i x h1 h2 h3 s hs j
    have hstep : ∀ l k : Fin p,
        Q l k j ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => s * ZSS t x i k')) ≤
          C3 ^ 2 * Q l k j (ZC t x) :=
      fun l k => hboxQ2 i x h1 h2 h3 s hs l k j
    have hsum1 : (∑ l : Fin p, ∑ k : Fin p,
          Q l k j ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => s * ZSS t x i k')))
        ≤ ∑ l : Fin p, ∑ k : Fin p, C3 ^ 2 * Q l k j (ZC t x) :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun k _ => hstep l k))
    have hsum2 : (∑ l : Fin p, ∑ k : Fin p, C3 ^ 2 * Q l k j (ZC t x))
        = C3 ^ 2 * (∑ l : Fin p, ∑ k : Fin p, Q l k j (ZC t x)) := by
      simp only [Finset.mul_sum]
    have hsum3 : (∑ l : Fin p, ∑ k : Fin p, Q l k j (ZC t x)) ≤
        C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := by
      have hmass := hQmass (ZC t x)
      have hinner : ∀ l : Fin p, (∑ k : Fin p, Q l k j (ZC t x)) ≤
          ∑ k : Fin p, ∑ c : Fin p, Q l k c (ZC t x) := by
        intro l
        exact Finset.sum_le_sum (fun k _ =>
          Finset.single_le_sum (fun c _ => hQnn l k c (ZC t x)) (Finset.mem_univ j))
      calc (∑ l : Fin p, ∑ k : Fin p, Q l k j (ZC t x))
          ≤ ∑ l : Fin p, ∑ k : Fin p, ∑ c : Fin p, Q l k c (ZC t x) :=
            Finset.sum_le_sum (fun l _ => hinner l)
        _ ≤ C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := hmass
    calc (∑ l : Fin p, ∑ k : Fin p,
          Q l k j ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => s * ZSS t x i k')))
        ≤ ∑ l : Fin p, ∑ k : Fin p, C3 ^ 2 * Q l k j (ZC t x) := hsum1
      _ = C3 ^ 2 * (∑ l : Fin p, ∑ k : Fin p, Q l k j (ZC t x)) := hsum2
      _ ≤ C3 ^ 2 * (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum3 (sq_nonneg C3)
  have hLYelem : ∀ r : Fin p,
      (m : ℝ)⁻¹ * ∑ i : Fin m, (∫ ω, |Y i ω r - muY r| ^ 3 ∂P) ≤ LY P m muY Y := by
    intro r
    have hbdd : BddAbove (Set.range (fun j : Fin p =>
        (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, |Y i ω j - muY j| ^ 3 ∂P)) :=
      (Set.finite_range (fun j : Fin p =>
        (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, |Y i ω j - muY j| ^ 3 ∂P)).bddAbove
    exact le_ciSup hbdd r
  have hY3bound : ∀ (i : Fin m) (r : Fin p),
      (∫ ω, |Y i ω r - muY r| ^ 3 ∂P) ≤ (m : ℝ) * LY P m muY Y := by
    intro i r
    have hsingle : (∫ ω, |Y i ω r - muY r| ^ 3 ∂P)
        ≤ ∑ i' : Fin m, ∫ ω, |Y i' ω r - muY r| ^ 3 ∂P :=
      Finset.single_le_sum (f := fun i' : Fin m => ∫ ω, |Y i' ω r - muY r| ^ 3 ∂P)
        (fun i' _ => integral_nonneg (fun ω => by positivity)) (Finset.mem_univ i)
    have hmul : (m : ℝ) * ((m : ℝ)⁻¹ * ∑ i' : Fin m, ∫ ω, |Y i' ω r - muY r| ^ 3 ∂P)
        = ∑ i' : Fin m, ∫ ω, |Y i' ω r - muY r| ^ 3 ∂P := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmR), one_mul]
    calc (∫ ω, |Y i ω r - muY r| ^ 3 ∂P)
        ≤ ∑ i' : Fin m, ∫ ω, |Y i' ω r - muY r| ^ 3 ∂P := hsingle
      _ = (m : ℝ) * ((m : ℝ)⁻¹ * ∑ i' : Fin m, ∫ ω, |Y i' ω r - muY r| ^ 3 ∂P) :=
          hmul.symm
      _ ≤ (m : ℝ) * LY P m muY Y :=
          mul_le_mul_of_nonneg_left (hLYelem r) (le_of_lt hmR)

  have habsSub : ∀ (a b : ℝ), |a - b| ≤ |a| + |b| := by
    intro a b
    have e : a - b = a + -b := by ring
    rw [e, ← abs_neg b]
    exact abs_add_le a (-b)
  have hZDβ : ∀ (i : Fin m) (x : Ω × Ω),
      (∀ r : Fin p, |Y i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.2 r - muY r| ≤ ell) →
      ∀ r : Fin p,
        |ZD t x i r| ≤ (Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
          ((2 * Real.sqrt t)⁻¹ * (2 * ell) + (2 * Real.sqrt (1 - t))⁻¹ * ell) := by
    intro i x h1 h2 h3 r
    have hYr : |Y i x.1 r - muY r| ≤ ell := h1 r
    have hGr : |G i x.1 r - muY r| ≤ ell := h2 r
    have hBr : |G i x.2 r - muY r| ≤ ell := h3 r
    have hsv : Real.sqrt v ≤ 1 := by simpa using Real.sqrt_le_sqrt hv1
    have hsv0 : (0 : ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
    have hsv' : Real.sqrt (1 - v) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) - v ≤ 1 by linarith)
    have hsv0' : (0 : ℝ) ≤ Real.sqrt (1 - v) := Real.sqrt_nonneg _
    have hX : |Real.sqrt v * (Y i x.1 r - muY r) +
        Real.sqrt (1 - v) * (G i x.1 r - muY r)| ≤ 2 * ell := by
      calc |Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)|
          ≤ |Real.sqrt v * (Y i x.1 r - muY r)| +
            |Real.sqrt (1 - v) * (G i x.1 r - muY r)| := abs_add_le _ _
        _ = Real.sqrt v * |Y i x.1 r - muY r| + Real.sqrt (1 - v) * |G i x.1 r - muY r| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hsv0']
        _ ≤ 1 * ell + 1 * ell :=
            add_le_add (mul_le_mul hsv hYr (abs_nonneg _) zero_le_one)
              (mul_le_mul hsv' hGr (abs_nonneg _) zero_le_one)
        _ = 2 * ell := by ring
    have hpt : (0 : ℝ) ≤ (2 * Real.sqrt t)⁻¹ :=
      le_of_lt (inv_pos.mpr (by have := Real.sqrt_pos.mpr ht0; linarith))
    have hpt' : (0 : ℝ) ≤ (2 * Real.sqrt (1 - t))⁻¹ :=
      le_of_lt (inv_pos.mpr (by have := Real.sqrt_pos.mpr (sub_pos.mpr ht1); linarith))
    have hem0 : (0 : ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ :=
      le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hmR))
    have hb0 : ZD t x i r = (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 r - muY r) +
            Real.sqrt (1 - v) * (G i x.1 r - muY r)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 r - muY r)) := rfl
    rw [hb0, abs_mul, abs_mul, abs_of_nonneg hem0]
    refine mul_le_mul (le_refl _) ?_ (abs_nonneg _) (mul_nonneg hem0 (abs_nonneg _))
    calc |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 r - muY r) +
            Real.sqrt (1 - v) * (G i x.1 r - muY r)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 r - muY r)|
        ≤ |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 r - muY r) +
            Real.sqrt (1 - v) * (G i x.1 r - muY r))| +
          |(2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 r - muY r)| := habsSub _ _
      _ = (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (Y i x.1 r - muY r) +
            Real.sqrt (1 - v) * (G i x.1 r - muY r)| +
          (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 r - muY r| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hpt, abs_of_nonneg hpt']
      _ ≤ (2 * Real.sqrt t)⁻¹ * (2 * ell) + (2 * Real.sqrt (1 - t))⁻¹ * ell :=
          add_le_add (mul_le_mul_of_nonneg_left hX hpt) (mul_le_mul_of_nonneg_left hBr hpt')
  let LG : ℝ := ⨆ j : Fin p, (m : ℝ)⁻¹ * ∑ i : Fin m, (∫ ω, |G i ω j - muY j| ^ 3 ∂P)
  have hLGelem : ∀ r : Fin p,
      (m : ℝ)⁻¹ * ∑ i : Fin m, (∫ ω, |G i ω r - muY r| ^ 3 ∂P) ≤ LG := by
    intro r
    have hbdd : BddAbove (Set.range (fun j : Fin p =>
        (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, |G i ω j - muY j| ^ 3 ∂P)) :=
      (Set.finite_range (fun j : Fin p =>
        (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, |G i ω j - muY j| ^ 3 ∂P)).bddAbove
    exact le_ciSup hbdd r
  have hG3bound : ∀ (i : Fin m) (r : Fin p),
      (∫ ω, |G i ω r - muY r| ^ 3 ∂P) ≤ (m : ℝ) * LG := by
    intro i r
    have hsingle : (∫ ω, |G i ω r - muY r| ^ 3 ∂P)
        ≤ ∑ i' : Fin m, ∫ ω, |G i' ω r - muY r| ^ 3 ∂P :=
      Finset.single_le_sum (f := fun i' : Fin m => ∫ ω, |G i' ω r - muY r| ^ 3 ∂P)
        (fun i' _ => integral_nonneg (fun ω => by positivity)) (Finset.mem_univ i)
    have hmul : (m : ℝ) * ((m : ℝ)⁻¹ * ∑ i' : Fin m, ∫ ω, |G i' ω r - muY r| ^ 3 ∂P)
        = ∑ i' : Fin m, ∫ ω, |G i' ω r - muY r| ^ 3 ∂P := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmR), one_mul]
    calc (∫ ω, |G i ω r - muY r| ^ 3 ∂P)
        ≤ ∑ i' : Fin m, ∫ ω, |G i' ω r - muY r| ^ 3 ∂P := hsingle
      _ = (m : ℝ) * ((m : ℝ)⁻¹ * ∑ i' : Fin m, ∫ ω, |G i' ω r - muY r| ^ 3 ∂P) :=
          hmul.symm
      _ ≤ (m : ℝ) * LG := mul_le_mul_of_nonneg_left (hLGelem r) (le_of_lt hmR)
  have hZCmeas : Measurable (fun x : Ω × Ω => ZC t x) := measurable_pi_iff.mpr hZCm
  have hWmeas : ∀ i : Fin m,
      Measurable (fun x : Ω × Ω => (fun k => ZC t x k - ZSS t x i k)) :=
    fun i => measurable_pi_iff.mpr (hUm i)
  have hmoment : ∀ (i : Fin m) (j k l : Fin p),
      Integrable (fun x : Ω × Ω => |ZSS t x i k * ZSS t x i l * ZD t x i j|) (P.prod P) ∧
        (∫ x : Ω × Ω, |ZSS t x i k * ZSS t x i l * ZD t x i j| ∂(P.prod P))
          ≤ (1 / 2) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3 * |delta n m| ^ 3 *
              ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
              (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) := by
    intro i j k l
    exact statopia_math_node_2105095423_f9567069 p Ω P m hm (delta n m) hd t ht0 ht1 v hv0 hv1
      muY (Y i) (G i)
      (fun r => (measurable_pi_apply r).comp (hYm i))
      (fun r => (measurable_pi_apply r).comp (hGm i))
      ((m : ℝ) * LY P m muY Y) ((m : ℝ) * LG)
      (fun r => ⟨hY3 i r, hY3bound i r, hG3 i r, hG3bound i r⟩) j k l
  have hcoord : ∀ (f : Fin p → ℝ) (r : Fin p), |f r| ≤ maxAbs f := by
    intro f r
    have hbdd : BddAbove (Set.range (fun j : Fin p => |f j|)) :=
      (Set.finite_range (fun j : Fin p => |f j|)).bddAbove
    exact le_ciSup hbdd r
  have hcoordY : ∀ (i : Fin m) (ω : Ω) (r : Fin p),
      |Y i ω r - muY r| ≤ maxAbs (fun j : Fin p => Y i ω j - muY j) :=
    fun i ω r => hcoord (fun j : Fin p => Y i ω j - muY j) r
  have hcoordG : ∀ (i : Fin m) (ω : Ω) (r : Fin p),
      |G i ω r - muY r| ≤ maxAbs (fun j : Fin p => G i ω j - muY j) :=
    fun i ω r => hcoord (fun j : Fin p => G i ω j - muY j) r
  have hZSSmax : ∀ (i : Fin m) (x : Ω × Ω) (r : Fin p),
      |ZSS t x i r| ≤ (Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
        (maxAbs (fun j : Fin p => Y i x.1 j - muY j) +
          maxAbs (fun j : Fin p => G i x.1 j - muY j) +
          maxAbs (fun j : Fin p => G i x.2 j - muY j)) := by
    intro i x r
    have hA : |Y i x.1 r - muY r| ≤ maxAbs (fun j : Fin p => Y i x.1 j - muY j) :=
      hcoordY i x.1 r
    have hA' : |G i x.1 r - muY r| ≤ maxAbs (fun j : Fin p => G i x.1 j - muY j) :=
      hcoordG i x.1 r
    have hB : |G i x.2 r - muY r| ≤ maxAbs (fun j : Fin p => G i x.2 j - muY j) :=
      hcoordG i x.2 r
    have hsv : Real.sqrt v ≤ 1 := by simpa using Real.sqrt_le_sqrt hv1
    have hsv0 : (0 : ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
    have hsv' : Real.sqrt (1 - v) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) - v ≤ 1 by linarith)
    have hsv0' : (0 : ℝ) ≤ Real.sqrt (1 - v) := Real.sqrt_nonneg _
    have hst : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt (le_of_lt ht1)
    have hst0 : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    have hst' : Real.sqrt (1 - t) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) - t ≤ 1 by linarith)
    have hst0' : (0 : ℝ) ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
    have h1 : |Real.sqrt v * (Y i x.1 r - muY r) +
        Real.sqrt (1 - v) * (G i x.1 r - muY r)|
        ≤ maxAbs (fun j : Fin p => Y i x.1 j - muY j) +
          maxAbs (fun j : Fin p => G i x.1 j - muY j) := by
      calc |Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)|
          ≤ |Real.sqrt v * (Y i x.1 r - muY r)| +
            |Real.sqrt (1 - v) * (G i x.1 r - muY r)| := abs_add_le _ _
        _ = Real.sqrt v * |Y i x.1 r - muY r| + Real.sqrt (1 - v) * |G i x.1 r - muY r| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hsv0']
        _ ≤ 1 * maxAbs (fun j : Fin p => Y i x.1 j - muY j) +
              1 * maxAbs (fun j : Fin p => G i x.1 j - muY j) :=
            add_le_add (mul_le_mul hsv hA (abs_nonneg _) zero_le_one)
              (mul_le_mul hsv' hA' (abs_nonneg _) zero_le_one)
        _ = maxAbs (fun j : Fin p => Y i x.1 j - muY j) +
              maxAbs (fun j : Fin p => G i x.1 j - muY j) := by ring
    have hinner : |Real.sqrt t *
          (Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)) +
          Real.sqrt (1 - t) * (G i x.2 r - muY r)|
        ≤ maxAbs (fun j : Fin p => Y i x.1 j - muY j) +
          maxAbs (fun j : Fin p => G i x.1 j - muY j) +
          maxAbs (fun j : Fin p => G i x.2 j - muY j) := by
      calc |Real.sqrt t *
            (Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)) +
            Real.sqrt (1 - t) * (G i x.2 r - muY r)|
          ≤ |Real.sqrt t *
              (Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r))| +
              |Real.sqrt (1 - t) * (G i x.2 r - muY r)| := abs_add_le _ _
        _ = Real.sqrt t *
              |Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)| +
              Real.sqrt (1 - t) * |G i x.2 r - muY r| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hst0, abs_of_nonneg hst0']
        _ ≤ 1 * (maxAbs (fun j : Fin p => Y i x.1 j - muY j) +
              maxAbs (fun j : Fin p => G i x.1 j - muY j)) +
              1 * maxAbs (fun j : Fin p => G i x.2 j - muY j) :=
            add_le_add (mul_le_mul hst h1 (abs_nonneg _) zero_le_one)
              (mul_le_mul hst' hB (abs_nonneg _) zero_le_one)
        _ = maxAbs (fun j : Fin p => Y i x.1 j - muY j) +
              maxAbs (fun j : Fin p => G i x.1 j - muY j) +
              maxAbs (fun j : Fin p => G i x.2 j - muY j) := by ring
    have hem0 : (0 : ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ :=
      le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hmR))
    have hb : ZSS t x i r = (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 r - muY r) +
            Real.sqrt (1 - v) * (G i x.1 r - muY r)) +
          Real.sqrt (1 - t) * (G i x.2 r - muY r)) := rfl
    rw [hb, abs_mul, abs_mul, abs_of_nonneg hem0]
    exact mul_le_mul (le_refl _) hinner (abs_nonneg _) (mul_nonneg hem0 (abs_nonneg _))
  have hsqrtmul : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hmR)
  have hsqrtne : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hmR)
  have hsqrtcube : (m : ℝ) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3 = (Real.sqrt (m : ℝ))⁻¹ := by
    calc (m : ℝ) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3
        = (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) *
            ((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹) := by
          rw [hsqrtmul]
          ring
      _ = (Real.sqrt (m : ℝ) * (Real.sqrt (m : ℝ))⁻¹) *
            (Real.sqrt (m : ℝ) * (Real.sqrt (m : ℝ))⁻¹) * (Real.sqrt (m : ℝ))⁻¹ := by ring
      _ = (Real.sqrt (m : ℝ))⁻¹ := by
          rw [mul_inv_cancel₀ hsqrtne]
          ring
  have hmomentSum : ∀ (j k l : Fin p),
      (∑ i : Fin m, ∫ x : Ω × Ω, |ZSS t x i k * ZSS t x i l * ZD t x i j| ∂(P.prod P))
        ≤ (1 / 2) * ((Real.sqrt (m : ℝ))⁻¹) * |delta n m| ^ 3 *
            ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
            (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) := by
    intro j k l
    have h2 : (∑ _i : Fin m, (1 / 2) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3 * |delta n m| ^ 3 *
          ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
          (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))))
        = (1 / 2) * ((m : ℝ) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3) * |delta n m| ^ 3 *
          ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
          (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have h4 : (1 / 2) * ((m : ℝ) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3) * |delta n m| ^ 3 *
          ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
          (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG)))
        = (1 / 2) * ((Real.sqrt (m : ℝ))⁻¹) * |delta n m| ^ 3 *
            ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
            (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) := by
      rw [hsqrtcube]
    calc (∑ i : Fin m, ∫ x : Ω × Ω, |ZSS t x i k * ZSS t x i l * ZD t x i j| ∂(P.prod P))
        ≤ ∑ _i : Fin m, (1 / 2) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3 * |delta n m| ^ 3 *
            ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
            (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) :=
          Finset.sum_le_sum (fun i _ => (hmoment i j k l).2)
      _ = (1 / 2) * ((m : ℝ) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3) * |delta n m| ^ 3 *
            ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
            (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) := h2
      _ = (1 / 2) * ((Real.sqrt (m : ℝ))⁻¹) * |delta n m| ^ 3 *
            ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
            (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) := h4
  have hLGnn : 0 ≤ LG := by
    show (0 : ℝ) ≤ ⨆ j : Fin p, (m : ℝ)⁻¹ * ∑ i : Fin m, (∫ ω, |G i ω j - muY j| ^ 3 ∂P)
    exact Real.iSup_nonneg (fun j =>
      mul_nonneg hminv (Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => by positivity))))
  have hmomnn : 0 ≤ (1 / 2) * ((Real.sqrt (m : ℝ))⁻¹) * |delta n m| ^ 3 *
      ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
      (27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) := by
    have h1 : (0 : ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ :=
      le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hmR))
    have h2 : (0 : ℝ) ≤ |delta n m| ^ 3 := by positivity
    have h3 : (0 : ℝ) ≤ (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹ :=
      add_nonneg (le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr ht0)))
        (le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr ht1))))
    have h4 : (0 : ℝ) ≤ (m : ℝ) * LY P m muY Y := mul_nonneg (le_of_lt hmR) hLYnn
    have h5 : (0 : ℝ) ≤ (m : ℝ) * LG := mul_nonneg (le_of_lt hmR) hLGnn
    have h6 : (0 : ℝ) ≤ 27 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG)) :=
      mul_nonneg (by norm_num) (add_nonneg h4 (mul_nonneg (by norm_num) h5))
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3) h6
  have hellmul : ell * (4 * |delta n m| * (min phi1 phi2 * Real.log (p : ℝ))) =
      Real.sqrt (m : ℝ) := by
    have hdabs : |delta n m| ≠ 0 := ne_of_gt (abs_pos.mpr hd)
    have hβ : (min phi1 phi2 * Real.log (p : ℝ)) ≠ 0 := ne_of_gt hbetapos
    have h4 : (4 : ℝ) * |delta n m| * (min phi1 phi2 * Real.log (p : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hdabs) hβ
    exact div_mul_cancel₀ (Real.sqrt (m : ℝ)) h4
  have hthreshpos : 0 < Real.sqrt (m : ℝ) / (4 * |delta n m| * phi2 * Real.log (p : ℝ)) := by
    have h1 : (0 : ℝ) < |delta n m| := abs_pos.mpr hd
    have h2 : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
    have hphi2pos : (0 : ℝ) < phi2 := lt_of_lt_of_le zero_lt_one hphi2
    have h3 : (0 : ℝ) < 4 * |delta n m| * phi2 * Real.log (p : ℝ) :=
      mul_pos (mul_pos (mul_pos (by norm_num) h1) hphi2pos) hlogp
    exact div_pos h2 h3
  have hZSSmaxβ : ∀ (i : Fin m) (x : Ω × Ω) (r : Fin p),
      |ZSS t x i r| * (min phi1 phi2 * Real.log (p : ℝ)) ≤
        (Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
          (maxAbs (fun j : Fin p => Y i x.1 j - muY j) +
            maxAbs (fun j : Fin p => G i x.1 j - muY j) +
            maxAbs (fun j : Fin p => G i x.2 j - muY j)) *
          (min phi1 phi2 * Real.log (p : ℝ)) :=
    fun i x r => mul_le_mul_of_nonneg_right (hZSSmax i x r) hbetapos.le
  have hellpos' : 0 < ell := by
    have h1 : (0 : ℝ) < |delta n m| := abs_pos.mpr hd
    have h2 : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
    have h3 : (0 : ℝ) < 4 * |delta n m| * (min phi1 phi2 * Real.log (p : ℝ)) :=
      mul_pos (mul_pos (by norm_num) h1) hbetapos
    exact div_pos h2 h3
  have hD1le : 4 * |delta n m| * (min phi1 phi2 * Real.log (p : ℝ)) ≤
      4 * |delta n m| * phi2 * Real.log (p : ℝ) := by
    have h4 : (0 : ℝ) ≤ 4 * |delta n m| := mul_nonneg (by norm_num) (abs_nonneg _)
    have hlogp' : (0 : ℝ) ≤ Real.log (p : ℝ) := le_of_lt hlogp
    calc 4 * |delta n m| * (min phi1 phi2 * Real.log (p : ℝ))
        ≤ 4 * |delta n m| * (phi2 * Real.log (p : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hphi_le_phi2 hlogp') h4
      _ = 4 * |delta n m| * phi2 * Real.log (p : ℝ) := by ring
  have hsqrt_le : Real.sqrt (m : ℝ) ≤
      ell * (4 * |delta n m| * phi2 * Real.log (p : ℝ)) := by
    rw [← hellmul]
    exact mul_le_mul_of_nonneg_left hD1le hellpos'.le
  have hbad_split : ∀ (i : Fin m) (x : Ω × Ω),
      ¬ ((∀ r : Fin p, |Y i x.1 r - muY r| ≤ ell) ∧
          (∀ r : Fin p, |G i x.1 r - muY r| ≤ ell) ∧
          (∀ r : Fin p, |G i x.2 r - muY r| ≤ ell)) →
        (∃ r : Fin p, ell < |Y i x.1 r - muY r|) ∨
          (∃ r : Fin p, ell < |G i x.1 r - muY r|) ∨
          (∃ r : Fin p, ell < |G i x.2 r - muY r|) := by
    intro i x h
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2, h3⟩ := hc
    exact h ⟨h1, h2, h3⟩
  have hbadY : ∀ (i : Fin m) (ω : Ω),
      ell < maxAbs (fun j : Fin p => Y i ω j - muY j) →
      Real.sqrt (m : ℝ) < maxAbs (fun j : Fin p => Y i ω j - muY j) *
        (4 * |delta n m| * phi2 * Real.log (p : ℝ)) := by
    intro i ω h
    have hphi2pos : (0 : ℝ) < phi2 := lt_of_lt_of_le zero_lt_one hphi2
    have h1 : (0 : ℝ) < |delta n m| := abs_pos.mpr hd
    have hDpos : (0 : ℝ) < 4 * |delta n m| * phi2 * Real.log (p : ℝ) :=
      mul_pos (mul_pos (mul_pos (by norm_num) h1) hphi2pos) hlogp
    calc Real.sqrt (m : ℝ) ≤ ell * (4 * |delta n m| * phi2 * Real.log (p : ℝ)) := hsqrt_le
      _ < maxAbs (fun j : Fin p => Y i ω j - muY j) *
            (4 * |delta n m| * phi2 * Real.log (p : ℝ)) :=
          mul_lt_mul_of_pos_right h hDpos
  have hbadYthresh : ∀ (i : Fin m) (ω : Ω),
      Real.sqrt (m : ℝ) / (4 * |delta n m| * phi2 * Real.log (p : ℝ)) <
        maxAbs (fun j : Fin p => Y i ω j - muY j) →
      Real.sqrt (m : ℝ) < maxAbs (fun j : Fin p => Y i ω j - muY j) *
        (4 * |delta n m| * phi2 * Real.log (p : ℝ)) := by
    intro i ω h
    have hphi2pos : (0 : ℝ) < phi2 := lt_of_lt_of_le zero_lt_one hphi2
    have h1 : (0 : ℝ) < |delta n m| := abs_pos.mpr hd
    have hDpos : (0 : ℝ) < 4 * |delta n m| * phi2 * Real.log (p : ℝ) :=
      mul_pos (mul_pos (mul_pos (by norm_num) h1) hphi2pos) hlogp
    have h2 : Real.sqrt (m : ℝ) / (4 * |delta n m| * phi2 * Real.log (p : ℝ)) *
        (4 * |delta n m| * phi2 * Real.log (p : ℝ)) <
        maxAbs (fun j : Fin p => Y i ω j - muY j) *
          (4 * |delta n m| * phi2 * Real.log (p : ℝ)) :=
      mul_lt_mul_of_pos_right h hDpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h2
  have hbadGthresh : ∀ (i : Fin m) (ω : Ω),
      Real.sqrt (m : ℝ) / (4 * |delta n m| * phi2 * Real.log (p : ℝ)) <
        maxAbs (fun j : Fin p => G i ω j - muY j) →
      Real.sqrt (m : ℝ) < maxAbs (fun j : Fin p => G i ω j - muY j) *
        (4 * |delta n m| * phi2 * Real.log (p : ℝ)) := by
    intro i ω h
    have hphi2pos : (0 : ℝ) < phi2 := lt_of_lt_of_le zero_lt_one hphi2
    have h1 : (0 : ℝ) < |delta n m| := abs_pos.mpr hd
    have hDpos : (0 : ℝ) < 4 * |delta n m| * phi2 * Real.log (p : ℝ) :=
      mul_pos (mul_pos (mul_pos (by norm_num) h1) hphi2pos) hlogp
    have h2 : Real.sqrt (m : ℝ) / (4 * |delta n m| * phi2 * Real.log (p : ℝ)) *
        (4 * |delta n m| * phi2 * Real.log (p : ℝ)) <
        maxAbs (fun j : Fin p => G i ω j - muY j) *
          (4 * |delta n m| * phi2 * Real.log (p : ℝ)) :=
      mul_lt_mul_of_pos_right h hDpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h2
  have hQmajKAP : ∀ (w : Fin p → ℝ) (j k l : Fin p),
      |(iteratedFDeriv ℝ 3 KAP w)
          (fun t : Fin 3 => Pi.single ((![j, k, l] : Fin 3 → Fin p) t) (1 : ℝ))| ≤
        Q j k l w :=
    fun w j k l => hQmaj j k l w
  have hQmajGood : ∀ (i : Fin m) (x : Ω × Ω),
      (∀ r : Fin p, |Y i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.1 r - muY r| ≤ ell) →
      (∀ r : Fin p, |G i x.2 r - muY r| ≤ ell) →
      ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ l k j : Fin p,
        |(iteratedFDeriv ℝ 3 KAP
            ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => s * ZSS t x i k')))
            (fun t : Fin 3 => Pi.single ((![l, k, j] : Fin 3 → Fin p) t) (1 : ℝ))| ≤
          C3 ^ 2 * Q l k j (ZC t x) := by
    intro i x h1 h2 h3 s hs l k j
    exact le_trans (hQmajKAP _ l k j) (hboxQ2 i x h1 h2 h3 s hs l k j)
  have hXdiffInt : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => X i ω j - muX j) P :=
    fun i j => ((hXL2 i j).integrable (by norm_num)).sub (integrable_const (muX j))
  have hYdiffIntP : ∀ (i : Fin m) (j : Fin p),
      Integrable (fun x : Ω × Ω => Y i x.1 j - muY j) (P.prod P) :=
    fun i j => (hYdiffInt i j).comp_fst P
  have hGdiffIntP : ∀ (i : Fin m) (j : Fin p),
      Integrable (fun x : Ω × Ω => G i x.1 j - muY j) (P.prod P) :=
    fun i j => (hGdiffInt i j).comp_fst P
  have hXdiffIntP : ∀ (i : Fin n) (j : Fin p),
      Integrable (fun x : Ω × Ω => X i x.1 j - muX j) (P.prod P) :=
    fun i j => (hXdiffInt i j).comp_fst P
  have hQmajSum : ∀ (j : Fin p) (w : Fin p → ℝ),
      (∑ l : Fin p, ∑ k : Fin p,
          |(iteratedFDeriv ℝ 3 KAP w)
            (fun t : Fin 3 => Pi.single ((![l, k, j] : Fin 3 → Fin p) t) (1 : ℝ))|) ≤
        C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := by
    intro j w
    have h1 : (∑ l : Fin p, ∑ k : Fin p,
        |(iteratedFDeriv ℝ 3 KAP w)
          (fun t : Fin 3 => Pi.single ((![l, k, j] : Fin 3 → Fin p) t) (1 : ℝ))|) ≤
        ∑ l : Fin p, ∑ k : Fin p, Q l k j w :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun k _ => hQmajKAP w l k j))
    refine le_trans h1 ?_
    have hmass := hQmass w
    have hinner : ∀ l : Fin p,
        (∑ k : Fin p, Q l k j w) ≤ ∑ k : Fin p, ∑ c : Fin p, Q l k c w := by
      intro l
      exact Finset.sum_le_sum (fun k _ =>
        Finset.single_le_sum (fun c _ => hQnn l k c w) (Finset.mem_univ j))
    calc (∑ l : Fin p, ∑ k : Fin p, Q l k j w)
        ≤ ∑ l : Fin p, ∑ k : Fin p, ∑ c : Fin p, Q l k c w :=
          Finset.sum_le_sum (fun l _ => hinner l)
      _ ≤ C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := hmass
  have hGmemDiff : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => G i ω j - muY j) 2 P := by
    intro i j
    exact (statopia_math_node_204015260_c65710ba P p hp (fun ω k => G i ω k - muY k)
      (fun k => (hGcoord i k).sub measurable_const) (covY P muY Y i) (hGcov i) j).2.1
  have hGdiffIntP2 : ∀ (i : Fin m) (j : Fin p),
      Integrable (fun x : Ω × Ω => G i x.2 j - muY j) (P.prod P) :=
    fun i j => ((hGmemDiff i j).comp_snd P).integrable (by norm_num)
  have hZSSint : ∀ (i : Fin m) (j : Fin p),
      Integrable (fun x : Ω × Ω => ZSS t x i j) (P.prod P) := by
    intro i j
    have hA : Integrable (fun x : Ω × Ω => Real.sqrt v * (Y i x.1 j - muY j)) (P.prod P) :=
      (hYdiffIntP i j).const_mul (Real.sqrt v)
    have hA' : Integrable (fun x : Ω × Ω => Real.sqrt (1 - v) * (G i x.1 j - muY j)) (P.prod P) :=
      (hGdiffIntP i j).const_mul (Real.sqrt (1 - v))
    have hB : Integrable (fun x : Ω × Ω => Real.sqrt (1 - t) * (G i x.2 j - muY j)) (P.prod P) :=
      (hGdiffIntP2 i j).const_mul (Real.sqrt (1 - t))
    have hbr : Integrable (fun x : Ω × Ω =>
        Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i x.2 j - muY j)) (P.prod P) :=
      ((hA.add hA').const_mul (Real.sqrt t)).add hB
    exact hbr.const_mul ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
  have hZDint : ∀ (i : Fin m) (j : Fin p),
      Integrable (fun x : Ω × Ω => ZD t x i j) (P.prod P) := by
    intro i j
    have hA : Integrable (fun x : Ω × Ω => Real.sqrt v * (Y i x.1 j - muY j)) (P.prod P) :=
      (hYdiffIntP i j).const_mul (Real.sqrt v)
    have hA' : Integrable (fun x : Ω × Ω => Real.sqrt (1 - v) * (G i x.1 j - muY j)) (P.prod P) :=
      (hGdiffIntP i j).const_mul (Real.sqrt (1 - v))
    have hB : Integrable (fun x : Ω × Ω =>
        (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)) (P.prod P) :=
      (hGdiffIntP2 i j).const_mul ((2 * Real.sqrt (1 - t))⁻¹)
    have hbr : Integrable (fun x : Ω × Ω =>
        (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)) (P.prod P) :=
      ((hA.add hA').const_mul ((2 * Real.sqrt t)⁻¹)).sub hB
    exact hbr.const_mul ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
  have hKAPcontDiff : ContDiff ℝ 3 KAP :=
    (statopia_math_node_2194576110_d2ad0cef p hp2 (min phi1 phi2) hphi phi0 hphi0_cont
      hphi0_left hphi0_right hphi0_range y).1
  have hgradMeasW : ∀ (w : Ω × Ω → Fin p → ℝ), Measurable w → ∀ j : Fin p,
      Measurable (fun x : Ω × Ω => (fderiv ℝ KAP (w x)) (Pi.single j (1 : ℝ))) := by
    intro w hw j
    have hcont : Continuous fun q : (Fin p → ℝ) × (Fin p → ℝ) =>
        (fderiv ℝ KAP q.1) q.2 :=
      hKAPcontDiff.continuous_fderiv_apply (by simp)
    have hmk : Measurable fun x : Ω × Ω => (w x, (Pi.single j (1 : ℝ) : Fin p → ℝ)) :=
      hw.prod measurable_const
    exact hcont.measurable.comp hmk
  have hgradBd : ∀ (j : Fin p) (w : Fin p → ℝ),
      ‖(fderiv ℝ KAP w) (Pi.single j (1 : ℝ))‖ ≤ Ckappa * (min phi1 phi2) := by
    intro j w
    rw [Real.norm_eq_abs]
    exact hgrad w j
  have hInt2 : ∀ (i : Fin m) (j : Fin p),
      Integrable (fun x : Ω × Ω =>
        (fderiv ℝ KAP (fun k' => ZC t x k' - ZSS t x i k')) (Pi.single j (1 : ℝ)) *
          ZD t x i j) (P.prod P) := by
    intro i j
    have hm : Measurable (fun x : Ω × Ω => (fderiv ℝ KAP
        (fun k' => ZC t x k' - ZSS t x i k')) (Pi.single j (1 : ℝ))) :=
      hgradMeasW _ (hWmeas i) j
    refine (hZDint i j).bdd_mul (c := Ckappa * min phi1 phi2) hm.aestronglyMeasurable ?_
    filter_upwards with x
    exact hgradBd j _
  have hInt1 : ∀ (i : Fin m) (j : Fin p),
      Integrable (fun x : Ω × Ω =>
        (fderiv ℝ KAP ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => ZSS t x i k')))
            (Pi.single j (1 : ℝ)) * ZD t x i j) (P.prod P) := by
    intro i j
    have hWU : Measurable (fun x : Ω × Ω =>
        (fun k' => ZC t x k' - ZSS t x i k') + (fun k' => ZSS t x i k')) :=
      (hWmeas i).add (measurable_pi_iff.mpr (hZSSm i))
    have hm : Measurable (fun x : Ω × Ω => (fderiv ℝ KAP
        ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => ZSS t x i k')))
          (Pi.single j (1 : ℝ))) :=
      hgradMeasW _ hWU j
    refine (hZDint i j).bdd_mul (c := Ckappa * min phi1 phi2) hm.aestronglyMeasurable ?_
    filter_upwards with x
    exact hgradBd j _
  have hInt3 : ∀ (i : Fin m) (j k : Fin p),
      Integrable (fun x : Ω × Ω =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ)))
            (fun k' => ZC t x k' - ZSS t x i k')) (Pi.single k (1 : ℝ)) *
          ZSS t x i k * ZD t x i j) (P.prod P) :=
    fun i j k => (hE1 i j k).1
  have hC12nn : 0 ≤ C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 :=
    le_trans
      (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun bb _ =>
        Finset.sum_nonneg (fun c _ => hQnn a bb c (fun _ => (0 : ℝ))))))
      (hQmass (fun _ => (0 : ℝ)))
  have hIntZC : ∀ (i : Fin m) (j : Fin p),
      Integrable (fun x : Ω × Ω =>
        (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j) (P.prod P) := by
    intro i j
    have hm : Measurable (fun x : Ω × Ω =>
        (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ))) :=
      hgradMeasW _ hZCmeas j
    refine (hZDint i j).bdd_mul (c := Ckappa * min phi1 phi2) hm.aestronglyMeasurable ?_
    filter_upwards with x
    exact hgradBd j _
  have hZC_add : ∀ (i : Fin m) (x : Ω × Ω),
      (fun k' => ZC t x k' - ZSS t x i k') + (fun k' => ZSS t x i k') = ZC t x := by
    intro i x
    funext k
    simp only [Pi.add_apply]
    ring
  have hQsingle : ∀ (j k l : Fin p) (w : Fin p → ℝ),
      Q j k l w ≤ C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := by
    intro j k l w
    have h1 : Q j k l w ≤ ∑ a : Fin p, Q a k l w :=
      Finset.single_le_sum (f := fun a : Fin p => Q a k l w)
        (fun a _ => hQnn a k l w) (Finset.mem_univ j)
    have h2 : (∑ a : Fin p, Q a k l w) ≤ ∑ a : Fin p, ∑ bb : Fin p, Q a bb l w :=
      Finset.sum_le_sum (fun a _ => Finset.single_le_sum (f := fun bb : Fin p => Q a bb l w)
        (fun bb _ => hQnn a bb l w) (Finset.mem_univ k))
    have h3 : (∑ a : Fin p, ∑ bb : Fin p, Q a bb l w) ≤
        ∑ a : Fin p, ∑ bb : Fin p, ∑ c : Fin p, Q a bb c w :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun bb _ =>
        Finset.single_le_sum (f := fun c : Fin p => Q a bb c w)
          (fun c _ => hQnn a bb c w) (Finset.mem_univ l)))
    exact le_trans h1 (le_trans h2 (le_trans h3 (hQmass w)))
  have hQmajConst : ∀ (w : Fin p → ℝ) (j k l : Fin p),
      |(iteratedFDeriv ℝ 3 KAP w)
          (fun t : Fin 3 => Pi.single ((![l, k, j] : Fin 3 → Fin p) t) (1 : ℝ))| ≤
        C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := by
    intro w j k l
    exact le_trans (hQmajKAP w l k j) (hQsingle l k j w)
  have hInt4raw : ∀ (i : Fin m) (j : Fin p),
      Integrable (fun x : Ω × Ω =>
        ∑ k : Fin p, ∑ l : Fin p,
          |ZSS t x i k| * |ZSS t x i l| * |ZD t x i j|) (P.prod P) := by
    intro i j
    have hkl : ∀ k l : Fin p, Integrable (fun x : Ω × Ω =>
        |ZSS t x i k| * |ZSS t x i l| * |ZD t x i j|) (P.prod P) := by
      intro k l
      simpa only [abs_mul] using (hmoment i j k l).1
    exact integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ => hkl k l))
  have hInt4const : ∀ (i : Fin m) (j : Fin p), Integrable (fun x : Ω × Ω =>
      ∑ k : Fin p, ∑ l : Fin p,
        (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
          |ZSS t x i k| * |ZSS t x i l| * |ZD t x i j|) (P.prod P) := by
    intro i j
    refine ((hInt4raw i j).const_mul
      (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2)).congr ?_
    filter_upwards with x
    simp only [Finset.mul_sum, mul_assoc]
  have hKnn : ∀ (k l : Fin p) (x : Ω × Ω),
      0 ≤ C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 :=
    fun k l x => hC12nn
  have hTaylor : ∀ (i : Fin m) (j : Fin p),
      |∫ x : Ω × Ω,
          (fderiv ℝ KAP ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => ZSS t x i k')))
            (Pi.single j (1 : ℝ)) * ZD t x i j ∂(P.prod P)|
        ≤ (1 / 2) * ∫ x : Ω × Ω,
            (∑ k : Fin p, ∑ l : Fin p,
              (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
                |ZSS t x i k| * |ZSS t x i l|) * |ZD t x i j| ∂(P.prod P) := by
    intro i j
    exact statopia_math_node_287517620_f22d7735 p hp (Ω × Ω) (P.prod P) KAP hKAPcontDiff j
      (fun x => fun k' => ZC t x k' - ZSS t x i k') (fun x => ZSS t x i)
      (fun x => ZD t x i j)
      (fun k l x => C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2)
      (fun l => hZSSm i l) (hZDm i j) hKnn
      (fun x s hs k l => hQmajConst _ j k l) (hInt1 i j) (hInt2 i j) (hInt3 i j)
      (hInt4const i j) (hE0 i j) (fun k => (hE1 i j k).2)
  have hRowInt : ∀ (j : Fin p), (∫ x : Ω × Ω, ∑ i : Fin m,
        (fderiv ℝ KAP ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => ZSS t x i k')))
          (Pi.single j (1 : ℝ)) * ZD t x i j ∂(P.prod P))
      = ∑ i : Fin m, ∫ x : Ω × Ω,
          (fderiv ℝ KAP ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => ZSS t x i k')))
            (Pi.single j (1 : ℝ)) * ZD t x i j ∂(P.prod P) :=
    fun j => integral_finset_sum (Finset.univ : Finset (Fin m)) (fun i _ => hInt1 i j)
  have hTaylorSum :
      |∫ x : Ω × Ω, (∑ j : Fin p, ∑ i : Fin m,
          (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j) ∂(P.prod P)|
        ≤ (1 / 2) * (∑ j : Fin p, ∑ i : Fin m, ∫ x : Ω × Ω,
            (∑ k : Fin p, ∑ l : Fin p,
              (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
                |ZSS t x i k| * |ZSS t x i l|) * |ZD t x i j| ∂(P.prod P)) := by
    have hpt : (fun x : Ω × Ω => ∑ j : Fin p, ∑ i : Fin m,
          (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j)
        = fun x : Ω × Ω => ∑ j : Fin p, ∑ i : Fin m,
          (fderiv ℝ KAP ((fun k' => ZC t x k' - ZSS t x i k') + (fun k' => ZSS t x i k')))
            (Pi.single j (1 : ℝ)) * ZD t x i j := by
      funext x
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by
        rw [hZC_add i x]))
    rw [hpt]
    rw [integral_finset_sum (Finset.univ : Finset (Fin p)) (fun j _ =>
      integrable_finset_sum Finset.univ (fun i _ => hInt1 i j))]
    simp only [hRowInt]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)) ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ =>
      (hTaylor i j)))) ?_
    rw [Finset.mul_sum]
    refine le_of_eq ?_
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  have hQmassJ : ∀ (j : Fin p) (w : Fin p → ℝ),
      (∑ l : Fin p, ∑ k : Fin p, Q l k j w) ≤
        C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := by
    intro j w
    have hmass := hQmass w
    have hinner : ∀ l : Fin p, (∑ k : Fin p, Q l k j w) ≤
        ∑ k : Fin p, ∑ c : Fin p, Q l k c w := by
      intro l
      exact Finset.sum_le_sum (fun k _ =>
        Finset.single_le_sum (fun c _ => hQnn l k c w) (Finset.mem_univ j))
    calc (∑ l : Fin p, ∑ k : Fin p, Q l k j w)
        ≤ ∑ l : Fin p, ∑ k : Fin p, ∑ c : Fin p, Q l k c w :=
          Finset.sum_le_sum (fun l _ => hinner l)
      _ ≤ C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := hmass
  have hQmax : ∀ (j : Fin p) (w d : Fin p → ℝ),
      (∑ l : Fin p, ∑ k : Fin p, Q l k j w * |d k| * |d l|) ≤
        (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
          (maxAbs d) ^ 2 := by
    intro j w d
    have hmaxnn : (0 : ℝ) ≤ maxAbs d := le_trans (abs_nonneg _) (hcoord d ⟨0, hp⟩)
    have hstep : ∀ l k : Fin p,
        Q l k j w * |d k| * |d l| ≤ Q l k j w * ((maxAbs d) * (maxAbs d)) := by
      intro l k
      have hk : |d k| ≤ maxAbs d := hcoord d k
      have hl : |d l| ≤ maxAbs d := hcoord d l
      have h0 : (0 : ℝ) ≤ Q l k j w := hQnn l k j w
      calc Q l k j w * |d k| * |d l| ≤ Q l k j w * (maxAbs d) * |d l| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk h0) (abs_nonneg _)
        _ ≤ Q l k j w * (maxAbs d) * (maxAbs d) :=
            mul_le_mul_of_nonneg_left hl (mul_nonneg h0 hmaxnn)
        _ = Q l k j w * ((maxAbs d) * (maxAbs d)) := by ring
    have hfac : (∑ l : Fin p, ∑ k : Fin p, Q l k j w) * ((maxAbs d) * (maxAbs d))
        = ∑ l : Fin p, ∑ k : Fin p, Q l k j w * ((maxAbs d) * (maxAbs d)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => Finset.sum_mul ..)
    calc (∑ l : Fin p, ∑ k : Fin p, Q l k j w * |d k| * |d l|)
        ≤ ∑ l : Fin p, ∑ k : Fin p, Q l k j w * ((maxAbs d) * (maxAbs d)) :=
          Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun k _ => hstep l k))
      _ = (∑ l : Fin p, ∑ k : Fin p, Q l k j w) * ((maxAbs d) * (maxAbs d)) := hfac.symm
      _ ≤ (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
            ((maxAbs d) * (maxAbs d)) :=
          mul_le_mul_of_nonneg_right (hQmassJ j w) (mul_nonneg hmaxnn hmaxnn)
      _ = (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
            (maxAbs d) ^ 2 := by ring
  have hQmaxAll : ∀ (w d e : Fin p → ℝ),
      (∑ j : Fin p, ∑ l : Fin p, ∑ k : Fin p,
          Q l k j w * |d k| * |d l| * |e j|) ≤
        (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
          (maxAbs d) ^ 2 * maxAbs e := by
    intro w d e
    have hdnn : (0 : ℝ) ≤ maxAbs d := le_trans (abs_nonneg _) (hcoord d ⟨0, hp⟩)
    have henn : (0 : ℝ) ≤ maxAbs e := le_trans (abs_nonneg _) (hcoord e ⟨0, hp⟩)
    have hstep : ∀ j l k : Fin p, Q l k j w * |d k| * |d l| * |e j| ≤
        Q l k j w * ((maxAbs d * maxAbs d) * maxAbs e) := by
      intro j l k
      have hk : |d k| ≤ maxAbs d := hcoord d k
      have hl : |d l| ≤ maxAbs d := hcoord d l
      have hj : |e j| ≤ maxAbs e := hcoord e j
      have h0 : (0 : ℝ) ≤ Q l k j w := hQnn l k j w
      have h12 : |d k| * |d l| ≤ maxAbs d * maxAbs d :=
        mul_le_mul hk hl (abs_nonneg _) hdnn
      have hprod : |d k| * |d l| * |e j| ≤ (maxAbs d * maxAbs d) * maxAbs e :=
        mul_le_mul h12 hj (abs_nonneg _) (mul_nonneg hdnn hdnn)
      calc Q l k j w * |d k| * |d l| * |e j| = Q l k j w * (|d k| * |d l| * |e j|) := by
            ring
        _ ≤ Q l k j w * ((maxAbs d * maxAbs d) * maxAbs e) :=
            mul_le_mul_of_nonneg_left hprod h0
    have hfac : (∑ j : Fin p, ∑ l : Fin p, ∑ k : Fin p, Q l k j w) *
            ((maxAbs d * maxAbs d) * maxAbs e)
        = ∑ j : Fin p, ∑ l : Fin p, ∑ k : Fin p,
            Q l k j w * ((maxAbs d * maxAbs d) * maxAbs e) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => Finset.sum_mul ..)
    have hperm : (∑ j : Fin p, ∑ l : Fin p, ∑ k : Fin p, Q l k j w)
        = ∑ a : Fin p, ∑ bb : Fin p, ∑ c : Fin p, Q a bb c w := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      exact Finset.sum_comm
    calc (∑ j : Fin p, ∑ l : Fin p, ∑ k : Fin p, Q l k j w * |d k| * |d l| * |e j|)
        ≤ ∑ j : Fin p, ∑ l : Fin p, ∑ k : Fin p,
            Q l k j w * ((maxAbs d * maxAbs d) * maxAbs e) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ =>
            Finset.sum_le_sum (fun k _ => hstep j l k)))
      _ = (∑ j : Fin p, ∑ l : Fin p, ∑ k : Fin p, Q l k j w) *
            ((maxAbs d * maxAbs d) * maxAbs e) := hfac.symm
      _ ≤ (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
            ((maxAbs d * maxAbs d) * maxAbs e) := by
          rw [hperm]
          exact mul_le_mul_of_nonneg_right (hQmass w)
            (mul_nonneg (mul_nonneg hdnn hdnn) henn)
      _ = (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
            (maxAbs d) ^ 2 * maxAbs e := by ring
  have hZDmaxAbs : ∀ (i : Fin m) (x : Ω × Ω) (r : Fin p),
      |ZD t x i r| ≤ (Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
        (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
          (maxAbs (fun j : Fin p => Y i x.1 j - muY j) +
            maxAbs (fun j : Fin p => G i x.1 j - muY j) +
            maxAbs (fun j : Fin p => G i x.2 j - muY j))) := by
    intro i x r
    set SY : ℝ := maxAbs (fun j : Fin p => Y i x.1 j - muY j) with hSY
    set SG : ℝ := maxAbs (fun j : Fin p => G i x.1 j - muY j) with hSG
    set SB : ℝ := maxAbs (fun j : Fin p => G i x.2 j - muY j) with hSB
    have hA : |Y i x.1 r - muY r| ≤ SY := hcoordY i x.1 r
    have hA' : |G i x.1 r - muY r| ≤ SG := hcoordG i x.1 r
    have hB : |G i x.2 r - muY r| ≤ SB := hcoordG i x.2 r
    have hSYnn : (0 : ℝ) ≤ SY := le_trans (abs_nonneg _) hA
    have hSGnn : (0 : ℝ) ≤ SG := le_trans (abs_nonneg _) hA'
    have hSBnn : (0 : ℝ) ≤ SB := le_trans (abs_nonneg _) hB
    have hSnn : (0 : ℝ) ≤ SY + SG + SB := by linarith
    have hsv : Real.sqrt v ≤ 1 := by simpa using Real.sqrt_le_sqrt hv1
    have hsv0 : (0 : ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
    have hsv' : Real.sqrt (1 - v) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) - v ≤ 1 by linarith)
    have hsv0' : (0 : ℝ) ≤ Real.sqrt (1 - v) := Real.sqrt_nonneg _
    have h1 : |Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)|
        ≤ SY + SG := by
      calc |Real.sqrt v * (Y i x.1 r - muY r) + Real.sqrt (1 - v) * (G i x.1 r - muY r)|
          ≤ |Real.sqrt v * (Y i x.1 r - muY r)| +
            |Real.sqrt (1 - v) * (G i x.1 r - muY r)| := abs_add_le _ _
        _ = Real.sqrt v * |Y i x.1 r - muY r| + Real.sqrt (1 - v) * |G i x.1 r - muY r| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hsv0']
        _ ≤ 1 * SY + 1 * SG :=
            add_le_add (mul_le_mul hsv hA (abs_nonneg _) zero_le_one)
              (mul_le_mul hsv' hA' (abs_nonneg _) zero_le_one)
        _ = SY + SG := by ring
    have hpt : (0 : ℝ) ≤ (2 * Real.sqrt t)⁻¹ :=
      le_of_lt (inv_pos.mpr (by have := Real.sqrt_pos.mpr ht0; linarith))
    have hpt' : (0 : ℝ) ≤ (2 * Real.sqrt (1 - t))⁻¹ :=
      le_of_lt (inv_pos.mpr (by have := Real.sqrt_pos.mpr (sub_pos.mpr ht1); linarith))
    have hem0 : (0 : ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ :=
      le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hmR))
    have hb : ZD t x i r = (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 r - muY r) +
            Real.sqrt (1 - v) * (G i x.1 r - muY r)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 r - muY r)) := rfl
    rw [hb, abs_mul, abs_mul, abs_of_nonneg hem0]
    refine mul_le_mul (le_refl _) ?_ (abs_nonneg _) (mul_nonneg hem0 (abs_nonneg _))
    have hleft : (2 * Real.sqrt t)⁻¹ * (SY + SG) ≤ (2 * Real.sqrt t)⁻¹ * (SY + SG + SB) :=
      mul_le_mul_of_nonneg_left (by linarith) hpt
    have hright : (2 * Real.sqrt (1 - t))⁻¹ * SB ≤
        (2 * Real.sqrt (1 - t))⁻¹ * (SY + SG + SB) :=
      mul_le_mul_of_nonneg_left (by linarith) hpt'
    calc |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 r - muY r) +
            Real.sqrt (1 - v) * (G i x.1 r - muY r)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 r - muY r)|
        ≤ |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 r - muY r) +
            Real.sqrt (1 - v) * (G i x.1 r - muY r))| +
          |(2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 r - muY r)| := habsSub _ _
      _ = (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (Y i x.1 r - muY r) +
            Real.sqrt (1 - v) * (G i x.1 r - muY r)| +
          (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 r - muY r| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hpt, abs_of_nonneg hpt']
      _ ≤ (2 * Real.sqrt t)⁻¹ * (SY + SG) + (2 * Real.sqrt (1 - t))⁻¹ * SB :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hpt) (mul_le_mul_of_nonneg_left hB hpt')
      _ ≤ (2 * Real.sqrt t)⁻¹ * (SY + SG + SB) + (2 * Real.sqrt (1 - t))⁻¹ * (SY + SG + SB) :=
          add_le_add hleft hright
      _ = ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) * (SY + SG + SB) := by ring
  have hZSSsum_sq : ∀ (i : Fin m) (x : Ω × Ω),
      (∑ k : Fin p, |ZSS t x i k|) ^ 2 =
        ∑ k : Fin p, ∑ l : Fin p, |ZSS t x i k| * |ZSS t x i l| := by
    intro i x
    rw [pow_two, Finset.sum_mul_sum]



  -- Replace the opaque majorant by its maximal lower-semicontinuous minorant.
  let box : Set (Fin p → ℝ) := {u | ∀ r, |u r| * (min phi1 phi2 * Real.log (p : ℝ)) ≤ 1}
  have hQboth : ∀ w u, u ∈ box → ∀ j k l,
      Q j k l w ≤ C3 * Q j k l (w + u) ∧ Q j k l (w + u) ≤ C3 * Q j k l w := by
    intro w u hu j k l
    refine ⟨?_, hQbox j k l w u hu⟩
    have hneg : ∀ r, |(-u) r| * (min phi1 phi2 * Real.log (p : ℝ)) ≤ 1 := by
      intro r
      simpa only [Pi.neg_apply, abs_neg] using hu r
    have H := hQbox j k l (w + u) (-u) hneg
    simpa only [add_neg_cancel_right] using H
  have hQall : ∀ (d : Fin 3 → Fin p) w,
      |(iteratedFDeriv ℝ 3 KAP w) (fun s : Fin 3 => Pi.single (d s) (1 : ℝ))| ≤
        Q (d 0) (d 1) (d 2) w := by
    intro d w
    have H := hQmaj (d 0) (d 1) (d 2) w
    have hdvec : (![d 0, d 1, d 2] : Fin 3 → Fin p) = d := by
      funext s
      fin_cases s <;> rfl
    change |(iteratedFDeriv ℝ 3 KAP w)
      (fun s : Fin 3 => Pi.single ((![d 0, d 1, d 2] : Fin 3 → Fin p) s) (1 : ℝ))| ≤ _ at H
    simpa only [hdvec] using H
  obtain ⟨R, hRm, hRnn, hRmaj, hRmass, _, hRbox⟩ :=
    DCFQReview.triple_regularization KAP hKAPcontDiff Q hQnn hQall
      (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2)
      (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2)
      C3 (lt_of_lt_of_le zero_lt_one hC3) box hQmass hQmass hQboth
  let W : Fin m → Ω × Ω → Fin p → ℝ := fun i x r => ZC t x r - ZSS t x i r
  let row : Fin m → Ω × Ω → (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) :=
    fun i x => (Y i x.1, (G i x.1, G i x.2))
  let goodRow : Set ((Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ))) :=
    {z | (∀ r, |z.1 r - muY r| ≤ ell) ∧
      (∀ r, |z.2.1 r - muY r| ≤ ell) ∧ (∀ r, |z.2.2 r - muY r| ≤ ell)}
  let good : Fin m → Set (Ω × Ω) := fun i => row i ⁻¹' goodRow
  have hrowm : ∀ i, Measurable (row i) := by
    intro i
    exact ((hYm i).comp measurable_fst).prodMk
      (((hGm i).comp measurable_fst).prodMk ((hGm i).comp measurable_snd))
  have hgoodRowm : MeasurableSet goodRow := by
    change MeasurableSet {z : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) |
      (∀ r, |z.1 r - muY r| ≤ ell) ∧
      (∀ r, |z.2.1 r - muY r| ≤ ell) ∧ (∀ r, |z.2.2 r - muY r| ≤ ell)}
    simp only [Set.setOf_and, Set.setOf_forall]
    refine MeasurableSet.inter (MeasurableSet.iInter (fun r => ?_))
      (MeasurableSet.inter (MeasurableSet.iInter (fun r => ?_))
        (MeasurableSet.iInter (fun r => ?_)))
    all_goals exact measurableSet_le (by fun_prop) measurable_const
  have hgoodm : ∀ i, MeasurableSet (good i) :=
    fun i => hgoodRowm.preimage (hrowm i)
  have hgood_fields : ∀ i x, x ∈ good i ↔
      (∀ r, |Y i x.1 r - muY r| ≤ ell) ∧
      (∀ r, |G i x.1 r - muY r| ≤ ell) ∧ (∀ r, |G i x.2 r - muY r| ≤ ell) := by
    intro i x
    rfl
  have hWindep : ∀ i, IndepFun (W i) (row i) (P.prod P) := by
    intro i
    have H := dcf_y_leave_one_out_independent Ω P n m p delta muX muY X Y F G
      hXm hYm hFm hGm hindep v t i
    change IndepFun (fun x k => (∑ i' : Fin n, ZST t x i' k) +
      ∑ i' : Fin m, if i' = i then 0 else ZSS t x i' k) (row i) (P.prod P) at H
    have heq : W i = fun x k => (∑ i' : Fin n, ZST t x i' k) +
        ∑ i' : Fin m, if i' = i then 0 else ZSS t x i' k := by
      funext x
      exact hZrest_eq i x
    rw [heq]
    exact H
  let smallStrip : Set (Fin p → ℝ) := {w |
    -(min phi1 phi2)⁻¹ - (min phi1 phi2 * Real.log (p : ℝ))⁻¹ < (⨆ r, w r - y r) ∧
    (⨆ r, w r - y r) ≤ (min phi1 phi2)⁻¹ + (min phi1 phi2 * Real.log (p : ℝ))⁻¹}
  have hmaxm : Measurable (fun w : Fin p → ℝ => ⨆ r : Fin p, w r - y r) :=
    Measurable.iSup (fun r => (measurable_pi_apply r).sub measurable_const)
  have hsmallStripm : MeasurableSet smallStrip :=
    (measurableSet_lt measurable_const hmaxm).inter
      (measurableSet_le hmaxm measurable_const)
  let weight : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ :=
    fun j k l => smallStrip.indicator (R j k l)
  have hweightm : ∀ j k l, Measurable (weight j k l) :=
    fun j k l => (hRm j k l).indicator hsmallStripm
  have hweightnn : ∀ j k l w, 0 ≤ weight j k l w := by
    intro j k l w
    by_cases hw : w ∈ smallStrip <;> simp [weight, hw, hRnn]
  have hweightint : ∀ i j k l, Integrable (fun x => weight j k l (W i x)) (P.prod P) := by
    intro i j k l
    have hmassbound : ∀ w, R j k l w ≤
        C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := by
      intro w
      have hj : R j k l w ≤ ∑ l', R j k l' w :=
        Finset.single_le_sum (fun l' _ => hRnn j k l' w) (Finset.mem_univ l)
      have hk : (∑ l', R j k l' w) ≤ ∑ k', ∑ l', R j k' l' w :=
        Finset.single_le_sum (fun k' _ => Finset.sum_nonneg (fun l' _ => hRnn j k' l' w))
          (Finset.mem_univ k)
      have hj' : (∑ k', ∑ l', R j k' l' w) ≤ ∑ j', ∑ k', ∑ l', R j' k' l' w :=
        Finset.single_le_sum (fun j' _ => Finset.sum_nonneg (fun k' _ =>
          Finset.sum_nonneg (fun l' _ => hRnn j' k' l' w))) (Finset.mem_univ j)
      exact (hj.trans (hk.trans hj')).trans (hRmass w)
    refine (integrable_const (C1 * C2 * (min phi1 phi2) *
      (min phi1 phi2 * Real.log (p : ℝ)) ^ 2)).mono'
      ((hweightm j k l).comp (hWmeas i)).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hweightnn j k l (W i x))]
    by_cases hw : W i x ∈ smallStrip
    · simpa [weight, hw] using hmassbound (W i x)
    · simpa [weight, hw] using hC12nn
  have hweight_good_indep : ∀ i j k l,
      IndepFun (fun x => weight j k l (W i x))
        ((good i).indicator (fun _ => (1 : ℝ))) (P.prod P) := by
    intro i j k l
    have H := (hWindep i).comp (hweightm j k l)
      ((show Measurable (fun _ : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => (1 : ℝ)) from measurable_const).indicator hgoodRowm)
    exact H
  have hweight_good_reinsert : ∀ i j k l,
      (1 / 2 : ℝ) ≤ (P.prod P).real (good i) →
      (∫ x, weight j k l (W i x) ∂(P.prod P)) ≤
        2 * ∫ x, (good i).indicator (fun x => weight j k l (W i x)) x ∂(P.prod P) := by
    intro i j k l hprob
    exact DCFYReview.expectation_le_twice_good (P.prod P) _ (hweightint i j k l)
      (fun x => hweightnn j k l (W i x)) (good i) (hgoodm i)
      (hweight_good_indep i j k l) hprob
  haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  let bigStrip : Set (Fin p → ℝ) := {w |
    -(min phi1 phi2)⁻¹ - 2 * (min phi1 phi2 * Real.log (p : ℝ))⁻¹ < (⨆ r, w r - y r) ∧
    (⨆ r, w r - y r) ≤ (min phi1 phi2)⁻¹ + 2 * (min phi1 phi2 * Real.log (p : ℝ))⁻¹}
  have hbigStripm : MeasurableSet bigStrip :=
    (measurableSet_lt measurable_const hmaxm).inter
      (measurableSet_le hmaxm measurable_const)
  have hsupclose : ∀ (a b : Fin p → ℝ) (r : ℝ),
      (∀ j, |a j - b j| ≤ r) →
      (⨆ j, a j - y j) ≤ (⨆ j, b j - y j) + r := by
    intro a b r hab
    apply ciSup_le
    intro j
    have hbdd : BddAbove (Set.range (fun j => b j - y j)) := (Set.finite_range _).bddAbove
    have hbj := le_ciSup hbdd j
    have haj := (abs_le.mp (hab j)).2
    linarith
  have hstrip_transfer : ∀ i x, x ∈ good i → W i x ∈ smallStrip → ZC t x ∈ bigStrip := by
    intro i x hx hW
    have hfields := (hgood_fields i x).mp hx
    have hU := hZSSβ i x hfields.1 hfields.2.1 hfields.2.2
    have hclose : ∀ r : Fin p,
        |ZC t x r - W i x r| ≤ (min phi1 phi2 * Real.log (p : ℝ))⁻¹ := by
      intro r
      have H := hU r
      have H' : |ZSS t x i r| ≤ 1 / (min phi1 phi2 * Real.log (p : ℝ)) :=
        (le_div_iff₀ hbetapos).mpr (by linarith)
      have HE : ZC t x r - W i x r = ZSS t x i r := by
        change ZC t x r - (ZC t x r - ZSS t x i r) = ZSS t x i r
        ring
      rw [HE]
      simpa only [one_div] using H'
    have hZW := hsupclose (ZC t x) (W i x) _ hclose
    have hWZ := hsupclose (W i x) (ZC t x) _ (fun r => by
      rw [abs_sub_comm]
      exact hclose r)
    have hW' : -(min phi1 phi2)⁻¹ - (min phi1 phi2 * Real.log (p : ℝ))⁻¹ <
        (⨆ r, W i x r - y r) ∧ (⨆ r, W i x r - y r) ≤
        (min phi1 phi2)⁻¹ + (min phi1 phi2 * Real.log (p : ℝ))⁻¹ := hW
    exact ⟨by linarith [hW'.1], by linarith [hW'.2]⟩
  let commonWeight : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ :=
    fun j k l => bigStrip.indicator (R j k l)
  have hcommonWeightm : ∀ j k l, Measurable (commonWeight j k l) :=
    fun j k l => (hRm j k l).indicator hbigStripm
  have hcommonWeightnn : ∀ j k l w, 0 ≤ commonWeight j k l w := by
    intro j k l w
    by_cases hw : w ∈ bigStrip <;> simp [commonWeight, hw, hRnn]
  have hweight_transfer : ∀ i x, x ∈ good i → ∀ j k l,
      weight j k l (W i x) ≤ C3 * commonWeight j k l (ZC t x) := by
    intro i x hx j k l
    have hfields := (hgood_fields i x).mp hx
    have hU := hZSSβ i x hfields.1 hfields.2.1 hfields.2.2
    by_cases hW : W i x ∈ smallStrip
    · have hZ : ZC t x ∈ bigStrip := hstrip_transfer i x hx hW
      have hnegU : (fun r => -ZSS t x i r) ∈ box := by
        intro r
        have H := hU r
        simp only [abs_neg]
        linarith
      have HR := (hRbox (ZC t x) (fun r => -ZSS t x i r) hnegU j k l).2
      have HE : ZC t x + (fun r => -ZSS t x i r) = W i x := by
        funext r
        rfl
      rw [HE] at HR
      simpa only [weight, commonWeight, Set.indicator_of_mem hW, Set.indicator_of_mem hZ] using HR
    · have H := mul_nonneg (le_trans zero_le_one hC3) (hcommonWeightnn j k l (ZC t x))
      simpa only [weight, Set.indicator_of_notMem hW] using H
  have hRsingle : ∀ j k l w, R j k l w ≤
      C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := by
    intro j k l w
    have hj : R j k l w ≤ ∑ l', R j k l' w :=
      Finset.single_le_sum (fun l' _ => hRnn j k l' w) (Finset.mem_univ l)
    have hk : (∑ l', R j k l' w) ≤ ∑ k', ∑ l', R j k' l' w :=
      Finset.single_le_sum (fun k' _ => Finset.sum_nonneg (fun l' _ => hRnn j k' l' w))
        (Finset.mem_univ k)
    have hj' : (∑ k', ∑ l', R j k' l' w) ≤ ∑ j', ∑ k', ∑ l', R j' k' l' w :=
      Finset.single_le_sum (fun j' _ => Finset.sum_nonneg (fun k' _ =>
        Finset.sum_nonneg (fun l' _ => hRnn j' k' l' w))) (Finset.mem_univ j)
    exact (hj.trans (hk.trans hj')).trans (hRmass w)
  have hcommonWeightint : ∀ j k l,
      Integrable (fun x => commonWeight j k l (ZC t x)) (P.prod P) := by
    intro j k l
    refine (integrable_const (C1 * C2 * (min phi1 phi2) *
      (min phi1 phi2 * Real.log (p : ℝ)) ^ 2)).mono'
      ((hcommonWeightm j k l).comp hZCmeas).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hcommonWeightnn j k l (ZC t x))]
    by_cases hz : ZC t x ∈ bigStrip
    · simpa [commonWeight, hz] using hRsingle j k l (ZC t x)
    · simpa [commonWeight, hz] using hC12nn
  have hweight_common_transfer : ∀ i j k l,
      (1 / 2 : ℝ) ≤ (P.prod P).real (good i) →
      (∫ x, weight j k l (W i x) ∂(P.prod P)) ≤
        2 * C3 * ∫ x, commonWeight j k l (ZC t x) ∂(P.prod P) := by
    intro i j k l hprob
    exact DCFYReview.expectation_le_twice_transfer (P.prod P) _ _ (hweightint i j k l)
      (hcommonWeightint j k l) (fun x => hweightnn j k l (W i x))
      (fun x => hcommonWeightnn j k l (ZC t x)) (good i) (hgoodm i)
      (hweight_good_indep i j k l) hprob C3 (le_trans zero_le_one hC3)
      (fun x hx => hweight_transfer i x hx j k l)
  -- Independence factors coordinate moments before summing the sample index.
  let rowU : ((Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ))) → Fin p → ℝ :=
    fun z r => (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t * (Real.sqrt v * (z.1 r - muY r) + Real.sqrt (1 - v) * (z.2.1 r - muY r)) +
        Real.sqrt (1 - t) * (z.2.2 r - muY r))
  let rowD : ((Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ))) → Fin p → ℝ :=
    fun z r => (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (z.1 r - muY r) + Real.sqrt (1 - v) * (z.2.1 r - muY r)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (z.2.2 r - muY r))
  have hrowproductm : ∀ j k l, Measurable (fun z => |rowU z k * rowU z l * rowD z j|) := by
    intro j k l
    dsimp only [rowU, rowD]
    fun_prop
  have hweight_rowproduct_indep : ∀ i j k l,
      IndepFun (fun x => weight j k l (W i x))
        (fun x => |ZSS t x i k * ZSS t x i l * ZD t x i j|) (P.prod P) := by
    intro i j k l
    exact (hWindep i).comp (hweightm j k l) (hrowproductm j k l)
  have hweight_rowproduct_factor : ∀ i j k l,
      (∫ x, weight j k l (W i x) * |ZSS t x i k * ZSS t x i l * ZD t x i j| ∂(P.prod P)) =
        (∫ x, weight j k l (W i x) ∂(P.prod P)) *
          (∫ x, |ZSS t x i k * ZSS t x i l * ZD t x i j| ∂(P.prod P)) := by
    intro i j k l
    exact (hweight_rowproduct_indep i j k l).integral_fun_mul_eq_mul_integral
      (hweightint i j k l).aestronglyMeasurable
      ((((hZSSm i k).mul (hZSSm i l)).mul (hZDm i j)).abs.aestronglyMeasurable)

  let rowMoment : Fin m → Fin p → Fin p → Fin p → ℝ := fun i j k l =>
    ∫ x, |ZSS t x i k * ZSS t x i l * ZD t x i j| ∂(P.prod P)
  have hrowMomentnn : ∀ i j k l, 0 ≤ rowMoment i j k l :=
    fun i j k l => integral_nonneg (fun x => abs_nonneg _)
  have hreal_row_moment : ∀ i j k l, rowMoment i j k l ≤
      (3 / 2) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3 * |delta n m| ^ 3 *
        ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
          (((∫ ω, |Y i ω j - muY j| ^ 3 ∂P) + 2 * (∫ ω, |G i ω j - muY j| ^ 3 ∂P)) +
          ((∫ ω, |Y i ω k - muY k| ^ 3 ∂P) + 2 * (∫ ω, |G i ω k - muY k| ^ 3 ∂P)) +
          ((∫ ω, |Y i ω l - muY l| ^ 3 ∂P) + 2 * (∫ ω, |G i ω l - muY l| ^ 3 ∂P))) := by
    intro i j k l
    exact (DCFManualXAudit.real_row_coordinate_moment p Ω P m hm (delta n m) hd t ht0 ht1 v hv0 hv1
      muY (Y i) (G i) (fun r => (measurable_pi_apply r).comp (hYm i))
      (fun r => (measurable_pi_apply r).comp (hGm i))
      (fun r => ∫ ω, |Y i ω r - muY r| ^ 3 ∂P)
      (fun r => ∫ ω, |G i ω r - muY r| ^ 3 ∂P)
      (fun r => ⟨hY3 i r, le_rfl, hG3 i r, le_rfl⟩) j k l).2
  have hLYsum : ∀ r, (∑ i, ∫ ω, |Y i ω r - muY r| ^ 3 ∂P) ≤ (m : ℝ) * LY P m muY Y := by
    intro r
    have H := mul_le_mul_of_nonneg_left (hLYelem r) hmR.le
    simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmR), one_mul] using H
  have hLGsum : ∀ r, (∑ i, ∫ ω, |G i ω r - muY r| ^ 3 ∂P) ≤ (m : ℝ) * LG := by
    intro r
    have H := mul_le_mul_of_nonneg_left (hLGelem r) hmR.le
    simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmR), one_mul] using H
  let momentCap : ℝ := (9 / 2) * (Real.sqrt (m : ℝ))⁻¹ * |delta n m| ^ 3 *
    ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * (LY P m muY Y + 2 * LG)
  have hmomentCapnn : 0 ≤ momentCap := by
    dsimp only [momentCap]
    positivity
  have hreal_moment_sum : ∀ j k l, ∑ i, rowMoment i j k l ≤ momentCap := by
    intro j k l
    let A : ℝ := (3 / 2) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3 * |delta n m| ^ 3 *
      ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)
    have hAnn : 0 ≤ A := by dsimp only [A]; positivity
    calc (∑ i, rowMoment i j k l)
        ≤ ∑ i, A * (((∫ ω, |Y i ω j - muY j| ^ 3 ∂P) + 2 * (∫ ω, |G i ω j - muY j| ^ 3 ∂P)) +
          ((∫ ω, |Y i ω k - muY k| ^ 3 ∂P) + 2 * (∫ ω, |G i ω k - muY k| ^ 3 ∂P)) +
          ((∫ ω, |Y i ω l - muY l| ^ 3 ∂P) + 2 * (∫ ω, |G i ω l - muY l| ^ 3 ∂P))) :=
          Finset.sum_le_sum (fun i _ => hreal_row_moment i j k l)
      _ = A * (((∑ i, ∫ ω, |Y i ω j - muY j| ^ 3 ∂P) + 2 * (∑ i, ∫ ω, |G i ω j - muY j| ^ 3 ∂P)) +
          ((∑ i, ∫ ω, |Y i ω k - muY k| ^ 3 ∂P) + 2 * (∑ i, ∫ ω, |G i ω k - muY k| ^ 3 ∂P)) +
          ((∑ i, ∫ ω, |Y i ω l - muY l| ^ 3 ∂P) + 2 * (∑ i, ∫ ω, |G i ω l - muY l| ^ 3 ∂P))) := by
          rw [← Finset.mul_sum]
          congr 1
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ A * (3 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) := by
          apply mul_le_mul_of_nonneg_left _ hAnn
          linarith [hLYsum j, hLYsum k, hLYsum l, hLGsum j, hLGsum k, hLGsum l]
      _ = momentCap := by
          dsimp only [A, momentCap]
          have H := hsqrtcube
          have HE : (3 / 2) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3 * |delta n m| ^ 3 *
              ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
              (3 * ((m : ℝ) * LY P m muY Y + 2 * ((m : ℝ) * LG))) =
              (9 / 2) * ((m : ℝ) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3) * |delta n m| ^ 3 *
              ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * (LY P m muY Y + 2 * LG) := by ring
          rw [HE, H]
  let commonMean : Fin p → Fin p → Fin p → ℝ := fun j k l =>
    ∫ x, commonWeight j k l (ZC t x) ∂(P.prod P)
  have hcommonMeannn : ∀ j k l, 0 ≤ commonMean j k l :=
    fun j k l => integral_nonneg (fun x => hcommonWeightnn j k l (ZC t x))
  have hcommonWeightSumInt : Integrable (fun x => ∑ j, ∑ k, ∑ l,
      commonWeight j k l (ZC t x)) (P.prod P) :=
    integrable_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
      (fun k _ => integrable_finset_sum Finset.univ (fun l _ => hcommonWeightint j k l)))
  have hbigIndicatorInt : Integrable (fun x => bigStrip.indicator (fun _ => (1 : ℝ)) (ZC t x))
      (P.prod P) := by
    refine (integrable_const (1 : ℝ)).mono'
      (((measurable_const.indicator hbigStripm).comp hZCmeas).aestronglyMeasurable) ?_
    filter_upwards with x
    by_cases hx : ZC t x ∈ bigStrip <;> simp [hx]
  have hcommonMeanSum : (∑ j, ∑ k, ∑ l, commonMean j k l) ≤
      (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
      (2 * rho P n m p (delta n m) muX muY X Y F G +
        Cb * ((min phi1 phi2)⁻¹ + 2 * ((min phi1 phi2) * Real.log (p : ℝ))⁻¹) *
          Real.sqrt (Real.log (p : ℝ))) := by
    have hdistribute : (∫ x, ∑ j, ∑ k, ∑ l, commonWeight j k l (ZC t x) ∂(P.prod P)) =
        ∑ j, ∑ k, ∑ l, commonMean j k l := by
      rw [integral_finset_sum Finset.univ (fun j _ =>
        integrable_finset_sum Finset.univ (fun k _ =>
          integrable_finset_sum Finset.univ (fun l _ => hcommonWeightint j k l)))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ => hcommonWeightint j k l))]
      apply Finset.sum_congr rfl
      intro k _
      exact integral_finset_sum Finset.univ (fun l _ => hcommonWeightint j k l)
    rw [← hdistribute]
    calc (∫ x, ∑ j, ∑ k, ∑ l, commonWeight j k l (ZC t x) ∂(P.prod P))
        ≤ ∫ x, (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
          bigStrip.indicator (fun _ => (1 : ℝ)) (ZC t x) ∂(P.prod P) := by
          apply integral_mono hcommonWeightSumInt (hbigIndicatorInt.const_mul _)
          intro x
          by_cases hx : ZC t x ∈ bigStrip
          · simpa only [commonWeight, Set.indicator_of_mem hx, mul_one] using hRmass (ZC t x)
          · simp only [commonWeight, Set.indicator_of_notMem hx, Finset.sum_const_zero, mul_zero]
            exact le_rfl
      _ = (C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ)) ^ 2) *
          ∫ x, bigStrip.indicator (fun _ => (1 : ℝ)) (ZC t x) ∂(P.prod P) :=
          integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hLoc hC12nn
  let goodMomentTerm : Fin m → Fin p × Fin p × Fin p → ℝ := fun i jkl =>
    if (1 / 2 : ℝ) ≤ (P.prod P).real (good i) then
      ∫ x, weight jkl.1 jkl.2.1 jkl.2.2 (W i x) *
        |ZSS t x i jkl.2.1 * ZSS t x i jkl.2.2 * ZD t x i jkl.1| ∂(P.prod P)
    else 0
  have hgoodMomentTerm : ∀ i jkl, goodMomentTerm i jkl ≤
      (2 * C3) * commonMean jkl.1 jkl.2.1 jkl.2.2 * rowMoment i jkl.1 jkl.2.1 jkl.2.2 := by
    intro i jkl
    by_cases hprob : (1 / 2 : ℝ) ≤ (P.prod P).real (good i)
    · dsimp only [goodMomentTerm]
      rw [if_pos hprob, hweight_rowproduct_factor]
      exact mul_le_mul_of_nonneg_right (hweight_common_transfer i jkl.1 jkl.2.1 jkl.2.2 hprob)
        (hrowMomentnn i jkl.1 jkl.2.1 jkl.2.2)
    · simp only [goodMomentTerm, if_neg hprob]
      exact mul_nonneg (mul_nonneg (by positivity) (hcommonMeannn _ _ _)) (hrowMomentnn _ _ _ _)
  have hgoodMomentGlobal : (∑ i, ∑ jkl, goodMomentTerm i jkl) ≤
      (2 * C3) * momentCap * (∑ j, ∑ k, ∑ l, commonMean j k l) := by
    have H := DCFYReview.weighted_row_sum_bound goodMomentTerm
      (fun i (jkl : Fin p × Fin p × Fin p) => rowMoment i jkl.1 jkl.2.1 jkl.2.2)
      (fun jkl => commonMean jkl.1 jkl.2.1 jkl.2.2)
      (2 * C3) momentCap (∑ jkl : Fin p × Fin p × Fin p, commonMean jkl.1 jkl.2.1 jkl.2.2)
      (by positivity) hmomentCapnn (fun jkl => hcommonMeannn _ _ _) hgoodMomentTerm
      (fun jkl => hreal_moment_sum _ _ _) le_rfl
    simpa only [Fintype.sum_prod_type] using H

  have hKAPsupport : ∀ d : Fin 3 → Fin p,
      Function.support (fun w : Fin p → ℝ =>
        (iteratedFDeriv ℝ 3 KAP w) (fun s : Fin 3 => Pi.single (d s) (1 : ℝ))) ⊆
      {w | -(min phi1 phi2)⁻¹ ≤ (⨆ r : Fin p, w r - y r) ∧
        (⨆ r : Fin p, w r - y r) ≤ (min phi1 phi2)⁻¹} :=
    (statopia_math_node_2194576110_d2ad0cef p hp2 (min phi1 phi2) hphi phi0
      hphi0_cont hphi0_left hphi0_right hphi0_range y).2.2.2.2.2.2.1
  have hseg_nonzero_strip : ∀ i x, x ∈ good i → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ d : Fin 3 → Fin p,
      (iteratedFDeriv ℝ 3 KAP (W i x + s • ZSS t x i))
        (fun a : Fin 3 => Pi.single (d a) (1 : ℝ)) ≠ 0 → W i x ∈ smallStrip := by
    intro i x hx s hs d hne
    have hfields := (hgood_fields i x).mp hx
    have hU := hZSSβ i x hfields.1 hfields.2.1 hfields.2.2
    have hsabs : |s| ≤ 1 := by simpa only [abs_of_nonneg hs.1] using hs.2
    have hclose : ∀ r : Fin p, |(W i x + s • ZSS t x i) r - W i x r| ≤
        (3 / 4) * (min phi1 phi2 * Real.log (p : ℝ))⁻¹ := by
      intro r
      have hprod : |s * ZSS t x i r| * (min phi1 phi2 * Real.log (p : ℝ)) ≤ 3 / 4 := by
        rw [abs_mul, mul_assoc]
        exact (mul_le_mul hsabs (hU r) (by positivity) zero_le_one).trans_eq (one_mul _)
      have H : |s * ZSS t x i r| ≤ (3 / 4) / (min phi1 phi2 * Real.log (p : ℝ)) :=
        (le_div_iff₀ hbetapos).mpr hprod
      have HE : (W i x + s • ZSS t x i) r - W i x r = s * ZSS t x i r := by
        change (W i x r + s * ZSS t x i r) - W i x r = _
        ring
      rw [HE]
      simpa only [div_eq_mul_inv] using H
    have hξW := hsupclose (W i x + s • ZSS t x i) (W i x) _ hclose
    have hWξ := hsupclose (W i x) (W i x + s • ZSS t x i) _ (fun r => by
      rw [abs_sub_comm]
      exact hclose r)
    have hsupp := hKAPsupport d (show (W i x + s • ZSS t x i) ∈ Function.support
      (fun w : Fin p → ℝ => (iteratedFDeriv ℝ 3 KAP w)
        (fun a : Fin 3 => Pi.single (d a) (1 : ℝ))) from hne)
    have hbpos : 0 < (min phi1 phi2 * Real.log (p : ℝ))⁻¹ := inv_pos.mpr hbetapos
    exact ⟨by linarith [hsupp.1], by linarith [hsupp.2]⟩
  have hRmajGood : ∀ i x, x ∈ good i → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ l k j : Fin p,
      |(iteratedFDeriv ℝ 3 KAP (W i x + s • ZSS t x i))
        (fun a : Fin 3 => Pi.single ((![l, k, j] : Fin 3 → Fin p) a) (1 : ℝ))| ≤
          C3 * weight l k j (W i x) := by
    intro i x hx s hs l k j
    have hfields := (hgood_fields i x).mp hx
    have hU := hZSSβ i x hfields.1 hfields.2.1 hfields.2.2
    by_cases hzero : (iteratedFDeriv ℝ 3 KAP (W i x + s • ZSS t x i))
        (fun a : Fin 3 => Pi.single ((![l, k, j] : Fin 3 → Fin p) a) (1 : ℝ)) = 0
    · rw [hzero, abs_zero]
      exact mul_nonneg (le_trans zero_le_one hC3) (hweightnn l k j (W i x))
    · have hw := hseg_nonzero_strip i x hx s hs (![l, k, j]) hzero
      have hsmall : s • ZSS t x i ∈ box := by
        intro r
        change |s * ZSS t x i r| * (min phi1 phi2 * Real.log (p : ℝ)) ≤ 1
        rw [abs_mul, mul_assoc]
        have hsabs : |s| ≤ 1 := by simpa only [abs_of_nonneg hs.1] using hs.2
        have H := mul_le_mul hsabs (hU r) (by positivity : (0 : ℝ) ≤ |ZSS t x i r| *
          (min phi1 phi2 * Real.log (p : ℝ))) zero_le_one
        linarith
      have HR := (hRbox (W i x) (s • ZSS t x i) hsmall l k j).2
      have HD := hRmaj (![l, k, j]) (W i x + s • ZSS t x i)
      have H := HD.trans HR
      simpa only [weight, Set.indicator_of_mem hw, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two] using H

  -- Actual row maximum, retaining only its own third-moment tails on bad rows.
  let SY : Fin m → Ω → ℝ := fun i ω => maxAbs (fun r => Y i ω r - muY r)
  let SG : Fin m → Ω → ℝ := fun i ω => maxAbs (fun r => G i ω r - muY r)
  let Trow : Fin m → Ω × Ω → ℝ := fun i x => max (SY i x.1) (max (SG i x.1) (SG i x.2))
  have hSYnn : ∀ i ω, 0 ≤ SY i ω :=
    fun i ω => Real.iSup_nonneg (fun r => abs_nonneg _)
  have hSGnn : ∀ i ω, 0 ≤ SG i ω :=
    fun i ω => Real.iSup_nonneg (fun r => abs_nonneg _)
  have hSYm : ∀ i, Measurable (SY i) :=
    fun i => Measurable.iSup (fun r => (((measurable_pi_apply r).comp (hYm i)).sub measurable_const).abs)
  have hSGm : ∀ i, Measurable (SG i) :=
    fun i => Measurable.iSup (fun r => (((measurable_pi_apply r).comp (hGm i)).sub measurable_const).abs)
  have hTrownn : ∀ i x, 0 ≤ Trow i x :=
    fun i x => (hSYnn i x.1).trans (le_max_left _ _)
  have hTrowm : ∀ i, Measurable (Trow i) := fun i =>
    ((hSYm i).comp measurable_fst).max
      (((hSGm i).comp measurable_fst).max ((hSGm i).comp measurable_snd))
  have hMaxInt : ∀ (A : Ω → Fin p → ℝ), Measurable A →
      (∀ r, Integrable (fun ω => |A ω r| ^ 3) P) →
      Integrable (fun ω => (maxAbs (A ω)) ^ 3) P := by
    intro A hAm hA3
    have hsumInt : Integrable (fun ω => ∑ r, |A ω r| ^ 3) P :=
      integrable_finset_sum Finset.univ (fun r _ => hA3 r)
    refine hsumInt.mono'
      ((Measurable.iSup (fun r => ((measurable_pi_apply r).comp hAm).abs)).pow_const 3).aestronglyMeasurable ?_
    filter_upwards with ω
    have h0 : 0 ≤ maxAbs (A ω) := Real.iSup_nonneg (fun r => abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 3)]
    obtain ⟨r, hr⟩ := exists_eq_ciSup_of_finite (f := fun r => |A ω r|)
    change (⨆ r, |A ω r|) ^ 3 ≤ _
    rw [← hr]
    exact Finset.single_le_sum (f := fun r : Fin p => |A ω r| ^ 3) (fun r _ => pow_nonneg (abs_nonneg _) 3) (Finset.mem_univ r)
  have hSY3 : ∀ i, Integrable (fun ω => (SY i ω) ^ 3) P := fun i =>
    hMaxInt (fun ω r => Y i ω r - muY r)
      (measurable_pi_iff.mpr (fun r => ((measurable_pi_apply r).comp (hYm i)).sub measurable_const))
      (hY3 i)
  have hSG3 : ∀ i, Integrable (fun ω => (SG i ω) ^ 3) P := fun i =>
    hMaxInt (fun ω r => G i ω r - muY r)
      (measurable_pi_iff.mpr (fun r => ((measurable_pi_apply r).comp (hGm i)).sub measurable_const))
      (hG3 i)
  have hTrow3 : ∀ i, Integrable (fun x => (Trow i x) ^ 3) (P.prod P) := by
    intro i
    have hdomInt := (((hSY3 i).comp_fst P).add ((hSG3 i).comp_fst P)).add ((hSG3 i).comp_snd P)
    refine hdomInt.mono' ((hTrowm i).pow_const 3).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hTrownn i x) 3)]
    have H := DCFYReview.max_cube_bad_le_own_tails (SY i x.1) (SG i x.1) (SG i x.2) (-1)
      (hSYnn i x.1) (hSGnn i x.1) (hSGnn i x.2)
    have ha : (-1 : ℝ) < SY i x.1 := by linarith [hSYnn i x.1]
    have hb : (-1 : ℝ) < SG i x.1 := by linarith [hSGnn i x.1]
    have hc : (-1 : ℝ) < SG i x.2 := by linarith [hSGnn i x.2]
    have hm : (-1 : ℝ) < Trow i x := by linarith [hTrownn i x]
    change (if (-1 : ℝ) < Trow i x then (Trow i x)^3 else 0) ≤
      (if (-1 : ℝ) < SY i x.1 then (SY i x.1)^3 else 0) +
      (if (-1 : ℝ) < SG i x.1 then (SG i x.1)^3 else 0) +
      (if (-1 : ℝ) < SG i x.2 then (SG i x.2)^3 else 0) at H
    rw [if_pos hm, if_pos ha, if_pos hb, if_pos hc] at H
    exact H
  have hgood_Trow : ∀ i x, x ∈ good i ↔ Trow i x ≤ ell := by
    intro i x
    rw [hgood_fields]
    have hSYiff : (∀ r, |Y i x.1 r - muY r| ≤ ell) ↔ SY i x.1 ≤ ell := by
      constructor
      · intro H; exact ciSup_le H
      · intro H r; exact (hcoordY i x.1 r).trans H
    have hSGiff : ∀ ω, (∀ r, |G i ω r - muY r| ≤ ell) ↔ SG i ω ≤ ell := by
      intro ω
      constructor
      · intro H; exact ciSup_le H
      · intro H r; exact (hcoordG i ω r).trans H
    exact (and_congr hSYiff (and_congr (hSGiff x.1) (hSGiff x.2))).trans
      (by simp only [Trow, max_le_iff])
  let badTail : Fin m → ℝ := fun i =>
    ∫ x, Set.indicator {x | ell < Trow i x} (fun x => (Trow i x) ^ 3) x ∂(P.prod P)
  have hbadTailInt : ∀ i, Integrable
      (Set.indicator {x | ell < Trow i x} (fun x => (Trow i x) ^ 3)) (P.prod P) :=
    fun i => (hTrow3 i).indicator (measurableSet_lt measurable_const (hTrowm i))
  have hbadTailnn : ∀ i, 0 ≤ badTail i := by
    intro i
    apply integral_nonneg
    intro x
    change 0 ≤ (if ell < Trow i x then (Trow i x)^3 else 0)
    by_cases hx : ell < Trow i x
    · rw [if_pos hx]
      exact pow_nonneg (hTrownn i x) 3
    · rw [if_neg hx]
  have hthreshold_bad : ∀ i, ell ^ 3 * (1 - (P.prod P).real (good i)) ≤ badTail i := by
    intro i
    have hbadEq : (good i)ᶜ = {x | ell < Trow i x} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hgood_Trow, not_le]
    have hindInt : Integrable ((good i)ᶜ.indicator (fun _ => ell ^ 3)) (P.prod P) :=
      (integrable_const _).indicator (hgoodm i).compl
    have H : (∫ x, (good i)ᶜ.indicator (fun _ => ell ^ 3) x ∂(P.prod P)) ≤ badTail i := by
      apply integral_mono hindInt (hbadTailInt i)
      intro x
      rw [hbadEq]
      change (if ell < Trow i x then ell^3 else 0) ≤
        (if ell < Trow i x then (Trow i x)^3 else 0)
      by_cases hx : ell < Trow i x
      · simp only [if_pos hx]
        exact pow_le_pow_left₀ hellpos'.le hx.le 3
      · simp only [if_neg hx, le_refl]
    have hIntEq : (∫ x, (good i)ᶜ.indicator (fun _ => ell ^ 3) x ∂(P.prod P)) =
        (P.prod P).real ((good i)ᶜ) * ell ^ 3 := by
      rw [integral_indicator (hgoodm i).compl, setIntegral_const, smul_eq_mul]
    rw [hIntEq, measureReal_compl (hgoodm i)] at H
    simpa only [measureReal_univ_eq_one, mul_comm] using H
  have hmoment_bad_split : ∀ i, (∫ x, (Trow i x)^3 ∂(P.prod P)) ≤ ell^3 + badTail i := by
    intro i
    have hsumInt := (integrable_const (ell^3)).add (hbadTailInt i)
    calc (∫ x, (Trow i x)^3 ∂(P.prod P))
        ≤ ∫ x, ell^3 + Set.indicator {x | ell < Trow i x} (fun x => (Trow i x)^3) x ∂(P.prod P) := by
          apply integral_mono (hTrow3 i) hsumInt
          intro x
          change (Trow i x)^3 ≤ ell^3 + (if ell < Trow i x then (Trow i x)^3 else 0)
          by_cases hx : ell < Trow i x
          · rw [if_pos hx]
            linarith [pow_nonneg hellpos'.le 3]
          · rw [if_neg hx, add_zero]
            exact pow_le_pow_left₀ (hTrownn i x) (le_of_not_gt hx) 3
      _ = ell^3 + badTail i := by
          rw [integral_add (integrable_const _) (hbadTailInt i), integral_const]
          simp only [measureReal_univ_eq_one, one_smul]
          rfl
  have hsmall_good_absorb : ∀ i, (P.prod P).real (good i) < (1 / 2 : ℝ) →
      (∫ x, (Trow i x)^3 ∂(P.prod P)) ≤ 3 * badTail i := by
    intro i hprob
    exact DCFYReview.small_good_moment_absorbed _ _ _ _ hprob (pow_nonneg hellpos'.le 3)
      (hthreshold_bad i) (hmoment_bad_split i)

  let tailY : Fin m → Ω → ℝ := fun i =>
    Set.indicator {ω | ell < SY i ω} (fun ω => (SY i ω)^3)
  let tailG : Fin m → Ω → ℝ := fun i =>
    Set.indicator {ω | ell < SG i ω} (fun ω => (SG i ω)^3)
  have htailYint : ∀ i, Integrable (tailY i) P := fun i =>
    (hSY3 i).indicator (measurableSet_lt measurable_const (hSYm i))
  have htailGint : ∀ i, Integrable (tailG i) P := fun i =>
    (hSG3 i).indicator (measurableSet_lt measurable_const (hSGm i))
  have htailYnn : ∀ i ω, 0 ≤ tailY i ω := by
    intro i ω
    change 0 ≤ (if ell < SY i ω then (SY i ω)^3 else 0)
    by_cases h : ell < SY i ω
    · simp only [if_pos h]
      exact pow_nonneg (hSYnn i ω) 3
    · simp only [if_neg h, le_refl]
  have htailGnn : ∀ i ω, 0 ≤ tailG i ω := by
    intro i ω
    change 0 ≤ (if ell < SG i ω then (SG i ω)^3 else 0)
    by_cases h : ell < SG i ω
    · simp only [if_pos h]
      exact pow_nonneg (hSGnn i ω) 3
    · simp only [if_neg h, le_refl]
  have hbadTail_own : ∀ i, badTail i ≤ (∫ ω, tailY i ω ∂P) + 2 * (∫ ω, tailG i ω ∂P) := by
    intro i
    have hsumsInt := (((htailYint i).comp_fst P).add ((htailGint i).comp_fst P)).add
      ((htailGint i).comp_snd P)
    calc badTail i ≤ ∫ x : Ω × Ω, tailY i x.1 + tailG i x.1 + tailG i x.2 ∂(P.prod P) := by
          apply integral_mono (hbadTailInt i) hsumsInt
          intro x
          have H := DCFYReview.max_cube_bad_le_own_tails (SY i x.1) (SG i x.1) (SG i x.2) ell
            (hSYnn i x.1) (hSGnn i x.1) (hSGnn i x.2)
          exact H
      _ = _ := by
          have H1 := integral_add (((htailYint i).comp_fst P).add ((htailGint i).comp_fst P))
            ((htailGint i).comp_snd P)
          have H2 := integral_add ((htailYint i).comp_fst P) ((htailGint i).comp_fst P)
          dsimp only [Pi.add_apply] at H1 H2
          rw [H1, H2, integral_fun_fst, integral_fun_fst, integral_fun_snd]
          simp only [measureReal_univ_eq_one, one_smul]
          ring
  have hMstar_identity : (m : ℝ) * Mstar P m (delta n m) muY Y G (min phi1 phi2) =
      (∑ i, ∫ ω, tailY i ω ∂P) + (∑ i, ∫ ω, tailG i ω ∂P) := by
    have hell_formula : ell = Real.sqrt (m : ℝ) /
        (4 * |delta n m| * min phi1 phi2 * Real.log (p : ℝ)) := by
      dsimp only [ell]
      congr 1
      ring
    unfold Mstar MY MG
    rw [if_neg hd, if_neg hd]
    change (m : ℝ) * ((m : ℝ)⁻¹ * (∑ i, ∫ ω, Set.indicator
        {ω | Real.sqrt (m : ℝ) / (4 * |delta n m| * min phi1 phi2 * Real.log (p : ℝ)) < SY i ω}
        (fun ω => (SY i ω)^3) ω ∂P) + (m : ℝ)⁻¹ * (∑ i, ∫ ω, Set.indicator
        {ω | Real.sqrt (m : ℝ) / (4 * |delta n m| * min phi1 phi2 * Real.log (p : ℝ)) < SG i ω}
        (fun ω => (SG i ω)^3) ω ∂P)) = _
    rw [← hell_formula]
    change (m : ℝ) * ((m : ℝ)⁻¹ * (∑ i, ∫ ω, tailY i ω ∂P) +
      (m : ℝ)⁻¹ * (∑ i, ∫ ω, tailG i ω ∂P)) = _
    calc _ = ((m : ℝ) * (m : ℝ)⁻¹) *
        ((∑ i, ∫ ω, tailY i ω ∂P) + (∑ i, ∫ ω, tailG i ω ∂P)) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hmR), one_mul]
  have hbadTail_sum : (∑ i, badTail i) ≤ 2 * (m : ℝ) * Mstar P m (delta n m) muY Y G phi2 := by
    have hYsum0 : 0 ≤ ∑ i, ∫ ω, tailY i ω ∂P :=
      Finset.sum_nonneg (fun i _ => integral_nonneg (htailYnn i))
    calc (∑ i, badTail i) ≤ ∑ i, ((∫ ω, tailY i ω ∂P) + 2 * (∫ ω, tailG i ω ∂P)) :=
          Finset.sum_le_sum (fun i _ => hbadTail_own i)
      _ = (∑ i, ∫ ω, tailY i ω ∂P) + 2 * (∑ i, ∫ ω, tailG i ω ∂P) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * ((∑ i, ∫ ω, tailY i ω ∂P) + (∑ i, ∫ ω, tailG i ω ∂P)) := by linarith
      _ = 2 * ((m : ℝ) * Mstar P m (delta n m) muY Y G (min phi1 phi2)) := by rw [hMstar_identity]
      _ ≤ 2 * ((m : ℝ) * Mstar P m (delta n m) muY Y G phi2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMstarmono hmR.le) (by norm_num)
      _ = _ := by ring
  have hG3_compare : ∀ i r, (∫ ω, |G i ω r - muY r|^3 ∂P) ≤
      8 * ∫ ω, |Y i ω r - muY r|^3 ∂P := by
    intro i r
    apply DCFGaussianThirdReview.gaussian_coordinate_centered_third_le_eight P
      (fun ω j => G i ω j - muY j) (covY P muY Y i) (hGcov i) r
      (fun ω => Y i ω r) (muY r) ((measurable_pi_apply r).comp (hYm i)) (hYL2 i r)
      (hYmean i r) (hY3 i r)
    simp only [covY, pow_two]
  have hLG_LY : LG ≤ 8 * LY P m muY Y := by
    apply ciSup_le
    intro r
    calc (m : ℝ)⁻¹ * (∑ i, ∫ ω, |G i ω r - muY r|^3 ∂P)
        ≤ (m : ℝ)⁻¹ * (∑ i, 8 * ∫ ω, |Y i ω r - muY r|^3 ∂P) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hG3_compare i r)) hminv
      _ = 8 * ((m : ℝ)⁻¹ * ∑ i, ∫ ω, |Y i ω r - muY r|^3 ∂P) := by rw [← Finset.mul_sum]; ring
      _ ≤ 8 * LY P m muY Y := mul_le_mul_of_nonneg_left (hLYelem r) (by norm_num)

  let remCoord : Fin m → Fin p → Ω × Ω → ℝ := fun i j x =>
    (fderiv ℝ KAP (W i x + ZSS t x i)) (Pi.single j 1) -
      (fderiv ℝ KAP (W i x)) (Pi.single j 1) -
      ∑ k, (fderiv ℝ (fun z => (fderiv ℝ KAP z) (Pi.single j 1)) (W i x))
        (Pi.single k 1) * ZSS t x i k
  let rem : Fin m → Ω × Ω → ℝ := fun i x => ∑ j, remCoord i j x * ZD t x i j
  have hremWhole : ∀ i x, |rem i x| ≤
      ((C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ))^2) / 2) *
        (maxAbs (ZSS t x i)) ^ 2 * maxAbs (ZD t x i) := by
    intro i x
    exact DCFDirectionalTaylor.whole_coordinate_remainder_majorant p hp KAP hKAPcontDiff
      (W i x) (ZSS t x i) (ZD t x i) R _ hRmaj (fun s hs => hRmass _)
  have hremCoordGood : ∀ i x, x ∈ good i → ∀ j,
      |remCoord i j x| ≤ (1 / 2) * ∑ k, ∑ l,
        (C3 * weight l k j (W i x)) * |ZSS t x i k| * |ZSS t x i l| := by
    intro i x hx j
    apply statopia_math_node_2945293653_548ae0bd p KAP hKAPcontDiff (W i x) (ZSS t x i) j
      (fun k l => C3 * weight l k j (W i x))
    intro s hs k l
    have H := hRmajGood i x hx s hs l k j
    have hvec : (fun a : Fin 3 => Pi.single ((![l,k,j] : Fin 3 → Fin p) a) (1 : ℝ)) =
        ![Pi.single l (1 : ℝ), Pi.single k (1 : ℝ), Pi.single j (1 : ℝ)] := by
      funext a
      fin_cases a <;> rfl
    rw [hvec, DCFDirectionalTaylor.iterated_third_eq_nested,
      ← DCFDirectionalTaylor.derivative_eval_third p KAP hKAPcontDiff] at H
    exact H
  have hremGood : ∀ i x, x ∈ good i → |rem i x| ≤
      (C3 / 2) * ∑ j, ∑ k, ∑ l,
        weight l k j (W i x) * |ZSS t x i k * ZSS t x i l * ZD t x i j| := by
    intro i x hx
    calc |rem i x| ≤ ∑ j, |remCoord i j x * ZD t x i j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |remCoord i j x| * |ZD t x i j| := by simp only [abs_mul]
      _ ≤ ∑ j, ((1 / 2) * ∑ k, ∑ l, C3 * weight l k j (W i x) *
          |ZSS t x i k| * |ZSS t x i l|) * |ZD t x i j| :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hremCoordGood i x hx j) (abs_nonneg _))
      _ = _ := by
          simp only [abs_mul, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          ring
  have hremCoordInt : ∀ i j, Integrable (fun x => remCoord i j x * ZD t x i j) (P.prod P) := by
    intro i j
    have H := ((hInt1 i j).sub (hInt2 i j)).sub
      (integrable_finset_sum Finset.univ (fun k _ => hInt3 i j k))
    refine H.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [remCoord, Pi.sub_apply, sub_mul, Finset.sum_mul]
    rfl
  have hremInt : ∀ i, Integrable (rem i) (P.prod P) := fun i =>
    integrable_finset_sum Finset.univ (fun j _ => hremCoordInt i j)
  have hremCoordExpectation : ∀ i j, (∫ x, remCoord i j x * ZD t x i j ∂(P.prod P)) =
      ∫ x, (fderiv ℝ KAP (ZC t x)) (Pi.single j 1) * ZD t x i j ∂(P.prod P) := by
    intro i j
    have H : (∫ x, remCoord i j x * ZD t x i j ∂(P.prod P)) =
        (∫ x, (fderiv ℝ KAP (W i x + ZSS t x i)) (Pi.single j 1) * ZD t x i j ∂(P.prod P)) -
        (∫ x, (fderiv ℝ KAP (W i x)) (Pi.single j 1) * ZD t x i j ∂(P.prod P)) -
        ∑ k, ∫ x, (fderiv ℝ (fun z => (fderiv ℝ KAP z) (Pi.single j 1)) (W i x))
          (Pi.single k 1) * ZSS t x i k * ZD t x i j ∂(P.prod P) := by
      have heq : (fun x => remCoord i j x * ZD t x i j) =
          (fun x => (fderiv ℝ KAP (W i x + ZSS t x i)) (Pi.single j 1) * ZD t x i j) -
          (fun x => (fderiv ℝ KAP (W i x)) (Pi.single j 1) * ZD t x i j) -
          (fun x => ∑ k, (fderiv ℝ (fun z => (fderiv ℝ KAP z) (Pi.single j 1)) (W i x))
            (Pi.single k 1) * ZSS t x i k * ZD t x i j) := by
        funext x
        simp only [remCoord, Pi.sub_apply, sub_mul, Finset.sum_mul]
      have HI1 : Integrable (fun x => (fderiv ℝ KAP (W i x + ZSS t x i))
          (Pi.single j 1) * ZD t x i j) (P.prod P) := hInt1 i j
      have HI2 : Integrable (fun x => (fderiv ℝ KAP (W i x))
          (Pi.single j 1) * ZD t x i j) (P.prod P) := hInt2 i j
      have HI3 : Integrable (fun x => ∑ k, (fderiv ℝ (fun z =>
          (fderiv ℝ KAP z) (Pi.single j 1)) (W i x)) (Pi.single k 1) *
          ZSS t x i k * ZD t x i j) (P.prod P) :=
        integrable_finset_sum Finset.univ (fun k _ => hInt3 i j k)
      rw [heq]
      refine (integral_sub (HI1.sub HI2) HI3).trans ?_
      dsimp only [Pi.sub_apply]
      rw [integral_sub HI1 HI2, integral_finset_sum Finset.univ (fun k _ => hInt3 i j k)]
    have hE1' : ∀ k, (∫ x, (fderiv ℝ (fun z => (fderiv ℝ KAP z) (Pi.single j 1)) (W i x))
        (Pi.single k 1) * ZSS t x i k * ZD t x i j ∂(P.prod P)) = 0 := fun k => (hE1 i j k).2
    rw [H, hE0 i j]
    simp only [hE1', sub_zero, Finset.sum_const_zero]
    apply integral_congr_ae
    filter_upwards with x
    have HE : W i x + ZSS t x i = ZC t x := hZC_add i x
    rw [HE]

  have hweight_factor_general : ∀ i a b c j k l,
      (∫ x, weight a b c (W i x) * |ZSS t x i k * ZSS t x i l * ZD t x i j| ∂(P.prod P)) =
        (∫ x, weight a b c (W i x) ∂(P.prod P)) * rowMoment i j k l := by
    intro i a b c j k l
    have H := (hWindep i).comp (hweightm a b c) (hrowproductm j k l)
    exact H.integral_fun_mul_eq_mul_integral (hweightint i a b c).aestronglyMeasurable
      ((((hZSSm i k).mul (hZSSm i l)).mul (hZDm i j)).abs.aestronglyMeasurable)
  have hweightedProductInt : ∀ i a b c j k l,
      Integrable (fun x => weight a b c (W i x) * |ZSS t x i k * ZSS t x i l * ZD t x i j|)
        (P.prod P) := by
    intro i a b c j k l
    refine (hmoment i j k l).1.bdd_mul (c := C1 * C2 * (min phi1 phi2) *
      (min phi1 phi2 * Real.log (p : ℝ))^2)
      (((hweightm a b c).comp (hWmeas i)).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hweightnn a b c (W i x))]
    by_cases hw : W i x ∈ smallStrip
    · simpa only [weight, Set.indicator_of_mem hw] using hRsingle a b c (W i x)
    · simpa only [weight, Set.indicator_of_notMem hw] using hC12nn
  let correctGoodTerm : Fin m → Fin p × Fin p × Fin p → ℝ := fun i abc =>
    if (1 / 2 : ℝ) ≤ (P.prod P).real (good i) then
      ∫ x, weight abc.1 abc.2.1 abc.2.2 (W i x) *
        |ZSS t x i abc.2.1 * ZSS t x i abc.1 * ZD t x i abc.2.2| ∂(P.prod P)
    else 0
  have hcorrectGoodTermnn : ∀ i abc, 0 ≤ correctGoodTerm i abc := by
    intro i abc
    dsimp only [correctGoodTerm]
    split_ifs
    · apply integral_nonneg
      intro x
      exact mul_nonneg (hweightnn _ _ _ _) (abs_nonneg _)
    · exact le_rfl
  have hcorrectGoodTermBound : ∀ i abc, correctGoodTerm i abc ≤
      (2 * C3) * commonMean abc.1 abc.2.1 abc.2.2 * rowMoment i abc.2.2 abc.2.1 abc.1 := by
    intro i abc
    by_cases hprob : (1 / 2 : ℝ) ≤ (P.prod P).real (good i)
    · dsimp only [correctGoodTerm]
      rw [if_pos hprob, hweight_factor_general]
      exact mul_le_mul_of_nonneg_right (hweight_common_transfer i abc.1 abc.2.1 abc.2.2 hprob)
        (hrowMomentnn _ _ _ _)
    · simp only [correctGoodTerm, if_neg hprob]
      exact mul_nonneg (mul_nonneg (by positivity) (hcommonMeannn _ _ _)) (hrowMomentnn _ _ _ _)
  have hcorrectGoodGlobal : (∑ i, ∑ abc, correctGoodTerm i abc) ≤
      (2 * C3) * momentCap * (∑ j, ∑ k, ∑ l, commonMean j k l) := by
    have H := DCFYReview.weighted_row_sum_bound correctGoodTerm
      (fun i (abc : Fin p × Fin p × Fin p) => rowMoment i abc.2.2 abc.2.1 abc.1)
      (fun abc => commonMean abc.1 abc.2.1 abc.2.2)
      (2 * C3) momentCap (∑ abc : Fin p × Fin p × Fin p, commonMean abc.1 abc.2.1 abc.2.2)
      (by positivity) hmomentCapnn (fun abc => hcommonMeannn _ _ _) hcorrectGoodTermBound
      (fun abc => hreal_moment_sum _ _ _) le_rfl
    simpa only [Fintype.sum_prod_type] using H
  let goodDensity : Fin m → Ω × Ω → ℝ := fun i x =>
    ∑ abc : Fin p × Fin p × Fin p, weight abc.1 abc.2.1 abc.2.2 (W i x) *
      |ZSS t x i abc.2.1 * ZSS t x i abc.1 * ZD t x i abc.2.2|
  have hgoodDensitynn : ∀ i x, 0 ≤ goodDensity i x := fun i x =>
    Finset.sum_nonneg (fun abc _ => mul_nonneg (hweightnn _ _ _ _) (abs_nonneg _))
  have hgoodDensityInt : ∀ i, Integrable (goodDensity i) (P.prod P) := fun i =>
    integrable_finset_sum Finset.univ (fun abc _ => hweightedProductInt i _ _ _ _ _ _)
  have hremGoodDensity : ∀ i x, x ∈ good i → |rem i x| ≤ (C3 / 2) * goodDensity i x := by
    intro i x hx
    have H := hremGood i x hx
    have HE : (∑ j, ∑ k, ∑ l, weight l k j (W i x) *
        |ZSS t x i k * ZSS t x i l * ZD t x i j|) = goodDensity i x := by
      dsimp only [goodDensity]
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_prod_type]
      calc (∑ j, ∑ k, ∑ l, weight l k j (W i x) * |ZSS t x i k * ZSS t x i l * ZD t x i j|)
          = ∑ j, ∑ l, ∑ k, weight l k j (W i x) * |ZSS t x i k * ZSS t x i l * ZD t x i j| :=
            Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
        _ = ∑ l, ∑ j, ∑ k, weight l k j (W i x) * |ZSS t x i k * ZSS t x i l * ZD t x i j| :=
            Finset.sum_comm
        _ = _ := Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
    rwa [HE] at H
  have hlarge_good_integral : ∀ i, (1 / 2 : ℝ) ≤ (P.prod P).real (good i) →
      (∫ x, (good i).indicator (fun x => |rem i x|) x ∂(P.prod P)) ≤
        (C3 / 2) * ∑ abc, correctGoodTerm i abc := by
    intro i hprob
    calc (∫ x, (good i).indicator (fun x => |rem i x|) x ∂(P.prod P))
        ≤ ∫ x, (C3 / 2) * goodDensity i x ∂(P.prod P) := by
          apply integral_mono ((hremInt i).abs.indicator (hgoodm i)) ((hgoodDensityInt i).const_mul _)
          intro x
          by_cases hx : x ∈ good i
          · simpa only [Set.indicator_of_mem hx] using hremGoodDensity i x hx
          · simpa only [Set.indicator_of_notMem hx] using
              mul_nonneg (div_nonneg (le_trans zero_le_one hC3) (by norm_num)) (hgoodDensitynn i x)
      _ = (C3 / 2) * ∑ abc, correctGoodTerm i abc := by
          rw [integral_const_mul, integral_finset_sum Finset.univ
            (fun abc _ => hweightedProductInt i _ _ _ _ _ _)]
          congr 1
          apply Finset.sum_congr rfl
          intro abc _
          simp only [correctGoodTerm, if_pos hprob]

  let scaleRow : ℝ := (Real.sqrt (m : ℝ))⁻¹ * |delta n m|
  let timeFactor : ℝ := (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹
  let derivativeBudget : ℝ := C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ))^2
  let coarseC : ℝ := (27 / 2) * derivativeBudget * ((Real.sqrt (m : ℝ))⁻¹)^3 *
    |delta n m|^3 * timeFactor
  have hscaleRownn : 0 ≤ scaleRow := by dsimp only [scaleRow]; positivity
  have htimeFactornn : 0 ≤ timeFactor := by dsimp only [timeFactor]; positivity
  have hcoarseCnn : 0 ≤ coarseC := by dsimp only [coarseC]; positivity
  have hRowMaxBounds : ∀ i x, maxAbs (ZSS t x i) ≤ 3 * scaleRow * Trow i x ∧
      maxAbs (ZD t x i) ≤ 3 * scaleRow * timeFactor * Trow i x := by
    intro i x
    have hA : SY i x.1 ≤ Trow i x := le_max_left _ _
    have hB : SG i x.1 ≤ Trow i x := (le_max_left _ _).trans (le_max_right _ _)
    have hC : SG i x.2 ≤ Trow i x := (le_max_right _ _).trans (le_max_right _ _)
    have hsum : SY i x.1 + SG i x.1 + SG i x.2 ≤ 3 * Trow i x := by linarith
    constructor
    · apply ciSup_le
      intro r
      calc |ZSS t x i r| ≤ scaleRow * (SY i x.1 + SG i x.1 + SG i x.2) := hZSSmax i x r
        _ ≤ scaleRow * (3 * Trow i x) := mul_le_mul_of_nonneg_left hsum hscaleRownn
        _ = _ := by ring
    · apply ciSup_le
      intro r
      have hcoeff : (2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹ = (1 / 2) * timeFactor := by
        dsimp only [timeFactor]
        rw [mul_inv, mul_inv]
        norm_num
        ring
      calc |ZD t x i r| ≤ scaleRow *
          (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
            (SY i x.1 + SG i x.1 + SG i x.2)) := hZDmaxAbs i x r
        _ = scaleRow * (((1 / 2) * timeFactor) * (SY i x.1 + SG i x.1 + SG i x.2)) := by rw [hcoeff]
        _ ≤ scaleRow * (timeFactor * (3 * Trow i x)) := by
          apply mul_le_mul_of_nonneg_left _ hscaleRownn
          exact mul_le_mul (by linarith) hsum
            (by linarith [hSYnn i x.1, hSGnn i x.1, hSGnn i x.2]) htimeFactornn
        _ = _ := by ring
  have hremCoarse : ∀ i x, |rem i x| ≤ coarseC * (Trow i x)^3 := by
    intro i x
    have hU0 : 0 ≤ maxAbs (ZSS t x i) := Real.iSup_nonneg (fun r => abs_nonneg _)
    have hD0 : 0 ≤ maxAbs (ZD t x i) := Real.iSup_nonneg (fun r => abs_nonneg _)
    have hsq := pow_le_pow_left₀ hU0 (hRowMaxBounds i x).1 2
    have hB0 : 0 ≤ derivativeBudget / 2 := div_nonneg hC12nn (by norm_num)
    calc |rem i x| ≤ (derivativeBudget / 2) * (maxAbs (ZSS t x i))^2 * maxAbs (ZD t x i) := hremWhole i x
      _ ≤ (derivativeBudget / 2) * (3 * scaleRow * Trow i x)^2 *
          (3 * scaleRow * timeFactor * Trow i x) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq hB0) (hRowMaxBounds i x).2 hD0
            (mul_nonneg hB0 (sq_nonneg _))
      _ = coarseC * (Trow i x)^3 := by dsimp only [coarseC, scaleRow]; ring
  have hremBadIntegral : ∀ i, (∫ x, (good i)ᶜ.indicator (fun x => |rem i x|) x ∂(P.prod P)) ≤
      coarseC * badTail i := by
    intro i
    calc (∫ x, (good i)ᶜ.indicator (fun x => |rem i x|) x ∂(P.prod P))
        ≤ ∫ x, coarseC * Set.indicator {x | ell < Trow i x} (fun x => (Trow i x)^3) x ∂(P.prod P) := by
          apply integral_mono ((hremInt i).abs.indicator (hgoodm i).compl) ((hbadTailInt i).const_mul _)
          intro x
          change (good i)ᶜ.indicator (fun x => |rem i x|) x ≤ coarseC *
            Set.indicator {x | ell < Trow i x} (fun x => (Trow i x)^3) x
          by_cases hx : x ∈ good i
          · have hcomp : x ∉ (good i)ᶜ := by simpa only [Set.mem_compl_iff, not_not] using hx
            have hbad : x ∉ {x | ell < Trow i x} := not_lt_of_ge ((hgood_Trow i x).mp hx)
            rw [Set.indicator_of_notMem hcomp, Set.indicator_of_notMem hbad, mul_zero]
          · have hcomp : x ∈ (good i)ᶜ := hx
            have hbad : x ∈ {x | ell < Trow i x} :=
              lt_of_not_ge (fun H => hx ((hgood_Trow i x).mpr H))
            rw [Set.indicator_of_mem hcomp, Set.indicator_of_mem hbad]
            exact hremCoarse i x
      _ = _ := integral_const_mul _ _
  have hremIntegralDichotomy : ∀ i, (∫ x, |rem i x| ∂(P.prod P)) ≤
      (C3 / 2) * ∑ abc, correctGoodTerm i abc + 3 * coarseC * badTail i := by
    intro i
    by_cases hprob : (1 / 2 : ℝ) ≤ (P.prod P).real (good i)
    · have HE : (∫ x, |rem i x| ∂(P.prod P)) =
          (∫ x, (good i).indicator (fun x => |rem i x|) x ∂(P.prod P)) +
          (∫ x, (good i)ᶜ.indicator (fun x => |rem i x|) x ∂(P.prod P)) := by
        rw [integral_indicator (hgoodm i), integral_indicator (hgoodm i).compl,
          integral_add_compl (hgoodm i) (hremInt i).abs]
      rw [HE]
      have H1 := hlarge_good_integral i hprob
      have H2 := hremBadIntegral i
      have H0 := mul_nonneg hcoarseCnn (hbadTailnn i)
      nlinarith
    · have hprob' : (P.prod P).real (good i) < (1 / 2 : ℝ) := lt_of_not_ge hprob
      have H1 : (∫ x, |rem i x| ∂(P.prod P)) ≤ coarseC * ∫ x, (Trow i x)^3 ∂(P.prod P) := by
        calc _ ≤ ∫ x, coarseC * (Trow i x)^3 ∂(P.prod P) :=
            integral_mono (hremInt i).abs ((hTrow3 i).const_mul _) (hremCoarse i)
          _ = _ := integral_const_mul _ _
      have H2 := mul_le_mul_of_nonneg_left (hsmall_good_absorb i hprob') hcoarseCnn
      have HE : (∑ abc, correctGoodTerm i abc) = 0 := by
        simp only [correctGoodTerm, if_neg hprob, Finset.sum_const_zero]
      rw [HE, mul_zero, zero_add]
      nlinarith

  let S : ℝ := (Real.sqrt (m : ℝ))⁻¹ * |delta n m|^3 * timeFactor
  let locBudget : ℝ := 2 * rho P n m p (delta n m) muX muY X Y F G +
    Cb * ((min phi1 phi2)⁻¹ + 2 * (min phi1 phi2 * Real.log (p : ℝ))⁻¹) *
      Real.sqrt (Real.log (p : ℝ))
  have hSnn : 0 ≤ S := by dsimp only [S]; positivity
  have hlocBudgetnn : 0 ≤ locBudget := by dsimp only [locBudget]; positivity
  have hcapCompare : momentCap ≤ (153 / 2) * S * LY P m muY Y := by
    have H := mul_le_mul_of_nonneg_left (show LY P m muY Y + 2 * LG ≤ 17 * LY P m muY Y by
      linarith [hLG_LY]) (show 0 ≤ (9 / 2 : ℝ) * S by positivity)
    change (9 / 2) * S * (LY P m muY Y + 2 * LG) ≤ _ at H
    convert H using 1 <;> dsimp only [momentCap, S] <;> ring
  have hgoodGlobalFinal : (C3 / 2) * (∑ i, ∑ abc, correctGoodTerm i abc) ≤
      C3^2 * ((153 / 2) * S * LY P m muY Y) * derivativeBudget * locBudget := by
    calc _ ≤ (C3 / 2) * ((2 * C3) * momentCap * (∑ j, ∑ k, ∑ l, commonMean j k l)) :=
          mul_le_mul_of_nonneg_left hcorrectGoodGlobal (by positivity)
      _ = C3^2 * momentCap * (∑ j, ∑ k, ∑ l, commonMean j k l) := by ring
      _ ≤ C3^2 * momentCap * (derivativeBudget * locBudget) :=
          mul_le_mul_of_nonneg_left hcommonMeanSum (mul_nonneg (sq_nonneg _) hmomentCapnn)
      _ ≤ C3^2 * ((153 / 2) * S * LY P m muY Y) * (derivativeBudget * locBudget) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcapCompare (sq_nonneg _)) (mul_nonneg hC12nn hlocBudgetnn)
      _ = _ := by ring
  have htailGlobalFinal : (3 * coarseC) * (∑ i, badTail i) ≤
      81 * derivativeBudget * S * Mstar P m (delta n m) muY Y G phi2 := by
    calc _ ≤ (3 * coarseC) * (2 * (m : ℝ) * Mstar P m (delta n m) muY Y G phi2) :=
          mul_le_mul_of_nonneg_left hbadTail_sum (by positivity)
      _ = 81 * derivativeBudget * ((m : ℝ) * ((Real.sqrt (m : ℝ))⁻¹)^3) *
          |delta n m|^3 * timeFactor * Mstar P m (delta n m) muY Y G phi2 := by
          dsimp only [coarseC]
          ring
      _ = _ := by rw [hsqrtcube]; dsimp only [S]; ring
  have htotalIntegral : (∑ i, ∫ x, |rem i x| ∂(P.prod P)) ≤
      C3^2 * ((153 / 2) * S * LY P m muY Y) * derivativeBudget * locBudget +
        81 * derivativeBudget * S * Mstar P m (delta n m) muY Y G phi2 := by
    have H : (∑ i, ∫ x, |rem i x| ∂(P.prod P)) ≤
        ∑ i, ((C3 / 2) * (∑ abc, correctGoodTerm i abc) + 3 * coarseC * badTail i) :=
      Finset.sum_le_sum (fun i _ => hremIntegralDichotomy i)
    have HE : (∑ i, ((C3 / 2) * (∑ abc, correctGoodTerm i abc) + 3 * coarseC * badTail i)) =
        (C3 / 2) * (∑ i, ∑ abc, correctGoodTerm i abc) + (3 * coarseC) * (∑ i, badTail i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [HE] at H
    exact H.trans (add_le_add hgoodGlobalFinal htailGlobalFinal)
  have hRootRem : (∫ x, (∑ j, ∑ i, (fderiv ℝ KAP (ZC t x)) (Pi.single j 1) *
      ZD t x i j) ∂(P.prod P)) = ∑ i, ∫ x, rem i x ∂(P.prod P) := by
    calc _ = ∑ j, ∑ i, ∫ x, (fderiv ℝ KAP (ZC t x)) (Pi.single j 1) * ZD t x i j ∂(P.prod P) := by
          rw [integral_finset_sum Finset.univ (fun j _ =>
            integrable_finset_sum Finset.univ (fun i _ => hIntZC i j))]
          exact Finset.sum_congr rfl (fun j _ => integral_finset_sum Finset.univ (fun i _ => hIntZC i j))
      _ = ∑ i, ∑ j, ∫ x, (fderiv ℝ KAP (ZC t x)) (Pi.single j 1) * ZD t x i j ∂(P.prod P) :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_finset_sum Finset.univ (fun j _ => hremCoordInt i j)]
          exact Finset.sum_congr rfl (fun j _ => (hremCoordExpectation i j).symm)
  have hRootBound : |∫ x, (∑ j, ∑ i, (fderiv ℝ KAP (ZC t x)) (Pi.single j 1) *
      ZD t x i j) ∂(P.prod P)| ≤ ∑ i, ∫ x, |rem i x| ∂(P.prod P) := by
    rw [hRootRem]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => abs_integral_le_integral_abs))
  have hC2nn : 0 ≤ C2 := by
    by_contra H
    have hC2neg : C2 < 0 := lt_of_not_ge H
    have Hneg : C1 * C2 * (min phi1 phi2) * (min phi1 phi2 * Real.log (p : ℝ))^2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (lt_of_lt_of_le zero_lt_one hC1) hC2neg) hphipos)
        (sq_pos_of_pos hbetapos)
    exact not_lt_of_ge hC12nn Hneg
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log (p : ℝ) := by
    have H : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
    linarith [Real.log_two_gt_d9]
  have HB := DCFManualBudget.remainder_budget (min phi1 phi2) phi2 (Real.log (p : ℝ)) S
    (LY P m muY Y) (rho P n m p (delta n m) muX muY X Y F G)
    (Mstar P m (delta n m) muY Y G phi2) C1 C3 C2 Cb
    hphi (min_le_right phi1 phi2) hloghalf hSnn hLYnn hrhonn hMstarnn hC1 hC3 hC2nn hCb
  have H := hRootBound.trans (htotalIntegral.trans HB)
  convert H using 1 <;> dsimp only [S, timeFactor] <;> ring
  /- @proof-region region.target-node.session.d04636c4d0dc09e5 end -/

end

end Statlib.Imported


