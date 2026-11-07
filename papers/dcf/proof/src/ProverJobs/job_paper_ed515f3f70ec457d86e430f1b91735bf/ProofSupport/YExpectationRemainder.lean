import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.YLocalizedRemainder
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ExternalNodes.Node_df9285a2e94441188459
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

set_option autoImplicit false in
theorem statopia_math_node_3680776236_d8bd4c8f : ∀ (b : ℝ) (hb : 0 < b)
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
    (hp2 : 2 ≤ p),
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
    |∫ x : Ω × Ω, (∫ t in (0 : ℝ)..1, ∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j) ∂(P.prod P)|
      ≤ (10000000 * (((Ckappa + 1) * (C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4 + 1)) *
          (Real.sqrt (m : ℝ))⁻¹ * |delta n m| ^ 3 *
        ((Real.log (p : ℝ)) ^ 2 *
          (phi2 ^ 2 * (phi2 * (LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G) +
            LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
            min phi1 phi2 * Mstar P m (delta n m) muY Y G phi2))) := by
  /- @proof-region region.target-node.session.fc07ea337b28e7e0 begin -/
  intro b hb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
    Ck C1 C2 C3 Cb hCk hC1 hC3 hCb hG hQ hL
    Ω mΩ P hP n m p delta muX muY X Y F G phi1 phi2 y v
    hn hm hp hlogp hdelta
    hXm hYm hFm hGm hindep
    hXL2 hYL2 hX3 hY3 hF3 hG3 hXmean hYmean hFcov hGcov
    hcombint hcomb hphi1 hphi2 hv0 hv1 hp2
  have hmn : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hphimin : (1 : ℝ) ≤ min phi1 phi2 := le_min hphi1 hphi2
  have hphipos : (0 : ℝ) < min phi1 phi2 := lt_of_lt_of_le zero_lt_one hphimin
  have hbeta : (0 : ℝ) < min phi1 phi2 * Real.log (p : ℝ) := mul_pos hphipos hlogp
  have hminle : min phi1 phi2 ≤ phi2 := min_le_right _ _
  have hsqrtm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmn
  have habsdelta : (0 : ℝ) < |delta n m| := abs_pos.2 hdelta
  obtain ⟨Q, hQnonneg, hQthird, hQsum, hQshift⟩ :=
    hQ p hp hlogp (min phi1 phi2) hphimin y
  have hC2nonneg : (0 : ℝ) ≤ C2 := by
    have h0 : (0 : ℝ) ≤
        ∑ a : Fin p, ∑ bb : Fin p, ∑ c : Fin p, Q a bb c (fun _ => (0 : ℝ)) :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun bb _ =>
        Finset.sum_nonneg fun c _ => hQnonneg a bb c _
    have hle := hQsum (fun _ => (0 : ℝ))
    have h1 : (0 : ℝ) < C1 := lt_of_lt_of_le zero_lt_one hC1
    have h2 : (0 : ℝ) < (min phi1 phi2 * Real.log (p : ℝ)) ^ 2 := pow_pos hbeta 2
    have hposfac : (0 : ℝ) < C1 * (min phi1 phi2) *
        ((min phi1 phi2) * Real.log (p : ℝ)) ^ 2 := by
      have h3 : (0 : ℝ) < C1 * (min phi1 phi2) := mul_pos h1 hphipos
      exact mul_pos h3 h2
    have hrew : C1 * C2 * (min phi1 phi2) * ((min phi1 phi2) * Real.log (p : ℝ)) ^ 2
        = (C1 * (min phi1 phi2) * ((min phi1 phi2) * Real.log (p : ℝ)) ^ 2) * C2 := by
      ring
    rw [hrew] at hle
    by_contra hcon
    have hneg : C2 < 0 := not_le.mp hcon
    have hlt := mul_neg_of_pos_of_neg hposfac hneg
    linarith
  have hphi1sq_mono : (min phi1 phi2) ^ 2 ≤ phi2 ^ 2 := by
    have h := mul_le_mul hminle hminle (le_of_lt hphipos) (le_trans (le_of_lt hphipos) hminle)
    simpa [pow_two] using h
  have hphi2gt : (0 : ℝ) < phi2 := lt_of_lt_of_le zero_lt_one hphi2
  have hB1 : (1 : ℝ) ≤ Ck + 1 := by linarith only [hCk]
  have hB2 : (1 : ℝ) ≤ Cb + 1 := by linarith only [hCb]
  have hCsum1 : (1 : ℝ) ≤ C1 + C3 + C2 + 1 := by linarith only [hC1, hC3, hC2nonneg]
  have hBprod : (1 : ℝ) ≤ (Ck + 1) * (C1 + C3 + C2 + 1) * (Cb + 1) := by
    have h1 : (1 : ℝ) ≤ (Ck + 1) * (C1 + C3 + C2 + 1) := by
      have h := mul_le_mul hB1 hCsum1 zero_le_one (le_trans zero_le_one hB1)
      simpa using h
    have h0 : (0 : ℝ) ≤ (Ck + 1) * (C1 + C3 + C2 + 1) := le_trans zero_le_one h1
    have h2 := mul_le_mul h1 hB2 zero_le_one h0
    simpa using h2
  have hIntW1 : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹) volume (0 : ℝ) 1 := by
    refine IntervalIntegrable.congr_ae
      ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
        (r := (-1 : ℝ) / 2) (by norm_num)).const_mul (1 / 2)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
    have ht0 : (0 : ℝ) < t := by
      have h := ht.1
      rw [min_eq_left (by norm_num : (0 : ℝ) ≤ 1)] at h
      exact h
    have htne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht0)
    have h1 : t ^ ((-1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
      rw [show (-1 : ℝ) / 2 = (1 / 2) * (-1) by norm_num,
        Real.rpow_mul (le_of_lt ht0), ← Real.sqrt_eq_rpow, Real.rpow_neg_one]
    rw [h1]
    field_simp
  have hWval : (∫ t in (0 : ℝ)..1, (2 * Real.sqrt t)⁻¹) = 1 := by
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => Real.sqrt t) ((2 * Real.sqrt x)⁻¹) x :=
      fun x hx => by simpa [one_div] using Real.hasDerivAt_sqrt (ne_of_gt hx.1)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => Real.sqrt t) (f' := fun t : ℝ => (2 * Real.sqrt t)⁻¹)
      (by norm_num) Real.continuous_sqrt.continuousOn hderiv hIntW1
    rw [h]
    simp
  have hWval2 : (∫ t in (0 : ℝ)..1, (2 * Real.sqrt (1 - t))⁻¹) = 1 := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := fun t : ℝ => (2 * Real.sqrt t)⁻¹) (a := (0 : ℝ)) (b := 1) (d := 1)
    rw [h]
    simp only [sub_self, sub_zero]
    exact hWval
  have hWinv : ∀ s : ℝ, (2 * s)⁻¹ * 2 = s⁻¹ := by
    intro s
    rcases eq_or_ne s 0 with h0 | hs
    · rw [h0]
      norm_num
    · have h2 : (2 : ℝ) ≠ 0 := by norm_num
      field_simp
  have hIntW1b : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt (1 - t))⁻¹) volume (0 : ℝ) 1 := by
    have h := hIntW1.comp_sub_left (c := 1)
    rw [show (1 : ℝ) - 0 = (1 : ℝ) from by norm_num,
      show (1 : ℝ) - 1 = (0 : ℝ) from by norm_num] at h
    exact h.symm
  have hWsum : (∫ t in (0 : ℝ)..1, ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)) = 4 := by
    have hcongr : (∫ t in (0 : ℝ)..1, ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹))
        = ∫ t in (0 : ℝ)..1,
            ((2 * Real.sqrt t)⁻¹ * 2 + (2 * Real.sqrt (1 - t))⁻¹ * 2) :=
      intervalIntegral.integral_congr (fun t _ => by
        rw [hWinv (Real.sqrt t), hWinv (Real.sqrt (1 - t))])
    rw [hcongr, intervalIntegral.integral_add (hIntW1.mul_const 2) (hIntW1b.mul_const 2),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, hWval, hWval2]
    norm_num




















































  have hRow : ∀ (t : ℝ), 0 < t → t < 1 →
      ‖∫ x : Ω × Ω, (∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ (fun w : Fin p → ℝ =>
          phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
            Real.log (∑ k : Fin p,
              Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w k - y k))))))
          (fun r : Fin p =>
            (∑ i2 : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
              (Real.sqrt t * (Real.sqrt v * (X i2 x.1 r - muX r) +
                  Real.sqrt (1 - v) * (F i2 x.1 r - muX r)) +
                Real.sqrt (1 - t) * (F i2 x.2 r - muX r))) +
            (∑ i2 : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
              (Real.sqrt t * (Real.sqrt v * (Y i2 x.1 r - muY r) +
                  Real.sqrt (1 - v) * (G i2 x.1 r - muY r)) +
                Real.sqrt (1 - t) * (G i2 x.2 r - muY r)))))
          (Pi.single j (1 : ℝ)) *
        ((Real.sqrt (m : ℝ))⁻¹ * delta n m *
          ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
              Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
            (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)))) ∂(P.prod P)‖
        ≤ 1000000 * ((C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4 * (Real.sqrt (m : ℝ))⁻¹ *
          |delta n m| ^ 3 * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
          ((min phi1 phi2) ^ 2 * (Real.log (p : ℝ)) ^ 2 *
            (phi2 * (LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G) +
              LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
              min phi1 phi2 * Mstar P m (delta n m) muY Y G phi2)) := by
    exact statopia_math_node_1559958170_cd7bf946 b hb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range Ck C1 C2 C3 Cb hCk hC1 hC3 hCb hG hQ hL Ω P n m p delta muX muY X Y F G phi1 phi2 y v hn hm hp hlogp hdelta hXm hYm hFm hGm hindep hXL2 hYL2 hX3 hY3 hF3 hG3 hXmean hYmean hFcov hGcov hcombint hcomb hphi1 hphi2 hv0 hv1 hp2

  set Ph : ℝ := phi2 * (LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G) +
      LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
      min phi1 phi2 * Mstar P m (delta n m) muY Y G phi2 with hPhdef
  set Kc : ℝ := 1000000 * ((C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4 * (Real.sqrt (m : ℝ))⁻¹ *
    |delta n m| ^ 3 with hKcdef
  set Mc : ℝ := (min phi1 phi2) ^ 2 * (Real.log (p : ℝ)) ^ 2 * Ph with hMcdef
  set Maj : ℝ → ℝ := fun t => Kc * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * Mc with hMajdef
  have hKcpos : (0 : ℝ) < Kc := by
    rw [hKcdef]
    have h1 : (0 : ℝ) < C1 + C3 + C2 + 1 := lt_of_lt_of_le zero_lt_one hCsum1
    have h2 : (0 : ℝ) < Cb + 1 := lt_of_lt_of_le zero_lt_one hB2
    have h3 : (0 : ℝ) < ((C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4 := pow_pos (mul_pos h1 h2) 4
    have h4 : (0 : ℝ) < (Real.sqrt (m : ℝ))⁻¹ := inv_pos.2 hsqrtm
    have h5 : (0 : ℝ) < |delta n m| ^ 3 := pow_pos habsdelta 3
    exact mul_pos (mul_pos (mul_pos (by norm_num) h3) h4) h5
  have hWp : (0 : ℝ) < (Real.sqrt (1 / 2 : ℝ))⁻¹ + (Real.sqrt (1 - 1 / 2 : ℝ))⁻¹ := by
    have ha : (0 : ℝ) < (Real.sqrt (1 / 2 : ℝ))⁻¹ :=
      inv_pos.2 (Real.sqrt_pos.2 (by norm_num))
    have hb : (0 : ℝ) < (Real.sqrt (1 - 1 / 2 : ℝ))⁻¹ :=
      inv_pos.2 (Real.sqrt_pos.2 (by norm_num))
    linarith
  have hMc_nonneg : (0 : ℝ) ≤ Mc := by
    by_contra hneg
    have hlt : Mc < 0 := not_le.mp hneg
    have hb1 := hRow (1 / 2 : ℝ) (by norm_num) (by norm_num)
    have hge : (0 : ℝ) ≤
        Kc * ((Real.sqrt (1 / 2 : ℝ))⁻¹ + (Real.sqrt (1 - 1 / 2 : ℝ))⁻¹) * Mc := by
      rw [hKcdef, hMcdef, hPhdef]
      exact le_trans (norm_nonneg _) hb1
    have hpos : (0 : ℝ) < Kc * ((Real.sqrt (1 / 2 : ℝ))⁻¹ + (Real.sqrt (1 - 1 / 2 : ℝ))⁻¹) :=
      mul_pos hKcpos hWp
    have hprod : Kc * ((Real.sqrt (1 / 2 : ℝ))⁻¹ + (Real.sqrt (1 - 1 / 2 : ℝ))⁻¹) * Mc < 0 :=
      mul_neg_of_pos_of_neg hpos hlt
    linarith only [hge, hprod]
  have hPhnn : (0 : ℝ) ≤ Ph := by
    have hpos2 : (0 : ℝ) < (min phi1 phi2) ^ 2 * (Real.log (p : ℝ)) ^ 2 :=
      mul_pos (pow_pos hphipos 2) (pow_pos hlogp 2)
    have h := hMc_nonneg
    rw [hMcdef] at h
    by_contra hc
    have hneg : Ph < 0 := not_le.mp hc
    have hlt : (min phi1 phi2) ^ 2 * (Real.log (p : ℝ)) ^ 2 * Ph < 0 :=
      mul_neg_of_pos_of_neg hpos2 hneg
    linarith only [h, hlt]
  have hne1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (1 : ℝ) := by
    have h : volume ({t : ℝ | ¬ t ≠ (1 : ℝ)}) = 0 := by
      simpa using measure_singleton (1 : ℝ)
    exact MeasureTheory.ae_iff.2 h
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖∫ x : Ω × Ω, (∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ (fun w : Fin p → ℝ =>
          phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
            Real.log (∑ k : Fin p,
              Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w k - y k))))))
          (fun r : Fin p =>
            (∑ i2 : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
              (Real.sqrt t * (Real.sqrt v * (X i2 x.1 r - muX r) +
                  Real.sqrt (1 - v) * (F i2 x.1 r - muX r)) +
                Real.sqrt (1 - t) * (F i2 x.2 r - muX r))) +
            (∑ i2 : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
              (Real.sqrt t * (Real.sqrt v * (Y i2 x.1 r - muY r) +
                  Real.sqrt (1 - v) * (G i2 x.1 r - muY r)) +
                Real.sqrt (1 - t) * (G i2 x.2 r - muY r)))))
          (Pi.single j (1 : ℝ)) *
        ((Real.sqrt (m : ℝ))⁻¹ * delta n m *
          ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
              Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
            (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)))) ∂(P.prod P)‖ ≤ Maj t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne1] with t htne ht
    have ht0 : (0 : ℝ) < t := ht.1
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne
    rw [hMajdef, hKcdef, hMcdef, hPhdef]
    exact hRow t ht0 ht1
  have hwt : IntervalIntegrable (fun t : ℝ => (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)
      volume (0 : ℝ) 1 := by
    have h1 : IntervalIntegrable (fun t : ℝ => (Real.sqrt t)⁻¹) volume (0 : ℝ) 1 := by
      have h := hIntW1.mul_const 2
      simpa only [hWinv] using h
    have h2 : IntervalIntegrable (fun t : ℝ => (Real.sqrt (1 - t))⁻¹) volume (0 : ℝ) 1 := by
      have h := hIntW1b.mul_const 2
      simpa only [hWinv] using h
    exact h1.add h2
  have hMajI : IntervalIntegrable Maj volume (0 : ℝ) 1 := by
    rw [hMajdef]
    exact (hwt.const_mul Kc).mul_const Mc
  have hIntM : Integrable Maj (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    first | exact hMajI.1 | exact hMajI.2



  have hlin1 : ∀ (f : Ω → ℝ), Measurable f → Integrable (fun ω => |f ω| ^ 3) P →
      Integrable f P := by
    intro f hfm hf
    have key : ∀ x : ℝ, |x| ≤ 1 + |x| ^ 3 := by
      intro x
      have h0 : (0 : ℝ) ≤ |x| := abs_nonneg x
      by_cases h1 : (|x|) ≤ 1
      · have h3 : (0 : ℝ) ≤ |x| ^ 3 := pow_nonneg h0 3
        linarith
      · push_neg at h1
        have h2 : (1 : ℝ) ≤ |x| ^ 2 := by
          have hm2 := mul_le_mul (le_of_lt h1) (le_of_lt h1) zero_le_one h0
          simpa [pow_two] using hm2
        calc |x| = |x| * 1 := (mul_one |x|).symm
          _ ≤ |x| * |x| ^ 2 := mul_le_mul_of_nonneg_left h2 h0
          _ = |x| ^ 3 := by ring
          _ ≤ 1 + |x| ^ 3 := by linarith
    have hg : Integrable (fun ω => 1 + |f ω| ^ 3) P := (integrable_const (1 : ℝ)).add hf
    refine hg.mono hfm.aestronglyMeasurable ?_
    filter_upwards with ω
    have h4 : (0 : ℝ) ≤ 1 + |f ω| ^ 3 := by positivity
    calc ‖f ω‖ = |f ω| := Real.norm_eq_abs _
      _ ≤ 1 + |f ω| ^ 3 := key (f ω)
      _ = ‖1 + |f ω| ^ 3‖ := by rw [Real.norm_eq_abs, abs_of_nonneg h4]
  have hX1 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => X i ω j - muX j) P := by
    intro i j
    exact hlin1 (fun ω => X i ω j - muX j)
      (((measurable_pi_apply j).comp (hXm i)).sub
        (measurable_const : Measurable (fun _ : Ω => muX j))) (hX3 i j)
  have hY1 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => Y i ω j - muY j) P := by
    intro i j
    exact hlin1 (fun ω => Y i ω j - muY j)
      (((measurable_pi_apply j).comp (hYm i)).sub
        (measurable_const : Measurable (fun _ : Ω => muY j))) (hY3 i j)
  have hF1 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => F i ω j - muX j) P := by
    intro i j
    exact hlin1 (fun ω => F i ω j - muX j)
      (((measurable_pi_apply j).comp (hFm i)).sub
        (measurable_const : Measurable (fun _ : Ω => muX j))) (hF3 i j)
  have hG1 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j - muY j) P := by
    intro i j
    exact hlin1 (fun ω => G i ω j - muY j)
      (((measurable_pi_apply j).comp (hGm i)).sub
        (measurable_const : Measurable (fun _ : Ω => muY j))) (hG3 i j)
  intro KAP ZST ZSS ZC ZD
  have hFub : (∫ x : Ω × Ω, (∫ t in (0 : ℝ)..1, ∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j) ∂(P.prod P))
      = ∫ t in (0 : ℝ)..1, ∫ x : Ω × Ω, (∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j) ∂(P.prod P) :=
    (statopia_math_node_3276301073_1a4e82d2 Ω P n m p hn hm hp hp2 delta muX muY X Y F G
      v hv0 hv1 phi1 phi2 hphi1 hphi2 y phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
      hXm hYm hFm hGm hX1 hY1 hF1 hG1).2
  rw [hFub]
  conv_lhs => rw [← Real.norm_eq_abs]
  refine le_trans
    (intervalIntegral.norm_integral_le_integral_norm (a := (0 : ℝ)) (b := 1) (by norm_num)) ?_
  have hMajEq : Maj = fun t : ℝ => ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * (Kc * Mc) := by
    rw [hMajdef]
    funext t
    ring
  have hMajInt : (∫ t in Set.Ioc (0 : ℝ) 1, Maj t) = Kc * Mc * 4 := by
    have h1 : (∫ t in Set.Ioc (0 : ℝ) 1, Maj t)
        = ∫ t in (0 : ℝ)..1, ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * (Kc * Mc) := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact intervalIntegral.integral_congr (fun t _ => by rw [hMajEq])
    rw [h1, intervalIntegral.integral_mul_const, hWsum]
    ring



  have hfinal : Kc * Mc * 4 ≤
      10000000 * (((Ck + 1) * (C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4 + 1) *
        (Real.sqrt (m : ℝ))⁻¹ * |delta n m| ^ 3 *
        ((Real.log (p : ℝ)) ^ 2 * (phi2 ^ 2 * Ph)) := by
    rw [hKcdef, hMcdef]
    set Xp : ℝ := (C1 + C3 + C2 + 1) * (Cb + 1) with hXdef
    set Yp : ℝ := (Ck + 1) * (C1 + C3 + C2 + 1) * (Cb + 1) with hYdef
    have hXnn : (0 : ℝ) ≤ Xp := by
      rw [hXdef]
      exact mul_nonneg (le_trans zero_le_one hCsum1) (le_trans zero_le_one hB2)
    have hXle : Xp ≤ Yp := by
      rw [hXdef, hYdef]
      have h1 : (C1 + C3 + C2 + 1) ≤ (Ck + 1) * (C1 + C3 + C2 + 1) := by
        have h := mul_le_mul_of_nonneg_right hB1 (le_trans zero_le_one hCsum1)
        linarith only [h]
      exact mul_le_mul_of_nonneg_right h1 (le_trans zero_le_one hB2)
    have hYnn : (0 : ℝ) ≤ Yp := le_trans hXnn hXle
    have hs2 : Xp ^ 2 ≤ Yp ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul hXle hXle hXnn hYnn
    have hs4 : Xp ^ 4 ≤ Yp ^ 4 := by
      have h := mul_le_mul hs2 hs2 (pow_nonneg hXnn 2) (pow_nonneg hYnn 2)
      have e4 : Xp ^ 4 = Xp ^ 2 * Xp ^ 2 := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
      have f4 : Yp ^ 2 * Yp ^ 2 = Yp ^ 4 := by
        rw [← pow_add, show (2 + 2 : ℕ) = 4 from rfl]
      calc Xp ^ 4 = Xp ^ 2 * Xp ^ 2 := e4
        _ ≤ Yp ^ 2 * Yp ^ 2 := h
        _ = Yp ^ 4 := f4
    have hQ2nn : (0 : ℝ) ≤ (min phi1 phi2) ^ 2 := pow_nonneg (le_trans zero_le_one hphimin) 2
    have hY4nn : (0 : ℝ) ≤ Yp ^ 4 := pow_nonneg hYnn 4
    have hXu : Xp ^ 4 ≤ Yp ^ 4 + 1 := le_trans hs4 (le_add_of_nonneg_right zero_le_one)
    have hYu : (0 : ℝ) ≤ Yp ^ 4 + 1 := le_trans hY4nn (le_add_of_nonneg_right zero_le_one)
    have hcoef : (1000000 * 4) * (Xp ^ 4 * (min phi1 phi2) ^ 2) ≤
        10000000 * ((Yp ^ 4 + 1) * phi2 ^ 2) :=
      mul_le_mul (by norm_num : (1000000 * 4 : ℝ) ≤ 10000000)
        (mul_le_mul hXu hphi1sq_mono hQ2nn hYu)
        (mul_nonneg (pow_nonneg hXnn 4) hQ2nn) (by norm_num)
    have hYn : (0 : ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ * |delta n m| ^ 3 *
        ((Real.log (p : ℝ)) ^ 2 * Ph) :=
      mul_nonneg (mul_nonneg (le_of_lt (inv_pos.2 hsqrtm)) (pow_nonneg (abs_nonneg _) 3))
        (mul_nonneg (sq_nonneg _) hPhnn)
    have hgen : ∀ (x4 yb m2 θ s dd T P : ℝ),
        (1000000 * 4) * (x4 * m2) ≤ 10000000 * (yb * θ) →
        0 ≤ s → 0 ≤ dd → 0 ≤ T → 0 ≤ P →
        1000000 * x4 * s * dd * (m2 * T * P) * 4
          ≤ 10000000 * yb * s * dd * (T * (θ * P)) := by
      intro x4 yb m2 θ s dd T P hcore hs hd hT hP
      have h1 : 1000000 * x4 * s * dd * (m2 * T * P) * 4
          = ((1000000 * 4) * (x4 * m2)) * (s * dd * (T * P)) := by ring
      have h2 : 10000000 * yb * s * dd * (T * (θ * P))
          = (10000000 * (yb * θ)) * (s * dd * (T * P)) := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hcore
        (mul_nonneg (mul_nonneg hs hd) (mul_nonneg hT hP))
    exact hgen (Xp ^ 4) (Yp ^ 4 + 1) ((min phi1 phi2) ^ 2) (phi2 ^ 2) (Real.sqrt (m : ℝ))⁻¹
      (|delta n m| ^ 3) ((Real.log (p : ℝ)) ^ 2) Ph hcoef
      (le_of_lt (inv_pos.2 hsqrtm)) (pow_nonneg (abs_nonneg _) 3) (sq_nonneg _) hPhnn
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hIntM hae) ?_
  · filter_upwards with t
    exact norm_nonneg _
  · rw [hMajInt]
    exact hfinal


























































































  /- @proof-region region.target-node.session.fc07ea337b28e7e0 end -/

end

end Statlib.Imported

