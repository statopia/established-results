import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.YExpectationRemainder
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

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option autoImplicit false in
theorem statopia_math_node_3553547395_a350ae57 : ∀ (b : ℝ) (hb : 0 < b)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1),
    ∃ K : ℝ, 0 < K ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
        (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
        (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
        (phi1 phi2 : ℝ) (v : ℝ) (y : Fin p → ℝ),
        0 < n → 0 < m → 0 < p → 0 < Real.log (p : ℝ) → delta n m ≠ 0 →
        (∀ i : Fin n, Measurable (X i)) →
        (∀ i : Fin m, Measurable (Y i)) →
        (∀ i : Fin n, Measurable (F i)) →
        (∀ i : Fin m, Measurable (G i)) →
        iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P →
        (∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j) →
        (∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j) →
        (∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P) →
        (∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P) →
        (∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P) →
        (∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P) →
        (∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P) →
        (∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P) →
        (∀ i : Fin n,
          IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i)) →
        (∀ i : Fin m,
          IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i)) →
        (∀ j : Fin p, b ≤ ∫ ω,
          (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P) →
        1 ≤ phi1 → 1 ≤ phi2 → 0 ≤ v → v ≤ 1 →
        (let kappa : (Fin p → ℝ) → ℝ := fun w =>
           phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
             Real.log (∑ j : Fin p, Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w j - y j)))))
         let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
           (Real.sqrt (n : ℝ))⁻¹ *
             (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
                 Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
               Real.sqrt (1 - t) * (F i x.2 j - muX j))
         let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
           (Real.sqrt (m : ℝ))⁻¹ * delta n m *
             (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
                 Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
               Real.sqrt (1 - t) * (G i x.2 j - muY j))
         let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
           (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
         let Zdot : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
           (Real.sqrt (m : ℝ))⁻¹ * delta n m *
             ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
                 Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
               (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
         Integrable (fun x : Ω × Ω =>
             ∫ t in (0 : ℝ)..1,
               ∑ j : Fin p, ∑ i : Fin m,
                 (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j)
             (P.prod P) ∧
           |∫ x : Ω × Ω,
               (∫ t in (0 : ℝ)..1,
                 ∑ j : Fin p, ∑ i : Fin m,
                   (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j)
               ∂(P.prod P)|
             ≤ K * (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
                 |delta n m| ^ 3 *
               (phi2 * (LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G) +
                 LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
                 phi2 * Mstar P m (delta n m) muY Y G phi2)) := by
  /- @proof-region region.target-node.session.74f35352d0951d5b begin -/
  intro b hb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  obtain ⟨Cκ, hCκnn, hCκ⟩ :=
    statopia_math_node_1967109576_c7239acb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  obtain ⟨C2, -, -, hC1C3⟩ :=
    PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported.paper_370f7a68a9a1447a9d903f9a55f08bd5
  obtain ⟨C1, C3, hC1le, hC3le, hC13⟩ :=
    hC1C3 phi0 hphi0_range hphi0_cont hphi0_left hphi0_right

  obtain ⟨Cb, hCbpos, hCb⟩ := statopia_math_node_2844047726_eb462809 b hb
  refine ⟨10000000 * (((Cκ + 1) * (C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4 + 1), by
    have h := sq_nonneg (((Cκ + 1) * (C1 + C3 + C2 + 1) * (Cb + 1)) ^ 2)
    linarith only [h], ?_⟩

  intro Ω _ P _ n m p delta muX muY X Y F G phi1 phi2 v y
  intro hn hm hp hlogp hdelta hXm hYm hFm hGm hindep hXmean hYmean hXL2 hYL2
    hX3 hY3 hF3 hG3 hFcov hGcov hcond hphi1 hphi2 hv0 hv1
  intro kap Zst Zsst Zv Zdt
  constructor
  · exact statopia_math_node_1910587795_b1904894 Ω P n m p hn hm hp hlogp delta muX muY
      X Y F G hXm hYm hFm hGm phi1 phi2 hphi1 hphi2 v hv0 hv1 y phi0 hphi0_cont
      hphi0_left hphi0_right hphi0_range hY3 hG3

  · have hp2 : 2 ≤ p := by
      have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
      have hlt : (1 : ℝ) < (p : ℝ) := by
        by_contra hcon
        have hle : (p : ℝ) ≤ 1 := le_of_not_gt hcon
        have hlog : Real.log (p : ℝ) ≤ Real.log 1 := Real.log_le_log hpos hle
        rw [Real.log_one] at hlog
        exact absurd hlog (not_le.mpr hlogp)
      have h1 : 1 < p := by exact_mod_cast hlt
      omega
    have hmin2 : min phi1 phi2 ≤ phi2 := min_le_right phi1 phi2
    have hmaxnn : ∀ (z : Fin p → ℝ), 0 ≤ maxAbs z :=
      fun z => Real.iSup_nonneg (fun j => abs_nonneg (z j))





    have hMstarnn : ∀ phi : ℝ, 0 ≤ Mstar P m (delta n m) muY Y G phi := by
      intro phi
      unfold Mstar
      refine add_nonneg ?_ ?_
      · unfold MY
        split_ifs with hd
        · exact le_refl 0
        · refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) (Finset.sum_nonneg ?_)
          intro i _
          refine MeasureTheory.integral_nonneg (fun ω => ?_)
          simp only [Set.indicator_apply]
          split_ifs with h
          · exact pow_nonneg (hmaxnn (fun j => Y i ω j - muY j)) 3
          · exact le_refl 0
      · unfold MG
        split_ifs with hd
        · exact le_refl 0
        · refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) (Finset.sum_nonneg ?_)
          intro i _
          refine MeasureTheory.integral_nonneg (fun ω => ?_)
          simp only [Set.indicator_apply]
          split_ifs with h
          · exact pow_nonneg (hmaxnn (fun j => G i ω j - muY j)) 3
          · exact le_refl 0
    have hphi2nn : (0 : ℝ) ≤ phi2 := le_trans zero_le_one hphi2


    have hA :
        0 ≤ (10000000 * (((Cκ + 1) * (C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4 + 1)) *
          (Real.sqrt (m : ℝ))⁻¹ * |delta n m| ^ 3 :=
      mul_nonneg
        (mul_nonneg
          (mul_pos (by norm_num) (by
            have h4 : (0 : ℝ) ≤
                (((Cκ + 1) * (C1 + C3 + C2 + 1) * (Cb + 1)) ^ 2) ^ 2 := sq_nonneg _
            have hpow : ((Cκ + 1) * (C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4
                = (((Cκ + 1) * (C1 + C3 + C2 + 1) * (Cb + 1)) ^ 2) ^ 2 := by
              rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
            rw [hpow]
            linarith only [h4])).le
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        (pow_nonneg (abs_nonneg _) 3)



    have hcombInt : ∀ j : Fin p, Integrable (fun ω =>
        (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2) P := by
      intro j
      by_contra hni
      have hzero : (∫ ω, (combVec n m (delta n m) muX muY
          (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P) = 0 :=
        MeasureTheory.integral_undef hni
      have hj := hcond j
      rw [hzero] at hj
      exact absurd hj (not_le.mpr hb)
    have hMainBd :
        |∫ x : Ω × Ω, (∫ t in (0 : ℝ)..1, ∑ j : Fin p, ∑ i : Fin m,
            (fderiv ℝ kap (Zv t x)) (Pi.single j (1 : ℝ)) * Zdt t x i j) ∂(P.prod P)|
          ≤ (10000000 * (((Cκ + 1) * (C1 + C3 + C2 + 1) * (Cb + 1)) ^ 4 + 1)) *
              (Real.sqrt (m : ℝ))⁻¹ * |delta n m| ^ 3 *
            ((Real.log (p : ℝ)) ^ 2 *
              (phi2 ^ 2 * (phi2 * (LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G) +
                LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
                min phi1 phi2 * Mstar P m (delta n m) muY Y G phi2))) := by
      refine statopia_math_node_3680776236_d8bd4c8f b hb phi0 hphi0_cont hphi0_left
        hphi0_right hphi0_range Cκ C1 C2 C3 Cb hCκnn hC1le hC3le hCbpos hCκ
        (fun p' hp' hlogp' phi' hphi' y' => by
          obtain ⟨Qm, hQmnn, hQmmaj, -, hQmsum, hQmstab⟩ := hC13 p' hp' hlogp' phi' hphi' y'
          refine ⟨Qm, ?_, ?_, ?_, ?_⟩
          · intro j k l w
            exact hQmnn j k l w
          · intro j k l w
            exact hQmmaj j k l w
          · intro w
            have h4 : C1 * C2 * (phi' * (phi' * Real.log (p' : ℝ)) ^ 2)
                = C1 * C2 * phi' * (phi' * Real.log (p' : ℝ)) ^ 2 := by ring
            rw [← h4]
            exact hQmsum w
          · intro j k l w w' hw
            exact (hQmstab j k l w w' hw).2)
        ?_ Ω P n m p delta muX muY X Y F G phi1 phi2 y v
        hn hm hp hlogp hdelta hXm hYm hFm hGm hindep hXL2 hYL2 hX3 hY3 hF3 hG3
        hXmean hYmean hFcov hGcov hcombInt hcond hphi1 hphi2 hv0 hv1 hp2
      intro ΩL _ PL _ nL mL pL deltaL muXL muYL XL YL FL GG phi1L phi2L yL vL
        hnL hmL hpL hlogpL hdeltaL hXLm hYLm hFLm hGGm hindepL hXLL2 hYLL2
        hXL3 hYL3 hFL3 hGG3 hXLmean hYLmean hXLcov hGGcov hcombL hcondL
        hphi1L hphi2L hv0L hv1L ZSTL ZSSL ZL rhoL hlocL t ht
      have hres := (hCb ΩL PL nL mL pL deltaL muXL muYL XL YL FL GG phi1L phi2L yL vL
        hnL hmL hpL hlogpL hdeltaL hXLm hYLm hFLm hGGm hindepL hXLL2 hYLL2
        hXLmean hYLmean hXLcov hGGcov hcombL hcondL hphi1L hphi2L hv0L hv1L).2 t ht
      exact le_trans hres.1 hres.2
    refine le_trans hMainBd ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hmin2 (hMstarnn phi2)))
          (pow_nonneg hphi2nn 2))
        (sq_nonneg (Real.log (p : ℝ)))) hA) ?_
    exact le_of_eq (by ac_rfl)
  /- @proof-region region.target-node.session.74f35352d0951d5b end -/

end

end Statlib.Imported

