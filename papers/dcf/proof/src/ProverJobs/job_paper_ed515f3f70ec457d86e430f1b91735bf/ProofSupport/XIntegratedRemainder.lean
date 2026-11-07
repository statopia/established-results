import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.YIntegratedRemainder
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.BlockSwap

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

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option autoImplicit false in
theorem statopia_math_node_2043147911_3b633e1b : ∀ (b : ℝ) (hb : 0 < b)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1),
    ∃ KX : ℝ, 0 < KX ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
        (hlogp : 0 < Real.log (p : ℝ))
        (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
        (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
        (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
        (hX : ∀ i : Fin n, Measurable (X i))
        (hY : ∀ i : Fin m, Measurable (Y i))
        (hF : ∀ i : Fin n, Measurable (F i))
        (hG : ∀ i : Fin m, Measurable (G i))
        (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
        (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
        (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
        (hX3 : ∀ (i : Fin n) (j : Fin p),
          Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
        (hY3 : ∀ (i : Fin m) (j : Fin p),
          Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
        (hF3 : ∀ (i : Fin n) (j : Fin p),
          Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
        (hG3 : ∀ (i : Fin m) (j : Fin p),
          Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
        (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
        (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
        (hFcov : ∀ i : Fin n,
          IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
        (hGcov : ∀ i : Fin m,
          IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
        (hcomb2 : ∀ j : Fin p, Integrable (fun ω =>
          (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2) P)
        (hbvar : ∀ j : Fin p, b ≤ ∫ ω,
          (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P)
        (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
        (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (y : Fin p → ℝ),
        let phi : ℝ := min phi1 phi2
        let beta : ℝ := phi * Real.log (p : ℝ)
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
        let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
          (Real.sqrt (n : ℝ))⁻¹ *
            ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
                Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
              (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
        let kappa : (Fin p → ℝ) → ℝ := fun w =>
          phi0 (phi * (beta⁻¹ * Real.log (∑ k : Fin p, Real.exp (beta * (w k - y k)))))
        let Istar : Ω × Ω → ℝ := fun x =>
          ∫ t in (0 : ℝ)..1,
            ∑ j : Fin p, ∑ i : Fin n,
              (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j
        Integrable Istar (P.prod P) ∧
          |∫ x, Istar x ∂(P.prod P)| ≤
            KX * (Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
              (phi1 * LX P n muX X * rho P n m p (delta n m) muX muY X Y F G +
                LX P n muX X * Real.sqrt (Real.log (p : ℝ)) +
                phi1 * Mn P n muX X F phi1) := by
  intro b hb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  obtain ⟨K, hK, hKY⟩ := statopia_math_node_3553547395_a350ae57 b hb phi0
    hphi0_cont hphi0_left hphi0_right hphi0_range
  refine ⟨K, hK, ?_⟩
  intro Ω _ P _ n m p hn hm hp hlogp delta muX muY X Y F G hX hY hF hG hindep
    hXL2 hYL2 hX3 hY3 hF3 hG3 hXmean hYmean hFcov hGcov hcomb2 hbvar
    phi1 phi2 hphi1 hphi2 v hv0 hv1 y
  intro phi beta Zstar Zstarstar Z Zdotstar kappa Istar
  let d : ℝ := delta n m
  let mus : Fin p → ℝ := fun j => d * muY j
  let Ys : Fin m → Ω → Fin p → ℝ := fun i w j => d * Y i w j
  let Gs : Fin m → Ω → Fin p → ℝ := fun i w j => d * G i w j
  have hYs : ∀ i : Fin m, Measurable (Ys i) := by
    intro i
    exact measurable_pi_lambda _ (fun j => measurable_const.mul
      ((measurable_pi_apply j).comp (hY i)))
  have hGs : ∀ i : Fin m, Measurable (Gs i) := by
    intro i
    exact measurable_pi_lambda _ (fun j => measurable_const.mul
      ((measurable_pi_apply j).comp (hG i)))
  have hYsL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun w => Ys i w j) 2 P :=
    fun i j => (hYL2 i j).const_mul d
  have hYs3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun w => |Ys i w j - mus j| ^ 3) P := by
    intro i j
    convert (hY3 i j).const_mul (|d| ^ 3) using 1
    funext w
    dsimp [Ys, mus]
    rw [← mul_sub, abs_mul, mul_pow]
  have hGs3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun w => |Gs i w j - mus j| ^ 3) P := by
    intro i j
    convert (hG3 i j).const_mul (|d| ^ 3) using 1
    funext w
    dsimp [Gs, mus]
    rw [← mul_sub, abs_mul, mul_pow]
  have hYsMean : ∀ (i : Fin m) (j : Fin p), ∫ w, Ys i w j ∂P = mus j := by
    intro i j
    dsimp [Ys, mus]
    rw [integral_const_mul, hYmean i j]
  have hGsCov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun w j => Gs i w j - mus j) (covX P mus Ys i) := by
    intro i
    dsimp [mus, Ys]
    rw [DCFBlockSwap.covariance_scale]
    convert DCFBlockSwap.gaussian_scale P (fun w j => G i w j - muY j)
      (covY P muY Y i) (hGcov i) d using 1
    funext w j
    dsimp [Gs, mus]
    ring
  have hFsCov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun w j => F i w j - muX j) (covY P muX X i) := by
    intro i
    exact hFcov i
  have hdep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam Ys X Gs F) P :=
    DCFBlockSwap.independent_swap P X F Y G hindep d
  have hbvarS : ∀ j : Fin p, b ≤ ∫ w,
      (combVec m n 1 mus muX (fun i => Ys i w) (fun i => X i w) j) ^ 2 ∂P := by
    intro j
    simpa only [mus, Ys, DCFBlockSwap.combVec_swap] using hbvar j
  have h := hKY Ω P m n p (fun _ _ => 1) mus muX Ys X Gs F
    phi2 phi1 v y hm hn hp hlogp one_ne_zero hYs hX hGs hF hdep hYsMean hXmean
    hYsL2 hXL2 hYs3 hX3 hGs3 hF3 hGsCov hFsCov hbvarS hphi2 hphi1 hv0 hv1
  dsimp only [] at h
  have hrow (t : ℝ) (x : Ω × Ω) (i : Fin m) (j : Fin p) :
      (Real.sqrt (m : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (Ys i x.1 j - mus j) +
          Real.sqrt (1 - v) * (Gs i x.1 j - mus j)) +
          Real.sqrt (1 - t) * (Gs i x.2 j - mus j)) = Zstarstar t x i j := by
    dsimp [Ys, mus, Gs, Zstarstar, d]
    ring
  have hZswap (t : ℝ) (x : Ω × Ω) :
      (fun j =>
        (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (Ys i x.1 j - mus j) +
            Real.sqrt (1 - v) * (Gs i x.1 j - mus j)) +
            Real.sqrt (1 - t) * (Gs i x.2 j - mus j))) +
        (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
            Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
            Real.sqrt (1 - t) * (F i x.2 j - muX j)))) = Z t x := by
    funext j
    simp_rw [hrow]
    exact add_comm _ _
  simpa only [one_mul, mul_one, abs_one, one_pow, min_comm phi2 phi1, hZswap,
    DCFBlockSwap.Mstar_one, DCFBlockSwap.LY_swap, mus, Ys, Gs, DCFBlockSwap.rho_swap,
    phi, beta, kappa, Zstar, Zstarstar, Z, Zdotstar, Istar, d, mul_assoc] using h

end

end Statlib.Imported


