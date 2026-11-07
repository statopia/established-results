import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.YIntegratedRemainder
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProofSupport.XIntegratedRemainder
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

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

theorem paper_ed515f3f70ec457d86e430f1b91735bf :
    ∀ (b : ℝ), 0 < b →
      ∃ Cb : ℝ, 0 < Cb ∧
        ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
          (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
          (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
          (phi1 phi2 : ℝ),
          0 < n → 0 < m → 0 < p → 0 < Real.log (p : ℝ) →
          (∀ i : Fin n, Measurable (X i)) → (∀ i : Fin m, Measurable (Y i)) →
          (∀ i : Fin n, Measurable (F i)) → (∀ i : Fin m, Measurable (G i)) →
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
          1 ≤ phi1 → 1 ≤ phi2 →
          rho P n m p (delta n m) muX muY X Y F G ≤
            Cb * ((Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
                (phi1 * LX P n muX X * rho P n m p (delta n m) muX muY X Y F G +
                  LX P n muX X * Real.sqrt (Real.log (p : ℝ)) +
                  phi1 * Mn P n muX X F phi1) +
              (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
                  |delta n m| ^ 3 *
                (phi2 * LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G +
                  LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
                  phi2 * Mstar P m (delta n m) muY Y G phi2) +
              (min phi1 phi2)⁻¹ * Real.sqrt (Real.log (p : ℝ)))
:= by
  /- @proof-region region.root.6bffa6e14453 begin -/
  intro b hb
  have hφc : ContDiff ℝ 3 (fun z : ℝ => Real.smoothTransition (1 - z)) :=
    (Real.smoothTransition.contDiff (n := 3)).comp (contDiff_const.sub contDiff_id)
  have hφl : ∀ z : ℝ, z ≤ 0 → Real.smoothTransition (1 - z) = 1 := by
    intro z hz
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hφr : ∀ z : ℝ, 1 ≤ z → Real.smoothTransition (1 - z) = 0 := by
    intro z hz
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  have hφrange : ∀ z : ℝ, Real.smoothTransition (1 - z) ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    exact ⟨Real.smoothTransition.nonneg (1 - z), Real.smoothTransition.le_one (1 - z)⟩
  obtain ⟨KX, hKXpos, hKX⟩ :=
    statopia_math_node_2043147911_3b633e1b.{u_1} b hb _ hφc hφl hφr hφrange
  obtain ⟨KY, hKYpos, hKY⟩ :=
    statopia_math_node_3553547395_a350ae57.{u_1} b hb _ hφc hφl hφr hφrange
  obtain ⟨CA, hCApos, hAC⟩ := statopia_math_node_3412747228_aa4ab764.{u_1} b hb
  refine ⟨16 * (KX + KY + CA + 1), by linarith, ?_⟩
  suffices hmain : ∀ (Ω : Type u_1) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
      (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
      (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ) (phi1 phi2 : ℝ),
      0 < n → 0 < m → 0 < p → 0 < Real.log (p : ℝ) →
      (∀ i : Fin n, Measurable (X i)) → (∀ i : Fin m, Measurable (Y i)) →
      (∀ i : Fin n, Measurable (F i)) → (∀ i : Fin m, Measurable (G i)) →
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
      1 ≤ phi1 → 1 ≤ phi2 → delta n m ≠ 0 →
      rho P n m p (delta n m) muX muY X Y F G ≤
        16 * (KX + KY + CA + 1) *
          ((Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
              (phi1 * LX P n muX X * rho P n m p (delta n m) muX muY X Y F G +
                LX P n muX X * Real.sqrt (Real.log (p : ℝ)) +
                phi1 * Mn P n muX X F phi1) +
            (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
                |delta n m| ^ 3 *
              (phi2 * LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G +
                LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
                phi2 * Mstar P m (delta n m) muY Y G phi2) +
            (min phi1 phi2)⁻¹ * Real.sqrt (Real.log (p : ℝ))) from by
    intro Ω instΩ P instP n m p delta muX muY X Y F G phi1 phi2
    intro hn hm hp hlogp hXm hYm hFm hGm hindep hMemX hMemY hIntX hIntY hIntF hIntG
      hmeanX hmeanY hGaussX hGaussY hSq hlow hphi1 hphi2
    by_cases hδz : delta n m = 0
    · haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
      have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hnormYc : ∀ j : Fin p, normSum m (fun _ : Fin m => muY) j = Real.sqrt (m : ℝ) * muY j := by
        intro j
        have hsum : (∑ i : Fin m, muY j) = (m : ℝ) * muY j := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
          Real.mul_self_sqrt hmreal.le
        have hn0 : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hmreal).ne'
        calc normSum m (fun _ : Fin m => muY) j
            = (Real.sqrt (m : ℝ))⁻¹ * ((m : ℝ) * muY j) := by
              simp only [normSum, hsum]
          _ = Real.sqrt (m : ℝ) * muY j := by
              have hexp : (m : ℝ) * muY j = Real.sqrt (m : ℝ) * (Real.sqrt (m : ℝ) * muY j) := by
                rw [← mul_assoc, hsq]
              rw [hexp, ← mul_assoc ((Real.sqrt (m : ℝ))⁻¹) (Real.sqrt (m : ℝ))
                (Real.sqrt (m : ℝ) * muY j), inv_mul_cancel₀ hn0, one_mul]
      have hconstYc : ∀ (d : ℝ) (Z : Fin n → Fin p → ℝ) (j : Fin p),
          combVec n m d muX muY Z (fun _ : Fin m => muY) j
            = normSum n Z j - Real.sqrt (n : ℝ) * muX j := by
        intro d Z j
        simp only [combVec, hnormYc j]
        ring
      have hYcm : ∀ i : Fin m, Measurable ((fun (_ : Fin m) (_ : Ω) => muY) i) :=
        fun i => measurable_const
      have hGcm : ∀ i : Fin m, Measurable ((fun (_ : Fin m) (_ : Ω) => muY) i) :=
        fun i => measurable_const
      have hMemY' : ∀ (i : Fin m) (j : Fin p),
          MemLp (fun ω => (fun (_ : Fin m) (_ : Ω) => muY) i ω j) 2 P :=
        fun i j => memLp_const (muY j)
      have hIntY' : ∀ (i : Fin m) (j : Fin p),
          Integrable (fun ω => |(fun (_ : Fin m) (_ : Ω) => muY) i ω j - muY j| ^ 3) P := by
        intro i j
        simp
      have hmeanY' : ∀ (i : Fin m) (j : Fin p),
          ∫ ω, (fun (_ : Fin m) (_ : Ω) => muY) i ω j ∂P = muY j := by
        intro i j
        simp
      have hXY0 : ∀ (ω : Ω) (j : Fin p),
          combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
            = combVec n m (1 : ℝ) muX muY (fun i => X i ω) (fun i => muY) j := by
        intro ω j
        rw [hconstYc (1 : ℝ) (fun i => X i ω) j, hδz]
        simp only [combVec, zero_mul, sub_zero, add_zero]
      have hFG0 : ∀ (ω : Ω) (j : Fin p),
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
            = combVec n m (1 : ℝ) muX muY (fun i => F i ω) (fun i => muY) j := by
        intro ω j
        rw [hconstYc (1 : ℝ) (fun i => F i ω) j, hδz]
        simp only [combVec, zero_mul, sub_zero, add_zero]
      have hSq' : ∀ j : Fin p, Integrable (fun ω =>
          (combVec n m (1 : ℝ) muX muY (fun i => X i ω) (fun _ : Fin m => muY) j) ^ 2) P := by
        intro j
        have h1 : (fun ω => (combVec n m (1 : ℝ) muX muY (fun i => X i ω)
              (fun _ : Fin m => muY) j) ^ 2)
            = fun ω => (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 := by
          funext ω
          rw [hconstYc (1 : ℝ) (fun i => X i ω) j, hδz]
          simp only [combVec, zero_mul, sub_zero, add_zero]
        rw [h1]
        exact hSq j
      have hlow' : ∀ j : Fin p, b ≤ ∫ ω,
          (combVec n m (1 : ℝ) muX muY (fun i => X i ω) (fun _ : Fin m => muY) j) ^ 2 ∂P := by
        intro j
        have h1 : (fun ω => (combVec n m (1 : ℝ) muX muY (fun i => X i ω)
              (fun _ : Fin m => muY) j) ^ 2)
            = fun ω => (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 := by
          funext ω
          rw [hconstYc (1 : ℝ) (fun i => X i ω) j, hδz]
          simp only [combVec, zero_mul, sub_zero, add_zero]
        rw [h1]
        exact hlow j
      have hly0 : LY P m muY (fun (_ : Fin m) (_ : Ω) => muY) = 0 := by
        simp [LY]
      have hrho : rho P n m p (delta n m) muX muY X Y F G
          = rho P n m p (1 : ℝ) muX muY X (fun (_ : Fin m) (_ : Ω) => muY) F
              (fun (_ : Fin m) (_ : Ω) => muY) := by
        simp only [rho, hXY0, hFG0]
      have hGaussY' : ∀ i : Fin m,
          IsCenteredGaussianVector P
            (fun ω j => (fun (_ : Fin m) (_ : Ω) => muY) i ω j - muY j)
            (covY P muY (fun (_ : Fin m) (_ : Ω) => muY) i) := by
        intro i
        have hzero : covY P muY (fun (_ : Fin m) (_ : Ω) => muY) i = 0 := by
          ext j k
          simp [covY]
        have hfun : (fun ω j => (fun (_ : Fin m) (_ : Ω) => muY) i ω j - muY j)
            = fun ω => (0 : Matrix (Fin p) (Fin p) ℝ).mulVec
                ((fun ω j => G i ω j - muY j) ω) := by
          funext ω j
          simp [Matrix.zero_mulVec]
        have hmat : covY P muY (fun (_ : Fin m) (_ : Ω) => muY) i
            = (0 : Matrix (Fin p) (Fin p) ℝ) * covY P muY Y i *
                (0 : Matrix (Fin p) (Fin p) ℝ).transpose := by
          rw [hzero]
          simp
        rw [hfun, hmat]
        exact IsCenteredGaussianVector.linearImage P (fun ω j => G i ω j - muY j)
          (covY P muY Y i) (hGaussY i) (0 : Matrix (Fin p) (Fin p) ℝ)
      have hind : iIndepFun (β := fun _ => Fin p → ℝ)
          (jointFam X (fun (_ : Fin m) (_ : Ω) => muY) F (fun (_ : Fin m) (_ : Ω) => muY)) P := by
        have hcomp := hindep.comp (β := fun _ => (Fin p → ℝ)) (γ := fun _ => (Fin p → ℝ))
          (fun i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)) =>
            match i with
            | Sum.inl _ => id
            | Sum.inr (Sum.inl _) => Function.const (Fin p → ℝ) muY
            | Sum.inr (Sum.inr (Sum.inl _)) => id
            | Sum.inr (Sum.inr (Sum.inr _)) => Function.const (Fin p → ℝ) muY)
          (fun i => by
            rcases i with i | (i | (i | i))
            · exact measurable_id
            · exact measurable_const
            · exact measurable_id
            · exact measurable_const)
        have hfam : (fun i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)) =>
            (fun i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)) =>
              match i with
              | Sum.inl _ => id
              | Sum.inr (Sum.inl _) => Function.const (Fin p → ℝ) muY
              | Sum.inr (Sum.inr (Sum.inl _)) => id
              | Sum.inr (Sum.inr (Sum.inr _)) => Function.const (Fin p → ℝ) muY) i ∘
              jointFam X Y F G i)
            = jointFam X (fun (_ : Fin m) (_ : Ω) => muY) F
                (fun (_ : Fin m) (_ : Ω) => muY) := by
          funext i
          rcases i with i | (i | (i | i)) <;> rfl
        rw [hfam] at hcomp
        exact hcomp
      have hmax0 : maxAbs (fun j : Fin p => muY j - muY j) = 0 := by
        simp [maxAbs]
      have hMY0 : ∀ phi : ℝ,
          MY P m (1 : ℝ) muY (fun (_ : Fin m) (_ : Ω) => muY) phi = 0 := by
        intro phi
        have hz : ∀ i : Fin m, ∫ ω, Set.indicator
            {ω' : Ω | maxAbs (fun j : Fin p => muY j - muY j) >
              Real.sqrt (m : ℝ) / (4 * |(1 : ℝ)| * phi * Real.log (p : ℝ))}
            (fun ω' => (maxAbs (fun j : Fin p => muY j - muY j)) ^ 3) ω ∂P = 0 := by
          intro _
          have hfun : (fun ω : Ω => Set.indicator
              {ω' : Ω | maxAbs (fun j : Fin p => muY j - muY j) >
                Real.sqrt (m : ℝ) / (4 * |(1 : ℝ)| * phi * Real.log (p : ℝ))}
              (fun ω' => (maxAbs (fun j : Fin p => muY j - muY j)) ^ 3) ω)
              = fun _ : Ω => (0 : ℝ) := by
            funext ω
            simp only [hmax0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
            by_cases hmem : ω ∈ {ω' : Ω |
                (0 : ℝ) > Real.sqrt (m : ℝ) / (4 * |(1 : ℝ)| * phi * Real.log (p : ℝ))}
            · rw [Set.indicator_of_mem hmem]
            · rw [Set.indicator_of_notMem hmem]
          rw [hfun]
          simp
        rw [MY, if_neg one_ne_zero]
        have hsum : (∑ i : Fin m, ∫ ω, Set.indicator
            {ω' : Ω | maxAbs (fun j : Fin p => muY j - muY j) >
              Real.sqrt (m : ℝ) / (4 * |(1 : ℝ)| * phi * Real.log (p : ℝ))}
            (fun ω' => (maxAbs (fun j : Fin p => muY j - muY j)) ^ 3) ω ∂P) = 0 := by
          exact Finset.sum_eq_zero (fun i _ => hz i)
        rw [hsum, mul_zero]
      have hMG0 : ∀ phi : ℝ,
          MG P m (1 : ℝ) muY (fun (_ : Fin m) (_ : Ω) => muY) phi = 0 :=
        fun phi => hMY0 phi
      have hms0 : ∀ phi : ℝ,
          Mstar P m (1 : ℝ) muY (fun (_ : Fin m) (_ : Ω) => muY)
            (fun (_ : Fin m) (_ : Ω) => muY) phi = 0 := by
        intro phi
        rw [Mstar, hMY0 phi, hMG0 phi, add_zero]
      have key := hmain Ω P n m p (fun _ _ => (1 : ℝ)) muX muY X
        (fun (_ : Fin m) (_ : Ω) => muY) F (fun (_ : Fin m) (_ : Ω) => muY) phi1 phi2
        hn hm hp hlogp hXm hYcm hFm hGcm hind hMemX hMemY' hIntX hIntY' hIntF hIntY'
        hmeanX hmeanY' hGaussX hGaussY' hSq' hlow' hphi1 hphi2 (by norm_num)
      have goalz : (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
          |delta n m| ^ 3 *
          (phi2 * LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G +
            LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
            phi2 * Mstar P m (delta n m) muY Y G phi2) = 0 := by
        rw [hδz]
        simp
      rw [goalz, hrho]
      simp only [hly0, hms0, abs_one, one_pow, mul_zero, mul_one, add_zero,
        zero_mul] at key ⊢
      exact key
    · exact hmain Ω P n m p delta muX muY X Y F G phi1 phi2 hn hm hp hlogp hXm hYm hFm hGm
        hindep hMemX hMemY hIntX hIntY hIntF hIntG hmeanX hmeanY hGaussX hGaussY hSq hlow
        hphi1 hphi2 hδz
  intro Ω instΩ P instP n m p delta muX muY X Y F G phi1 phi2
  intro hn hm hp hlogp hXm hYm hFm hGm hindep hMemX hMemY hIntX hIntY hIntF hIntG
    hmeanX hmeanY hGaussX hGaussY hSq hlow hphi1 hphi2 hδ0
  have hXu := @hKX Ω instΩ
  have hYu := @hKY Ω instΩ
  have hp2 : 2 ≤ p := by
    rcases Nat.lt_or_ge p 2 with h | h
    · interval_cases p <;> simp at hlogp
    · exact h
  have hφpos : (0 : ℝ) < min phi1 phi2 := lt_of_lt_of_le one_pos (le_min hphi1 hphi2)
  haveI : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  haveI : Nonempty (Fin p → ℝ) := ⟨fun _ => 0⟩
  conv_lhs => unfold rho
  refine ciSup_le (fun v => ciSup_le (fun y => ?_))
  have hXY : Measurable (fun ω : Ω => combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω)) := by
    rw [measurable_pi_iff]
    intro j
    have hsX : Measurable (fun ω : Ω => ∑ i : Fin n, X i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hXm i))
    have hsY : Measurable (fun ω : Ω => ∑ i : Fin m, Y i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hYm i))
    have hfun : (fun ω : Ω => combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j)
        = fun ω => (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, X i ω j) - Real.sqrt (n : ℝ) * muX j
            + (delta n m) * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, Y i ω j))
            - (delta n m) * Real.sqrt (m : ℝ) * muY j := by
      funext ω
      simp only [combVec, normSum]
    rw [hfun]
    exact (((hsX.const_mul _).sub measurable_const).add
      ((hsY.const_mul _).const_mul (delta n m))).sub measurable_const
  have hFG : Measurable (fun ω : Ω => combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω)) := by
    rw [measurable_pi_iff]
    intro j
    have hsF : Measurable (fun ω : Ω => ∑ i : Fin n, F i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hFm i))
    have hsG : Measurable (fun ω : Ω => ∑ i : Fin m, G i ω j) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (hGm i))
    have hfun : (fun ω : Ω => combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)
        = fun ω => (Real.sqrt (n : ℝ))⁻¹ * (∑ i : Fin n, F i ω j) - Real.sqrt (n : ℝ) * muX j
            + (delta n m) * ((Real.sqrt (m : ℝ))⁻¹ * (∑ i : Fin m, G i ω j))
            - (delta n m) * Real.sqrt (m : ℝ) * muY j := by
      funext ω
      simp only [combVec, normSum]
    rw [hfun]
    exact (((hsF.const_mul _).sub measurable_const).add
      ((hsG.const_mul _).const_mul (delta n m))).sub measurable_const
  set Z1 : Ω × Ω → Fin p → ℝ := fun x j =>
      Real.sqrt (v : ℝ) * combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j
    + Real.sqrt (1 - (v : ℝ)) * combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j with hZ1def
  set Z0 : Ω × Ω → Fin p → ℝ := fun x j =>
      combVec n m (delta n m) muX muY (fun i => F i x.2) (fun i => G i x.2) j with hZ0def
  have hZ1m : Measurable Z1 := by
    rw [hZ1def, measurable_pi_iff]
    intro j
    have h1 : Measurable (fun x : Ω × Ω =>
        combVec n m (delta n m) muX muY (fun i => X i x.1) (fun i => Y i x.1) j) :=
      (measurable_pi_apply j).comp (hXY.comp measurable_fst)
    have h2 : Measurable (fun x : Ω × Ω =>
        combVec n m (delta n m) muX muY (fun i => F i x.1) (fun i => G i x.1) j) :=
      (measurable_pi_apply j).comp (hFG.comp measurable_fst)
    exact (h1.const_mul _).add (h2.const_mul _)
  have hZ0m : Measurable Z0 := by
    rw [hZ0def, measurable_pi_iff]
    intro j
    exact (measurable_pi_apply j).comp (hFG.comp measurable_snd)
  haveI hPprob : IsProbabilityMeasure P := instP
  have hsan := statopia_math_node_2755391374_6e6ed0b4 p hp2 (min phi1 phi2) (le_min hphi1 hphi2)
    (fun z : ℝ => Real.smoothTransition (1 - z)) hφc hφl hφr hφrange
    (Ω × Ω) (P.prod P) Z1 Z0 hZ1m hZ0m
  have hB := hsan.2.2 y
  have hset1 : {x : Ω × Ω | ∀ j : Fin p, Z1 x j ≤ y j}
      = {ω : Ω | ∀ j : Fin p,
            Real.sqrt (v : ℝ) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
          + Real.sqrt (1 - (v : ℝ)) *
              combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j} ×ˢ Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true, hZ1def]
  have hm1 : (P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z1 x j ≤ y j}
      = P {ω : Ω | ∀ j : Fin p,
            Real.sqrt (v : ℝ) * combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
          + Real.sqrt (1 - (v : ℝ)) *
              combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j} := by
    rw [hset1, Measure.prod_prod, measure_univ, mul_one]
  have hset0 : {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j}
      = Set.univ ×ˢ {ω : Ω | ∀ j : Fin p,
            combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, hZ0def]
  have hm0 : (P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j}
      = P {ω : Ω | ∀ j : Fin p,
            combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ y j} := by
    rw [hset0, Measure.prod_prod, measure_univ, one_mul]
  have hm0gen : ∀ (u : Fin p → ℝ), (P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ u j}
      = P {ω : Ω | ∀ j : Fin p,
            combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ u j} := by
    intro u
    have hset : {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ u j}
        = Set.univ ×ˢ {ω : Ω | ∀ j : Fin p,
            combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ u j} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, hZ0def]
    rw [hset, Measure.prod_prod, measure_univ, one_mul]
  have hbr0 := hm0gen (fun j : Fin p => y j + 2 * (min phi1 phi2)⁻¹)
  have hbr1 := hm0gen (fun j : Fin p => y j - 2 * (min phi1 phi2)⁻¹)
  have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
    Real.mul_self_sqrt hmreal.le
  have hnormC : ∀ j : Fin p, normSum m (fun _ : Fin m => muY) j = Real.sqrt (m : ℝ) * muY j := by
    intro j
    have hn0 : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hmreal).ne'
    have hsum : (∑ i : Fin m, muY j) = (m : ℝ) * muY j := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc normSum m (fun _ : Fin m => muY) j
        = (Real.sqrt (m : ℝ))⁻¹ * ((m : ℝ) * muY j) := by
          simp only [normSum, hsum]
      _ = Real.sqrt (m : ℝ) * muY j := by
          have hexp : (m : ℝ) * muY j = Real.sqrt (m : ℝ) * (Real.sqrt (m : ℝ) * muY j) := by
            rw [← mul_assoc, hmsq]
          rw [hexp, ← mul_assoc ((Real.sqrt (m : ℝ))⁻¹) (Real.sqrt (m : ℝ))
            (Real.sqrt (m : ℝ) * muY j), inv_mul_cancel₀ hn0, one_mul]
  have hconst : ∀ (d : ℝ) (Z : Fin n → Fin p → ℝ) (j : Fin p),
      combVec n m d muX muY Z (fun _ => muY) j = normSum n Z j - Real.sqrt (n : ℝ) * muX j := by
    intro d Z j
    simp only [combVec, hnormC j]
    ring
  have hwin2 : ∀ (u : Fin p → ℝ) (c : ℝ), 0 < c →
      (P {ω : Ω | ∀ j : Fin p,
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ u j + c}).toReal
        - (P {ω : Ω | ∀ j : Fin p,
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j ≤ u j}).toReal
        ≤ CA * c * Real.sqrt (Real.log (p : ℝ)) := by
    intro u c hc
    by_cases hδ : delta n m = 0
    · exact absurd hδ hδ0
    · exact (hAC Ω P n m p delta muX muY X Y F G hn hm hp hlogp hδ hFm hGm hindep
        hMemX hMemY hmeanX hmeanY hGaussX hGaussY hSq hlow).2 u c hc
  have hbrid : (P {ω : Ω | ∀ j : Fin p,
        combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ y j + 2 * (min phi1 phi2)⁻¹}).toReal
      - (P {ω : Ω | ∀ j : Fin p,
        combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          ≤ y j - 2 * (min phi1 phi2)⁻¹}).toReal
      ≤ 4 * CA * (min phi1 phi2)⁻¹ * Real.sqrt (Real.log (p : ℝ)) := by
    have hc : 0 < 2 * (min phi1 phi2)⁻¹ := mul_pos two_pos (inv_pos.mpr hφpos)
    have e1 := hwin2 y (2 * (min phi1 phi2)⁻¹) hc
    have e2 := hwin2 (fun j : Fin p => y j - 2 * (min phi1 phi2)⁻¹) (2 * (min phi1 phi2)⁻¹) hc
    have hlim : (∀ j : Fin p, y j - 2 * (min phi1 phi2)⁻¹ + 2 * (min phi1 phi2)⁻¹ = y j) :=
      fun j => by ring
    have e2' := e2
    simp only [hlim] at e2'
    linarith [e1, e2']
  have hZ1eq : Z1 = fun x j =>
      (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt 1 * (Real.sqrt (v : ℝ) * (X i x.1 j - muX j) +
          Real.sqrt (1 - (v : ℝ)) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - 1) * (F i x.2 j - muX j))) +
      (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (delta n m) *
        (Real.sqrt 1 * (Real.sqrt (v : ℝ) * (Y i x.1 j - muY j) +
          Real.sqrt (1 - (v : ℝ)) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - 1) * (G i x.2 j - muY j))) := by
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmreal' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hsqrt_inv_mul : ∀ {N : ℕ}, (0 : ℝ) < (N : ℝ) → ∀ c : ℝ,
        (Real.sqrt (N : ℝ))⁻¹ * ((N : ℝ) * c) = Real.sqrt (N : ℝ) * c := by
      intro N hN c
      have hNne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
      have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt hN.le
      have hexp : (N : ℝ) * c = Real.sqrt (N : ℝ) * (Real.sqrt (N : ℝ) * c) := by
        rw [← mul_assoc, hsq]
      rw [hexp, ← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
    funext x j
    rw [hZ1def]
    have hTX : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j))
        = normSum n (fun i => X i x.1) j - Real.sqrt (n : ℝ) * muX j := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, normSum, mul_sub, hsqrt_inv_mul hnreal]
    have hTF : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j))
        = normSum n (fun i => F i x.1) j - Real.sqrt (n : ℝ) * muX j := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, normSum, mul_sub, hsqrt_inv_mul hnreal]
    have hTY : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (delta n m) * (Y i x.1 j - muY j))
        = delta n m * (normSum m (fun i => Y i x.1) j - Real.sqrt (m : ℝ) * muY j) := by
      have h1 : (∑ i : Fin m, (Y i x.1 j - muY j))
          = (∑ i : Fin m, Y i x.1 j) - (m : ℝ) * muY j := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      have hstep : ((Real.sqrt (m : ℝ))⁻¹ * delta n m) * ((m : ℝ) * muY j)
          = delta n m * (Real.sqrt (m : ℝ) * muY j) := by
        rw [← hsqrt_inv_mul hmreal' (muY j)]
        ring
      rw [← Finset.mul_sum, h1, normSum, mul_sub, hstep]
      ring
    have hTG : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (delta n m) * (G i x.1 j - muY j))
        = delta n m * (normSum m (fun i => G i x.1) j - Real.sqrt (m : ℝ) * muY j) := by
      have h1 : (∑ i : Fin m, (G i x.1 j - muY j))
          = (∑ i : Fin m, G i x.1 j) - (m : ℝ) * muY j := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      have hstep : ((Real.sqrt (m : ℝ))⁻¹ * delta n m) * ((m : ℝ) * muY j)
          = delta n m * (Real.sqrt (m : ℝ) * muY j) := by
        rw [← hsqrt_inv_mul hmreal' (muY j)]
        ring
      rw [← Finset.mul_sum, h1, normSum, mul_sub, hstep]
      ring
    have hsplit : ∀ {N : ℕ} (c p q : ℝ) (a b : Fin N → ℝ),
        (∑ i : Fin N, c * (p * a i + q * b i)) = p * (∑ i, c * a i) + q * (∑ i, c * b i) := by
      intro N c p q a b
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hAn : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt (v : ℝ) * (X i x.1 j - muX j) +
            Real.sqrt (1 - (v : ℝ)) * (F i x.1 j - muX j)))
        = Real.sqrt (v : ℝ) * (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (X i x.1 j - muX j))
          + Real.sqrt (1 - (v : ℝ)) *
              (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.1 j - muX j)) := by
      simpa using hsplit (Real.sqrt (n : ℝ))⁻¹ (Real.sqrt (v : ℝ)) (Real.sqrt (1 - (v : ℝ)))
        (fun i => X i x.1 j - muX j) (fun i => F i x.1 j - muX j)
    have hAm : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (delta n m) *
          (Real.sqrt (v : ℝ) * (Y i x.1 j - muY j) +
            Real.sqrt (1 - (v : ℝ)) * (G i x.1 j - muY j)))
        = Real.sqrt (v : ℝ) *
              (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (delta n m) * (Y i x.1 j - muY j))
          + Real.sqrt (1 - (v : ℝ)) *
              (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (delta n m) * (G i x.1 j - muY j)) := by
      simpa using hsplit ((Real.sqrt (m : ℝ))⁻¹ * delta n m) (Real.sqrt (v : ℝ))
        (Real.sqrt (1 - (v : ℝ))) (fun i => Y i x.1 j - muY j) (fun i => G i x.1 j - muY j)
    simp only [Real.sqrt_one, one_mul, sub_self, Real.sqrt_zero, zero_mul, add_zero]
    rw [hAn, hAm, hTX, hTF, hTY, hTG]
    simp only [combVec]
    ring
  have hZ0eq : Z0 = fun x j =>
      (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt 0 * (Real.sqrt (v : ℝ) * (X i x.1 j - muX j) +
          Real.sqrt (1 - (v : ℝ)) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - 0) * (F i x.2 j - muX j))) +
      (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (delta n m) *
        (Real.sqrt 0 * (Real.sqrt (v : ℝ) * (Y i x.1 j - muY j) +
          Real.sqrt (1 - (v : ℝ)) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - 0) * (G i x.2 j - muY j))) := by
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmreal' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hsqrt_inv_mul : ∀ {N : ℕ}, (0 : ℝ) < (N : ℝ) → ∀ c : ℝ,
        (Real.sqrt (N : ℝ))⁻¹ * ((N : ℝ) * c) = Real.sqrt (N : ℝ) * c := by
      intro N hN c
      have hNne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
      have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt hN.le
      have hexp : (N : ℝ) * c = Real.sqrt (N : ℝ) * (Real.sqrt (N : ℝ) * c) := by
        rw [← mul_assoc, hsq]
      rw [hexp, ← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
    funext x j
    rw [hZ0def]
    have hAn : (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j))
        = normSum n (fun i => F i x.2) j - Real.sqrt (n : ℝ) * muX j := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, normSum, mul_sub, hsqrt_inv_mul hnreal]
    have hAm : (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * (delta n m) * (G i x.2 j - muY j))
        = delta n m * (normSum m (fun i => G i x.2) j - Real.sqrt (m : ℝ) * muY j) := by
      have h1 : (∑ i : Fin m, (G i x.2 j - muY j))
          = (∑ i : Fin m, G i x.2 j) - (m : ℝ) * muY j := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      have hstep : ((Real.sqrt (m : ℝ))⁻¹ * delta n m) * ((m : ℝ) * muY j)
          = delta n m * (Real.sqrt (m : ℝ) * muY j) := by
        rw [← hsqrt_inv_mul hmreal' (muY j)]
        ring
      rw [← Finset.mul_sum, h1, normSum, mul_sub, hstep]
      ring
    simp only [Real.sqrt_zero, Real.sqrt_one, sub_zero, zero_mul, zero_add, one_mul]
    rw [hAn, hAm]
    simp only [combVec]
    ring
  set Xe := (Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
      (phi1 * LX P n muX X * rho P n m p (delta n m) muX muY X Y F G +
        LX P n muX X * Real.sqrt (Real.log (p : ℝ)) +
        phi1 * Mn P n muX X F phi1) with hXedef
  set Ye := (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 * |delta n m| ^ 3 *
      (phi2 * LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G +
        LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
        phi2 * Mstar P m (delta n m) muY Y G phi2) with hYedef
  set We := (min phi1 phi2)⁻¹ * Real.sqrt (Real.log (p : ℝ)) with hWedef
  have step2 : 2 * (KX * Xe) + 2 * (KY * Ye) + 4 * CA * We ≤
      16 * (KX + KY + CA + 1) * (Xe + Ye + We) := by
    obtain ⟨-, hRx⟩ := hXu P n m p hn hm hp hlogp delta muX muY X Y F G hXm hYm hFm hGm
      hindep hMemX hMemY hIntX hIntY hIntF hIntG hmeanX hmeanY hGaussX hGaussY hSq hlow
      phi1 phi2 hphi1 hphi2 (v : ℝ) v.2.1 v.2.2 y
    obtain ⟨-, hRy⟩ := hYu P n m p delta muX muY X Y F G phi1 phi2 (v : ℝ) y
      hn hm hp hlogp hδ0 hXm hYm hFm hGm hindep hmeanX hmeanY hMemX hMemY hIntX hIntY hIntF hIntG
      hGaussX hGaussY hlow hphi1 hphi2 v.2.1 v.2.2
    rw [← mul_assoc phi2 (LY P m muY Y) (rho P n m p (delta n m) muX muY X Y F G)] at hRy
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have h1pos : (0 : ℝ) < phi1 := lt_of_lt_of_le one_pos hphi1
    have h2pos : (0 : ℝ) < phi2 := lt_of_lt_of_le one_pos hphi2
    have hCX : (0 : ℝ) < KX * (Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 :=
      mul_pos (mul_pos (mul_pos hKXpos (inv_pos.mpr (Real.sqrt_pos.mpr hnreal)))
        (pow_pos h1pos 2)) (pow_pos hlogp 2)
    have hCY : (0 : ℝ) <
        KY * (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 * |delta n m| ^ 3 :=
      mul_pos (mul_pos (mul_pos (mul_pos hKYpos (inv_pos.mpr (Real.sqrt_pos.mpr hmreal)))
        (pow_pos h2pos 2)) (pow_pos hlogp 2)) (pow_pos (abs_pos.mpr hδ0) 3)
    have h0x : (0 : ℝ) ≤ KX * (Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
        (phi1 * LX P n muX X * rho P n m p (delta n m) muX muY X Y F G +
          LX P n muX X * Real.sqrt (Real.log (p : ℝ)) + phi1 * Mn P n muX X F phi1) :=
      le_trans (abs_nonneg _) hRx
    have h0y : (0 : ℝ) ≤
        KY * (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 * |delta n m| ^ 3 *
        (phi2 * LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G +
          LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) + phi2 * Mstar P m (delta n m) muY Y G phi2) :=
      le_trans (abs_nonneg _) hRy
    have hXnn : (0 : ℝ) ≤ Xe := by
      rw [hXedef]
      by_cases h : 0 ≤ (phi1 * LX P n muX X * rho P n m p (delta n m) muX muY X Y F G +
          LX P n muX X * Real.sqrt (Real.log (p : ℝ)) + phi1 * Mn P n muX X F phi1)
      · exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
          (sq_nonneg phi1)) (sq_nonneg (Real.log (p : ℝ)))) h
      · exact absurd h0x (not_le.mpr (mul_neg_of_pos_of_neg hCX (not_le.mp h)))
    have hYnn : (0 : ℝ) ≤ Ye := by
      rw [hYedef]
      by_cases h : 0 ≤ (phi2 * LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G +
          LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
          phi2 * Mstar P m (delta n m) muY Y G phi2)
      · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
          (sq_nonneg phi2)) (sq_nonneg (Real.log (p : ℝ)))) (pow_nonneg (abs_nonneg _) 3)) h
      · exact absurd h0y (not_le.mpr (mul_neg_of_pos_of_neg hCY (not_le.mp h)))
    have hWnn : (0 : ℝ) ≤ We := by
      rw [hWedef]
      exact mul_nonneg (inv_nonneg.mpr hφpos.le) (Real.sqrt_nonneg _)
    have hb1 : 2 * (KX * Xe) ≤ 16 * (KX + KY + CA + 1) * Xe := by
      have h : 2 * KX ≤ 16 * (KX + KY + CA + 1) := by linarith
      calc 2 * (KX * Xe) = (2 * KX) * Xe := by ring
        _ ≤ 16 * (KX + KY + CA + 1) * Xe := mul_le_mul_of_nonneg_right h hXnn
    have hb2 : 2 * (KY * Ye) ≤ 16 * (KX + KY + CA + 1) * Ye := by
      have h : 2 * KY ≤ 16 * (KX + KY + CA + 1) := by linarith
      calc 2 * (KY * Ye) = (2 * KY) * Ye := by ring
        _ ≤ 16 * (KX + KY + CA + 1) * Ye := mul_le_mul_of_nonneg_right h hYnn
    have hb3 : 4 * (CA * We) ≤ 16 * (KX + KY + CA + 1) * We := by
      have h : 4 * CA ≤ 16 * (KX + KY + CA + 1) := by linarith
      calc 4 * (CA * We) = (4 * CA) * We := by ring
        _ ≤ 16 * (KX + KY + CA + 1) * We := mul_le_mul_of_nonneg_right h hWnn
    calc 2 * (KX * Xe) + 2 * (KY * Ye) + 4 * CA * We
        = 2 * (KX * Xe) + 2 * (KY * Ye) + 4 * (CA * We) := by ring
      _ ≤ 16 * (KX + KY + CA + 1) * (Xe + Ye + We) := by linarith [hb1, hb2, hb3]
  have step1 : |((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z1 x j ≤ y j}).toReal
      - ((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j}).toReal| ≤
      2 * (KX * Xe) + 2 * (KY * Ye) + 4 * CA * We := by
    let K : (Fin p → ℝ) → (Fin p → ℝ) → ℝ := fun u w =>
      (fun z : ℝ => Real.smoothTransition (1 - z)) (min phi1 phi2 *
        (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
          Real.log (∑ j : Fin p, Real.exp ((min phi1 phi2 * Real.log (p : ℝ)) * (w j - u j)))))
    have hBK : |((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z1 x j ≤ y j}).toReal
        - ((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j}).toReal|
        ≤ |∫ x, (K (fun j : Fin p => y j + (min phi1 phi2)⁻¹) (Z1 x) -
              K (fun j : Fin p => y j + (min phi1 phi2)⁻¹) (Z0 x)) ∂(P.prod P)|
          + |∫ x, (K (fun j : Fin p => y j - (min phi1 phi2)⁻¹) (Z1 x) -
              K (fun j : Fin p => y j - (min phi1 phi2)⁻¹) (Z0 x)) ∂(P.prod P)|
          + (((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j + 2 * (min phi1 phi2)⁻¹}).toReal
            - ((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j - 2 * (min phi1 phi2)⁻¹}).toReal) :=
      hB
    have hW : ((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j + 2 * (min phi1 phi2)⁻¹}).toReal
        - ((P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j - 2 * (min phi1 phi2)⁻¹}).toReal
        ≤ 4 * CA * We := by
      rw [show (P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j + 2 * (min phi1 phi2)⁻¹}
            = P {ω : Ω | ∀ j : Fin p,
                combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
                  ≤ y j + 2 * (min phi1 phi2)⁻¹} from hbr0,
          show (P.prod P) {x : Ω × Ω | ∀ j : Fin p, Z0 x j ≤ y j - 2 * (min phi1 phi2)⁻¹}
            = P {ω : Ω | ∀ j : Fin p,
                combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
                  ≤ y j - 2 * (min phi1 phi2)⁻¹} from hbr1,
          hWedef]
      linarith [hbrid]
    have hp1 : |∫ x, (K (fun j : Fin p => y j + (min phi1 phi2)⁻¹) (Z1 x) -
          K (fun j : Fin p => y j + (min phi1 phi2)⁻¹) (Z0 x)) ∂(P.prod P)| ≤
        KX * Xe + KY * Ye := by
      obtain ⟨-, -, hEq⟩ := statopia_math_node_2978248555_2b2dc1fc.{u_1} b hb
        (fun z : ℝ => Real.smoothTransition (1 - z)) hφc hφl hφr hφrange
        Ω P n m p delta muX muY X Y F G phi1 phi2
        (fun j : Fin p => y j + (min phi1 phi2)⁻¹) (v : ℝ)
        hn hm hp hlogp hδ0 hXm hYm hFm hGm hMemX hMemY hIntX hIntY hIntF hIntG hphi1 hphi2
        v.2.1 v.2.2
      obtain ⟨-, hRx⟩ := hXu P n m p hn hm hp hlogp delta muX muY X Y F G hXm hYm hFm hGm
        hindep hMemX hMemY hIntX hIntY hIntF hIntG hmeanX hmeanY hGaussX hGaussY hSq hlow
        phi1 phi2 hphi1 hphi2 (v : ℝ) v.2.1 v.2.2 (fun j : Fin p => y j + (min phi1 phi2)⁻¹)
      obtain ⟨-, hRy⟩ := hYu P n m p delta muX muY X Y F G phi1 phi2 (v : ℝ) (fun j : Fin p => y j + (min phi1 phi2)⁻¹)
        hn hm hp hlogp hδ0 hXm hYm hFm hGm hindep hmeanX hmeanY hMemX hMemY hIntX hIntY hIntF hIntG
        hGaussX hGaussY hlow hphi1 hphi2 v.2.1 v.2.2
      rw [← mul_assoc phi2 (LY P m muY Y) (rho P n m p (delta n m) muX muY X Y F G)] at hRy
      have cX : KX * (Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
          (phi1 * LX P n muX X * rho P n m p (delta n m) muX muY X Y F G +
            LX P n muX X * Real.sqrt (Real.log (p : ℝ)) + phi1 * Mn P n muX X F phi1) =
          KX * Xe := by
        rw [hXedef]
        ring
      have cY : KY * (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
          |delta n m| ^ 3 *
          (phi2 * LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G +
            LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
            phi2 * Mstar P m (delta n m) muY Y G phi2) =
          KY * Ye := by
        rw [hYedef]
        ring
      have hRx' := cX ▸ hRx
      have hRy' := cY ▸ hRy
      rw [hZ1eq, hZ0eq]
      rw [hEq]
      refine le_trans (abs_add_le _ _) ?_
      linarith [hRx', hRy']
    have hp2c : |∫ x, (K (fun j : Fin p => y j - (min phi1 phi2)⁻¹) (Z1 x) -
          K (fun j : Fin p => y j - (min phi1 phi2)⁻¹) (Z0 x)) ∂(P.prod P)| ≤
        KX * Xe + KY * Ye := by
      obtain ⟨-, -, hEq⟩ := statopia_math_node_2978248555_2b2dc1fc.{u_1} b hb
        (fun z : ℝ => Real.smoothTransition (1 - z)) hφc hφl hφr hφrange
        Ω P n m p delta muX muY X Y F G phi1 phi2
        (fun j : Fin p => y j - (min phi1 phi2)⁻¹) (v : ℝ)
        hn hm hp hlogp hδ0 hXm hYm hFm hGm hMemX hMemY hIntX hIntY hIntF hIntG hphi1 hphi2
        v.2.1 v.2.2
      obtain ⟨-, hRx⟩ := hXu P n m p hn hm hp hlogp delta muX muY X Y F G hXm hYm hFm hGm
        hindep hMemX hMemY hIntX hIntY hIntF hIntG hmeanX hmeanY hGaussX hGaussY hSq hlow
        phi1 phi2 hphi1 hphi2 (v : ℝ) v.2.1 v.2.2 (fun j : Fin p => y j - (min phi1 phi2)⁻¹)
      obtain ⟨-, hRy⟩ := hYu P n m p delta muX muY X Y F G phi1 phi2 (v : ℝ) (fun j : Fin p => y j - (min phi1 phi2)⁻¹)
        hn hm hp hlogp hδ0 hXm hYm hFm hGm hindep hmeanX hmeanY hMemX hMemY hIntX hIntY hIntF hIntG
        hGaussX hGaussY hlow hphi1 hphi2 v.2.1 v.2.2
      rw [← mul_assoc phi2 (LY P m muY Y) (rho P n m p (delta n m) muX muY X Y F G)] at hRy
      have cX : KX * (Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
          (phi1 * LX P n muX X * rho P n m p (delta n m) muX muY X Y F G +
            LX P n muX X * Real.sqrt (Real.log (p : ℝ)) + phi1 * Mn P n muX X F phi1) =
          KX * Xe := by
        rw [hXedef]
        ring
      have cY : KY * (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
          |delta n m| ^ 3 *
          (phi2 * LY P m muY Y * rho P n m p (delta n m) muX muY X Y F G +
            LY P m muY Y * Real.sqrt (Real.log (p : ℝ)) +
            phi2 * Mstar P m (delta n m) muY Y G phi2) =
          KY * Ye := by
        rw [hYedef]
        ring
      have hRx' := cX ▸ hRx
      have hRy' := cY ▸ hRy
      rw [hZ1eq, hZ0eq]
      rw [hEq]
      refine le_trans (abs_add_le _ _) ?_
      linarith [hRx', hRy']
    refine le_trans hBK ?_
    linarith [hp1, hp2c, hW]
  rw [← hm1, ← hm0]
  exact le_trans step1 step2
  /- @proof-region region.root.6bffa6e14453 end -/

end

end Statlib.Imported

-- Paper root revision 92f11ca6-d24b-4c93-947e-9f07945fd04b

