import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1071104920_3e9ffb8e_a1f23a7a
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3377209132_cbbc544b_686c37e5
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_351002483_30a1f705_1578c4bd
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_4050339779_734b360b_cdfed423

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
theorem statopia_math_node_1208774784_f8ea2879 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (hFcov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (y : Fin p → ℝ),
    (let phi : ℝ := min phi1 phi2
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
       phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
     ∀ (t : ℝ), 0 < t → t < 1 → ∀ (i : Fin n) (j k : Fin p),
       Integrable (fun x : Ω × Ω =>
         (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ)))
             (fun k' : Fin p => Z t x k' - Zstar t x i k')) (Pi.single k (1 : ℝ)) *
           (Zstar t x i k * Zdotstar t x i j)) (P.prod P) ∧
         (∫ x : Ω × Ω,
           (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ)))
               (fun k' : Fin p => Z t x k' - Zstar t x i k')) (Pi.single k (1 : ℝ)) *
             (Zstar t x i k * Zdotstar t x i j) ∂(P.prod P)) = 0) := by
  /- @proof-region region.target-node.session.e9712dccf8320f15 begin -/
  intro Ω instΩ P instP n m p delta muX muY X Y F G hn hm hp hlogp hX hY hF hG hindep
    hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov phi0 hphi0_cont hphi0_left hphi0_right
    hphi0_range phi1 phi2 hphi1 hphi2 v hv0 hv1 y phi beta Zstar Zstarstar Z Zdotstar kappa
    t ht0 ht1 i j k
  have hB := statopia_math_node_4050339779_734b360b Ω P n m p delta muX muY X Y F G
    hn hm hp hX hY hF hG hindep hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov
    v hv0 hv1 t ht0 ht1 i j k
  have hBint : Integrable (fun x : Ω × Ω => Zstar t x i k * Zdotstar t x i j) (P.prod P) :=
    hB.1
  have hBzero : (∫ x : Ω × Ω, Zstar t x i k * Zdotstar t x i j ∂(P.prod P)) = 0 := hB.2
  set Atr : Ω × Ω → ℝ := fun x =>
    (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ)))
        (fun k' : Fin p => Z t x k' - Zstar t x i k')) (Pi.single k (1 : ℝ)) with hAtr
  obtain ⟨Cbd, hCbdpos, hCbd⟩ :=
    statopia_math_node_1071104920_3e9ffb8e phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  have hSecond := hCbd p hlogp (min phi1 phi2) (le_min hphi1 hphi2) y j k
  have hAcont : Continuous (fun w : Fin p → ℝ =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ))) w)
        (Pi.single k (1 : ℝ))) := hSecond.2
  have hAbdd : ∃ c : ℝ, ∀ᵐ x ∂(P.prod P), ‖Atr x‖ ≤ c := by
    refine ⟨Cbd * beta ^ 2, ?_⟩
    filter_upwards with x
    have hx : |Atr x| ≤ Cbd * beta ^ 2 :=
      hSecond.1 (fun k' : Fin p => Z t x k' - Zstar t x i k')
    simpa using hx
  have hAmeas : AEStronglyMeasurable Atr (P.prod P) := by
    have hX1 : ∀ (i' : Fin n) (j' : Fin p), Measurable (fun x : Ω × Ω => X i' x.1 j') :=
      fun i' j' => (measurable_pi_apply j').comp ((hX i').comp measurable_fst)
    have hF1 : ∀ (i' : Fin n) (j' : Fin p), Measurable (fun x : Ω × Ω => F i' x.1 j') :=
      fun i' j' => (measurable_pi_apply j').comp ((hF i').comp measurable_fst)
    have hF2 : ∀ (i' : Fin n) (j' : Fin p), Measurable (fun x : Ω × Ω => F i' x.2 j') :=
      fun i' j' => (measurable_pi_apply j').comp ((hF i').comp measurable_snd)
    have hY1 : ∀ (i' : Fin m) (j' : Fin p), Measurable (fun x : Ω × Ω => Y i' x.1 j') :=
      fun i' j' => (measurable_pi_apply j').comp ((hY i').comp measurable_fst)
    have hG1 : ∀ (i' : Fin m) (j' : Fin p), Measurable (fun x : Ω × Ω => G i' x.1 j') :=
      fun i' j' => (measurable_pi_apply j').comp ((hG i').comp measurable_fst)
    have hG2 : ∀ (i' : Fin m) (j' : Fin p), Measurable (fun x : Ω × Ω => G i' x.2 j') :=
      fun i' j' => (measurable_pi_apply j').comp ((hG i').comp measurable_snd)
    have hZs : ∀ (i' : Fin n) (j' : Fin p), Measurable (fun x : Ω × Ω =>
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i' x.1 j' - muX j') +
              Real.sqrt (1 - v) * (F i' x.1 j' - muX j')) +
            Real.sqrt (1 - t) * (F i' x.2 j' - muX j'))) := by
      intro i' j'
      exact Measurable.const_mul
        (Measurable.add
          (Measurable.const_mul
            (Measurable.add
              (Measurable.const_mul ((hX1 i' j').sub measurable_const) (Real.sqrt v))
              (Measurable.const_mul ((hF1 i' j').sub measurable_const) (Real.sqrt (1 - v))))
            (Real.sqrt t))
          (Measurable.const_mul ((hF2 i' j').sub measurable_const) (Real.sqrt (1 - t))))
        ((Real.sqrt (n : ℝ))⁻¹)
    have hSsm : ∀ (i' : Fin m) (j' : Fin p), Measurable (fun x : Ω × Ω =>
        (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i' x.1 j' - muY j') +
              Real.sqrt (1 - v) * (G i' x.1 j' - muY j')) +
            Real.sqrt (1 - t) * (G i' x.2 j' - muY j'))) := by
      intro i' j'
      exact Measurable.const_mul
        (Measurable.add
          (Measurable.const_mul
            (Measurable.add
              (Measurable.const_mul ((hY1 i' j').sub measurable_const) (Real.sqrt v))
              (Measurable.const_mul ((hG1 i' j').sub measurable_const) (Real.sqrt (1 - v))))
            (Real.sqrt t))
          (Measurable.const_mul ((hG2 i' j').sub measurable_const) (Real.sqrt (1 - t))))
        ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
    have hZc : ∀ j' : Fin p, Measurable (fun x : Ω × Ω => Z t x j') := by
      intro j'
      exact (Finset.measurable_sum (Finset.univ : Finset (Fin n))
        (fun i' _ => hZs i' j')).add
        (Finset.measurable_sum (Finset.univ : Finset (Fin m))
          (fun i' _ => hSsm i' j'))
    have hu : Measurable (fun x : Ω × Ω => fun k' : Fin p => Z t x k' - Zstar t x i k') := by
      rw [measurable_pi_iff]
      intro k'
      exact (hZc k').sub (hZs i k')
    exact hAcont.comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hIndep : IndepFun Atr (fun x : Ω × Ω => Zstar t x i k * Zdotstar t x i j) (P.prod P) := by
    have hp2 : 2 ≤ p := by
      by_contra h
      have h1 : p ≤ 1 := by omega
      have h2 : p = 1 := by omega
      rw [h2] at hlogp
      simp only [Nat.cast_one, Real.log_one] at hlogp
      exact absurd hlogp (lt_irrefl 0)
    have hk3 : ContDiff ℝ 3 kappa :=
      (statopia_math_node_2194576110_d2ad0cef p hp2 (min phi1 phi2) (le_min hphi1 hphi2) phi0
        hphi0_cont hphi0_left hphi0_right hphi0_range y).1
    have hkap : ContDiff ℝ 1 (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ))) := by
      have h1 : ContDiff ℝ 1 (fun q : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ kappa q.1) q.2) :=
        hk3.contDiff_fderiv_apply (by decide)
      have h2 : ContDiff ℝ 1 (fun z : Fin p → ℝ => (z, (Pi.single j (1 : ℝ) : Fin p → ℝ))) := by
        fun_prop
      exact h1.comp h2
    have hsplit : ∀ (f : Fin n → ℝ),
        (∑ i' : Fin n, (if i' = i then (0 : ℝ) else f i')) = (∑ i' : Fin n, f i') - f i := by
      intro f
      have h1 : (∑ i' : Fin n, (if i' = i then (0 : ℝ) else f i'))
          = ∑ i' : Fin n, (f i' - if i' = i then f i' else 0) := by
        apply Finset.sum_congr rfl
        intro i' _
        by_cases h : i' = i <;> simp [h]
      rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      simp
    set Zrest : Ω × Ω → Fin p → ℝ := fun x k' =>
      (∑ i' : Fin n, if i' = i then (0 : ℝ) else
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i' x.1 k' - muX k') +
              Real.sqrt (1 - v) * (F i' x.1 k' - muX k')) +
            Real.sqrt (1 - t) * (F i' x.2 k' - muX k')))
      + (∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k' - muY k') +
              Real.sqrt (1 - v) * (G i' x.1 k' - muY k')) +
            Real.sqrt (1 - t) * (G i' x.2 k' - muY k'))) with hZrestdef
    have hZrest_eq : ∀ (x : Ω × Ω) (k' : Fin p), Zrest x k' = Z t x k' - Zstar t x i k' := by
      intro x k'
      have hZbody : Z t x k' =
          (∑ i' : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (X i' x.1 k' - muX k') +
                Real.sqrt (1 - v) * (F i' x.1 k' - muX k')) +
              Real.sqrt (1 - t) * (F i' x.2 k' - muX k')))
          + (∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
              (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k' - muY k') +
                  Real.sqrt (1 - v) * (G i' x.1 k' - muY k')) +
                Real.sqrt (1 - t) * (G i' x.2 k' - muY k'))) := rfl
      have hZsbody : Zstar t x i k' = (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i x.1 k' - muX k') +
              Real.sqrt (1 - v) * (F i x.1 k' - muX k')) +
            Real.sqrt (1 - t) * (F i x.2 k' - muX k')) := rfl
      have hZrestbody : Zrest x k' =
          (∑ i' : Fin n, if i' = i then (0 : ℝ) else
            (Real.sqrt (n : ℝ))⁻¹ *
              (Real.sqrt t * (Real.sqrt v * (X i' x.1 k' - muX k') +
                  Real.sqrt (1 - v) * (F i' x.1 k' - muX k')) +
                Real.sqrt (1 - t) * (F i' x.2 k' - muX k')))
          + (∑ i' : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
              (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k' - muY k') +
                  Real.sqrt (1 - v) * (G i' x.1 k' - muY k')) +
                Real.sqrt (1 - t) * (G i' x.2 k' - muY k'))) := rfl
      rw [hZrestbody, hZbody, hZsbody,
        hsplit (fun i' : Fin n => (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i' x.1 k' - muX k') +
              Real.sqrt (1 - v) * (F i' x.1 k' - muX k')) +
            Real.sqrt (1 - t) * (F i' x.2 k' - muX k')))]
      ring
    have hLO := statopia_math_node_3377209132_cbbc544b Ω P n m p delta muX muY X Y F G
      hX hY hF hG hindep (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ))) hkap
      v t i k
    set Tfun : Ω × Ω → (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) :=
      fun x => (X i x.1, (F i x.1, F i x.2)) with hTfun
    have hmain : IndepFun (fun x : Ω × Ω =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ)))
          (Zrest x)) (Pi.single k (1 : ℝ))) Tfun (P.prod P) := hLO
    have hm1 : Measurable (fun w : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => w.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    have hm2 : Measurable (fun w : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => w.2.1 k) :=
      (measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)
    have hm3 : Measurable (fun w : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => w.2.2 k) :=
      (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
    have hm1' : Measurable (fun w : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => w.1 j) :=
      (measurable_pi_apply j).comp measurable_fst
    have hm2' : Measurable (fun w : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => w.2.1 j) :=
      (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
    have hm3' : Measurable (fun w : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => w.2.2 j) :=
      (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
    set g : ((Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ))) → ℝ := fun w =>
      ((Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (w.1 k - muX k) +
            Real.sqrt (1 - v) * (w.2.1 k - muX k)) +
          Real.sqrt (1 - t) * (w.2.2 k - muX k)))
      * ((Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (w.1 j - muX j) +
            Real.sqrt (1 - v) * (w.2.1 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (w.2.2 j - muX j))) with hgdef
    have hg : Measurable g := by
      have hA : Measurable (fun w : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) =>
          (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (w.1 k - muX k) +
                Real.sqrt (1 - v) * (w.2.1 k - muX k)) +
              Real.sqrt (1 - t) * (w.2.2 k - muX k))) :=
        Measurable.const_mul
          (Measurable.add
            (Measurable.const_mul
              (Measurable.add
                (Measurable.const_mul (hm1.sub measurable_const) (Real.sqrt v))
                (Measurable.const_mul (hm2.sub measurable_const) (Real.sqrt (1 - v))))
              (Real.sqrt t))
            (Measurable.const_mul (hm3.sub measurable_const) (Real.sqrt (1 - t))))
          ((Real.sqrt (n : ℝ))⁻¹)
      have hD : Measurable (fun w : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) =>
          (Real.sqrt (n : ℝ))⁻¹ *
            ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (w.1 j - muX j) +
                Real.sqrt (1 - v) * (w.2.1 j - muX j)) -
              (2 * Real.sqrt (1 - t))⁻¹ * (w.2.2 j - muX j))) :=
        Measurable.const_mul
          (Measurable.sub
            (Measurable.const_mul
              (Measurable.add
                (Measurable.const_mul (hm1'.sub measurable_const) (Real.sqrt v))
                (Measurable.const_mul (hm2'.sub measurable_const) (Real.sqrt (1 - v))))
              ((2 * Real.sqrt t)⁻¹))
            (Measurable.const_mul (hm3'.sub measurable_const) ((2 * Real.sqrt (1 - t))⁻¹)))
          ((Real.sqrt (n : ℝ))⁻¹)
      exact hA.mul hD
    have hBfun : (g ∘ Tfun) = (fun x : Ω × Ω => Zstar t x i k * Zdotstar t x i j) := by
      funext x
      rfl
    have hcomp : IndepFun (fun x : Ω × Ω =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ)))
          (Zrest x)) (Pi.single k (1 : ℝ))) (g ∘ Tfun) (P.prod P) :=
      hmain.comp measurable_id hg
    have hPsi_eq : (fun x : Ω × Ω =>
        (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ)))
          (Zrest x)) (Pi.single k (1 : ℝ))) = Atr := by
      funext x
      have hx : Zrest x = fun k' => Z t x k' - Zstar t x i k' := by
        funext k'
        exact hZrest_eq x k'
      rw [hx]
    rw [hPsi_eq, hBfun] at hcomp
    exact hcomp
  have hAint : Integrable Atr (P.prod P) := by
    obtain ⟨c, hc⟩ := hAbdd
    exact Integrable.of_bound hAmeas c hc
  have hint : Integrable (fun x : Ω × Ω => Atr x * (Zstar t x i k * Zdotstar t x i j)) (P.prod P) := by
    obtain ⟨c, hc⟩ := hAbdd
    exact hBint.bdd_mul hAmeas hc
  refine ⟨hint, ?_⟩
  have hprod : (∫ x : Ω × Ω, Atr x * (Zstar t x i k * Zdotstar t x i j) ∂(P.prod P))
      = (∫ x : Ω × Ω, Atr x ∂(P.prod P)) *
          (∫ x : Ω × Ω, Zstar t x i k * Zdotstar t x i j ∂(P.prod P)) := by
    have h := hIndep.integral_mul_eq_mul_integral hAmeas hBint.1
    simpa using h
  rw [hprod, hBzero, mul_zero]
  /- @proof-region region.target-node.session.e9712dccf8320f15 end -/

end

end Statlib.Imported

