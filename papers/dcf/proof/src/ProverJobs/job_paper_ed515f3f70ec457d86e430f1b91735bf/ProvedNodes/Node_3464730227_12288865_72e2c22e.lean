import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1071104920_3e9ffb8e_a1f23a7a
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3377209132_cbbc544b_686c37e5
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
theorem statopia_math_node_3464730227_12288865 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi0 : ℝ → ℝ)
    (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
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
       ∫ x : Ω × Ω,
         (fderiv ℝ (fun w : Fin p → ℝ =>
             (fderiv ℝ kappa w) (Pi.single j (1 : ℝ)))
             (fun r : Fin p => Z t x r - Zstar t x i r)) (Pi.single k (1 : ℝ)) *
           (Zstar t x i k * Zdotstar t x i j) ∂(P.prod P) = 0) := by
  /- @proof-region region.target-node.session.14dfefdcd39cad1b begin -/
  intro Ω mΩ P hP n m p delta muX muY X Y F G phi0 hphi0_cont hphi0_left hphi0_right hphi0_range hn hm hp hlogp
  intro hXm hYm hFm hGm hindep hXL2 hYL2 hX3 hY3 hF3 hG3 hXmean hYmean hFcov hGcov phi1 phi2 hphi1 hphi2 v hv0 hv1 y
  intro phi beta Zstar Zstarstar Z Zdotstar kappa t ht0 ht1 i j k
  let Zr : Ω × Ω → Fin p → ℝ := fun x r => Z t x r - Zstar t x i r
  let kap : (Fin p → ℝ) → ℝ := fun w => (fderiv ℝ kappa w) (Pi.single j (1 : ℝ))
  let kap2 : (Fin p → ℝ) → ℝ := fun u => (fderiv ℝ kap u) (Pi.single k (1 : ℝ))
  let bk : Ω × Ω → (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) := fun x => (X i x.1, (F i x.1, F i x.2))
  let HD : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) → ℝ := fun s =>
    ((Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (s.1 k - muX k) + Real.sqrt (1 - v) * (s.2.1 k - muX k)) +
          Real.sqrt (1 - t) * (s.2.2 k - muX k))) *
      ((Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (s.1 j - muX j) + Real.sqrt (1 - v) * (s.2.1 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (s.2.2 j - muX j)))
  show (∫ x : Ω × Ω, kap2 (Zr x) * (Zstar t x i k * Zdotstar t x i j) ∂(P.prod P)) = 0
  have hmin : 1 ≤ min phi1 phi2 := le_min hphi1 hphi2
  have hp2 : 2 ≤ p := by
    have h1 : (1 : ℝ) < (p : ℝ) := by
      nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < (p : ℝ) by exact_mod_cast hp), hlogp]
    have h2 : 1 < p := by exact_mod_cast h1
    omega
  have hκC3 : ContDiff ℝ 3 kappa :=
    (statopia_math_node_2194576110_d2ad0cef p hp2 (min phi1 phi2) hmin phi0 hphi0_cont hphi0_left hphi0_right hphi0_range y).1
  obtain ⟨Cbd, hCbd_pos, hbd⟩ := statopia_math_node_1071104920_3e9ffb8e phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  have hbdjk := hbd p hlogp (min phi1 phi2) hmin y j k
  have hbd_bound : ∀ w : Fin p → ℝ, |kap2 w| ≤ Cbd * beta ^ 2 := hbdjk.1
  have hbd_cont : Continuous kap2 := hbdjk.2
  have hkapC1 : ContDiff ℝ 1 kap := by
    have hfd : ContDiff ℝ 1 (fun q : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ kappa q.1) q.2) :=
      hκC3.contDiff_fderiv_apply (by norm_num)
    have hconst : ContDiff ℝ 1 (fun _ : Fin p → ℝ => (Pi.single j (1 : ℝ) : Fin p → ℝ)) := contDiff_const
    have hpair : ContDiff ℝ 1 (fun w : Fin p → ℝ => (w, (Pi.single j (1 : ℝ) : Fin p → ℝ))) :=
      contDiff_id.prodMk hconst
    have hcomp : ContDiff ℝ 1 ((fun q : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ kappa q.1) q.2) ∘
        (fun w : Fin p → ℝ => (w, (Pi.single j (1 : ℝ) : Fin p → ℝ)))) := hfd.comp hpair
    exact hcomp
  have hsum_gen : ∀ (g : Fin n → ℝ),
      (∑ i' : Fin n, (if i' = i then (0 : ℝ) else g i')) = (∑ i' : Fin n, g i') - g i := by
    intro g
    have hterm : ∀ i' : Fin n, (if i' = i then (0 : ℝ) else g i') = g i' - (if i' = i then g i' else 0) := by
      intro i'
      by_cases h : i' = i
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    have h2 : (∑ i' : Fin n, (if i' = i then g i' else 0)) = g i := by
      simp
    calc (∑ i' : Fin n, (if i' = i then (0 : ℝ) else g i'))
        = ∑ i' : Fin n, (g i' - (if i' = i then g i' else 0)) := Finset.sum_congr rfl (fun i' _ => hterm i')
      _ = (∑ i' : Fin n, g i') - (∑ i' : Fin n, (if i' = i then g i' else 0)) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i' : Fin n, g i') - g i := by rw [h2]
  have hZr_pt : ∀ x : Ω × Ω, Zr x = fun r : Fin p =>
      (∑ i' : Fin n, (if i' = i then (0 : ℝ) else Zstar t x i' r)) + (∑ i' : Fin m, Zstarstar t x i' r) := by
    intro x
    funext r
    show Z t x r - Zstar t x i r = _
    rw [show Z t x r = (∑ i' : Fin n, Zstar t x i' r) + (∑ i' : Fin m, Zstarstar t x i' r) from rfl,
      hsum_gen (fun i' => Zstar t x i' r)]
    ring
  have hmX : ∀ (i' : Fin n) (r : Fin p), Measurable (fun x : Ω × Ω => X i' x.1 r) :=
    fun i' r => (measurable_pi_apply r).comp ((hXm i').comp measurable_fst)
  have hmF1 : ∀ (i' : Fin n) (r : Fin p), Measurable (fun x : Ω × Ω => F i' x.1 r) :=
    fun i' r => (measurable_pi_apply r).comp ((hFm i').comp measurable_fst)
  have hmF2 : ∀ (i' : Fin n) (r : Fin p), Measurable (fun x : Ω × Ω => F i' x.2 r) :=
    fun i' r => (measurable_pi_apply r).comp ((hFm i').comp measurable_snd)
  have hmY : ∀ (i' : Fin m) (r : Fin p), Measurable (fun x : Ω × Ω => Y i' x.1 r) :=
    fun i' r => (measurable_pi_apply r).comp ((hYm i').comp measurable_fst)
  have hmG1 : ∀ (i' : Fin m) (r : Fin p), Measurable (fun x : Ω × Ω => G i' x.1 r) :=
    fun i' r => (measurable_pi_apply r).comp ((hGm i').comp measurable_fst)
  have hmG2 : ∀ (i' : Fin m) (r : Fin p), Measurable (fun x : Ω × Ω => G i' x.2 r) :=
    fun i' r => (measurable_pi_apply r).comp ((hGm i').comp measurable_snd)
  have hmZs2 : ∀ (i' : Fin n) (r : Fin p), Measurable (fun x : Ω × Ω => Zstar t x i' r) := by
    intro i' r
    have hA : Measurable (fun x : Ω × Ω => X i' x.1 r - muX r) := (hmX i' r).sub measurable_const
    have hB : Measurable (fun x : Ω × Ω => F i' x.1 r - muX r) := (hmF1 i' r).sub measurable_const
    have hC : Measurable (fun x : Ω × Ω => F i' x.2 r - muX r) := (hmF2 i' r).sub measurable_const
    have e1 : Measurable (fun x : Ω × Ω =>
        Real.sqrt v * (X i' x.1 r - muX r) + Real.sqrt (1 - v) * (F i' x.1 r - muX r)) :=
      (hA.const_mul _).add (hB.const_mul _)
    have e2 : Measurable (fun x : Ω × Ω =>
        Real.sqrt t * (Real.sqrt v * (X i' x.1 r - muX r) + Real.sqrt (1 - v) * (F i' x.1 r - muX r)) +
          Real.sqrt (1 - t) * (F i' x.2 r - muX r)) :=
      (e1.const_mul _).add (hC.const_mul _)
    have e3 : Measurable (fun x : Ω × Ω =>
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X i' x.1 r - muX r) + Real.sqrt (1 - v) * (F i' x.1 r - muX r)) +
            Real.sqrt (1 - t) * (F i' x.2 r - muX r))) := e2.const_mul _
    exact e3
  have hmZss2 : ∀ (i' : Fin m) (r : Fin p), Measurable (fun x : Ω × Ω => Zstarstar t x i' r) := by
    intro i' r
    have hA : Measurable (fun x : Ω × Ω => Y i' x.1 r - muY r) := (hmY i' r).sub measurable_const
    have hB : Measurable (fun x : Ω × Ω => G i' x.1 r - muY r) := (hmG1 i' r).sub measurable_const
    have hC : Measurable (fun x : Ω × Ω => G i' x.2 r - muY r) := (hmG2 i' r).sub measurable_const
    have e1 : Measurable (fun x : Ω × Ω =>
        Real.sqrt v * (Y i' x.1 r - muY r) + Real.sqrt (1 - v) * (G i' x.1 r - muY r)) :=
      (hA.const_mul _).add (hB.const_mul _)
    have e2 : Measurable (fun x : Ω × Ω =>
        Real.sqrt t * (Real.sqrt v * (Y i' x.1 r - muY r) + Real.sqrt (1 - v) * (G i' x.1 r - muY r)) +
          Real.sqrt (1 - t) * (G i' x.2 r - muY r)) :=
      (e1.const_mul _).add (hC.const_mul _)
    have e3 : Measurable (fun x : Ω × Ω =>
        (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y i' x.1 r - muY r) + Real.sqrt (1 - v) * (G i' x.1 r - muY r)) +
            Real.sqrt (1 - t) * (G i' x.2 r - muY r))) :=
      e2.const_mul ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
    exact e3
  have hZr_meas : Measurable Zr := by
    rw [measurable_pi_iff]
    intro r
    have hZc : Measurable (fun x : Ω × Ω => Z t x r) := by
      have h1 : Measurable (fun x : Ω × Ω => ∑ i' : Fin n, Zstar t x i' r) :=
        Finset.measurable_sum Finset.univ (fun i' _ => hmZs2 i' r)
      have h2 : Measurable (fun x : Ω × Ω => ∑ i' : Fin m, Zstarstar t x i' r) :=
        Finset.measurable_sum Finset.univ (fun i' _ => hmZss2 i' r)
      exact h1.add h2
    exact hZc.sub (hmZs2 i r)
  have hPsi_meas : Measurable (fun x : Ω × Ω => kap2 (Zr x)) := hbd_cont.measurable.comp hZr_meas
  have hhbb : (0 : ℝ) ≤ Cbd * beta ^ 2 := by positivity
  have hPsi_int : Integrable (fun x : Ω × Ω => kap2 (Zr x)) (P.prod P) := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω × Ω => Cbd * beta ^ 2) (integrable_const _) hPsi_meas.aestronglyMeasurable ?_
    filter_upwards with x
    exact hbd_bound (Zr x)
  have hbk : (fun x : Ω × Ω => Zstar t x i k * Zdotstar t x i j) = fun x : Ω × Ω => HD (bk x) := by
    funext x
    rfl
  have hPsi_eq : (fun x : Ω × Ω => kap2 (Zr x)) = fun x : Ω × Ω => kap2 (fun r : Fin p =>
      (∑ i' : Fin n, (if i' = i then (0 : ℝ) else Zstar t x i' r)) + (∑ i' : Fin m, Zstarstar t x i' r)) := by
    funext x
    rw [hZr_pt x]
  have hIndep_raw := statopia_math_node_3377209132_cbbc544b Ω P n m p delta muX muY X Y F G hXm hYm hFm hGm hindep kap hkapC1 v t i k
  have hHD_meas : Measurable HD := by
    have p1k : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => s.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    have p21k : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => s.2.1 k) :=
      (measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)
    have p22k : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => s.2.2 k) :=
      (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
    have p1j : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => s.1 j) :=
      (measurable_pi_apply j).comp measurable_fst
    have p21j : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => s.2.1 j) :=
      (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
    have p22j : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) => s.2.2 j) :=
      (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
    have e1 : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) =>
        Real.sqrt v * (s.1 k - muX k) + Real.sqrt (1 - v) * (s.2.1 k - muX k)) :=
      ((p1k.sub measurable_const).const_mul _).add ((p21k.sub measurable_const).const_mul _)
    have e2 : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) =>
        Real.sqrt t * (Real.sqrt v * (s.1 k - muX k) + Real.sqrt (1 - v) * (s.2.1 k - muX k)) +
          Real.sqrt (1 - t) * (s.2.2 k - muX k)) :=
      (e1.const_mul _).add ((p22k.sub measurable_const).const_mul _)
    have e3 : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) =>
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (s.1 k - muX k) + Real.sqrt (1 - v) * (s.2.1 k - muX k)) +
            Real.sqrt (1 - t) * (s.2.2 k - muX k))) := e2.const_mul _
    have f1 : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) =>
        Real.sqrt v * (s.1 j - muX j) + Real.sqrt (1 - v) * (s.2.1 j - muX j)) :=
      ((p1j.sub measurable_const).const_mul _).add ((p21j.sub measurable_const).const_mul _)
    have f2 : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) =>
        (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (s.1 j - muX j) + Real.sqrt (1 - v) * (s.2.1 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (s.2.2 j - muX j)) :=
      (f1.const_mul _).sub ((p22j.sub measurable_const).const_mul _)
    have f3 : Measurable (fun s : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) =>
        (Real.sqrt (n : ℝ))⁻¹ *
          ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (s.1 j - muX j) + Real.sqrt (1 - v) * (s.2.1 j - muX j)) -
            (2 * Real.sqrt (1 - t))⁻¹ * (s.2.2 j - muX j))) := f2.const_mul _
    exact e3.mul f3
  have hIndep : IndepFun (fun x : Ω × Ω => kap2 (Zr x))
      (fun x : Ω × Ω => Zstar t x i k * Zdotstar t x i j) (P.prod P) := by
    rw [hbk, hPsi_eq]
    exact hIndep_raw.comp measurable_id hHD_meas
  have hsecond := statopia_math_node_4050339779_734b360b Ω P n m p delta muX muY X Y F G hn hm hp hXm hYm hFm hGm hindep hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov v hv0 hv1 t ht0 ht1 i j k
  have hsecond_int : Integrable (fun x : Ω × Ω => Zstar t x i k * Zdotstar t x i j) (P.prod P) := hsecond.1
  have hsecond_zero : ∫ x : Ω × Ω, Zstar t x i k * Zdotstar t x i j ∂(P.prod P) = 0 := hsecond.2
  have hfact : (∫ x : Ω × Ω, kap2 (Zr x) * (Zstar t x i k * Zdotstar t x i j) ∂(P.prod P))
      = (∫ x : Ω × Ω, kap2 (Zr x) ∂(P.prod P)) *
        (∫ x : Ω × Ω, Zstar t x i k * Zdotstar t x i j ∂(P.prod P)) :=
    ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral hIndep hPsi_meas.aestronglyMeasurable hsecond_int.aestronglyMeasurable
  rw [hfact, hsecond_zero, mul_zero]
  /- @proof-region region.target-node.session.14dfefdcd39cad1b end -/

end

end Statlib.Imported

