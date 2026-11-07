import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_792479139_d2da39bf_b95169e5

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
theorem statopia_math_node_1107436538_1f73fb85 : ∀ (b : ℝ) (hb : 0 < b),
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
        (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
        (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
        (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
        (hX : ∀ i : Fin n, Measurable (X i))
        (hY : ∀ i : Fin m, Measurable (Y i))
        (hF : ∀ i : Fin n, Measurable (F i))
        (hG : ∀ i : Fin m, Measurable (G i))
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
        (hbvar : ∀ (j : Fin p),
          b ≤ ∫ (ω : Ω),
            combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j ^ 2 ∂P)
        (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
        (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (y : Fin p → ℝ),
        let phi : ℝ := min phi1 phi2
        let beta : ℝ := phi * Real.log (p : ℝ)
        let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
          (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
              Real.sqrt (1 - t) * (F i x.2 j - muX j))
        let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
              Real.sqrt (1 - t) * (G i x.2 j - muY j))
        let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
          (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
        let kappa0 : ℝ := phi⁻¹ + 2 * beta⁻¹
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i : Fin n,
          (∫ x : Ω × Ω,
            Set.indicator
              {x : Ω × Ω |
                beta * maxAbs (fun k : Fin p => Zstar t x i k) ≤ 1 ∧
                -(kappa0 + beta⁻¹) <
                  (⨆ j : Fin p, ((fun k : Fin p => Z t x k - Zstar t x i k) j - y j)) ∧
                (⨆ j : Fin p, ((fun k : Fin p => Z t x k - Zstar t x i k) j - y j)) ≤
                  kappa0 + beta⁻¹}
              (fun _ => (1 : ℝ)) x ∂(P.prod P)) ≤
            2 * rho P n m p (delta n m) muX muY X Y F G +
              Cb * kappa0 * (Real.sqrt (Real.log (p : ℝ)) + 1) := by
  /- @proof-region region.target-node.session.964b75702cbfc882 begin -/
  intro b hb
  obtain ⟨Cb, hCbpos, hCb⟩ := statopia_math_node_792479139_d2da39bf b hb
  refine ⟨Cb, hCbpos, ?_⟩
  intro Ω hΩ P hP n m p delta muX muY X Y F G hn hm hp hlogp hX hY hF hG hindep
    hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov hbvar phi1 phi2 hphi1 hphi2 v hv0 hv1 y
  dsimp only
  intro t ht i
  have hshell := hCb Ω P n m p delta muX muY X Y F G hn hm hp hlogp hX hY hF hG hindep
    hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov hbvar phi1 phi2 hphi1 hphi2 v hv0 hv1 y t ht
  refine le_trans ?_ hshell
  let ph : ℝ := min phi1 phi2
  let bt : ℝ := ph * Real.log (p : ℝ)
  let kW : ℝ := ph⁻¹ + 2 * bt⁻¹ + bt⁻¹
  let k3 : ℝ := ph⁻¹ + 2 * bt⁻¹ + 2 * bt⁻¹
  let Zd : Ω × Ω → Fin p → ℝ := fun x j =>
    (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - t) * (F i x.2 j - muX j)))
      + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i x.2 j - muY j)))
  let Zs : Ω × Ω → Fin p → ℝ := fun x j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
        Real.sqrt (1 - t) * (F i x.2 j - muX j))
  let mA : Set (Ω × Ω) :=
    {x | bt * maxAbs (fun k : Fin p => Zs x k) ≤ 1 ∧
      -kW < (⨆ j : Fin p, (Zd x j - Zs x j - y j)) ∧
      (⨆ j : Fin p, (Zd x j - Zs x j - y j)) ≤ kW}
  let mB : Set (Ω × Ω) :=
    {x | -k3 < (⨆ j : Fin p, (Zd x j - y j)) ∧ (⨆ j : Fin p, (Zd x j - y j)) ≤ k3}
  show ∫ x : Ω × Ω, mA.indicator (fun _ => (1 : ℝ)) x ∂(P.prod P) ≤
    ∫ x : Ω × Ω, mB.indicator (fun _ => (1 : ℝ)) x ∂(P.prod P)
  have hXfst : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => X i x.1 j) :=
    fun i j => ((measurable_pi_iff.mp (hX i)) j).comp measurable_fst
  have hFfst : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => F i x.1 j) :=
    fun i j => ((measurable_pi_iff.mp (hF i)) j).comp measurable_fst
  have hFsnd : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => F i x.2 j) :=
    fun i j => ((measurable_pi_iff.mp (hF i)) j).comp measurable_snd
  have hYfst : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => Y i x.1 j) :=
    fun i j => ((measurable_pi_iff.mp (hY i)) j).comp measurable_fst
  have hGfst : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => G i x.1 j) :=
    fun i j => ((measurable_pi_iff.mp (hG i)) j).comp measurable_fst
  have hGsnd : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => G i x.2 j) :=
    fun i j => ((measurable_pi_iff.mp (hG i)) j).comp measurable_snd
  have hZd : Measurable Zd := by
    rw [measurable_pi_iff]
    intro j
    have h1 : Measurable (fun x : Ω × Ω => ∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - t) * (F i x.2 j - muX j))) := by
      refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
      have e1 : Measurable (fun x : Ω × Ω => Real.sqrt v * (X i x.1 j - muX j)) :=
        measurable_const.mul ((hXfst i j).sub measurable_const)
      have e2 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - v) * (F i x.1 j - muX j)) :=
        measurable_const.mul ((hFfst i j).sub measurable_const)
      have e3 : Measurable (fun x : Ω × Ω =>
          Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
            Real.sqrt (1 - v) * (F i x.1 j - muX j))) :=
        measurable_const.mul (e1.add e2)
      have e4 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - t) * (F i x.2 j - muX j)) :=
        measurable_const.mul ((hFsnd i j).sub measurable_const)
      exact measurable_const.mul (e3.add e4)
    have h2 : Measurable (fun x : Ω × Ω => ∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i x.2 j - muY j))) := by
      refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
      have e1 : Measurable (fun x : Ω × Ω => Real.sqrt v * (Y i x.1 j - muY j)) :=
        measurable_const.mul ((hYfst i j).sub measurable_const)
      have e2 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - v) * (G i x.1 j - muY j)) :=
        measurable_const.mul ((hGfst i j).sub measurable_const)
      have e3 : Measurable (fun x : Ω × Ω =>
          Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j))) :=
        measurable_const.mul (e1.add e2)
      have e4 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - t) * (G i x.2 j - muY j)) :=
        measurable_const.mul ((hGsnd i j).sub measurable_const)
      exact measurable_const.mul (e3.add e4)
    exact h1.add h2
  have hZs : Measurable Zs := by
    rw [measurable_pi_iff]
    intro j
    have e1 : Measurable (fun x : Ω × Ω => Real.sqrt v * (X i x.1 j - muX j)) :=
      measurable_const.mul ((hXfst i j).sub measurable_const)
    have e2 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - v) * (F i x.1 j - muX j)) :=
      measurable_const.mul ((hFfst i j).sub measurable_const)
    have e3 : Measurable (fun x : Ω × Ω =>
        Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
          Real.sqrt (1 - v) * (F i x.1 j - muX j))) :=
      measurable_const.mul (e1.add e2)
    have e4 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - t) * (F i x.2 j - muX j)) :=
      measurable_const.mul ((hFsnd i j).sub measurable_const)
    exact measurable_const.mul (e3.add e4)
  have hZdc : ∀ k : Fin p, Measurable (fun x : Ω × Ω => Zd x k) :=
    fun k => measurable_pi_iff.mp hZd k
  have hSd : Measurable (fun x : Ω × Ω => ⨆ j : Fin p, (Zd x j - y j)) :=
    Measurable.iSup (fun j => (hZdc j).sub measurable_const)
  have hmB : MeasurableSet mB := (hSd measurableSet_Ioi).inter (hSd measurableSet_Iic)
  have hIntB : Integrable (mB.indicator (fun _ => (1 : ℝ))) (P.prod P) :=
    (MeasureTheory.integrable_const (1 : ℝ)).indicator hmB
  have hcont : mA ⊆ mB := by
    haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    intro x hx
    obtain ⟨hxM, hxW1, hxW2⟩ := hx
    have hph1 : (1 : ℝ) ≤ ph := le_min hphi1 hphi2
    have hph : (0 : ℝ) < ph := lt_of_lt_of_le zero_lt_one hph1
    have hbt : (0 : ℝ) < bt := mul_pos hph hlogp
    have hMle : maxAbs (fun k : Fin p => Zs x k) ≤ bt⁻¹ := by
      have h := mul_le_mul_of_nonneg_left hxM (le_of_lt (inv_pos.mpr hbt))
      have h2 : bt⁻¹ * (bt * maxAbs (fun k : Fin p => Zs x k)) =
          maxAbs (fun k : Fin p => Zs x k) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hbt), one_mul]
      have h3 : bt⁻¹ * 1 = bt⁻¹ := mul_one _
      rwa [h2, h3] at h
    have hZj : ∀ j : Fin p, |Zs x j| ≤ bt⁻¹ := by
      intro j
      have hbd : BddAbove (Set.range fun k : Fin p => |Zs x k|) := (Set.toFinite _).bddAbove
      have h1 : |Zs x j| ≤ maxAbs (fun k : Fin p => Zs x k) := le_ciSup hbd j
      linarith
    have hbdZ : BddAbove (Set.range fun j : Fin p => Zd x j - y j) := (Set.toFinite _).bddAbove
    have hbdW : BddAbove (Set.range fun j : Fin p => Zd x j - Zs x j - y j) :=
      (Set.toFinite _).bddAbove
    have hZW : (⨆ j : Fin p, (Zd x j - y j)) ≤
        (⨆ j : Fin p, (Zd x j - Zs x j - y j)) + bt⁻¹ := by
      refine (ciSup_le_iff hbdZ).mpr (fun j => ?_)
      have h1 : Zd x j - Zs x j - y j ≤ (⨆ j : Fin p, (Zd x j - Zs x j - y j)) :=
        le_ciSup hbdW j
      have h2 : Zs x j ≤ bt⁻¹ := (abs_le.mp (hZj j)).2
      linarith
    have hWZ : (⨆ j : Fin p, (Zd x j - Zs x j - y j)) ≤
        (⨆ j : Fin p, (Zd x j - y j)) + bt⁻¹ := by
      refine (ciSup_le_iff hbdW).mpr (fun j => ?_)
      have h1 : Zd x j - y j ≤ (⨆ j : Fin p, (Zd x j - y j)) := le_ciSup hbdZ j
      have h2 : -bt⁻¹ ≤ Zs x j := (abs_le.mp (hZj j)).1
      linarith
    have hk3 : kW + bt⁻¹ = k3 := by
      show ph⁻¹ + 2 * bt⁻¹ + bt⁻¹ + bt⁻¹ = ph⁻¹ + 2 * bt⁻¹ + 2 * bt⁻¹
      ring
    have hk3' : -kW - bt⁻¹ = -k3 := by
      show -(ph⁻¹ + 2 * bt⁻¹ + bt⁻¹) - bt⁻¹ = -(ph⁻¹ + 2 * bt⁻¹ + 2 * bt⁻¹)
      ring
    constructor
    · linarith
    · linarith
  refine MeasureTheory.integral_mono_of_nonneg ?_ hIntB ?_
  · filter_upwards with x
    by_cases hx : x ∈ mA
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  · filter_upwards with x
    by_cases hx : x ∈ mA
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hcont hx)]
    · rw [Set.indicator_of_notMem hx]
      by_cases h : x ∈ mB
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
  /- @proof-region region.target-node.session.964b75702cbfc882 end -/

end

end Statlib.Imported

