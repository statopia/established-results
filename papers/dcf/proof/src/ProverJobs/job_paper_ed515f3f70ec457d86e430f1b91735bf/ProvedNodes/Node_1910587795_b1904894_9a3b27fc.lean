import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1967109576_c7239acb_4f2497e8
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604

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
theorem statopia_math_node_1910587795_b1904894 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hlogp : 0 < Real.log (p : ℝ))
    (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hX : ∀ i : Fin n, Measurable (X i)) (hY : ∀ i : Fin m, Measurable (Y i))
    (hF : ∀ i : Fin n, Measurable (F i)) (hG : ∀ i : Fin m, Measurable (G i))
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (y : Fin p → ℝ)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P),
    (let phi : ℝ := min phi1 phi2
     let beta : ℝ := phi * Real.log (p : ℝ)
     let Zstar : Fin n → Fin p → ℝ → (Ω × Ω) → ℝ := fun i j t x =>
       (Real.sqrt (n : ℝ))⁻¹ *
         (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
            Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - t) * (F i x.2 j - muX j))
     let Zstarstar : Fin m → Fin p → ℝ → (Ω × Ω) → ℝ := fun i' j t x =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         (Real.sqrt t * (Real.sqrt v * (Y i' x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i' x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i' x.2 j - muY j))
     let Z : ℝ → (Ω × Ω) → (Fin p → ℝ) := fun t x j =>
       (∑ i : Fin n, Zstar i j t x) + (∑ i' : Fin m, Zstarstar i' j t x)
     let Zdot : Fin m → Fin p → ℝ → (Ω × Ω) → ℝ := fun i' j t x =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i' x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i' x.1 j - muY j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i' x.2 j - muY j))
     let kappa : (Fin p → ℝ) → ℝ := fun w =>
       phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
     Integrable (fun x : Ω × Ω =>
       ∫ t in (0 : ℝ)..1,
         ∑ j : Fin p, ∑ i' : Fin m,
           (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot i' j t x)
       (P.prod P)) := by
  /- @proof-region region.target-node.session.31536d0f22d62e88 begin -/
  intro Ω instΩ P instP n m p hn hm hp hlogp delta muX muY X Y F G hX hY hF hG phi1 phi2 hphi1 hphi2 v hv0 hv1 y phi0 hphi0_cont hphi0_left hphi0_right hphi0_range hY3 hG3
  dsimp only
  obtain ⟨Cκ, hCκ0, hCκ⟩ :=
    statopia_math_node_1967109576_c7239acb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  have hp2 : 2 ≤ p := by
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have h1 : (1:ℝ) < (p:ℝ) := by
      have h := Real.exp_lt_exp.2 hlogp
      rwa [Real.exp_zero, Real.exp_log hp0] at h
    have h2 : (1:ℕ) < p := by exact_mod_cast h1
    omega
  let phi : ℝ := min phi1 phi2
  let beta : ℝ := phi * Real.log (p : ℝ)
  let Zstar : Fin n → Fin p → ℝ → (Ω × Ω) → ℝ := fun i j t x =>
    (Real.sqrt (n : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
         Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
       Real.sqrt (1 - t) * (F i x.2 j - muX j))
  let Zstarstar : Fin m → Fin p → ℝ → (Ω × Ω) → ℝ := fun i' j t x =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t * (Real.sqrt v * (Y i' x.1 j - muY j) +
         Real.sqrt (1 - v) * (G i' x.1 j - muY j)) +
       Real.sqrt (1 - t) * (G i' x.2 j - muY j))
  let Z : ℝ → (Ω × Ω) → (Fin p → ℝ) := fun t x j =>
    (∑ i : Fin n, Zstar i j t x) + (∑ i' : Fin m, Zstarstar i' j t x)
  let Zdot : Fin m → Fin p → ℝ → (Ω × Ω) → ℝ := fun i' j t x =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i' x.1 j - muY j) +
         Real.sqrt (1 - v) * (G i' x.1 j - muY j)) -
       (2 * Real.sqrt (1 - t))⁻¹ * (G i' x.2 j - muY j))
  let kappa : (Fin p → ℝ) → ℝ := fun w =>
    phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
  have hphi1' : 1 ≤ phi := le_min hphi1 hphi2
  have hphile2 : phi ≤ phi2 := min_le_right _ _
  have hgrad : ∀ (w : Fin p → ℝ) (j : Fin p),
      |(fderiv ℝ kappa w) (Pi.single j (1:ℝ))| ≤ Cκ * phi2 := by
    intro w j
    have h1 := hCκ p hp2 phi hphi1' y w j
    exact le_trans h1 (mul_le_mul_of_nonneg_left hphile2 hCκ0)
  let D : Ω × Ω → ℝ := fun x =>
    ∑ j : Fin p, ∑ i' : Fin m,
      (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|)
  let Kc : ℝ := Cκ * phi2 * |delta n m| * (Real.sqrt (m : ℝ))⁻¹ * 2
  have hKc0 : 0 ≤ Kc := by
    have hsq : (0:ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ := by positivity
    have hθ : (0:ℝ) ≤ phi2 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCκ0 hθ) (abs_nonneg _)) hsq) (by norm_num)
  have hDint : Integrable D (P.prod P) := by
    have aux : ∀ (f : Ω → ℝ), Measurable f → Integrable (fun ω => |f ω| ^ 3) P →
        Integrable (fun ω => |f ω|) P := by
      intro f hfm hf
      have h1 : Integrable (fun ω => (1:ℝ) + |f ω| ^ 3) P := by
        simpa using (integrable_const (1:ℝ) : Integrable (fun _ : Ω => (1:ℝ)) P).add hf
      have hmeas1 : AEStronglyMeasurable (fun ω => |f ω|) P :=
        (continuous_abs.measurable.comp hfm).aestronglyMeasurable
      refine h1.mono hmeas1 ?_
      filter_upwards with ω
      have hnn : (0:ℝ) ≤ |f ω| := abs_nonneg _
      have hle1 : |f ω| ≤ 1 + |f ω| ^ 3 := by
        by_cases ha : (|f ω| ≤ 1)
        · have h0 : (0:ℝ) ≤ |f ω| ^ 3 := by positivity
          linarith
        · push_neg at ha
          have h2 : |f ω| ≤ |f ω| * |f ω| := by
            have hh := mul_le_mul_of_nonneg_left (le_of_lt ha) hnn
            simpa using hh
          have h3 : |f ω| * |f ω| ≤ |f ω| ^ 3 := by
            have h4 : |f ω| * |f ω| ≤ (|f ω| * |f ω|) * |f ω| := by
              have hh := mul_le_mul_of_nonneg_left (le_of_lt ha)
                (by positivity : (0:ℝ) ≤ |f ω| * |f ω|)
              simpa using hh
            calc |f ω| * |f ω| ≤ (|f ω| * |f ω|) * |f ω| := h4
              _ = |f ω| ^ 3 := by ring
          linarith
      calc ‖|f ω|‖ = |f ω| := by rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        _ ≤ 1 + |f ω| ^ 3 := hle1
        _ = ‖(1:ℝ) + |f ω| ^ 3‖ := by
              rw [Real.norm_eq_abs]
              exact (abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + |f ω| ^ 3)).symm
    have hYint : ∀ (i' : Fin m) (j : Fin p), Integrable (fun ω => |Y i' ω j - muY j|) P := by
      intro i' j
      exact aux (fun ω => Y i' ω j - muY j)
        (((measurable_pi_apply j).comp (hY i')).sub measurable_const) (hY3 i' j)
    have hGint : ∀ (i' : Fin m) (j : Fin p), Integrable (fun ω => |G i' ω j - muY j|) P := by
      intro i' j
      exact aux (fun ω => G i' ω j - muY j)
        (((measurable_pi_apply j).comp (hG i')).sub measurable_const) (hG3 i' j)
    have hterm : ∀ (j : Fin p) (i' : Fin m),
        Integrable (fun x : Ω × Ω =>
          |Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|)
          (P.prod P) := by
      intro j i'
      have h1 : Integrable (fun x : Ω × Ω => |Y i' x.1 j - muY j|) (P.prod P) :=
        (hYint i' j).comp_fst P
      have h2 : Integrable (fun x : Ω × Ω => |G i' x.1 j - muY j|) (P.prod P) :=
        (hGint i' j).comp_fst P
      have h3 : Integrable (fun x : Ω × Ω => |G i' x.2 j - muY j|) (P.prod P) :=
        (hGint i' j).comp_snd P
      exact (h1.add h2).add h3
    have hinner : ∀ j : Fin p, Integrable (fun x : Ω × Ω => ∑ i' : Fin m,
        (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|))
        (P.prod P) := by
      intro j
      exact MeasureTheory.integrable_finset_sum Finset.univ (fun i' _ => hterm j i')
    exact MeasureTheory.integrable_finset_sum Finset.univ (fun j _ => hinner j)
  have hmeas : AEStronglyMeasurable
      (fun x : Ω × Ω => ∫ t in (0:ℝ)..1, ∑ j : Fin p, ∑ i' : Fin m,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x) (P.prod P) := by
    have hκ3 : ContDiff ℝ 3 kappa :=
      (statopia_math_node_2194576110_d2ad0cef p hp2 phi hphi1' phi0 hphi0_cont hphi0_left
        hphi0_right hphi0_range y).1
    have hΦc : Continuous (fun q : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ kappa q.1) q.2) :=
      hκ3.continuous_fderiv_apply (by norm_num)
    have mA : ∀ (i : Fin n) (j : Fin p), Measurable (fun r : (Ω × Ω) × ℝ => X i r.1.1 j) := by
      intro i j
      exact ((measurable_pi_apply j).comp (hX i)).comp (measurable_fst.comp measurable_fst)
    have mB : ∀ (i : Fin n) (j : Fin p), Measurable (fun r : (Ω × Ω) × ℝ => F i r.1.1 j) := by
      intro i j
      exact ((measurable_pi_apply j).comp (hF i)).comp (measurable_fst.comp measurable_fst)
    have mC : ∀ (i : Fin n) (j : Fin p), Measurable (fun r : (Ω × Ω) × ℝ => F i r.1.2 j) := by
      intro i j
      exact ((measurable_pi_apply j).comp (hF i)).comp (measurable_snd.comp measurable_fst)
    have mY1 : ∀ (i : Fin m) (j : Fin p), Measurable (fun r : (Ω × Ω) × ℝ => Y i r.1.1 j) := by
      intro i j
      exact ((measurable_pi_apply j).comp (hY i)).comp (measurable_fst.comp measurable_fst)
    have mG1 : ∀ (i : Fin m) (j : Fin p), Measurable (fun r : (Ω × Ω) × ℝ => G i r.1.1 j) := by
      intro i j
      exact ((measurable_pi_apply j).comp (hG i)).comp (measurable_fst.comp measurable_fst)
    have mG2 : ∀ (i : Fin m) (j : Fin p), Measurable (fun r : (Ω × Ω) × ℝ => G i r.1.2 j) := by
      intro i j
      exact ((measurable_pi_apply j).comp (hG i)).comp (measurable_snd.comp measurable_fst)
    have mst : Measurable (fun r : (Ω × Ω) × ℝ => Real.sqrt r.2) :=
      Real.continuous_sqrt.measurable.comp measurable_snd
    have ms1t : Measurable (fun r : (Ω × Ω) × ℝ => Real.sqrt (1 - r.2)) :=
      Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_snd)
    have hZs : ∀ (i : Fin n) (j : Fin p),
        Measurable (fun r : (Ω × Ω) × ℝ => Zstar i j r.2 r.1) := by
      intro i j
      have h1 : Measurable (fun r : (Ω × Ω) × ℝ => Real.sqrt v * (X i r.1.1 j - muX j)) :=
        measurable_const.mul ((mA i j).sub measurable_const)
      have h2 : Measurable (fun r : (Ω × Ω) × ℝ =>
          Real.sqrt (1 - v) * (F i r.1.1 j - muX j)) :=
        measurable_const.mul ((mB i j).sub measurable_const)
      have h3 : Measurable (fun r : (Ω × Ω) × ℝ =>
          Real.sqrt v * (X i r.1.1 j - muX j) +
            Real.sqrt (1 - v) * (F i r.1.1 j - muX j)) := h1.add h2
      have h4 : Measurable (fun r : (Ω × Ω) × ℝ => Real.sqrt r.2 *
          (Real.sqrt v * (X i r.1.1 j - muX j) +
            Real.sqrt (1 - v) * (F i r.1.1 j - muX j))) := mst.mul h3
      have h5 : Measurable (fun r : (Ω × Ω) × ℝ =>
          Real.sqrt (1 - r.2) * (F i r.1.2 j - muX j)) :=
        ms1t.mul ((mC i j).sub measurable_const)
      exact measurable_const.mul (h4.add h5)
    have hZss : ∀ (i : Fin m) (j : Fin p),
        Measurable (fun r : (Ω × Ω) × ℝ => Zstarstar i j r.2 r.1) := by
      intro i j
      have h1 : Measurable (fun r : (Ω × Ω) × ℝ => Real.sqrt v * (Y i r.1.1 j - muY j)) :=
        measurable_const.mul ((mY1 i j).sub measurable_const)
      have h2 : Measurable (fun r : (Ω × Ω) × ℝ =>
          Real.sqrt (1 - v) * (G i r.1.1 j - muY j)) :=
        measurable_const.mul ((mG1 i j).sub measurable_const)
      have h3 : Measurable (fun r : (Ω × Ω) × ℝ =>
          Real.sqrt v * (Y i r.1.1 j - muY j) +
            Real.sqrt (1 - v) * (G i r.1.1 j - muY j)) := h1.add h2
      have h4 : Measurable (fun r : (Ω × Ω) × ℝ => Real.sqrt r.2 *
          (Real.sqrt v * (Y i r.1.1 j - muY j) +
            Real.sqrt (1 - v) * (G i r.1.1 j - muY j))) := mst.mul h3
      have h5 : Measurable (fun r : (Ω × Ω) × ℝ =>
          Real.sqrt (1 - r.2) * (G i r.1.2 j - muY j)) :=
        ms1t.mul ((mG2 i j).sub measurable_const)
      exact measurable_const.mul (h4.add h5)
    have mZcoord : ∀ j : Fin p, Measurable (fun r : (Ω × Ω) × ℝ => Z r.2 r.1 j) := by
      intro j
      have h1 : Measurable (fun r : (Ω × Ω) × ℝ => ∑ i : Fin n, Zstar i j r.2 r.1) :=
        Finset.measurable_sum Finset.univ (fun i _ => hZs i j)
      have h2 : Measurable (fun r : (Ω × Ω) × ℝ => ∑ i' : Fin m, Zstarstar i' j r.2 r.1) :=
        Finset.measurable_sum Finset.univ (fun i' _ => hZss i' j)
      exact h1.add h2
    have mZ : Measurable (fun r : (Ω × Ω) × ℝ => Z r.2 r.1) :=
      measurable_pi_iff.mpr mZcoord
    have mfderiv : ∀ j : Fin p, Measurable (fun r : (Ω × Ω) × ℝ =>
        (fderiv ℝ kappa (Z r.2 r.1)) (Pi.single j (1:ℝ))) := by
      intro j
      have hcw : Continuous (fun w : Fin p → ℝ => (w, (Pi.single j (1:ℝ) : Fin p → ℝ))) :=
        Continuous.prodMk continuous_id continuous_const
      have hg : Continuous (fun w : Fin p → ℝ => (fderiv ℝ kappa w) (Pi.single j (1:ℝ))) :=
        hΦc.comp hcw
      exact hg.measurable.comp mZ
    have mZdot : ∀ (i' : Fin m) (j : Fin p), Measurable (fun r : (Ω × Ω) × ℝ =>
        Zdot i' j r.2 r.1) := by
      intro i' j
      have h1 : Measurable (fun r : (Ω × Ω) × ℝ => (2 * Real.sqrt r.2)⁻¹ *
          (Real.sqrt v * (Y i' r.1.1 j - muY j) +
            Real.sqrt (1 - v) * (G i' r.1.1 j - muY j))) :=
        ((measurable_const.mul mst).inv).mul
          ((measurable_const.mul ((mY1 i' j).sub measurable_const)).add
            (measurable_const.mul ((mG1 i' j).sub measurable_const)))
      have h2 : Measurable (fun r : (Ω × Ω) × ℝ => (2 * Real.sqrt (1 - r.2))⁻¹ *
          (G i' r.1.2 j - muY j)) :=
        ((measurable_const.mul ms1t).inv).mul ((mG2 i' j).sub measurable_const)
      exact measurable_const.mul (h1.sub h2)
    have hjoint : Measurable (fun r : (Ω × Ω) × ℝ => ∑ j : Fin p, ∑ i' : Fin m,
        (fderiv ℝ kappa (Z r.2 r.1)) (Pi.single j (1:ℝ)) * Zdot i' j r.2 r.1) := by
      have h1 : ∀ j : Fin p, Measurable (fun r : (Ω × Ω) × ℝ => ∑ i' : Fin m,
          (fderiv ℝ kappa (Z r.2 r.1)) (Pi.single j (1:ℝ)) * Zdot i' j r.2 r.1) := by
        intro j
        exact Finset.measurable_sum Finset.univ (fun i' _ => (mfderiv j).mul (mZdot i' j))
      exact Finset.measurable_sum Finset.univ (fun j _ => h1 j)
    have hres : AEStronglyMeasurable
        (fun x : Ω × Ω => ∫ t, (∑ j : Fin p, ∑ i' : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x)
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) (P.prod P) :=
      hjoint.aestronglyMeasurable.integral_prod_right'
    have hiff : ∀ x : Ω × Ω, (∫ t in (0:ℝ)..1, ∑ j : Fin p, ∑ i' : Fin m,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x)
        = ∫ t, (∑ j : Fin p, ∑ i' : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x)
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      intro x
      exact intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)
    rw [show (fun x : Ω × Ω => ∫ t in (0:ℝ)..1, ∑ j : Fin p, ∑ i' : Fin m,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x)
        = (fun x : Ω × Ω => ∫ t, (∑ j : Fin p, ∑ i' : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x)
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) from funext hiff]
    exact hres
  have hbound : ∀ x : Ω × Ω,
      ‖∫ t in (0:ℝ)..1, ∑ j : Fin p, ∑ i' : Fin m,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖ ≤ Kc * D x := by
    intro x
    have hsummand : ∀ (i' : Fin m) (j : Fin p) (t : ℝ),
        ‖(fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖ ≤
          (Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
            (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
              (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|))) := by
      intro i' j t
      let A : ℝ := Y i' x.1 j - muY j
      let B : ℝ := G i' x.1 j - muY j
      let Cc : ℝ := G i' x.2 j - muY j
      have hθ : (0:ℝ) ≤ phi2 := by linarith
      have hCφ : (0:ℝ) ≤ Cκ * phi2 := mul_nonneg hCκ0 hθ
      have hmh : (0:ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ := by positivity
      have hδ : (0:ℝ) ≤ |delta n m| := abs_nonneg _
      have hs1 : (0:ℝ) ≤ (2 * Real.sqrt t)⁻¹ := by positivity
      have hs2 : (0:ℝ) ≤ (2 * Real.sqrt (1 - t))⁻¹ := by positivity
      have hA : (0:ℝ) ≤ |A| := abs_nonneg A
      have hB : (0:ℝ) ≤ |B| := abs_nonneg B
      have hC : (0:ℝ) ≤ |Cc| := abs_nonneg Cc
      have hsv : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 hv1
      have hs1v : Real.sqrt (1 - v) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
      have hsv0 : (0:ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
      have hs1v0 : (0:ℝ) ≤ Real.sqrt (1 - v) := Real.sqrt_nonneg (1 - v)
      have hX : |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A + Real.sqrt (1 - v) * B)| ≤
          (2 * Real.sqrt t)⁻¹ * (|A| + |B|) := by
        have hstep1 : |Real.sqrt v * A + Real.sqrt (1 - v) * B| ≤
            Real.sqrt v * |A| + Real.sqrt (1 - v) * |B| := by
          calc |Real.sqrt v * A + Real.sqrt (1 - v) * B|
              ≤ |Real.sqrt v * A| + |Real.sqrt (1 - v) * B| := abs_add_le _ _
            _ = Real.sqrt v * |A| + Real.sqrt (1 - v) * |B| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hs1v0]
        have hstep2 : Real.sqrt v * |A| + Real.sqrt (1 - v) * |B| ≤ |A| + |B| := by
          have h1 := mul_le_mul_of_nonneg_right hsv hA
          have h2 := mul_le_mul_of_nonneg_right hs1v hB
          linarith
        calc |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A + Real.sqrt (1 - v) * B)|
            = (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * A + Real.sqrt (1 - v) * B| := by
                rw [abs_mul, abs_of_nonneg hs1]
          _ ≤ (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * |A| + Real.sqrt (1 - v) * |B|) :=
                mul_le_mul_of_nonneg_left hstep1 hs1
          _ ≤ (2 * Real.sqrt t)⁻¹ * (|A| + |B|) :=
                mul_le_mul_of_nonneg_left hstep2 hs1
      have hYb : |(2 * Real.sqrt (1 - t))⁻¹ * Cc| ≤ (2 * Real.sqrt (1 - t))⁻¹ * |Cc| := by
        rw [abs_mul, abs_of_nonneg hs2]
      have hZdot : ‖Zdot i' j t x‖ ≤ (Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
          (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) * (|A| + |B| + |Cc|)) := by
        rw [Real.norm_eq_abs]
        show |(Real.sqrt (m : ℝ))⁻¹ * delta n m *
            ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A + Real.sqrt (1 - v) * B) -
              (2 * Real.sqrt (1 - t))⁻¹ * Cc)| ≤
            (Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
              (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) * (|A| + |B| + |Cc|))
        rw [abs_mul, abs_mul, abs_of_nonneg hmh]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hmh hδ)
        calc |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A + Real.sqrt (1 - v) * B) -
              (2 * Real.sqrt (1 - t))⁻¹ * Cc|
            = |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A + Real.sqrt (1 - v) * B) +
                -((2 * Real.sqrt (1 - t))⁻¹ * Cc)| := by rw [sub_eq_add_neg]
          _ ≤ |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A + Real.sqrt (1 - v) * B)| +
                |(2 * Real.sqrt (1 - t))⁻¹ * Cc| := by
              have h := abs_add_le ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A + Real.sqrt (1 - v) * B))
                (-((2 * Real.sqrt (1 - t))⁻¹ * Cc))
              rwa [abs_neg] at h
          _ ≤ (2 * Real.sqrt t)⁻¹ * (|A| + |B|) + (2 * Real.sqrt (1 - t))⁻¹ * |Cc| :=
              add_le_add hX hYb
          _ ≤ ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) * (|A| + |B| + |Cc|) := by
              have h1 : (0:ℝ) ≤ (2 * Real.sqrt t)⁻¹ * |Cc| := mul_nonneg hs1 hC
              have h2 : (0:ℝ) ≤ (2 * Real.sqrt (1 - t))⁻¹ * (|A| + |B|) :=
                mul_nonneg hs2 (by linarith)
              nlinarith [h1, h2]
      calc ‖(fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖
          = ‖(fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ))‖ * ‖Zdot i' j t x‖ := norm_mul _ _
        _ ≤ (Cκ * phi2) * ‖Zdot i' j t x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [Real.norm_eq_abs]
            exact hgrad (Z t x) j
        _ ≤ (Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
            (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) * (|A| + |B| + |Cc|))) :=
            mul_le_mul_of_nonneg_left hZdot hCφ
    have hpt : ∀ t : ℝ, ‖∑ j : Fin p, ∑ i' : Fin m,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖ ≤
        ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
          (Cκ * phi2 * (Real.sqrt (m : ℝ))⁻¹ * |delta n m| * D x) := by
      intro t
      have hstep : ∑ j : Fin p, ∑ i' : Fin m,
          ‖(fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖ ≤
          ∑ j : Fin p, ∑ i' : Fin m,
            (Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
              (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
                (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|))) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i' _ => hsummand i' j t))
      have hfac : ∑ j : Fin p, ∑ i' : Fin m,
            (Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
              (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
                (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|)))
          = ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
              (Cκ * phi2 * (Real.sqrt (m : ℝ))⁻¹ * |delta n m| * D x) := by
        have hinner : ∀ j : Fin p, (∑ i' : Fin m,
              (Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
                (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
                  (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|))))
            = ((Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
                ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹))) *
              (∑ i' : Fin m,
                (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|)) := by
          intro j
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i' _ => by ring)
        calc ∑ j : Fin p, ∑ i' : Fin m,
              (Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
                (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
                  (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|)))
            = ∑ j : Fin p, ((Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
                ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹))) *
              (∑ i' : Fin m,
                (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|)) :=
              Finset.sum_congr rfl (fun j _ => hinner j)
          _ = ((Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
                ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹))) *
              (∑ j : Fin p, ∑ i' : Fin m,
                (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|)) := by
              rw [Finset.mul_sum]
          _ = ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
              (Cκ * phi2 * (Real.sqrt (m : ℝ))⁻¹ * |delta n m| * D x) := by
              have hD : D x = ∑ j : Fin p, ∑ i' : Fin m,
                  (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|) := rfl
              rw [hD]
              ring
      calc ‖∑ j : Fin p, ∑ i' : Fin m,
            (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖
          ≤ ∑ j : Fin p, ‖∑ i' : Fin m,
              (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j : Fin p, ∑ i' : Fin m,
              ‖(fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖ :=
            Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
        _ ≤ ∑ j : Fin p, ∑ i' : Fin m,
            (Cκ * phi2) * ((Real.sqrt (m : ℝ))⁻¹ * |delta n m| *
              (((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹) *
                (|Y i' x.1 j - muY j| + |G i' x.1 j - muY j| + |G i' x.2 j - muY j|))) := hstep
        _ = _ := hfac
    have hIoc : Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 := Set.uIoc_of_le (by norm_num)
    have hAint : Integrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      have hg : Integrable (fun t : ℝ => t ^ ((-(1/2) : ℝ)))
          (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
        have h : IntervalIntegrable (fun t : ℝ => t ^ ((-(1/2) : ℝ))) volume (0:ℝ) 1 :=
          intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1) (r := (-(1/2) : ℝ))
            (by norm_num)
        unfold IntervalIntegrable at h
        obtain ⟨h1, -⟩ := h
        unfold IntegrableOn at h1
        exact h1
      have hm : AEStronglyMeasurable (fun t : ℝ => (2 * Real.sqrt t)⁻¹)
          (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
        ((measurable_const.mul Real.continuous_sqrt.measurable).inv).aestronglyMeasurable
      have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ‖(2 * Real.sqrt t)⁻¹‖ ≤ ‖t ^ ((-(1/2) : ℝ))‖ := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : (0:ℝ) < t := ht.1
        have hinv : (2 * Real.sqrt t)⁻¹ = 2⁻¹ * t ^ ((-(1/2) : ℝ)) := by
          rw [Real.sqrt_eq_rpow, mul_inv, ← Real.rpow_neg (le_of_lt ht0) (1/2)]
        have hnn : (0:ℝ) ≤ t ^ ((-(1/2) : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt ht0) (1/2), ← Real.sqrt_eq_rpow]
          exact inv_nonneg.2 (Real.sqrt_nonneg t)
        calc ‖(2 * Real.sqrt t)⁻¹‖ = 2⁻¹ * t ^ ((-(1/2) : ℝ)) := by
              rw [Real.norm_eq_abs, hinv, abs_of_nonneg (mul_nonneg (by norm_num) hnn)]
          _ ≤ t ^ ((-(1/2) : ℝ)) := by linarith
          _ = ‖t ^ ((-(1/2) : ℝ))‖ := by
              rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hg.mono hm hb
    have hAval : ∫ t in (0:ℝ)..1, (2 * Real.sqrt t)⁻¹ = 1 := by
      have hII : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹) volume (0:ℝ) 1 := by
        unfold IntervalIntegrable
        refine ⟨?_, ?_⟩
        · unfold IntegrableOn
          exact hAint
        · unfold IntegrableOn
          simp
      have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1,
          HasDerivAt (fun t : ℝ => Real.sqrt t) ((2 * Real.sqrt x)⁻¹) x := by
        intro x hx
        have h := Real.hasDerivAt_sqrt (ne_of_gt hx.1)
        rwa [one_div] at h
      have hcont : ContinuousOn (fun t : ℝ => Real.sqrt t) (Set.Icc (0:ℝ) 1) :=
        Real.continuous_sqrt.continuousOn
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0:ℝ)) (b := 1)
        (by norm_num) hcont hderiv hII
      simpa using h
    have hAint' : Integrable (fun t : ℝ => (2 * Real.sqrt (1 - t))⁻¹)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      have hg : Integrable (fun t : ℝ => (1 - t) ^ ((-(1/2) : ℝ)))
          (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
        have h : IntervalIntegrable (fun t : ℝ => t ^ ((-(1/2) : ℝ))) volume (0:ℝ) 1 :=
          intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1) (r := (-(1/2) : ℝ))
            (by norm_num)
        have h1 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ ((-(1/2) : ℝ))) volume (1:ℝ) 0 := by
          simpa using h.comp_sub_left 1
        unfold IntervalIntegrable at h1
        obtain ⟨-, h3⟩ := h1
        unfold IntegrableOn at h3
        exact h3
      have hm : AEStronglyMeasurable (fun t : ℝ => (2 * Real.sqrt (1 - t))⁻¹)
          (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
        ((measurable_const.mul (Real.continuous_sqrt.measurable.comp
          (measurable_const.sub measurable_id))).inv).aestronglyMeasurable
      have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ‖(2 * Real.sqrt (1 - t))⁻¹‖ ≤ ‖(1 - t) ^ ((-(1/2) : ℝ))‖ := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
        have hinv : (2 * Real.sqrt (1 - t))⁻¹ = 2⁻¹ * (1 - t) ^ ((-(1/2) : ℝ)) := by
          rw [Real.sqrt_eq_rpow, mul_inv, ← Real.rpow_neg ht0 (1/2)]
        have hnn : (0:ℝ) ≤ (1 - t) ^ ((-(1/2) : ℝ)) := by
          rw [Real.rpow_neg ht0 (1/2), ← Real.sqrt_eq_rpow]
          exact inv_nonneg.2 (Real.sqrt_nonneg (1 - t))
        calc ‖(2 * Real.sqrt (1 - t))⁻¹‖ = 2⁻¹ * (1 - t) ^ ((-(1/2) : ℝ)) := by
              rw [Real.norm_eq_abs, hinv, abs_of_nonneg (mul_nonneg (by norm_num) hnn)]
          _ ≤ (1 - t) ^ ((-(1/2) : ℝ)) := by linarith
          _ = ‖(1 - t) ^ ((-(1/2) : ℝ))‖ := by
              rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hg.mono hm hb
    have hAval' : ∫ t in (0:ℝ)..1, (2 * Real.sqrt (1 - t))⁻¹ = 1 := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun u : ℝ => (2 * Real.sqrt u)⁻¹) (a := (0:ℝ)) (b := 1) (d := 1)
      rw [show (1:ℝ) - 1 = 0 by norm_num, show (1:ℝ) - 0 = 1 by norm_num] at h
      rw [h, hAval]
    have hSint : Integrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := hAint.add hAint'
    have hSval : ∫ t, ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)
        ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) = 2 := by
      rw [MeasureTheory.integral_add hAint hAint']
      have e1 : (∫ t, (2 * Real.sqrt t)⁻¹ ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
          = ∫ t in (0:ℝ)..1, (2 * Real.sqrt t)⁻¹ :=
        (intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)).symm
      have e2 : (∫ t, (2 * Real.sqrt (1 - t))⁻¹ ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
          = ∫ t in (0:ℝ)..1, (2 * Real.sqrt (1 - t))⁻¹ :=
        (intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)).symm
      rw [e1, e2, hAval, hAval']
      norm_num
    have hmono : (∫ t, ‖∑ j : Fin p, ∑ i' : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
        ≤ ∫ t, ((Cκ * phi2 * (Real.sqrt (m : ℝ))⁻¹ * |delta n m| * D x) *
          ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹))
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards with t
        exact norm_nonneg _
      · exact hSint.const_mul _
      · filter_upwards with t
        rw [mul_comm]
        exact hpt t
    have hiff : (∫ t in (0:ℝ)..1, ∑ j : Fin p, ∑ i' : Fin m,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x)
        = ∫ t, (∑ j : Fin p, ∑ i' : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x)
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)
    rw [hiff]
    calc ‖∫ t, (∑ j : Fin p, ∑ i' : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x)
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1))‖
        ≤ ∫ t, ‖∑ j : Fin p, ∑ i' : Fin m,
            (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot i' j t x‖
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t, ((Cκ * phi2 * (Real.sqrt (m : ℝ))⁻¹ * |delta n m| * D x) *
            ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹))
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := hmono
      _ = (Cκ * phi2 * (Real.sqrt (m : ℝ))⁻¹ * |delta n m| * D x) *
            (∫ t, ((2 * Real.sqrt t)⁻¹ + (2 * Real.sqrt (1 - t))⁻¹)
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) :=
          MeasureTheory.integral_const_mul _ _
      _ = (Cκ * phi2 * (Real.sqrt (m : ℝ))⁻¹ * |delta n m| * D x) * 2 := by rw [hSval]
      _ = Kc * D x := by
          have hKc : Kc = Cκ * phi2 * |delta n m| * (Real.sqrt (m : ℝ))⁻¹ * 2 := rfl
          rw [hKc]
          ring
  refine MeasureTheory.Integrable.mono' (g := fun x : Ω × Ω => Kc * D x) ?_ hmeas ?_
  · exact hDint.const_mul Kc
  · filter_upwards with x
    exact hbound x
  /- @proof-region region.target-node.session.31536d0f22d62e88 end -/

end

end Statlib.Imported

