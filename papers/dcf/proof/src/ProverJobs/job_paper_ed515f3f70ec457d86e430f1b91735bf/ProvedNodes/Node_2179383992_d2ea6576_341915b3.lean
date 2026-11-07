import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

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
theorem statopia_math_node_2179383992_d2ea6576 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hX : ∀ i : Fin n, Measurable (X i)) (hY : ∀ i : Fin m, Measurable (Y i))
    (hF : ∀ i : Fin n, Measurable (F i)) (hG : ∀ i : Fin m, Measurable (G i))
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (y : Fin p → ℝ) (Cκ : ℝ),
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
    let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
    let kappa : (Fin p → ℝ) → ℝ := fun w =>
      phi0 (phi * (beta⁻¹ * Real.log (∑ k : Fin p, Real.exp (beta * (w k - y k)))))
    let gfun : ℝ → Ω × Ω → ℝ := fun t x =>
      ∑ j : Fin p, ∑ i : Fin n,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j
    (∀ (w : Fin p → ℝ) (j : Fin p), |(fderiv ℝ kappa w) (Pi.single j (1 : ℝ))| ≤ Cκ * phi) →
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, Integrable (fun x => gfun t x) (P.prod P) := by
  /- @proof-region region.target-node.session.74f405e58e4f4a0b begin -/
  intro Ω _ P _ n m p delta muX muY X Y F G hX hY hF hG hX3 hF3 phi0 hphi0_cont phi1 phi2 hphi1 hphi2 v hv0 hv1 y Cκ phi beta Zstar Zstarstar Z Zdotstar kappa gfun hgrad t ht
  show Integrable (fun x => ∑ j : Fin p, ∑ i : Fin n, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j) (P.prod P)
  by_cases hp : p = 0
  · subst hp
    simpa [Fin.sum_univ_zero] using (integrable_zero : Integrable (fun _ : Ω × Ω => (0 : ℝ)) (P.prod P))
  · have integ_shift : ∀ (W : Ω → Fin p → ℝ), Measurable W →
        (∀ j : Fin p, Integrable (fun ω => |W ω j - muX j| ^ 3) P) →
        ∀ j : Fin p, Integrable (fun ω : Ω => W ω j - muX j) P := by
      intro W hW h3 j
      have hb : Integrable (fun ω : Ω => 1 + |W ω j - muX j| ^ 3) P :=
        (integrable_const (1 : ℝ)).add (h3 j)
      have hm : Measurable (fun ω : Ω => W ω j - muX j) :=
        ((measurable_pi_apply j).comp hW).sub measurable_const
      refine Integrable.mono' hb hm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
      intro ω
      have ha : (0 : ℝ) ≤ |W ω j - muX j| := abs_nonneg _
      have hle : |W ω j - muX j| ≤ 1 + |W ω j - muX j| ^ 3 := by
        nlinarith [mul_nonneg ha (sq_nonneg (|W ω j - muX j| - 1 / 2)),
          sq_nonneg (|W ω j - muX j| - 5 / 8)]
      simpa [Real.norm_eq_abs] using hle
    have hX1m : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => X i x.1 j - muX j) := by
      intro i j
      exact ((measurable_pi_apply j).comp ((hX i).comp measurable_fst)).sub measurable_const
    have hF1m : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => F i x.1 j - muX j) := by
      intro i j
      exact ((measurable_pi_apply j).comp ((hF i).comp measurable_fst)).sub measurable_const
    have hF2m : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => F i x.2 j - muX j) := by
      intro i j
      exact ((measurable_pi_apply j).comp ((hF i).comp measurable_snd)).sub measurable_const
    have hY1m : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => Y i x.1 j - muY j) := by
      intro i j
      exact ((measurable_pi_apply j).comp ((hY i).comp measurable_fst)).sub measurable_const
    have hG1m : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => G i x.1 j - muY j) := by
      intro i j
      exact ((measurable_pi_apply j).comp ((hG i).comp measurable_fst)).sub measurable_const
    have hG2m : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => G i x.2 j - muY j) := by
      intro i j
      exact ((measurable_pi_apply j).comp ((hG i).comp measurable_snd)).sub measurable_const
    have hXi : ∀ (i : Fin n) (j : Fin p), Integrable (fun x : Ω × Ω => X i x.1 j - muX j) (P.prod P) :=
      fun i j => (integ_shift (X i) (hX i) (hX3 i) j).comp_fst P
    have hFi : ∀ (i : Fin n) (j : Fin p), Integrable (fun x : Ω × Ω => F i x.1 j - muX j) (P.prod P) :=
      fun i j => (integ_shift (F i) (hF i) (hF3 i) j).comp_fst P
    have hFi2 : ∀ (i : Fin n) (j : Fin p), Integrable (fun x : Ω × Ω => F i x.2 j - muX j) (P.prod P) :=
      fun i j => (integ_shift (F i) (hF i) (hF3 i) j).comp_snd P
    have hZd : ∀ (i : Fin n) (j : Fin p), Integrable (fun x : Ω × Ω => Zdotstar t x i j) (P.prod P) := by
      intro i j
      show Integrable (fun x : Ω × Ω => (Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))) (P.prod P)
      have s1 : Integrable (fun x : Ω × Ω => (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) (P.prod P) :=
        (((hXi i j).const_mul (Real.sqrt v)).add ((hFi i j).const_mul (Real.sqrt (1 - v)))).const_mul (2 * Real.sqrt t)⁻¹
      have s2 : Integrable (fun x : Ω × Ω => (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)) (P.prod P) :=
        s1.sub ((hFi2 i j).const_mul (2 * Real.sqrt (1 - t))⁻¹)
      exact s2.const_mul (Real.sqrt (n : ℝ))⁻¹
    have hZsm : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => Zstar t x i j) := by
      intro i j
      show Measurable (fun x : Ω × Ω => (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) + Real.sqrt (1 - t) * (F i x.2 j - muX j)))
      have s1 : Measurable (fun x : Ω × Ω => Real.sqrt v * (X i x.1 j - muX j)) := measurable_const.mul (hX1m i j)
      have s2 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - v) * (F i x.1 j - muX j)) := measurable_const.mul (hF1m i j)
      have s3 : Measurable (fun x : Ω × Ω => Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) := measurable_const.mul (s1.add s2)
      have s4 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - t) * (F i x.2 j - muX j)) := measurable_const.mul (hF2m i j)
      exact measurable_const.mul (s3.add s4)
    have hZssm : ∀ (i : Fin m) (j : Fin p), Measurable (fun x : Ω × Ω => Zstarstar t x i j) := by
      intro i j
      show Measurable (fun x : Ω × Ω => (Real.sqrt (m : ℝ))⁻¹ * delta n m * (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) + Real.sqrt (1 - t) * (G i x.2 j - muY j)))
      have s1 : Measurable (fun x : Ω × Ω => Real.sqrt v * (Y i x.1 j - muY j)) := measurable_const.mul (hY1m i j)
      have s2 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - v) * (G i x.1 j - muY j)) := measurable_const.mul (hG1m i j)
      have s3 : Measurable (fun x : Ω × Ω => Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))) := measurable_const.mul (s1.add s2)
      have s4 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - t) * (G i x.2 j - muY j)) := measurable_const.mul (hG2m i j)
      exact measurable_const.mul (s3.add s4)
    have hZdm : ∀ (i : Fin n) (j : Fin p), Measurable (fun x : Ω × Ω => Zdotstar t x i j) := by
      intro i j
      show Measurable (fun x : Ω × Ω => (Real.sqrt (n : ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)))
      have s1 : Measurable (fun x : Ω × Ω => Real.sqrt v * (X i x.1 j - muX j)) := measurable_const.mul (hX1m i j)
      have s2 : Measurable (fun x : Ω × Ω => Real.sqrt (1 - v) * (F i x.1 j - muX j)) := measurable_const.mul (hF1m i j)
      have s3 : Measurable (fun x : Ω × Ω => (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) := measurable_const.mul (s1.add s2)
      have s4 : Measurable (fun x : Ω × Ω => (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)) := measurable_const.mul (hF2m i j)
      exact measurable_const.mul (s3.sub s4)
    have hZ : Measurable (fun x : Ω × Ω => Z t x) := by
      rw [measurable_pi_iff]
      intro j
      show Measurable (fun x : Ω × Ω => (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j))
      exact (Finset.measurable_sum _ (fun i _ => hZsm i j)).add (Finset.measurable_sum _ (fun i _ => hZssm i j))
    have hSp : ∀ w : Fin p → ℝ, 0 < ∑ k : Fin p, Real.exp (beta * (w k - y k)) := by
      intro w
      have hk : (⟨0, Nat.pos_of_ne_zero hp⟩ : Fin p) ∈ Finset.univ := Finset.mem_univ _
      have hs : Real.exp (beta * (w ⟨0, Nat.pos_of_ne_zero hp⟩ - y ⟨0, Nat.pos_of_ne_zero hp⟩)) ≤ ∑ k : Fin p, Real.exp (beta * (w k - y k)) :=
        Finset.single_le_sum (f := fun k : Fin p => Real.exp (beta * (w k - y k))) (fun i _ => (Real.exp_pos _).le) hk
      linarith [Real.exp_pos (beta * (w ⟨0, Nat.pos_of_ne_zero hp⟩ - y ⟨0, Nat.pos_of_ne_zero hp⟩))]
    have hS : ContDiff ℝ 3 (fun w : Fin p → ℝ => ∑ k : Fin p, Real.exp (beta * (w k - y k))) := by
      apply ContDiff.sum
      intro k _
      have hproj : ContDiff ℝ 3 (fun w : Fin p → ℝ => w k) := by fun_prop
      exact Real.contDiff_exp.comp (contDiff_const.mul (hproj.sub contDiff_const))
    have hlog : ContDiff ℝ 3 (fun w : Fin p → ℝ => Real.log (∑ k : Fin p, Real.exp (beta * (w k - y k)))) :=
      Real.contDiffOn_log.comp_contDiff hS (fun w => by simpa using ne_of_gt (hSp w))
    have hκ : ContDiff ℝ 3 kappa := by
      show ContDiff ℝ 3 (fun w : Fin p → ℝ => phi0 (phi * (beta⁻¹ * Real.log (∑ k : Fin p, Real.exp (beta * (w k - y k))))))
      exact hphi0_cont.comp (contDiff_const.mul (contDiff_const.mul hlog))
    have hgrad_meas : ∀ j : Fin p, Measurable (fun x : Ω × Ω => (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ))) := by
      intro j
      have hcont : Continuous (fun q : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ kappa q.1) q.2) :=
        hκ.continuous_fderiv_apply (by simp)
      have hsingle : Continuous (fun w : Fin p → ℝ => (w, (Pi.single j (1 : ℝ) : Fin p → ℝ))) :=
        continuous_id.prodMk continuous_const
      exact (hcont.comp hsingle).measurable.comp hZ
    have hdata : Measurable (fun x : Ω × Ω => ∑ j : Fin p, ∑ i : Fin n, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j) :=
      Finset.measurable_sum _ (fun j _ => Finset.measurable_sum _ (fun i _ => (hgrad_meas j).mul (hZdm i j)))
    have int_sum : ∀ (ι : Type) [Fintype ι] (fr : ι → Ω × Ω → ℝ),
        (∀ i, Integrable (fr i) (P.prod P)) → Integrable (fun x => ∑ i, fr i x) (P.prod P) := by
      classical
      intro ι _ fr hfr
      have key : ∀ s : Finset ι, Integrable (fun x : Ω × Ω => ∑ i ∈ s, fr i x) (P.prod P) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using (integrable_zero : Integrable (fun _ : Ω × Ω => (0 : ℝ)) (P.prod P))
        | insert a s ha ih => simpa [Finset.sum_insert ha] using (hfr a).add ih
      simpa using key Finset.univ
    have hSabs : Integrable (fun x : Ω × Ω => ∑ j : Fin p, ∑ i : Fin n, |Zdotstar t x i j|) (P.prod P) := by
      have h1 : ∀ j : Fin p, Integrable (fun x : Ω × Ω => ∑ i : Fin n, |Zdotstar t x i j|) (P.prod P) :=
        fun j => int_sum (Fin n) (fun i x => |Zdotstar t x i j|) (fun i => (hZd i j).abs)
      exact int_sum (Fin p) (fun j x => ∑ i : Fin n, |Zdotstar t x i j|) (fun j => h1 j)
    refine Integrable.mono' (hSabs.const_mul (|Cκ * phi|)) hdata.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    have h1 : ∀ j : Fin p, |(fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ))| ≤ |Cκ * phi| := by
      intro j
      exact le_trans (hgrad (Z t x) j) (le_abs_self (Cκ * phi))
    calc |∑ j : Fin p, ∑ i : Fin n, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j|
        ≤ ∑ j : Fin p, |∑ i : Fin n, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin p, ∑ i : Fin n, |(fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ))| * |Zdotstar t x i j| := by
          apply Finset.sum_le_sum
          intro j _
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul]
      _ ≤ ∑ j : Fin p, ∑ i : Fin n, |Cκ * phi| * |Zdotstar t x i j| := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (h1 j) (abs_nonneg _)
      _ = |Cκ * phi| * ∑ j : Fin p, ∑ i : Fin n, |Zdotstar t x i j| := by
          simp only [Finset.mul_sum]
  /- @proof-region region.target-node.session.74f405e58e4f4a0b end -/

end

end Statlib.Imported

