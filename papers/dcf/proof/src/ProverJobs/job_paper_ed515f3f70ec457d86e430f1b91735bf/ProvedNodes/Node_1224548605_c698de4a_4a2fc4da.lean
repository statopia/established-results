import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3265138570_1cd724f8_eb0f666c

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
theorem statopia_math_node_1224548605_c698de4a : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m p : ℕ} (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hind : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hMemX : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hMemY : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hMeanX : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hMeanY : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hGaussF : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGaussG : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i)),
    ProbabilityTheory.IsGaussian
      (MeasureTheory.Measure.map (fun ω => fun j : Fin p =>
        combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) P)
    ∧ (∫ z : Fin p → ℝ,
        z ∂(MeasureTheory.Measure.map (fun ω => fun j : Fin p =>
          combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) P)
        = fun _ => (0 : ℝ)) := by
  /- @proof-region region.target-node.session.361c52760883993f begin -/
  classical
  intro Ω instΩ P instP n m p hn hm hp delta muX muY X Y F G hFm hGm hind hMemX hMemY hMeanX hMeanY
    hGaussF hGaussG
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
  have hsm : Real.sqrt (m:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hmpos).ne'
  have hsqn : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := Real.mul_self_sqrt hnpos.le
  have hsqm : Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = (m:ℝ) := Real.mul_self_sqrt hmpos.le
  have hinvn : (Real.sqrt (n:ℝ))⁻¹ * (n:ℝ) = Real.sqrt (n:ℝ) := by
    have h : (Real.sqrt (n:ℝ))⁻¹ * (n:ℝ)
        = (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) := by rw [hsqn]
    rw [h, ← mul_assoc, inv_mul_cancel₀ hsn, one_mul]
  have hinvm : (Real.sqrt (m:ℝ))⁻¹ * (m:ℝ) = Real.sqrt (m:ℝ) := by
    have h : (Real.sqrt (m:ℝ))⁻¹ * (m:ℝ)
        = (Real.sqrt (m:ℝ))⁻¹ * (Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ)) := by rw [hsqm]
    rw [h, ← mul_assoc, inv_mul_cancel₀ hsm, one_mul]
  have hpsdX : ∀ i : Fin n, (covX P muX X i).PosSemidef := by
    intro i
    have hsym : (covX P muX X i).transpose = covX P muX X i := by
      ext a b
      simp only [Matrix.transpose_apply, covX]
      have hfun : (fun ω => (X i ω a - muX a) * (X i ω b - muX b))
          = (fun ω => (X i ω b - muX b) * (X i ω a - muX a)) := by
        funext ω
        ring
      rw [hfun]
    have h := IsCenteredGaussianVector.posSemidef_symmetrizedCovariance (hGaussF i) (show 1 ≤ p from hp)
    have h2 : (2:ℝ)⁻¹ • ((covX P muX X i) + (covX P muX X i).transpose) = covX P muX X i := by
      rw [hsym]
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rwa [h2] at h
  have hpsdY : ∀ i : Fin m, (covY P muY Y i).PosSemidef := by
    intro i
    have hsym : (covY P muY Y i).transpose = covY P muY Y i := by
      ext a b
      simp only [Matrix.transpose_apply, covY]
      have hfun : (fun ω => (Y i ω a - muY a) * (Y i ω b - muY b))
          = (fun ω => (Y i ω b - muY b) * (Y i ω a - muY a)) := by
        funext ω
        ring
      rw [hfun]
    have h := IsCenteredGaussianVector.posSemidef_symmetrizedCovariance (hGaussG i) (show 1 ≤ p from hp)
    have h2 : (2:ℝ)⁻¹ • ((covY P muY Y i) + (covY P muY Y i).transpose) = covY P muY Y i := by
      rw [hsym]
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rwa [h2] at h
  have hsingle : ∀ (j : Fin p) (g : Fin p → ℝ),
      ∑ j' : Fin p, (Pi.single j (1:ℝ) : Fin p → ℝ) j' * g j' = g j := by
    intro j g
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
    · simp
  have hlawF : ∀ (i : Fin n) (j : Fin p),
      ∃ v : NNReal, Measure.map (fun ω => F i ω j - muX j) P = gaussianReal 0 v := by
    intro i j
    have hmap := IsCenteredGaussianVector.map_linearCombination P
      _ _ (hGaussF i) (hpsdX i) (Pi.single j (1:ℝ))
    rw [show (fun ω => F i ω j - muX j)
        = (fun ω => ∑ b : Fin p, (Pi.single j (1:ℝ) : Fin p → ℝ) b * (F i ω b - muX b)) from by
      funext ω
      exact (hsingle j (fun b => F i ω b - muX b)).symm]
    exact ⟨_, hmap⟩
  have hlawG : ∀ (i : Fin m) (j : Fin p),
      ∃ v : NNReal, Measure.map (fun ω => G i ω j - muY j) P = gaussianReal 0 v := by
    intro i j
    have hmap := IsCenteredGaussianVector.map_linearCombination P
      _ _ (hGaussG i) (hpsdY i) (Pi.single j (1:ℝ))
    rw [show (fun ω => G i ω j - muY j)
        = (fun ω => ∑ b : Fin p, (Pi.single j (1:ℝ) : Fin p → ℝ) b * (G i ω b - muY b)) from by
      funext ω
      exact (hsingle j (fun b => G i ω b - muY b)).symm]
    exact ⟨_, hmap⟩
  have hint0F : ∀ (i : Fin n) (j : Fin p), ∫ ω, (F i ω j - muX j) ∂P = 0 := by
    intro i j
    obtain ⟨v, hv⟩ := hlawF i j
    have hm : AEMeasurable (fun ω => F i ω j - muX j) P :=
      (((measurable_pi_apply j).comp (hFm i)).sub_const (muX j)).aemeasurable
    have h1 : (∫ x : ℝ, x ∂Measure.map (fun ω => F i ω j - muX j) P)
        = ∫ ω, (F i ω j - muX j) ∂P := by
      rw [integral_map (f := fun x : ℝ => x) hm aestronglyMeasurable_id]
    rw [← h1, hv, integral_id_gaussianReal]
  have hint0G : ∀ (i : Fin m) (j : Fin p), ∫ ω, (G i ω j - muY j) ∂P = 0 := by
    intro i j
    obtain ⟨v, hv⟩ := hlawG i j
    have hm : AEMeasurable (fun ω => G i ω j - muY j) P :=
      (((measurable_pi_apply j).comp (hGm i)).sub_const (muY j)).aemeasurable
    have h1 : (∫ x : ℝ, x ∂Measure.map (fun ω => G i ω j - muY j) P)
        = ∫ ω, (G i ω j - muY j) ∂P := by
      rw [integral_map (f := fun x : ℝ => x) hm aestronglyMeasurable_id]
    rw [← h1, hv, integral_id_gaussianReal]
  have hG : ProbabilityTheory.IsGaussian
      (MeasureTheory.Measure.map (fun ω => fun j : Fin p =>
        combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) P) :=
    statopia_math_node_3265138570_1cd724f8 P hn hm hp delta muX muY X Y F G hFm hGm hind hMemX
      hMemY hMeanX hMeanY hGaussF hGaussG
  have hdec : ∀ (ω : Ω) (j : Fin p),
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
        = (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, (F i ω j - muX j))
          + delta n m * (Real.sqrt (m:ℝ))⁻¹ * (∑ i : Fin m, (G i ω j - muY j)) := by
    intro ω j
    have h1 : (∑ i : Fin n, (F i ω j - muX j)) = (∑ i : Fin n, F i ω j) - (n:ℝ) * muX j := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have h2 : (∑ i : Fin m, (G i ω j - muY j)) = (∑ i : Fin m, G i ω j) - (m:ℝ) * muY j := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    simp only [combVec, normSum]
    rw [h1, h2]
    linear_combination (muX j) * hinvn + (delta n m * muY j) * hinvm
  refine ⟨hG, ?_⟩
  let U : Ω → Fin p → ℝ := fun ω j =>
    combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
  change (∫ z : Fin p → ℝ, z ∂Measure.map U P) = fun _ => (0 : ℝ)
  have hmF : ∀ (i : Fin n) (j : Fin p), Measurable (fun ω => F i ω j - muX j) :=
    fun i j => ((measurable_pi_apply j).comp (hFm i)).sub_const (muX j)
  have hmG : ∀ (i : Fin m) (j : Fin p), Measurable (fun ω => G i ω j - muY j) :=
    fun i j => ((measurable_pi_apply j).comp (hGm i)).sub_const (muY j)
  have hint_of_law : ∀ (Z : Ω → ℝ) (v : NNReal), AEMeasurable Z P →
      Measure.map Z P = gaussianReal 0 v → Integrable Z P := by
    intro Z v hZ hv
    have hmem : MemLp (fun x : ℝ => x) 1 (gaussianReal 0 v) := by
      simpa using memLp_pow_id_gaussianReal (μ₀ := 0) (v := v) 1 (1 : ENNReal) (by simp)
    have h3 : MemLp (fun x : ℝ => x) 1 (Measure.map Z P) := by
      rw [hv]
      exact hmem
    have h5 := (MeasureTheory.memLp_map_measure_iff (f := Z) (g := fun x : ℝ => x) (p := 1)
      aestronglyMeasurable_id hZ).mp h3
    exact MeasureTheory.memLp_one_iff_integrable.mp h5
  have hintF : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => F i ω j - muX j) P :=
    fun i j => hint_of_law _ _ (hmF i j).aemeasurable (hlawF i j).choose_spec
  have hintG : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j - muY j) P :=
    fun i j => hint_of_law _ _ (hmG i j).aemeasurable (hlawG i j).choose_spec
  have hS : ∀ j : Fin p, (∫ ω, ∑ i : Fin n, (F i ω j - muX j) ∂P) = 0 := by
    intro j
    rw [integral_finset_sum Finset.univ (fun i _ => hintF i j)]
    simp [hint0F]
  have hT : ∀ j : Fin p, (∫ ω, ∑ i : Fin m, (G i ω j - muY j) ∂P) = 0 := by
    intro j
    rw [integral_finset_sum Finset.univ (fun i _ => hintG i j)]
    simp [hint0G]
  have hUmeas : Measurable U := by
    have h1 : U = fun ω (j : Fin p) =>
        (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, (F i ω j - muX j))
          + delta n m * (Real.sqrt (m:ℝ))⁻¹ * (∑ i : Fin m, (G i ω j - muY j)) := by
      funext ω j
      exact hdec ω j
    rw [h1]
    refine measurable_pi_iff.2 fun j => ?_
    have hA : Measurable (fun ω : Ω => ∑ i : Fin n, (F i ω j - muX j)) :=
      Finset.measurable_sum _ (fun i _ => hmF i j)
    have hB : Measurable (fun ω : Ω => ∑ i : Fin m, (G i ω j - muY j)) :=
      Finset.measurable_sum _ (fun i _ => hmG i j)
    exact (measurable_const.mul hA).add (measurable_const.mul hB)
  have hUj : ∀ j : Fin p, (∫ ω, U ω j ∂P) = 0 := by
    intro j
    have hfun : (fun ω => U ω j) = (fun ω =>
        (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, (F i ω j - muX j))
          + delta n m * (Real.sqrt (m:ℝ))⁻¹ * (∑ i : Fin m, (G i ω j - muY j))) := by
      funext ω
      exact hdec ω j
    rw [hfun]
    have hIA : Integrable
        (fun ω => (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, (F i ω j - muX j))) P :=
      (integrable_finset_sum Finset.univ (fun i _ => hintF i j)).const_mul _
    have hIB : Integrable
        (fun ω => delta n m * (Real.sqrt (m:ℝ))⁻¹ * (∑ i : Fin m, (G i ω j - muY j))) P :=
      (integrable_finset_sum Finset.univ (fun i _ => hintG i j)).const_mul _
    have hA : (∫ ω, (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, (F i ω j - muX j)) ∂P) = 0 := by
      rw [integral_const_mul, hS j, mul_zero]
    have hB : (∫ ω, delta n m * (Real.sqrt (m:ℝ))⁻¹
        * (∑ i : Fin m, (G i ω j - muY j)) ∂P) = 0 := by
      rw [integral_const_mul, hT j, mul_zero]
    rw [integral_add hIA hIB, hA, hB, add_zero]
  by_cases hInt : Integrable (fun z : Fin p → ℝ => z) (Measure.map U P)
  · funext j
    have hproj : (∫ z : Fin p → ℝ, z ∂Measure.map U P) j
        = ∫ z : Fin p → ℝ, z j ∂Measure.map U P := by
      have hcomm := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (E := Fin p → ℝ)
        (Fₗ := ℝ) (φ := fun z : Fin p → ℝ => z)
        (L := ContinuousLinearMap.proj j) (μ := Measure.map U P) hInt
      simpa using hcomm.symm
    rw [hproj]
    have hcoord : (∫ z : Fin p → ℝ, z j ∂Measure.map U P) = ∫ ω, U ω j ∂P :=
      integral_map (f := fun z : Fin p → ℝ => z j) hUmeas.aemeasurable
        ((measurable_pi_apply j).aemeasurable.aestronglyMeasurable)
    rw [hcoord, hUj j]
  · rw [integral_undef hInt]
    rfl
  /- @proof-region region.target-node.session.361c52760883993f end -/

end

end Statlib.Imported

