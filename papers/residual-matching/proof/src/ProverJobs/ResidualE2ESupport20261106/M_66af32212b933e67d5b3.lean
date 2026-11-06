import Statlib.HighDim.MatrixAnalysis.FrobeniusNormSvdRelation
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.Vocabulary.SVD
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_f00de8b445341c78f04b

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ResidualLoss20261106.Statlib.Imported
noncomputable section

private theorem mean_bias_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (N b a q : ℝ) (hN : 1 ≤ N) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ)
    (hsecond : ∫ ω, f ω ^ 2 ∂μ ≤ 2 * N)
    (hbad : μ {ω | a < |f ω - b|} ≤ ENNReal.ofReal q) :
    |(∫ ω, f ω ∂μ) - b| ≤ a + 4 * Real.sqrt (N * q) := by
  classical
  let B : Set Ω := {ω | a < |f ω - b|}
  have hB : MeasurableSet B := measurableSet_lt measurable_const ((hf.sub_const b).abs)
  have hLp : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hf2
  have hdiffLp : MemLp (fun ω => f ω - b) 2 μ := hLp.sub (memLp_const b)
  have hdiff2 := hdiffLp.integrable_sq
  have hfi : Integrable f μ := hLp.integrable (by norm_num)
  have habsi : Integrable (fun ω => |f ω - b|) μ := by
    simpa only [Real.norm_eq_abs] using (hfi.sub (integrable_const b)).norm
  have hdiffsecond : (∫ ω, (f ω - b) ^ 2 ∂μ) ≤ 16 * N := by
    have hmaj : Integrable (fun ω => 2 * f ω ^ 2 + 2 * b ^ 2) μ :=
      (hf2.const_mul 2).add (integrable_const _)
    have h := integral_mono hdiff2 hmaj (fun ω => by nlinarith [sq_nonneg (f ω + b)])
    simp [integral_add (hf2.const_mul 2) (integrable_const (2 * b ^ 2)),
      integral_const_mul] at h
    nlinarith [sq_nonneg b]
  let ind : Ω → ℝ := B.indicator (fun _ => 1)
  have hindLp : MemLp ind 2 μ := (memLp_const (1 : ℝ)).indicator hB
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ)
    Real.HolderConjugate.two_two
    (f := fun ω => |f ω - b|) (g := ind)
    (ae_of_all μ (fun _ => abs_nonneg _))
    (ae_of_all μ (fun ω => by by_cases h : ω ∈ B <;> simp [ind, h]))
    (by simpa [Real.norm_eq_abs] using hdiffLp.norm)
    (by simpa using hindLp)
  have hprod : (∫ ω, |f ω - b| * ind ω ∂μ) = ∫ ω in B, |f ω - b| ∂μ := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards with ω
    by_cases h : ω ∈ B <;> simp [ind, h]
  have hpow : (∫ ω, |f ω - b| ^ (2 : ℝ) ∂μ) = ∫ ω, (f ω - b) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Real.rpow_ofNat, sq_abs]
  have hindpow : (∫ ω, ind ω ^ (2 : ℝ) ∂μ) = (μ B).toReal := by
    have heq : (fun ω => ind ω ^ (2 : ℝ)) = B.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : ω ∈ B <;> simp [ind, h]
    rw [heq, integral_indicator_const _ hB]
    simp [Measure.real]
  rw [hprod, hpow, hindpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  have hprob : (μ B).toReal ≤ q := by
    have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hbad
    simpa [B, ENNReal.toReal_ofReal hq] using h
  have htail : (∫ ω in B, |f ω - b| ∂μ) ≤ 4 * Real.sqrt (N * q) := by
    calc
      (∫ ω in B, |f ω - b| ∂μ) ≤
          Real.sqrt (∫ ω, (f ω - b) ^ 2 ∂μ) * Real.sqrt ((μ B).toReal) := hCS
      _ ≤ Real.sqrt (16 * N) * Real.sqrt q :=
        mul_le_mul (Real.sqrt_le_sqrt hdiffsecond) (Real.sqrt_le_sqrt hprob)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = 4 * Real.sqrt (N * q) := by
        rw [← Real.sqrt_mul (by positivity), show 16 * N * q = 16 * (N * q) by ring,
          Real.sqrt_mul (by norm_num)]
        norm_num
  have hgood : (∫ ω in Bᶜ, |f ω - b| ∂μ) ≤ a := by
    have h := setIntegral_mono_on habsi.integrableOn (integrable_const a).integrableOn
      hB.compl (fun ω hω => by
        have hn : ¬ a < |f ω - b| := hω
        exact le_of_not_gt hn)
    have hp : (μ Bᶜ).toReal ≤ 1 := by
      have hle : μ Bᶜ ≤ 1 := prob_le_one
      simpa using ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hle
    calc
      (∫ ω in Bᶜ, |f ω - b| ∂μ) ≤ ∫ _ in Bᶜ, a ∂μ := h
      _ = (μ Bᶜ).toReal * a := by simp [Measure.real]
      _ ≤ a := by nlinarith [ENNReal.toReal_nonneg (a := μ Bᶜ)]
  have hsplit := integral_add_compl hB habsi
  have habound : (∫ ω, |f ω - b| ∂μ) ≤ a + 4 * Real.sqrt (N * q) := by linarith
  have hid : (∫ ω, f ω - b ∂μ) = (∫ ω, f ω ∂μ) - b := by
    rw [integral_sub hfi (integrable_const _)]
    simp
  rw [← hid]
  exact (abs_integral_le_integral_abs).trans habound

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

set_option maxHeartbeats 2000000 in
theorem statopia_math_node_800008803_e75f9479 : ∀ (m n : ℕ) (hnm : n ≤ m)
    (p : ℝ) (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (O : Matrix (Fin m) (Fin n) ℝ) (hO_nonneg : ∀ i j, 0 ≤ O i j)
    (hO_le_one : ∀ i j, O i j ≤ 1)
    (hO_sum : ∑ i : Fin m, ∑ j : Fin n, O i j ≤ 2 * ((m : ℝ) * (n : ℝ) * p))
    (μG : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure μG]
    (hG_int : ∀ i j, Integrable (fun G : Matrix (Fin m) (Fin n) ℝ => G i j ^ 2) μG)
    (hG_second : ∀ i j, ∫ G : Matrix (Fin m) (Fin n) ℝ, G i j ^ 2 ∂μG = 1)
    (g : Fin n → ℝ) (hg_nonneg : ∀ i, 0 ≤ g i) (hg_le_two : ∀ i, g i ≤ 2)
    (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hdev : ∀ G : Matrix (Fin m) (Fin n) ℝ,
      maxDeviation (svals (maskedScaled p G O)) g ≤ C * δ →
      ∀ i : Fin n, |svals (maskedScaled p G O) i - g i| ≤ C * δ)
    (q : ℝ) (hq : 0 ≤ q)
    (hbad : μG {G : Matrix (Fin m) (Fin n) ℝ |
      C * δ < maxDeviation (svals (maskedScaled p G O)) g} ≤ ENNReal.ofReal q)
    (i : Fin n),
    |∫ G : Matrix (Fin m) (Fin n) ℝ, svals (maskedScaled p G O) i ∂μG - g i|
      ≤ C * δ + 4 * Real.sqrt ((n : ℝ) * q) := by
  intro m n hnm p hp_pos hp_le_one O hO_nonneg hO_le_one hO_sum μG hμG
    hG_int hG_second g hg_nonneg hg_le_two C δ hC hδ hdev q hq hbad i
  classical
  have hn : 1 ≤ n := by have := i.isLt; omega
  have hm : 1 ≤ m := le_trans hn hnm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmp : 0 < (m : ℝ) * p := mul_pos hmpos hp_pos
  let F : Matrix (Fin m) (Fin n) ℝ → ℝ := fun G => svals (maskedScaled p G O) i
  let H : Matrix (Fin m) (Fin n) ℝ → ℝ := fun G =>
    ∑ a : Fin m, ∑ b : Fin n, (O a b ^ 2 / ((m : ℝ) * p)) * G a b ^ 2
  let k : Fin (min m n) := Fin.cast (by omega : n = min m n) i
  have hsvals : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      svals A i = Statlib.HighDim.MatrixAnalysis.singularValues A k := by
    intro A
    rw [Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary]
    simp only [svals, Statlib.HighDim.Vocabulary.singularValues, k]
    congr 2
  have hFmeas : Measurable F := by
    have hM : Measurable (fun G : Matrix (Fin m) (Fin n) ℝ => maskedScaled p G O) := by
      refine measurable_pi_iff.mpr (fun a => measurable_pi_iff.mpr (fun b => ?_))
      have hc : Measurable (fun G : Matrix (Fin m) (Fin n) ℝ => G a b) :=
        (measurable_pi_apply b).comp (measurable_pi_apply a)
      exact (hc.const_mul (O a b)).div_const _
    have h := (statopia_math_node_3334131066_c2302711 k).comp hM
    simpa only [F, hsvals] using h
  have hpoint : ∀ G, F G ^ 2 ≤ H G := by
    intro G
    have hsingle : Statlib.HighDim.MatrixAnalysis.singularValues (maskedScaled p G O) k ^ 2 ≤
        ∑ l : Fin (min m n),
          Statlib.HighDim.MatrixAnalysis.singularValues (maskedScaled p G O) l ^ 2 :=
      Finset.single_le_sum (fun l _ => sq_nonneg _) (Finset.mem_univ k)
    have hfrob := (Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation
      (maskedScaled p G O)).1
    calc
      F G ^ 2 = Statlib.HighDim.MatrixAnalysis.singularValues (maskedScaled p G O) k ^ 2 := by
        change svals (maskedScaled p G O) i ^ 2 = _
        rw [hsvals]
      _ ≤ ∑ l : Fin (min m n), Statlib.HighDim.MatrixAnalysis.singularValues (maskedScaled p G O) l ^ 2 := hsingle
      _ = ∑ a : Fin m, ∑ b : Fin n, (maskedScaled p G O a b) ^ 2 := hfrob.symm
      _ = H G := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [maskedScaled]
        rw [div_pow, Real.sq_sqrt hmp.le]
        ring
  have hHint : Integrable H μG := by
    exact integrable_finset_sum _ (fun a _ => integrable_finset_sum _
      (fun b _ => (hG_int a b).const_mul _))
  have hF2int : Integrable (fun G => F G ^ 2) μG := by
    refine hHint.mono' (hFmeas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with G
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F G))] using hpoint G
  have hHmean : (∫ G, H G ∂μG) =
      (∑ a : Fin m, ∑ b : Fin n, O a b ^ 2) / ((m : ℝ) * p) := by
    change (∫ G, ∑ a : Fin m, ∑ b : Fin n,
      (O a b ^ 2 / ((m : ℝ) * p)) * G a b ^ 2 ∂μG) = _
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _
      (fun b _ => (hG_int a b).const_mul _))]
    simp_rw [integral_finset_sum _ (fun b _ => (hG_int _ b).const_mul _),
      integral_const_mul, hG_second, mul_one]
    simp_rw [Finset.sum_div]
  have hFsecond : (∫ G, F G ^ 2 ∂μG) ≤ 2 * (n : ℝ) := by
    have hsq : (∑ a : Fin m, ∑ b : Fin n, O a b ^ 2) ≤ ∑ a : Fin m, ∑ b : Fin n, O a b := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      nlinarith [hO_nonneg a b, hO_le_one a b]
    calc
      (∫ G, F G ^ 2 ∂μG) ≤ ∫ G, H G ∂μG := integral_mono hF2int hHint hpoint
      _ = (∑ a : Fin m, ∑ b : Fin n, O a b ^ 2) / ((m : ℝ) * p) := hHmean
      _ ≤ (2 * ((m : ℝ) * (n : ℝ) * p)) / ((m : ℝ) * p) :=
        div_le_div_of_nonneg_right (hsq.trans hO_sum) hmp.le
      _ = 2 * (n : ℝ) := by field_simp
  have hbadF : μG {G | C * δ < |F G - g i|} ≤ ENNReal.ofReal q := by
    refine (measure_mono ?_).trans hbad
    intro G hG
    change C * δ < maxDeviation (svals (maskedScaled p G O)) g
    by_contra h
    have hi := hdev G (le_of_not_gt h) i
    change C * δ < |svals (maskedScaled p G O) i - g i| at hG
    linarith
  exact mean_bias_of_second_moment μG F hFmeas (n : ℝ) (g i) (C * δ) q
    (by exact_mod_cast hn) (hg_nonneg i) (hg_le_two i) (mul_nonneg hC hδ) hq
    hF2int hFsecond hbadF

end
end ResidualLoss20261106.Statlib.Imported

#print axioms ResidualLoss20261106.Statlib.Imported.statopia_math_node_800008803_e75f9479

