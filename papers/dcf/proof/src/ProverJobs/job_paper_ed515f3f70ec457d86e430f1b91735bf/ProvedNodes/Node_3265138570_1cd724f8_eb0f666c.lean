import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
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
theorem statopia_math_node_3265138570_1cd724f8 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
        combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) P) := by
  /- @proof-region region.target-node.session.847ece2df6d0e60d begin -/
  classical
  intro Ω _ P _ n m p hn hm hp delta muX muY X Y F G hFm hGm hind hMemX hMemY hMeanX hMeanY
    hGaussF hGaussG
  have hzero : Measure.map (fun _ : Ω => (0 : ℝ)) P = gaussianReal 0 0 := by
    simp
  have kernel : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (ν : ι → NNReal) (Z : ι → Ω → ℝ),
      iIndepFun Z P → (∀ i, Measurable (Z i)) →
      (∀ i, Measure.map (Z i) P = gaussianReal 0 (ν i)) →
      Measure.map (fun ω => ∑ i, Z i ω) P = gaussianReal 0 (∑ i, ν i) := by
    intro ι _ _ ν Z hindZ hZm hZlaw
    have key : ∀ s : Finset ι,
        Measure.map (fun ω => ∑ i ∈ s, Z i ω) P = gaussianReal 0 (∑ i ∈ s, ν i) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using hzero
      | insert k s hk ih =>
        have hmem : k ∈ ({k} : Finset ι) := Finset.mem_singleton_self k
        have hind_part : (fun ω => ∑ i ∈ s, Z i ω) ⟂ᵢ[P] Z k := by
          have h := hindZ.indepFun_finset s {k} (Finset.disjoint_singleton_right.mpr hk) hZm
          have h' := h.comp (Finset.measurable_sum s.attach (fun i _ => measurable_pi_apply i))
            (measurable_pi_apply (⟨k, hmem⟩ : ↥({k} : Finset ι)))
          have e1 : ((fun a : ↥s → ℝ => ∑ i ∈ s.attach, a i) ∘ fun a (i : ↥s) => Z (↑i : ι) a)
              = (fun ω => ∑ i ∈ s, Z i ω) := by
            funext ω
            show ∑ i ∈ s.attach, Z (↑i : ι) ω = ∑ i ∈ s, Z i ω
            exact Finset.sum_attach s (fun i => Z i ω)
          have e2 : ((fun f : ↥({k} : Finset ι) → ℝ => f ⟨k, hmem⟩) ∘
              fun a (i : ↥({k} : Finset ι)) => Z (↑i : ι) a) = Z k := by
            funext ω
            simp
          simpa only [e1, e2] using h'
        have hfun : (fun ω => ∑ i ∈ insert k s, Z i ω)
            = (fun ω => (∑ i ∈ s, Z i ω) + Z k ω) := by
          funext ω
          rw [Finset.sum_insert hk]
          ring
        rw [hfun]
        change Measure.map ((fun ω => ∑ i ∈ s, Z i ω) + Z k) P
          = gaussianReal 0 (∑ i ∈ insert k s, ν i)
        rw [ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun hind_part ih (hZlaw k),
          Finset.sum_insert hk, zero_add, add_comm]
    simpa using key Finset.univ
  refine ProbabilityTheory.isGaussian_of_map_eq_gaussianReal (fun L => ?_)
  set c : Fin p → ℝ := fun j => L (Pi.single j (1 : ℝ)) with hc
  have hL : ∀ y : Fin p → ℝ, L y = ∑ j, c j * y j := by
    intro y
    have hy : y = ∑ j : Fin p, y j • (Pi.single j (1 : ℝ) : Fin p → ℝ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]
    simp [c, smul_eq_mul, mul_comm]
  set a : ℝ := Real.sqrt (n : ℝ) with ha
  set b : ℝ := Real.sqrt (m : ℝ) with hb
  set d : ℝ := delta n m with hd
  have hapos : 0 < a := by rw [ha]; exact Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hbpos : 0 < b := by rw [hb]; exact Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have haa : a * a = (n : ℝ) := by rw [ha]; exact Real.mul_self_sqrt (by positivity)
  have hbb : b * b = (m : ℝ) := by rw [hb]; exact Real.mul_self_sqrt (by positivity)
  have hainv : a⁻¹ * (n : ℝ) = a := by
    rw [← haa, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hapos), one_mul]
  have hbinv : b⁻¹ * (m : ℝ) = b := by
    rw [← hbb, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hbpos), one_mul]
  have hU' : ∀ (ω : Ω) (j : Fin p),
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
        = a⁻¹ * (∑ i : Fin n, (F i ω j - muX j))
          + (d * b⁻¹) * (∑ i : Fin m, (G i ω j - muY j)) := by
    intro ω j
    have hX : ∑ i : Fin n, (F i ω j - muX j)
        = (∑ i : Fin n, F i ω j) - (n : ℝ) * muX j := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have hGY : ∑ i : Fin m, (G i ω j - muY j)
        = (∑ i : Fin m, G i ω j) - (m : ℝ) * muY j := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    simp only [combVec, normSum, ← ha, ← hb, ← hd, hX, hGY]
    rw [show (n : ℝ) = a * a from haa.symm, show (m : ℝ) = b * b from hbb.symm]
    field_simp [ne_of_gt hapos, ne_of_gt hbpos]
    ring
  have hsymmX : ∀ i : Fin n, (covX P muX X i).transpose = covX P muX X i := by
    intro i
    funext j k
    simp only [covX, Matrix.transpose_apply]
    apply integral_congr_ae
    filter_upwards with ω
    ring
  have hpsdX : ∀ i : Fin n, (covX P muX X i).PosSemidef := by
    intro i
    have htwo : (2⁻¹ : ℝ) • (covX P muX X i + covX P muX X i) = covX P muX X i := by
      funext j k
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
      rw [← two_mul, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul]
    have h1 := IsCenteredGaussianVector.posSemidef_symmetrizedCovariance (hGaussF i) hp
    rw [hsymmX i, htwo] at h1
    exact h1
  have hsymmG : ∀ i : Fin m, (covY P muY Y i).transpose = covY P muY Y i := by
    intro i
    funext j k
    simp only [covY, Matrix.transpose_apply]
    apply integral_congr_ae
    filter_upwards with ω
    ring
  have hpsdG : ∀ i : Fin m, (covY P muY Y i).PosSemidef := by
    intro i
    have htwo : (2⁻¹ : ℝ) • (covY P muY Y i + covY P muY Y i) = covY P muY Y i := by
      funext j k
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
      rw [← two_mul, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul]
    have h1 := IsCenteredGaussianVector.posSemidef_symmetrizedCovariance (hGaussG i) hp
    rw [hsymmG i, htwo] at h1
    exact h1
  have hFexists : ∀ i : Fin n, ∃ v : NNReal,
      Measure.map (fun ω => a⁻¹ * ∑ j : Fin p, c j * (F i ω j - muX j)) P
        = gaussianReal 0 v := by
    intro i
    have h := IsCenteredGaussianVector.map_linearCombination P (fun ω j => F i ω j - muX j)
      (covX P muX X i) (hGaussF i) (hpsdX i) (fun j => a⁻¹ * c j)
    have hfun : (fun ω => ∑ j : Fin p, (a⁻¹ * c j) * (F i ω j - muX j))
        = (fun ω => a⁻¹ * ∑ j : Fin p, c j * (F i ω j - muX j)) := by
      funext ω
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hfun] at h
    exact ⟨_, h⟩
  have hGexists : ∀ i : Fin m, ∃ v : NNReal,
      Measure.map (fun ω => d * b⁻¹ * ∑ j : Fin p, c j * (G i ω j - muY j)) P
        = gaussianReal 0 v := by
    intro i
    have h := IsCenteredGaussianVector.map_linearCombination P (fun ω j => G i ω j - muY j)
      (covY P muY Y i) (hGaussG i) (hpsdG i) (fun j => d * b⁻¹ * c j)
    have hfun : (fun ω => ∑ j : Fin p, (d * b⁻¹ * c j) * (G i ω j - muY j))
        = (fun ω => d * b⁻¹ * ∑ j : Fin p, c j * (G i ω j - muY j)) := by
      funext ω
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hfun] at h
    exact ⟨_, h⟩
  let νF : Fin n → NNReal := fun i => Classical.choose (hFexists i)
  have hνF : ∀ i : Fin n,
      Measure.map (fun ω => a⁻¹ * ∑ j : Fin p, c j * (F i ω j - muX j)) P
        = gaussianReal 0 (νF i) := fun i => Classical.choose_spec (hFexists i)
  let νG : Fin m → NNReal := fun i => Classical.choose (hGexists i)
  have hνG : ∀ i : Fin m,
      Measure.map (fun ω => d * b⁻¹ * ∑ j : Fin p, c j * (G i ω j - muY j)) P
        = gaussianReal 0 (νG i) := fun i => Classical.choose_spec (hGexists i)
  let g : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → (Fin p → ℝ) → ℝ := fun k v =>
    match k with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl i)) => a⁻¹ * ∑ j : Fin p, c j * (v j - muX j)
    | Sum.inr (Sum.inr (Sum.inr i)) => d * b⁻¹ * ∑ j : Fin p, c j * (v j - muY j)
  let ν : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → NNReal := fun k =>
    match k with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl i)) => νF i
    | Sum.inr (Sum.inr (Sum.inr i)) => νG i
  let Yf : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → Ω → ℝ := fun k => g k ∘ jointFam X Y F G k
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    rcases k with i | (i | (i | i))
    · exact measurable_const
    · exact measurable_const
    · exact measurable_const.mul (Finset.measurable_sum Finset.univ (fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).sub measurable_const)))
    · exact measurable_const.mul (Finset.measurable_sum Finset.univ (fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).sub measurable_const)))
  have hindY : iIndepFun Yf P := hind.comp g hgm
  have hYm : ∀ k, Measurable (Yf k) := by
    intro k
    rcases k with i | (i | (i | i))
    · exact measurable_const
    · exact measurable_const
    · have h1 : Measurable (fun ω : Ω => ∑ j : Fin p, c j * (F i ω j - muX j)) :=
        Finset.measurable_sum Finset.univ (fun j _ =>
          measurable_const.mul (((measurable_pi_apply j).comp (hFm i)).sub measurable_const))
      exact measurable_const.mul h1
    · have h1 : Measurable (fun ω : Ω => ∑ j : Fin p, c j * (G i ω j - muY j)) :=
        Finset.measurable_sum Finset.univ (fun j _ =>
          measurable_const.mul (((measurable_pi_apply j).comp (hGm i)).sub measurable_const))
      exact measurable_const.mul h1
  have hYlaw : ∀ k, Measure.map (Yf k) P = gaussianReal 0 (ν k) := by
    intro k
    rcases k with i | (i | (i | i))
    · show Measure.map (fun _ : Ω => (0 : ℝ)) P = gaussianReal 0 0
      exact hzero
    · show Measure.map (fun _ : Ω => (0 : ℝ)) P = gaussianReal 0 0
      exact hzero
    · show Measure.map (fun ω : Ω => a⁻¹ * ∑ j : Fin p, c j * (F i ω j - muX j)) P
        = gaussianReal 0 (νF i)
      exact hνF i
    · show Measure.map (fun ω : Ω => d * b⁻¹ * ∑ j : Fin p, c j * (G i ω j - muY j)) P
        = gaussianReal 0 (νG i)
      exact hνG i
  have hA1 : ∀ ω : Ω, (∑ j : Fin p, c j * (a⁻¹ * ∑ i : Fin n, (F i ω j - muX j)))
      = ∑ j : Fin p, ∑ i : Fin n, c j * (a⁻¹ * (F i ω j - muX j)) := by
    intro ω
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Finset.mul_sum]
  have hA2 : ∀ ω : Ω, (∑ j : Fin p, ∑ i : Fin n, c j * (a⁻¹ * (F i ω j - muX j)))
      = ∑ i : Fin n, ∑ j : Fin p, c j * (a⁻¹ * (F i ω j - muX j)) := by
    intro ω
    exact Finset.sum_comm
  have hA3 : ∀ ω : Ω, (∑ i : Fin n, ∑ j : Fin p, c j * (a⁻¹ * (F i ω j - muX j)))
      = ∑ i : Fin n, a⁻¹ * ∑ j : Fin p, c j * (F i ω j - muX j) := by
    intro ω
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hB1 : ∀ ω : Ω, (∑ j : Fin p, c j * (d * b⁻¹ * ∑ i : Fin m, (G i ω j - muY j)))
      = ∑ j : Fin p, ∑ i : Fin m, c j * (d * b⁻¹ * (G i ω j - muY j)) := by
    intro ω
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Finset.mul_sum]
  have hB2 : ∀ ω : Ω, (∑ j : Fin p, ∑ i : Fin m, c j * (d * b⁻¹ * (G i ω j - muY j)))
      = ∑ i : Fin m, ∑ j : Fin p, c j * (d * b⁻¹ * (G i ω j - muY j)) := by
    intro ω
    exact Finset.sum_comm
  have hB3 : ∀ ω : Ω, (∑ i : Fin m, ∑ j : Fin p, c j * (d * b⁻¹ * (G i ω j - muY j)))
      = ∑ i : Fin m, (d * b⁻¹) * ∑ j : Fin p, c j * (G i ω j - muY j) := by
    intro ω
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hleft : ∀ ω : Ω, L (fun j : Fin p =>
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)
      = (∑ i : Fin n, a⁻¹ * ∑ j : Fin p, c j * (F i ω j - muX j))
        + (∑ i : Fin m, (d * b⁻¹) * ∑ j : Fin p, c j * (G i ω j - muY j)) := by
    intro ω
    have s1 : L (fun j : Fin p =>
        combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)
        = ∑ j : Fin p, (c j * (a⁻¹ * ∑ i : Fin n, (F i ω j - muX j))
            + c j * (d * b⁻¹ * ∑ i : Fin m, (G i ω j - muY j))) := by
      rw [hL]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show c j * combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j
          = c j * (a⁻¹ * ∑ i : Fin n, (F i ω j - muX j))
            + c j * (d * b⁻¹ * ∑ i : Fin m, (G i ω j - muY j))
      rw [hU' ω j, mul_add]
    rw [s1, Finset.sum_add_distrib, hA1 ω, hA2 ω, hA3 ω, hB1 ω, hB2 ω, hB3 ω]
  have hright : ∀ ω : Ω, (∑ k : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))), Yf k ω)
      = (∑ i : Fin n, a⁻¹ * ∑ j : Fin p, c j * (F i ω j - muX j))
        + (∑ i : Fin m, (d * b⁻¹) * ∑ j : Fin p, c j * (G i ω j - muY j)) := by
    intro ω
    simp only [Fintype.sum_sum_type]
    have hz1 : (∑ i : Fin n, Yf (Sum.inl i) ω) = 0 :=
      Finset.sum_eq_zero (fun i _ => rfl)
    have hz2 : (∑ i : Fin m, Yf (Sum.inr (Sum.inl i)) ω) = 0 :=
      Finset.sum_eq_zero (fun i _ => rfl)
    have hSF : (∑ i : Fin n, Yf (Sum.inr (Sum.inr (Sum.inl i))) ω)
        = ∑ i : Fin n, a⁻¹ * ∑ j : Fin p, c j * (F i ω j - muX j) :=
      Finset.sum_congr rfl (fun i _ => rfl)
    have hSG : (∑ i : Fin m, Yf (Sum.inr (Sum.inr (Sum.inr i))) ω)
        = ∑ i : Fin m, (d * b⁻¹) * ∑ j : Fin p, c j * (G i ω j - muY j) :=
      Finset.sum_congr rfl (fun i _ => rfl)
    rw [hz1, hz2, hSF, hSG]
    simp only [zero_add]
  have hsum : ∀ ω : Ω, L (fun j : Fin p =>
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)
      = ∑ k, Yf k ω := by
    intro ω
    rw [hleft ω]
    exact (hright ω).symm
  have hU'fun : (fun ω : Ω => fun j : Fin p =>
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)
      = fun ω j => a⁻¹ * (∑ i : Fin n, (F i ω j - muX j))
          + (d * b⁻¹) * (∑ i : Fin m, (G i ω j - muY j)) := by
    funext ω j
    exact hU' ω j
  have hU'm : Measurable (fun ω : Ω => fun j : Fin p =>
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) := by
    rw [hU'fun]
    refine measurable_pi_iff.mpr (fun j => ?_)
    exact (measurable_const.mul (Finset.measurable_sum Finset.univ (fun i _ =>
      ((measurable_pi_apply j).comp (hFm i)).sub measurable_const))).add
      (measurable_const.mul (Finset.measurable_sum Finset.univ (fun i _ =>
      ((measurable_pi_apply j).comp (hGm i)).sub measurable_const)))
  refine ⟨0, ∑ k, ν k, ?_⟩
  rw [Measure.map_map L.continuous.measurable hU'm]
  change Measure.map (fun ω : Ω => L (fun j : Fin p =>
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j)) P
    = gaussianReal 0 (∑ k, ν k)
  rw [show (fun ω : Ω => L (fun j : Fin p =>
      combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j))
      = (fun ω => ∑ k, Yf k ω) from funext hsum]
  exact kernel ν Yf hindY hYm hYlaw
  /- @proof-region region.target-node.session.847ece2df6d0e60d end -/

end

end Statlib.Imported

