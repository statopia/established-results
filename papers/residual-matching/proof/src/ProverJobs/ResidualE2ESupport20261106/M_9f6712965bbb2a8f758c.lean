import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_489da0ccea6cf497f853

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_817079420_981e1edb : ∀ (m n : ℕ) (hnm : n ≤ m)
    (OmF : Matrix (Fin m) (Fin n) ℝ)
    (μG : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure μG]
    (hgauss : IsStdGaussianMatrixLaw μG),
    ∀ i : Fin n,
      Integrable (fun A : Matrix (Fin m) (Fin n) ℝ =>
        sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i) μG := by
  /- @proof-region region.target-node.session.e9e7598c8d151bcf begin -/
  intro m n hnm OmF muG hprob hgauss i
  haveI := hprob
  have qA : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) := by
    have h := (MeasureTheory.memLp_one_iff_integrable).mp
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 1)
    simpa using h
  have qC : ∀ (a : Fin m) (b : Fin n), Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => A a b) muG := by
    intro a b
    have hmeas : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => A a b) :=
      (measurable_pi_apply b).comp (measurable_pi_apply a)
    have hmap : muG.map (fun A : Matrix (Fin m) (Fin n) ℝ => A a b) = gaussianReal 0 1 :=
      hgauss.1 a b
    exact MeasureTheory.Integrable.comp_measurable (hmap.symm ▸ qA) hmeas
  have pC : ∀ X : Matrix (Fin m) (Fin n) ℝ,
      Statlib.HighDim.MatrixAnalysis.opNorm X ≤ ∑ a, ∑ b, |X a b| :=
    statopia_math_node_3319165159_31a3e20a m n
  have habs : ∀ (a : Fin m) (b : Fin n),
      Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => |A a b|) muG := by
    intro a b
    first
      | exact (qC a b).norm
      | (simpa [Real.norm_eq_abs] using (qC a b).norm)
  have hsum : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => ∑ a, ∑ b, |A a b|) muG := by
    have hrow : ∀ a : Fin m,
        Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => ∑ b, |A a b|) muG := by
      intro a
      first
        | exact integrable_finset_sum _ (fun b _ => habs a b)
        | exact integrable_finset_sum (fun b _ => habs a b)
    first
      | exact integrable_finset_sum _ (fun a _ => hrow a)
      | exact integrable_finset_sum (fun a _ => hrow a)
  have hmaj : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (0 : Matrix (Fin m) (Fin n) ℝ))) i|
        + ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * ∑ a, ∑ b, |A a b|) muG := by
    have hconst : Integrable (fun _ : Matrix (Fin m) (Fin n) ℝ =>
        |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (0 : Matrix (Fin m) (Fin n) ℝ))) i|) muG :=
      integrable_const _
    exact hconst.add (hsum.const_mul _)
  have hS : ∀ (a : Fin m) (b : Fin n), |OmF a b| ≤ ∑ a, ∑ b, |OmF a b| := by
    intro a b
    have h1 : |OmF a b| ≤ ∑ b', |OmF a b'| :=
      Finset.single_le_sum (f := fun b' => |OmF a b'|) (fun i _ => abs_nonneg _) (Finset.mem_univ b)
    have h2 : (∑ b', |OmF a b'|) ≤ ∑ a', ∑ b', |OmF a' b'| :=
      Finset.single_le_sum (f := fun a' => ∑ b', |OmF a' b'|)
        (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ a)
    exact le_trans h1 h2
  have hweyl : ∀ (P Q : Matrix (Fin m) (Fin n) ℝ),
      sv hnm P i ≤ sv hnm Q i + Statlib.HighDim.MatrixAnalysis.opNorm (P - Q) := by
    intro P Q
    show Statlib.HighDim.MatrixAnalysis.singularValues P (Fin.castLE (le_min hnm le_rfl) i)
        ≤ Statlib.HighDim.MatrixAnalysis.singularValues Q (Fin.castLE (le_min hnm le_rfl) i)
          + Statlib.HighDim.MatrixAnalysis.opNorm (P - Q)
    have h := Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper Q (P - Q)
      (Fin.castLE (le_min hnm le_rfl) i)
    have hPQ : Q + (P - Q) = P := by abel
    rwa [hPQ] at h
  have hstep : ∀ D : Matrix (Fin m) (Fin n) ℝ,
      Statlib.HighDim.MatrixAnalysis.opNorm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • D))
        ≤ ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * ∑ a, ∑ b, |D a b| := by
    intro D
    refine le_trans (pC (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • D))) ?_
    calc ∑ a, ∑ b, |(maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • D)) a b|
        = ∑ a, ∑ b, |OmF a b| * |(Real.sqrt (m : ℝ))⁻¹| * |D a b| := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
          first
            | (simp only [maskOp, Matrix.smul_apply, smul_eq_mul, abs_mul]; ring)
            | (simp only [maskOp, Pi.smul_apply, smul_eq_mul, abs_mul]; ring)
            | (show |OmF a b * ((Real.sqrt (m : ℝ))⁻¹ * D a b)|
                  = |OmF a b| * |(Real.sqrt (m : ℝ))⁻¹| * |D a b|; rw [abs_mul, abs_mul]; ring)
      _ ≤ ∑ a, ∑ b, ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * |D a b| := by
          refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hS a b) (abs_nonneg _)) (abs_nonneg _)
      _ = ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * ∑ a, ∑ b, |D a b| := by
          simp only [Finset.mul_sum]
  have hdiff : ∀ A A' : Matrix (Fin m) (Fin n) ℝ,
      maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A) - maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A')
        = maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (A - A')) := by
    intro A A'
    ext a b
    first
      | (simp only [maskOp, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring)
      | (simp only [maskOp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
      | (show OmF a b * ((Real.sqrt (m : ℝ))⁻¹ * A a b)
              - OmF a b * ((Real.sqrt (m : ℝ))⁻¹ * A' a b)
              = OmF a b * ((Real.sqrt (m : ℝ))⁻¹ * (A a b - A' a b)); ring)
  have hbd : ∀ A A' : Matrix (Fin m) (Fin n) ℝ,
      |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i
        - sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A')) i|
        ≤ ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * ∑ a, ∑ b, |A a b - A' a b| := by
    intro A A'
    have hPQ := hweyl (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A))
      (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A'))
    have hQP := hweyl (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A'))
      (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A))
    rw [hdiff A A'] at hPQ
    rw [hdiff A' A] at hQP
    have h1 : Statlib.HighDim.MatrixAnalysis.opNorm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (A - A')))
        ≤ ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * ∑ a, ∑ b, |A a b - A' a b| :=
      hstep (A - A')
    have h2 : Statlib.HighDim.MatrixAnalysis.opNorm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (A' - A)))
        ≤ ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * ∑ a, ∑ b, |A a b - A' a b| := by
      have hb := hstep (A' - A)
      have hswap : (∑ a, ∑ b, |(A' - A) a b|) = ∑ a, ∑ b, |A a b - A' a b| := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        first
          | (simp only [Matrix.sub_apply, abs_sub_comm])
          | (simp only [Pi.sub_apply, abs_sub_comm])
          | (show |A' a b - A a b| = |A a b - A' a b|; rw [abs_sub_comm])
      rwa [hswap] at hb
    rw [abs_le]
    constructor <;> linarith [hPQ, hQP, h1, h2]
  have hpt : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i|
        ≤ |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (0 : Matrix (Fin m) (Fin n) ℝ))) i|
          + ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * ∑ a, ∑ b, |A a b| := by
    intro A
    have h := hbd A 0
    have hz : (∑ a, ∑ b, |A a b - (0 : Matrix (Fin m) (Fin n) ℝ) a b|) = ∑ a, ∑ b, |A a b| := by
      simp
    rw [hz] at h
    have h3 : |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i|
        ≤ |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i
            - sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (0 : Matrix (Fin m) (Fin n) ℝ))) i|
          + |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (0 : Matrix (Fin m) (Fin n) ℝ))) i| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i
            - sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (0 : Matrix (Fin m) (Fin n) ℝ))) i),
          neg_abs_le (sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (0 : Matrix (Fin m) (Fin n) ℝ))) i)]
      · linarith [le_abs_self (sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i
            - sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (0 : Matrix (Fin m) (Fin n) ℝ))) i),
          le_abs_self (sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (0 : Matrix (Fin m) (Fin n) ℝ))) i)]
    linarith
  have hcont : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ =>
      sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i) := by
    rw [continuous_iff_continuousAt]
    intro A₀
    have hcoord : ∀ (a : Fin m) (b : Fin n),
        Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => A a b) := by
      intro a b
      first
        | exact (continuous_apply b).comp (continuous_apply a)
        | fun_prop
    have hgc : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => ∑ a, ∑ b, |A a b - A₀ a b|) := by
      first
        | fun_prop
        | (refine continuous_finset_sum _ (fun a _ => continuous_finset_sum _ (fun b _ => ?_))
           exact ((hcoord a b).sub continuous_const).abs)
    have hg : Filter.Tendsto (fun A : Matrix (Fin m) (Fin n) ℝ => ∑ a, ∑ b, |A a b - A₀ a b|)
        (nhds A₀) (nhds 0) := by
      have h0 : (∑ a, ∑ b, |A₀ a b - A₀ a b|) = 0 := by simp
      have h := hgc.tendsto A₀
      rwa [h0] at h
    have hle : ∀ A : Matrix (Fin m) (Fin n) ℝ,
        |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i
          - sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A₀)) i|
        ≤ ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * ∑ a, ∑ b, |A a b - A₀ a b| :=
      fun A => hbd A A₀
    have hmul : Filter.Tendsto (fun A : Matrix (Fin m) (Fin n) ℝ =>
        ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|) * ∑ a, ∑ b, |A a b - A₀ a b|)
        (nhds A₀) (nhds 0) := by
      have h := hg.const_mul ((∑ a, ∑ b, |OmF a b|) * |(Real.sqrt (m : ℝ))⁻¹|)
      simpa using h
    have hsq : Filter.Tendsto (fun A : Matrix (Fin m) (Fin n) ℝ =>
        |sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i
          - sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A₀)) i|) (nhds A₀) (nhds 0) :=
      squeeze_zero (fun A => abs_nonneg _) (fun A => hle A) hmul
    have hdiff : Filter.Tendsto (fun A : Matrix (Fin m) (Fin n) ℝ =>
        sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i
          - sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A₀)) i) (nhds A₀) (nhds 0) := by
      first
        | exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hsq)
        | exact tendsto_zero_iff_abs_tendsto_zero.mp hsq
        | exact tendsto_zero_iff_norm_tendsto_zero.mp hsq
    have hfin := hdiff.add_const (sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A₀)) i)
    simpa using hfin
  have hmeas : AEStronglyMeasurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i) muG := by
    first
      | exact hcont.measurable.aestronglyMeasurable
      | exact hcont.aestronglyMeasurable
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards with A
  simpa only [Real.norm_eq_abs] using hpt A
  /- @proof-region region.target-node.session.e9e7598c8d151bcf end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_817079420_981e1edb


