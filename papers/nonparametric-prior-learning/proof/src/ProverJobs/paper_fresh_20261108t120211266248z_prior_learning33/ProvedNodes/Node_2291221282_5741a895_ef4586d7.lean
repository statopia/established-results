import Statlib.StatFoundation.Convergence.AnalysisTools.ConvergenceModes
import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2291221282_5741a895 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (μ : Measure U) [IsProbabilityMeasure μ]
    (mUM mNU : U)
    (hsum : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))
    (hae : ∀ᵐ u ∂μ,
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) atTop
        (𝓝 (∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))))
    (hfin : ∀ n : ℕ,
      Measure.map (fun u : U =>
          ∑ k : {k : ℕ // k ∈ Finset.range n},
            ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM)) * (inner ℝ (e k) u - inner ℝ (e k) mUM)) μ
        = ProbabilityTheory.gaussianReal 0
            (Real.toNNReal (∑ k : {k : ℕ // k ∈ Finset.range n},
              ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM)) ^ 2 * c k))),
    Measure.map (fun u : U =>
        ∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) μ
      = ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) := by
  /- @proof-region region.target-node.session.5c4efc10ce35c5bc begin -/
  intro U _ _ _ _ _ _ e c μ _ mUM mNU hsum hae hfin
  classical
  set b : ℕ → ℝ := fun k => inner ℝ (e k) (mNU - mUM) with hb
  set a : ℕ → ℝ := fun k => (c k)⁻¹ * b k with ha
  set Zn : ℕ → U → ℝ := fun n u => ∑ k ∈ Finset.range n, a k * inner ℝ (e k) (u - mUM) with hZn
  set Z : U → ℝ := fun u => ∑' k : ℕ, a k * inner ℝ (e k) (u - mUM) with hZ
  set vn : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, (c k)⁻¹ * (b k) ^ 2 with hvn
  set v : ℝ := ∑' k : ℕ, (c k)⁻¹ * (b k) ^ 2 with hv
  have hterm : ∀ x y : ℝ, (x⁻¹ * y) ^ 2 * x = x⁻¹ * y ^ 2 := by
    intro x y
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    · field_simp
  have hconv : ∀ (n : ℕ) (f : ℕ → ℝ),
      (∑ k : {k : ℕ // k ∈ Finset.range n}, f k) = ∑ k ∈ Finset.range n, f k := by
    intro n f
    exact Finset.sum_attach (Finset.range n) f
  have hZn_cont : ∀ n : ℕ, Continuous (Zn n) := by
    intro n
    rw [hZn]
    fun_prop
  have hZn_meas : ∀ n : ℕ, Measurable (Zn n) := fun n => (hZn_cont n).measurable
  have hmap_n : ∀ n : ℕ, Measure.map (Zn n) μ = gaussianReal 0 (Real.toNNReal (vn n)) := by
    intro n
    have hfun : (fun u : U =>
        ∑ k : {k : ℕ // k ∈ Finset.range n},
          ((c k)⁻¹ * b k) * (inner ℝ (e k) u - inner ℝ (e k) mUM)) = Zn n := by
      funext u
      simp only [hZn]
      rw [hconv n (fun j => ((c j)⁻¹ * b j) * (inner ℝ (e j) u - inner ℝ (e j) mUM))]
      simp only [inner_sub_right, ha]
    have hvar : (∑ k : {k : ℕ // k ∈ Finset.range n}, ((c k)⁻¹ * b k) ^ 2 * c k) = vn n := by
      rw [hconv n (fun j => ((c j)⁻¹ * b j) ^ 2 * c j), hvn]
      exact Finset.sum_congr rfl (fun k _ => hterm (c k) (b k))
    rw [← hfun, ← hvar]
    exact hfin n
  have hvn_tendsto : Tendsto vn atTop (𝓝 v) := by
    simpa only [hvn, hv, hb] using hsum.hasSum.tendsto_sum_nat
  have hZ_ae : AEMeasurable Z μ := by
    refine Statlib.StatFoundation.Convergence.tendstoInMeasure_aemeasurable
      (f := fun n : ℕ => Zn n) (g := Z) (u := atTop) ?_ ?_
    · intro n
      exact (hZn_meas n).aemeasurable
    · exact MeasureTheory.tendstoInMeasure_of_tendsto_ae (f := fun n : ℕ => Zn n) (g := Z)
        (fun n => (hZn_meas n).aestronglyMeasurable) hae
  have hchar : ∀ t : ℝ, charFun (Measure.map Z μ) t = charFun (gaussianReal 0 (Real.toNNReal v)) t := by
    intro t
    have hg_cont : Continuous fun x : ℝ => Complex.exp (↑(inner ℝ t x) * Complex.I) := by fun_prop
    have hswap_pt : ∀ y : ℝ, Complex.exp (↑(inner ℝ y t) * Complex.I)
        = Complex.exp (↑(inner ℝ t y) * Complex.I) := by
      intro y
      rw [real_inner_comm y t]
    have hcf_eq : ∀ ν : Measure ℝ,
        charFun ν t = ∫ y : ℝ, Complex.exp (↑(inner ℝ t y) * Complex.I) ∂ν := by
      intro ν
      unfold charFun
      first
        | rfl
        | rw [show (∫ y : ℝ, Complex.exp (↑(inner ℝ y t) * Complex.I) ∂ν)
              = ∫ y : ℝ, Complex.exp (↑(inner ℝ t y) * Complex.I) ∂ν from
              integral_congr_ae (Filter.Eventually.of_forall hswap_pt)]
    have hInt_n : ∀ n : ℕ,
        ∫ u, Complex.exp (↑(inner ℝ t (Zn n u)) * Complex.I) ∂μ
          = charFun (gaussianReal 0 (Real.toNNReal (vn n))) t := by
      intro n
      rw [← hmap_n n, hcf_eq]
      exact (MeasureTheory.integral_map (μ := μ) (φ := Zn n)
        (f := fun y : ℝ => Complex.exp (↑(inner ℝ t y) * Complex.I))
        (hZn_meas n).aemeasurable (hg_cont.measurable.aestronglyMeasurable)).symm
    have hstep : ∀ n : ℕ,
        ∫ u, Complex.exp (↑(inner ℝ t (Zn n u)) * Complex.I) ∂μ
          = Complex.exp ((↑t : ℂ) * (↑(0 : ℝ) : ℂ) * Complex.I
              - ((Real.toNNReal (vn n) : ℝ) : ℂ) * (↑t : ℂ) ^ 2 / 2) := by
      intro n
      rw [hInt_n n, charFun_gaussianReal]
    have hDCT : Tendsto (fun n => ∫ u, Complex.exp (↑(inner ℝ t (Zn n u)) * Complex.I) ∂μ) atTop
        (𝓝 (∫ u, Complex.exp (↑(inner ℝ t (Z u)) * Complex.I) ∂μ)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (F := fun (n : ℕ) (u : U) => Complex.exp (↑(inner ℝ t (Zn n u)) * Complex.I))
        (f := fun u : U => Complex.exp (↑(inner ℝ t (Z u)) * Complex.I))
        (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
      · intro n
        exact ((hg_cont.comp (hZn_cont n)).measurable).aestronglyMeasurable
      · exact integrable_const 1
      · intro n
        filter_upwards with u
        simp [Complex.norm_exp]
      · filter_upwards [hae] with u hu
        exact hg_cont.tendsto (Z u) |>.comp hu
    have hlim : Tendsto (fun n => Complex.exp ((↑t : ℂ) * (↑(0 : ℝ) : ℂ) * Complex.I
          - ((Real.toNNReal (vn n) : ℝ) : ℂ) * (↑t : ℂ) ^ 2 / 2)) atTop
        (𝓝 (∫ u, Complex.exp (↑(inner ℝ t (Z u)) * Complex.I) ∂μ)) := by
      simpa only [hstep] using hDCT
    have hcoe : ∀ x : ℝ, ((Real.toNNReal x : NNReal) : ℝ) = max x 0 := by
      intro x
      unfold Real.toNNReal
      first
        | rfl
        | (split_ifs with h
           · simp [max_eq_left h]
           · simp [max_eq_right (le_of_lt (not_le.mp h))])
        | simp
    have hargcont : Continuous fun w : ℝ => Complex.exp ((↑t : ℂ) * (↑(0 : ℝ) : ℂ) * Complex.I
        - (w : ℂ) * (↑t : ℂ) ^ 2 / 2) :=
      Complex.continuous_exp.comp
        (continuous_const.sub ((Complex.continuous_ofReal.mul continuous_const).div_const 2))
    have hmax : Tendsto (fun n => max (vn n) 0) atTop (𝓝 (max v 0)) := by
      have hcont : Continuous fun w : ℝ => max w 0 := continuous_id.max continuous_const
      exact hcont.tendsto v |>.comp hvn_tendsto
    have hRHS : Tendsto (fun n => Complex.exp ((↑t : ℂ) * (↑(0 : ℝ) : ℂ) * Complex.I
          - ((Real.toNNReal (vn n) : ℝ) : ℂ) * (↑t : ℂ) ^ 2 / 2)) atTop
        (𝓝 (Complex.exp ((↑t : ℂ) * (↑(0 : ℝ) : ℂ) * Complex.I
          - ((Real.toNNReal v : ℝ) : ℂ) * (↑t : ℂ) ^ 2 / 2))) := by
      have h := hargcont.tendsto (max v 0) |>.comp hmax
      simpa only [hcoe] using h
    have hkey : ∫ u, Complex.exp (↑(inner ℝ t (Z u)) * Complex.I) ∂μ
        = Complex.exp ((↑t : ℂ) * (↑(0 : ℝ) : ℂ) * Complex.I
            - ((Real.toNNReal v : ℝ) : ℂ) * (↑t : ℂ) ^ 2 / 2) :=
      tendsto_nhds_unique hlim hRHS
    have hcharZ : charFun (Measure.map Z μ) t
        = ∫ u, Complex.exp (↑(inner ℝ t (Z u)) * Complex.I) ∂μ := by
      rw [hcf_eq]
      exact (MeasureTheory.integral_map (μ := μ) (φ := Z)
        (f := fun y : ℝ => Complex.exp (↑(inner ℝ t y) * Complex.I))
        hZ_ae (hg_cont.measurable.aestronglyMeasurable))
    rw [hcharZ, hkey, charFun_gaussianReal]
  haveI : IsProbabilityMeasure (Measure.map Z μ) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hZ_ae
  exact MeasureTheory.Measure.ext_of_charFun (funext fun t => hchar t)
  /- @proof-region region.target-node.session.5c4efc10ce35c5bc end -/

end Statlib.Imported
end

