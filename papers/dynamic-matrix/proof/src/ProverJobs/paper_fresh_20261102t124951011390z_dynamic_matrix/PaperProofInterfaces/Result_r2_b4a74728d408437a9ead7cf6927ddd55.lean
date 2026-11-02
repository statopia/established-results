import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

theorem Theorem_1_thm_error_bound_corrected_general_positive_definite_design_error_bound_with_explicit_kappa_Sigma_smoothing_bia
    (m1 m2 T : ℕ) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (t : Fin T) (n : Fin T → ℕ) (hn : ∀ j, 0 < n j)
    (Sigma : Matrix (Fin m1 × Fin m2) (Fin m1 × Fin m2) ℝ) (hSigma : Sigma.PosDef)
    (mu kappa : ℝ)
    
    (hmu : mu = lamMin hSigma.isHermitian.eigenvalues)
    (hmu_pos : 0 < mu)
    
    (hkappa : kappa = lamMax hSigma.isHermitian.eigenvalues / mu)
    (hkappa_ge : 1 ≤ kappa)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (j : Fin T) → Fin (n j) → Ω → Matrix (Fin m1) (Fin m2) ℝ)
    (hX_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (X j i))
    (xi : (j : Fin T) → Fin (n j) → Ω → ℝ)
    (hxi_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (xi j i))
    (M0 : Fin T → Matrix (Fin m1) (Fin m2) ℝ)
    (Y : (j : Fin T) → Fin (n j) → Ω → ℝ)
    
    (hY : ∀ (j : Fin T) (i : Fin (n j)) (ω : Ω),
      Y j i ω = frobInner (M0 j) (X j i ω) + xi j i ω)
    
    (hX2 : ∀ (j : Fin T) (i : Fin (n j)),
      Integrable (fun ω => frobNorm (X j i ω) ^ 2) P)
    
    (hXi : ∀ (j : Fin T) (i : Fin (n j)),
      Integrable (fun ω => |xi j i ω| * frobNorm (X j i ω)) P)
    
    (hXi_zero : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      ∫ ω, xi j i ω * (X j i ω) a b ∂P = 0)
    
    (hXi_int : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      Integrable (fun ω => xi j i ω * (X j i ω) a b) P)
    
    (hYX_int : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      Integrable (fun ω => Y j i ω * (X j i ω) a b) P)
    (hq_int : ∀ (j : Fin T) (M : Matrix (Fin m1) (Fin m2) ℝ) (i : Fin (n j)),
      Integrable (fun ω => frobInner M (X j i ω) ^ 2) P)
    
    (hDesign : ∀ (j : Fin T) (M : Matrix (Fin m1) (Fin m2) ℝ),
      (1 / (n j : ℝ)) * ∑ i : Fin (n j), ∫ ω, frobInner M (X j i ω) ^ 2 ∂P
        = secondMomentForm Sigma M)
    
    (w : Fin T → ℝ) (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_sum : ∑ j : Fin T, w j = 1)
    
    (Mset : Set (Matrix (Fin m1) (Fin m2) ℝ))
    (hMne : Mset.Nonempty) (hMclosed : IsClosed Mset) (hMconv : Convex ℝ Mset)
    (hM0mem : M0 t ∈ Mset)
    
    (Mtilde : ℝ → Ω → Matrix (Fin m1) (Fin m2) ℝ)
    
    (hMtilde_mem : ∀ (lam : ℝ) (ω : Ω), Mtilde lam ω ∈ Mset)
    (hMtilde : ∀ (lam : ℝ) (ω : Ω),
      IsMinOn (fun M => localObj Sigma P n Y X w lam M ω) Mset (Mtilde lam ω))
    (lam : ℝ) :
    (∀ ω : Ω, 2 * WDelta P n Y X w ω ≤ lam →
      frobNorm (Mtilde lam ω - M0 t) ≤
        kappa * biasH M0 w t +
          min
            (Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
              (2 * lam / mu) * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)))
            ((1 + Real.sqrt 2) / 2 * (lam / mu) *
              Real.sqrt ((Matrix.rank (M0 t) : ℝ)))) ∧
    (∀ ω : Ω,
      frobNorm (Mtilde (2 * WDelta P n Y X w ω) ω - M0 t) ≤
        kappa * biasH M0 w t +
          min
            (Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
              (2 * WDelta P n Y X w ω / mu) * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)))
            ((1 + Real.sqrt 2) * (WDelta P n Y X w ω / mu) *
              Real.sqrt ((Matrix.rank (M0 t) : ℝ))))
:= by
  /- @proof-region region.root.b3a2059eb30e begin -/
  have key : ∀ (b c e : ℝ), 0 ≤ b → 0 ≤ c → e ^ 2 - b * e ≤ c →
      e ≤ b + Real.sqrt (b ^ 2 + 2 * c) ∧ e ≤ b + Real.sqrt (b ^ 2 + c) := by
    intro b c e hb hc hmain
    have hsq : (e - b / 2) ^ 2 ≤ c + b ^ 2 / 4 := by nlinarith [hmain]
    have hle : e - b / 2 ≤ Real.sqrt (c + b ^ 2 / 4) := by
      have h := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq_eq_abs] at h
      exact le_trans (le_abs_self _) h
    have e1 : e ≤ b / 2 + Real.sqrt (c + b ^ 2 / 4) := by linarith
    have hb2 : b / 2 ≤ b := by linarith
    have hsq2 : b ^ 2 / 4 ≤ b ^ 2 := by linarith [sq_nonneg b]
    have hs1 : Real.sqrt (c + b ^ 2 / 4) ≤ Real.sqrt (b ^ 2 + 2 * c) :=
      Real.sqrt_le_sqrt (by linarith)
    have hs2 : Real.sqrt (c + b ^ 2 / 4) ≤ Real.sqrt (b ^ 2 + c) :=
      Real.sqrt_le_sqrt (by linarith)
    constructor <;> linarith
  constructor
  · intro ω hlam
    have hslow := statopia_math_node_1468296047_3d04a208 m1 m2 T hm1 hm2 t n hn
      Sigma hSigma mu kappa hmu hmu_pos hkappa hkappa_ge P X hX_m xi hxi_m M0 Y hY
      hX2 hXi hXi_zero hXi_int hYX_int hq_int hDesign w hw_nonneg hw_sum Mset hMne
      hMconv hM0mem Mtilde hMtilde_mem hMtilde lam ω hlam
    have hrank := statopia_math_node_975363148_a48ae5fa m1 m2 T hm1 hm2 t n hn
      Sigma hSigma mu kappa hmu hmu_pos hkappa hkappa_ge P X hX_m xi hxi_m M0 Y hY
      hX2 hXi hXi_zero hXi_int hYX_int hq_int hDesign w hw_nonneg hw_sum Mset hMne
      hMclosed hMconv hM0mem Mtilde hMtilde_mem hMtilde lam ω hlam
    have hW : 0 ≤ WDelta P n Y X w ω := by
      unfold WDelta
      exact Statlib.HighDim.MatrixAnalysis.opNorm_nonneg _
    have hlam0 : 0 ≤ lam := by linarith
    have hb : 0 ≤ kappa * biasH M0 w t := by
      have h1 : (0 : ℝ) ≤ kappa := by linarith
      have h2 : 0 ≤ biasH M0 w t := by
        unfold biasH
        exact Real.sqrt_nonneg _
      exact mul_nonneg h1 h2
    have hN : 0 ≤ Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) :=
      (Statlib.HighDim.MatrixAnalysis.nuclearNorm_nonneg (M0 t)).1
    have hc : 0 ≤ lam * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) / mu :=
      div_nonneg (mul_nonneg hlam0 hN) (le_of_lt hmu_pos)
    have hk := key (kappa * biasH M0 w t)
      (lam * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) / mu)
      (frobNorm (Mtilde lam ω - M0 t)) hb hc hslow
    have hA : frobNorm (Mtilde lam ω - M0 t) ≤
        kappa * biasH M0 w t +
          Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
            (2 * lam / mu) * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)) := by
      have hEq : 2 * (lam * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) / mu)
          = (2 * lam / mu) * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) := by ring
      calc frobNorm (Mtilde lam ω - M0 t)
          ≤ kappa * biasH M0 w t +
              Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
                2 * (lam * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) / mu)) := hk.1
        _ = kappa * biasH M0 w t +
              Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
                (2 * lam / mu) * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)) := by rw [hEq]
    have hB : frobNorm (Mtilde lam ω - M0 t) ≤
        kappa * biasH M0 w t +
          ((1 + Real.sqrt 2) / 2 * (lam / mu) *
            Real.sqrt ((Matrix.rank (M0 t) : ℝ))) := hrank
    rcases le_total
        (Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
          (2 * lam / mu) * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)))
        ((1 + Real.sqrt 2) / 2 * (lam / mu) *
          Real.sqrt ((Matrix.rank (M0 t) : ℝ))) with h | h
    · rw [min_eq_left h]
      exact hA
    · rw [min_eq_right h]
      exact hB
  · intro ω
    have hslow := statopia_math_node_1468296047_3d04a208 m1 m2 T hm1 hm2 t n hn
      Sigma hSigma mu kappa hmu hmu_pos hkappa hkappa_ge P X hX_m xi hxi_m M0 Y hY
      hX2 hXi hXi_zero hXi_int hYX_int hq_int hDesign w hw_nonneg hw_sum Mset hMne
      hMconv hM0mem Mtilde hMtilde_mem hMtilde (2 * WDelta P n Y X w ω) ω (le_refl _)
    have hrank := statopia_math_node_975363148_a48ae5fa m1 m2 T hm1 hm2 t n hn
      Sigma hSigma mu kappa hmu hmu_pos hkappa hkappa_ge P X hX_m xi hxi_m M0 Y hY
      hX2 hXi hXi_zero hXi_int hYX_int hq_int hDesign w hw_nonneg hw_sum Mset hMne
      hMclosed hMconv hM0mem Mtilde hMtilde_mem hMtilde (2 * WDelta P n Y X w ω) ω (le_refl _)
    have hW : 0 ≤ WDelta P n Y X w ω := by
      unfold WDelta
      exact Statlib.HighDim.MatrixAnalysis.opNorm_nonneg _
    have hb : 0 ≤ kappa * biasH M0 w t := by
      have h1 : (0 : ℝ) ≤ kappa := by linarith
      have h2 : 0 ≤ biasH M0 w t := by
        unfold biasH
        exact Real.sqrt_nonneg _
      exact mul_nonneg h1 h2
    have hN : 0 ≤ Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) :=
      (Statlib.HighDim.MatrixAnalysis.nuclearNorm_nonneg (M0 t)).1
    have hc : 0 ≤ (2 * WDelta P n Y X w ω) *
        Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) / mu :=
      div_nonneg (mul_nonneg (by linarith) hN) (le_of_lt hmu_pos)
    have hk := key (kappa * biasH M0 w t)
      ((2 * WDelta P n Y X w ω) * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) / mu)
      (frobNorm (Mtilde (2 * WDelta P n Y X w ω) ω - M0 t)) hb hc hslow
    have hA : frobNorm (Mtilde (2 * WDelta P n Y X w ω) ω - M0 t) ≤
        kappa * biasH M0 w t +
          Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
            (2 * WDelta P n Y X w ω / mu) *
              Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)) := by
      have hEq : (2 * WDelta P n Y X w ω) *
            Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) / mu
          = (2 * WDelta P n Y X w ω / mu) *
            Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) := by ring
      calc frobNorm (Mtilde (2 * WDelta P n Y X w ω) ω - M0 t)
          ≤ kappa * biasH M0 w t +
              Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
                (2 * WDelta P n Y X w ω) *
                  Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) / mu) := hk.2
        _ = kappa * biasH M0 w t +
              Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
                (2 * WDelta P n Y X w ω / mu) *
                  Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)) := by rw [hEq]
    have hB : frobNorm (Mtilde (2 * WDelta P n Y X w ω) ω - M0 t) ≤
        kappa * biasH M0 w t +
          ((1 + Real.sqrt 2) * (WDelta P n Y X w ω / mu) *
            Real.sqrt ((Matrix.rank (M0 t) : ℝ))) := by
      have hEq : ((1 + Real.sqrt 2) / 2) * ((2 * WDelta P n Y X w ω) / mu) *
            Real.sqrt ((Matrix.rank (M0 t) : ℝ))
          = (1 + Real.sqrt 2) * (WDelta P n Y X w ω / mu) *
            Real.sqrt ((Matrix.rank (M0 t) : ℝ)) := by ring
      calc frobNorm (Mtilde (2 * WDelta P n Y X w ω) ω - M0 t)
          ≤ kappa * biasH M0 w t +
              ((1 + Real.sqrt 2) / 2) * ((2 * WDelta P n Y X w ω) / mu) *
                Real.sqrt ((Matrix.rank (M0 t) : ℝ)) := hrank
        _ = kappa * biasH M0 w t +
              ((1 + Real.sqrt 2) * (WDelta P n Y X w ω / mu) *
                Real.sqrt ((Matrix.rank (M0 t) : ℝ))) := by rw [hEq]
    rcases le_total
        (Real.sqrt ((kappa * biasH M0 w t) ^ 2 +
          (2 * WDelta P n Y X w ω / mu) *
            Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)))
        ((1 + Real.sqrt 2) * (WDelta P n Y X w ω / mu) *
          Real.sqrt ((Matrix.rank (M0 t) : ℝ))) with h | h
    · rw [min_eq_left h]
      exact hA
    · rw [min_eq_right h]
      exact hB
  /- @proof-region region.root.b3a2059eb30e end -/

end Statlib.Imported

-- Paper root revision 5518f816-5a99-4045-a87d-f2a7958b24fc

