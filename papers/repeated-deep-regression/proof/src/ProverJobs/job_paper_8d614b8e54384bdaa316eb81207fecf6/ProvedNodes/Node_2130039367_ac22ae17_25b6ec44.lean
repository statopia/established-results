import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_1156518618_e13ca37b_de059a44
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ExternalNodes.Node_6515c10a3b2a6920f75d

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6


open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open _root_.PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
noncomputable section
set_option maxHeartbeats 1000000

set_option autoImplicit false in
theorem statopia_math_node_2130039367_ac22ae17 : ∀ (S : Type*) [MeasurableSpace S]
    (Rand : Type*) [MeasurableSpace Rand]
    (P : Measure Rand) [IsProbabilityMeasure P]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (B1 : ℝ) (hB1 : 0 < B1)
    (f0 : S → ℝ) (X : Fin n → Fin m → Rand → S)
    (sigma : Fin n → Fin m → Rand → ℝ)
    (Fs : Finset (S → ℝ))
    (hf0_meas : Measurable f0)
    (hFs_meas : ∀ f ∈ (Fs : Set (S → ℝ)), Measurable f)
    (hf0_bound : ∀ x : S, |f0 x| ≤ B1)
    (hFs_bound : ∀ f ∈ (Fs : Set (S → ℝ)), ∀ x : S, |f x| ≤ B1)
    (hX_meas : ∀ p : Fin n × Fin m, Measurable (X p.1 p.2))
    (hsigma_meas : ∀ p : Fin n × Fin m, Measurable (sigma p.1 p.2))
    (hsigma_law : ∀ p : Fin n × Fin m,
      Measure.map (sigma p.1 p.2) P = Statlib.Imported.rademacherLaw)
    (hsigma_indep : iIndepFun (fun p : Fin n × Fin m => sigma p.1 p.2) P)
    (hsigma_indep_X :
      IndepFun (fun ω => fun p : Fin n × Fin m => sigma p.1 p.2 ω)
        (fun ω => fun p : Fin n × Fin m => X p.1 p.2 ω) P),
    ∫ ω, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) '' (Fs : Set (S → ℝ))) ∂P
      ≤ 8 * B1 * ∫ ω, sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω))|) '' (Fs : Set (S → ℝ))) ∂P := by
  /- @proof-region region.target-node.session.5c58d0485df39824 begin -/
  intro S _instS Rand _instRand P _instP n m hn hm B1 hB1 f0 X sigma Fs
  intro hf0_meas hFs_meas hf0_bound hFs_bound hX_meas hsigma_meas hsigma_law
    hsigma_indep hsigma_indep_X
  let Phi : ℝ → ℝ := fun t => if |t| ≤ 2 * B1 then t ^ 2 else 4 * B1 ^ 2 + 4 * B1 * (|t| - 2 * B1)
  have hkey : ∀ t : ℝ, Phi t =
      (if |t| ≤ 2 * B1 then |t| ^ 2 else 4 * B1 ^ 2 + 4 * B1 * (|t| - 2 * B1)) := by
    intro t
    change (if |t| ≤ 2 * B1 then t ^ 2 else 4 * B1 ^ 2 + 4 * B1 * (|t| - 2 * B1))
      = (if |t| ≤ 2 * B1 then |t| ^ 2 else 4 * B1 ^ 2 + 4 * B1 * (|t| - 2 * B1))
    by_cases h : |t| ≤ 2 * B1
    · rw [if_pos h, if_pos h, sq_abs]
    · rw [if_neg h, if_neg h]
  have hpiece : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
      |(if u ≤ 2 * B1 then u ^ 2 else 4 * B1 ^ 2 + 4 * B1 * (u - 2 * B1))
        - (if v ≤ 2 * B1 then v ^ 2 else 4 * B1 ^ 2 + 4 * B1 * (v - 2 * B1))|
      ≤ 4 * B1 * |u - v| := by
    intro u v hu hv
    rcases le_total u v with huv | huv
    · have habs : |u - v| = v - u := by
        rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
        ring
      rw [habs]
      by_cases hvR : v ≤ 2 * B1
      · have huR : u ≤ 2 * B1 := by linarith
        rw [if_pos huR, if_pos hvR, abs_le]
        exact ⟨by nlinarith, by nlinarith⟩
      · by_cases huR : u ≤ 2 * B1
        · rw [if_pos huR, if_neg hvR, abs_le]
          exact ⟨by nlinarith, by nlinarith⟩
        · rw [if_neg huR, if_neg hvR, abs_le]
          exact ⟨by nlinarith, by nlinarith⟩
    · have habs : |u - v| = u - v := by
        rw [abs_of_nonneg (by linarith : 0 ≤ u - v)]
      rw [habs]
      by_cases huR : u ≤ 2 * B1
      · have hvR : v ≤ 2 * B1 := by linarith
        rw [if_pos huR, if_pos hvR, abs_le]
        exact ⟨by nlinarith, by nlinarith⟩
      · by_cases hvR : v ≤ 2 * B1
        · rw [if_neg huR, if_pos hvR, abs_le]
          exact ⟨by nlinarith, by nlinarith⟩
        · rw [if_neg huR, if_neg hvR, abs_le]
          exact ⟨by nlinarith, by nlinarith⟩
  have hPhi_lip : LipschitzWith ⟨4 * B1, by linarith⟩ Phi := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro s t
    rw [Real.dist_eq, Real.dist_eq]
    show |Phi s - Phi t| ≤ 4 * B1 * |s - t|
    have h1 : |Phi s - Phi t| ≤ 4 * B1 * |(|s| - |t|)| := by
      rw [hkey s, hkey t]
      exact hpiece |s| |t| (abs_nonneg s) (abs_nonneg t)
    have h2 : |(|s| - |t|)| ≤ |s - t| := by
      have ha : |s| ≤ |s - t| + |t| := by
        have h := abs_add_le (s - t) t
        have e : s - t + t = s := by ring
        rw [e] at h
        exact h
      have hb : |t| ≤ |s - t| + |s| := by
        have h := abs_add_le (-(s - t)) s
        have e : -(s - t) + s = t := by ring
        rw [e, abs_neg] at h
        exact h
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by linarith))
  have hPhi_sq : ∀ t : ℝ, |t| ≤ 2 * B1 → Phi t = t ^ 2 := by
    intro t ht
    change (if |t| ≤ 2 * B1 then t ^ 2 else 4 * B1 ^ 2 + 4 * B1 * (|t| - 2 * B1)) = t ^ 2
    rw [if_pos ht]
  have hpt : ∀ (ω : Rand) (f : S → ℝ), f ∈ (Fs : Set (S → ℝ)) → ∀ (i : Fin n) (j : Fin m),
      |f (X i j ω) - f0 (X i j ω)| ≤ 2 * B1 := by
    intro ω f hf i j
    have h1 : |f (X i j ω)| ≤ B1 := hFs_bound f hf (X i j ω)
    have h2 : |f0 (X i j ω)| ≤ B1 := hf0_bound (X i j ω)
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hAE : (fun ω : Rand => sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) '' (Fs : Set (S → ℝ))))
      = (fun ω : Rand => sSup ((fun f : S → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * Phi (f (X i j ω) - f0 (X i j ω))|) '' (Fs : Set (S → ℝ)))) := by
    funext ω
    have hterm : ∀ f : S → ℝ, f ∈ (Fs : Set (S → ℝ)) →
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|
        = |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * Phi (f (X i j ω) - f0 (X i j ω))| := by
      intro f hf
      have hs : (∑ i : Fin n, ∑ j : Fin m, sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2)
          = (∑ i : Fin n, ∑ j : Fin m, sigma i j ω * Phi (f (X i j ω) - f0 (X i j ω))) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hPhi_sq _ (hpt ω f hf i j)]
      rw [hs]
    congr 1
    ext y
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, hf, (hterm f hf).symm⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, hf, hterm f hf⟩
  rw [hAE]
  have hPhi_zero : Phi 0 = 0 := by
    have hd : Phi = fun t : ℝ => if |t| ≤ 2 * B1 then t ^ 2 else 4 * B1 ^ 2 + 4 * B1 * (|t| - 2 * B1) := rfl
    rw [hd]
    show (if |(0 : ℝ)| ≤ 2 * B1 then (0 : ℝ) ^ 2 else 4 * B1 ^ 2 + 4 * B1 * (|(0 : ℝ)| - 2 * B1)) = 0
    have h0 : (0 : ℝ) ≤ 2 * B1 := by linarith
    rw [abs_zero, if_pos h0]
    norm_num
  exact @statopia_math_node_1156518618_e13ca37b S _instS Rand _instRand P _instP n m hn hm
    B1 hB1 f0 X sigma Fs Phi hf0_meas hFs_meas hf0_bound hFs_bound hX_meas hsigma_meas
    hsigma_law hsigma_indep hsigma_indep_X hPhi_lip hPhi_zero
  /- @proof-region region.target-node.session.5c58d0485df39824 end -/

end

end Statlib.Imported

