import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548
import ProverJobs.ResidualE2EAssembly20261106.M_c5bbe177e625061e278b
import ProverJobs.ResidualE2EAssembly20261106.M_b4414e1bde94b5677d57

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching


run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_3618029434_b97fb471 : ∀ (m n r : ℕ) (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m) (hr : 1 ≤ r)
    (p sigma K : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) (hsigma : 0 < sigma)
    (hK : 1 ≤ K) (hlog : 1 ≤ Real.log (m : ℝ))
    (Om M0 M : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ (i : Fin m) (j : Fin n), Om i j = 0 ∨ Om i j = 1)
    (hrank : Matrix.rank (M - M0) ≤ 2 * r)
    (s : ℝ) (hs : 0 ≤ s)
    (hop : spectralNorm (projMask Om (M - M0)) ≤
      K * (s + sigma) * Real.sqrt ((m : ℝ) * p))
    (hscale : s ≤ sigma * (1 + K / Real.log (m : ℝ)) +
      K * Real.sqrt ((frobNorm (projMask Om (M - M0))) ^ 2) /
        Real.sqrt ((m : ℝ) * (n : ℝ) * p)),
    0 ≤ (frobNorm (projMask Om (M - M0))) ^ 2 ∧
      (frobNorm (projMask Om (M - M0))) ^ 2 ≤
        10 * K ^ 4 *
          (sigma * Real.sqrt ((r : ℝ) * (m : ℝ) * p) * frobNorm (M - M0) +
            ((r : ℝ) / (n : ℝ)) * (frobNorm (M - M0)) ^ 2) := by
  /- @proof-region region.target-node.session.fbb58bb82083b0e4 begin -/
  intro m n r hm hn hnm hr
  intro p sigma K hp_pos hp_le hsigma hK hlog
  intro Om M0 M hOm hrank
  intro s hs hop hscale
  refine ⟨?_, ?_⟩
  · exact sq_nonneg _
  · obtain hEnergy := statopia_math_node_3416671836_4f7362e6 m n r Om M0 M hOm hrank
    set W : ℝ := spectralNorm (projMask Om (M - M0)) with hW
    set dl : ℝ := frobNorm (M - M0) with hdl
    set Qm : ℝ := (frobNorm (projMask Om (M - M0)))^2 with hQm
    set Sm : ℝ := Real.sqrt Qm with hSm
    have hQnn : 0 ≤ Qm := by rw [hQm]; exact sq_nonneg _
    have he2 : Sm^2 = Qm := by rw [hSm]; exact Real.sq_sqrt hQnn
    have hdnn : 0 ≤ dl := by
      rw [hdl]; unfold frobNorm Statlib.HighDim.MatrixAnalysis.frobeniusNorm; positivity
    have hWnn : 0 ≤ W := by
      have H : 0 < min m n := lt_min_iff.mpr ⟨hm, hn⟩
      rw [hW]
      unfold spectralNorm
      rw [dif_pos H]
      exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties _ (Or.inl ⟨⟨0, hm⟩⟩)).2.1 ⟨0, H⟩
    have hWbound : W ≤ K * (2 + K) * sigma * Real.sqrt ((m : ℝ) * p) + K ^ 2 * Sm / Real.sqrt (n : ℝ) := by
      have hlogpos : 0 < Real.log (m : ℝ) := by linarith
      have hKlog : K / Real.log (m : ℝ) ≤ K := by
        rw [div_le_iff₀ hlogpos]
        nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0:ℝ) ≤ K)]
      have hs1 : s + sigma ≤ sigma * (2 + K / Real.log (m : ℝ)) + K * Sm / Real.sqrt ((m : ℝ) * (n : ℝ) * p) := by
        linarith [hscale]
      have hs2 : sigma * (2 + K / Real.log (m : ℝ)) + K * Sm / Real.sqrt ((m : ℝ) * (n : ℝ) * p) ≤ sigma * (2 + K) + K * Sm / Real.sqrt ((m : ℝ) * (n : ℝ) * p) := by
        have hh := mul_le_mul_of_nonneg_left hKlog (le_of_lt hsigma)
        linarith [hh]
      have hstep : W ≤ K * (sigma * (2 + K) + K * Sm / Real.sqrt ((m : ℝ) * (n : ℝ) * p)) * Real.sqrt ((m : ℝ) * p) := by
        calc W ≤ K * (s + sigma) * Real.sqrt ((m : ℝ) * p) := hop
          _ ≤ K * (sigma * (2 + K) + K * Sm / Real.sqrt ((m : ℝ) * (n : ℝ) * p)) * Real.sqrt ((m : ℝ) * p) := by
              apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
              apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ K)
              linarith [hs1, hs2]
      have hexpand : K * (sigma * (2 + K) + K * Sm / Real.sqrt ((m : ℝ) * (n : ℝ) * p)) * Real.sqrt ((m : ℝ) * p) = K * (2 + K) * sigma * Real.sqrt ((m : ℝ) * p) + K ^ 2 * Sm * (Real.sqrt ((m : ℝ) * p) / Real.sqrt ((m : ℝ) * (n : ℝ) * p)) := by ring
      rw [hexpand] at hstep
      have hsqrtdiv : Real.sqrt ((m : ℝ) * p) / Real.sqrt ((m : ℝ) * (n : ℝ) * p) = 1 / Real.sqrt (n : ℝ) := by
        have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hmp : (0 : ℝ) < (m : ℝ) * p := mul_pos hmpos hp_pos
        have hp1 : 0 < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.mpr hmp
        have hp2 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
        have hkey : Real.sqrt ((m : ℝ) * (n : ℝ) * p) = Real.sqrt ((m : ℝ) * p) * Real.sqrt (n : ℝ) := by
          rw [show (m : ℝ) * (n : ℝ) * p = (m : ℝ) * p * (n : ℝ) by ring]
          exact Real.sqrt_mul (le_of_lt hmp) ((n : ℝ))
        have h1 : Real.sqrt ((m : ℝ) * p) * Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (mul_pos hp1 hp2)
        rw [hkey, div_eq_iff h1]
        field_simp
      rw [hsqrtdiv] at hstep
      have heq : K ^ 2 * Sm * (1 / Real.sqrt (n : ℝ)) = K ^ 2 * Sm / Real.sqrt (n : ℝ) := by ring
      rw [heq] at hstep
      exact hstep
    have hB : Qm ≤ Real.sqrt (2*(r:ℝ)) * dl * (K*(2+K)*sigma*Real.sqrt ((m:ℝ)*p) + K^2*Sm/Real.sqrt (n:ℝ)) := by
      calc Qm ≤ Real.sqrt (2*(r:ℝ)) * dl * W := hEnergy
        _ ≤ Real.sqrt (2*(r:ℝ)) * dl * (K*(2+K)*sigma*Real.sqrt ((m:ℝ)*p) + K^2*Sm/Real.sqrt (n:ℝ)) := by
            apply mul_le_mul_of_nonneg_left hWbound
            exact mul_nonneg (Real.sqrt_nonneg (2*(r:ℝ))) hdnn
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hnN : (n:ℝ) ≠ 0 := ne_of_gt hnpos
    have hid1 : Real.sqrt (2*(r:ℝ)) * Real.sqrt ((m:ℝ)*p) = Real.sqrt 2 * Real.sqrt ((r:ℝ)*(m:ℝ)*p) := by
      rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*(r:ℝ)) ((m:ℝ)*p)]
      rw [show 2*(r:ℝ)*((m:ℝ)*p) = 2*((r:ℝ)*(m:ℝ)*p) by ring]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) ((r:ℝ)*(m:ℝ)*p)]
    have hkey2 : Real.sqrt (2*(r:ℝ)) = Real.sqrt (2*(r:ℝ)/(n:ℝ)) * Real.sqrt (n:ℝ) := by
      rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*(r:ℝ)/(n:ℝ)) (n:ℝ)]
      congr 1
      rw [div_mul_cancel₀ (2*(r:ℝ)) hnN]
    have hid2 : Real.sqrt (2*(r:ℝ)) / Real.sqrt (n:ℝ) = Real.sqrt (2*(r:ℝ)/(n:ℝ)) := by
      rw [hkey2]
      have h2 : Real.sqrt (n:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
      field_simp
    have hs : (Real.sqrt (2*(r:ℝ)/(n:ℝ)))^2 = 2*(r:ℝ)/(n:ℝ) := Real.sq_sqrt (by positivity)
    have hY2 : (K^2 * Real.sqrt (2*(r:ℝ)/(n:ℝ)) * dl)^2 = K^4 * (2*(r:ℝ)/(n:ℝ)) * dl^2 := by
      have h1 : (K^2 * Real.sqrt (2*(r:ℝ)/(n:ℝ)) * dl)^2 = K^4 * (Real.sqrt (2*(r:ℝ)/(n:ℝ)))^2 * dl^2 := by ring
      rw [h1, hs]
    have hYoung : K^2 * Real.sqrt (2*(r:ℝ)/(n:ℝ)) * Sm * dl ≤ Qm/2 + K^4 * ((r:ℝ)/(n:ℝ)) * dl^2 := by
      have hab := two_mul_le_add_sq Sm (K^2 * Real.sqrt (2*(r:ℝ)/(n:ℝ)) * dl)
      rw [he2, hY2] at hab
      have hbr : K^4 * (2*(r:ℝ)/(n:ℝ)) * dl^2 = 2 * (K^4 * ((r:ℝ)/(n:ℝ)) * dl^2) := by ring
      rw [hbr] at hab
      linarith [hab]
    rw [mul_add] at hB
    have hPT : (Real.sqrt (2*(r:ℝ)) * dl) * (K * (2 + K) * sigma * Real.sqrt ((m:ℝ)*p)) = Real.sqrt 2 * K * (2 + K) * sigma * Real.sqrt ((r:ℝ)*(m:ℝ)*p) * dl := by
      rw [show (Real.sqrt (2*(r:ℝ)) * dl) * (K * (2 + K) * sigma * Real.sqrt ((m:ℝ)*p)) = K * (2 + K) * sigma * dl * (Real.sqrt (2*(r:ℝ)) * Real.sqrt ((m:ℝ)*p)) by ring]
      rw [hid1]
      ring
    have hST : (Real.sqrt (2*(r:ℝ)) * dl) * (K^2 * Sm / Real.sqrt (n:ℝ)) = K^2 * Real.sqrt (2*(r:ℝ)/(n:ℝ)) * Sm * dl := by
      rw [show (Real.sqrt (2*(r:ℝ)) * dl) * (K^2 * Sm / Real.sqrt (n:ℝ)) = K^2 * Sm * dl * (Real.sqrt (2*(r:ℝ)) / Real.sqrt (n:ℝ)) by ring]
      rw [hid2]
      ring
    rw [hPT, hST] at hB
    have hmain : Qm ≤ Real.sqrt 2 * K * (2 + K) * sigma * Real.sqrt ((r:ℝ)*(m:ℝ)*p) * dl + Qm/2 + K^4 * ((r:ℝ)/(n:ℝ)) * dl^2 := by
      linarith [hB, hYoung]
    have hfinal1 : Qm ≤ 2 * Real.sqrt 2 * K * (2 + K) * sigma * Real.sqrt ((r:ℝ)*(m:ℝ)*p) * dl + 2 * K^4 * ((r:ℝ)/(n:ℝ)) * dl^2 := by
      linarith [hmain]
    have h2le : Real.sqrt 2 ≤ 3/2 := by
      have hsq2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have hkey : 0 ≤ ((3:ℝ)/2 - Real.sqrt 2)^2 := sq_nonneg _
      have hexp : ((3:ℝ)/2 - Real.sqrt 2)^2 = ((3:ℝ)/2)^2 - 3 * Real.sqrt 2 + (Real.sqrt 2)^2 := by ring
      rw [hexp, hsq2] at hkey
      linarith [hkey]
    have hKnonneg : (0:ℝ) ≤ K := by linarith [hK]
    have hK2nn : (0:ℝ) ≤ K^2 := sq_nonneg K
    have hK2 : K ≤ K^2 := by
      have h1 : K * 1 ≤ K * K := mul_le_mul_of_nonneg_left hK hKnonneg
      simpa [pow_two] using h1
    have hK2ge1 : (1:ℝ) ≤ K^2 := by
      have h1 : (1:ℝ) * 1 ≤ K * K := mul_le_mul hK hK (by norm_num : (0:ℝ) ≤ 1) hKnonneg
      simpa [pow_two] using h1
    have hKsq : K^2 ≤ K^4 := by
      have h1 : (0:ℝ) ≤ K^2 - 1 := by linarith [hK2ge1]
      have h2 : 0 ≤ K^2 * (K^2 - 1) := mul_nonneg hK2nn h1
      have he : K^2 * (K^2 - 1) = K^4 - K^2 := by ring
      rw [he] at h2
      linarith [h2]
    have hconst1 : 2 * Real.sqrt 2 * K * (2 + K) ≤ 10 * K^4 := by
      have h2' : 2 * Real.sqrt 2 ≤ 3 := by linarith [h2le]
      have hKpos : (0:ℝ) ≤ K * (2 + K) := mul_nonneg hKnonneg (by linarith : (0:ℝ) ≤ 2 + K)
      have hstep1 : 2 * Real.sqrt 2 * K * (2 + K) ≤ 3 * K * (2 + K) := by
        have hraw := mul_le_mul_of_nonneg_right h2' hKpos
        linarith [hraw]
      have hstep2 : 3 * K * (2 + K) ≤ 10 * K^4 := by linarith [hK2, hKsq, sq_nonneg K]
      linarith [hstep1, hstep2]
    have hAnn : 0 ≤ sigma * Real.sqrt ((r:ℝ)*(m:ℝ)*p) * dl :=
      mul_nonneg (mul_nonneg (le_of_lt hsigma) (Real.sqrt_nonneg ((r:ℝ)*(m:ℝ)*p))) hdnn
    have hBnn : 0 ≤ ((r:ℝ)/(n:ℝ)) * dl^2 :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg n)) (sq_nonneg dl)
    have hterm1 : 2 * Real.sqrt 2 * K * (2 + K) * sigma * Real.sqrt ((r:ℝ)*(m:ℝ)*p) * dl ≤ 10 * K^4 * sigma * Real.sqrt ((r:ℝ)*(m:ℝ)*p) * dl := by
      have hraw := mul_le_mul_of_nonneg_right hconst1 hAnn
      linarith [hraw]
    have hterm2 : 2 * K^4 * ((r:ℝ)/(n:ℝ)) * dl^2 ≤ 10 * K^4 * ((r:ℝ)/(n:ℝ)) * dl^2 := by
      have h2K : 2 * K^4 ≤ 10 * K^4 := by
        have hK4 : 0 ≤ K^4 := pow_nonneg hKnonneg 4
        linarith [hK4]
      have hraw := mul_le_mul_of_nonneg_right h2K hBnn
      linarith [hraw]
    linarith [hfinal1, hterm1, hterm2]
  /- @proof-region region.target-node.session.fbb58bb82083b0e4 end -/

end Statlib.Imported

