import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
namespace ResidualLoss20261106.Statlib.Imported

lemma mc_scale_le_logarithmic (m n T : ℕ) (hn : 2 ≤ n) (hnm : n ≤ m) (hT : 1 ≤ T)
    (p alpha : ℝ) (hp : 0 ≤ p) (halpha : 3 ≤ alpha)
    (hlog : 1 ≤ Real.log (m:ℝ))
    (hmp : Real.rpow (Real.log (m:ℝ)) alpha ≤ (m:ℝ)*p) :
    Real.sqrt (Real.log (n:ℝ) / ((m:ℝ)*(T:ℝ))) ≤ Real.sqrt p * deltaM m := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hT1 : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0:ℝ) < T := by linarith
  have hlpos : 0 < Real.log (m:ℝ) := by linarith
  have hlogn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlognm : Real.log (n:ℝ) ≤ Real.log (m:ℝ) :=
    Real.log_le_log hnpos (by exact_mod_cast hnm)
  have hpow : Real.log (m:ℝ)^3 ≤ (m:ℝ)*p := by
    have hh := Real.rpow_le_rpow_of_exponent_le hlog halpha
    rw [Real.rpow_ofNat] at hh
    exact hh.trans hmp
  have hden : (m:ℝ) ≤ (m:ℝ)*(T:ℝ) := by nlinarith
  have hfirst : Real.log (n:ℝ) / ((m:ℝ)*(T:ℝ)) ≤ Real.log (m:ℝ)/(m:ℝ) := by
    apply (div_le_div₀ (le_trans hlogn hlognm) hlognm hmpos hden)
  have hsecond : Real.log (m:ℝ)/(m:ℝ) ≤ p / Real.log (m:ℝ)^2 := by
    apply (div_le_div_iff₀ hmpos (sq_pos_of_pos hlpos)).2
    nlinarith [hpow]
  calc
    Real.sqrt (Real.log (n:ℝ) / ((m:ℝ)*(T:ℝ)))
      ≤ Real.sqrt (p / Real.log (m:ℝ)^2) := Real.sqrt_le_sqrt (hfirst.trans hsecond)
    _ = Real.sqrt p * deltaM m := by
      rw [Real.sqrt_div hp, Real.sqrt_sq hlpos.le]
      rfl

lemma probability_inter_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S T : Set Ω) (hT : MeasurableSet T)
    (q r : ℝ) (hSprob : ENNReal.ofReal (1-q) ≤ μ S) (hTprob : ENNReal.ofReal (1-r) ≤ μ T) :
    ENNReal.ofReal (1-(q+r)) ≤ μ (S ∩ T) := by
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).2
  have hS := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).1 hSprob
  have hT' := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).1 hTprob
  have hu : μ.real (S ∪ T) ≤ 1 := by
    exact measureReal_le_one
  have he := measureReal_union_add_inter (μ := μ) (s := S) hT
  change 1-(q+r) ≤ μ.real (S ∩ T)
  change 1-q ≤ μ.real S at hS
  change 1-r ≤ μ.real T at hT'
  linarith

lemma sv_zero_eq_opNorm {m n : ℕ} (hnm : n ≤ m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    sv hnm A ⟨0,hn⟩ = Statlib.HighDim.MatrixAnalysis.opNorm A := by
  have hmin : 0 < min m n := lt_min (hn.trans_le hnm) hn
  have hh := (Statlib.HighDim.MatrixAnalysis.singular_value_properties A
    (Or.inr ⟨⟨0,hn⟩⟩)).1 hmin
  have hidx : Fin.castLE (le_min hnm le_rfl) (⟨0,hn⟩ : Fin n) = (⟨0,hmin⟩ : Fin (min m n)) := by rfl
  unfold sv
  rw [hidx, hh]
  exact Matrix.l2_opNorm_def A

end ResidualLoss20261106.Statlib.Imported
#print axioms ResidualLoss20261106.Statlib.Imported.mc_scale_le_logarithmic

#print axioms ResidualLoss20261106.Statlib.Imported.probability_inter_lower

#print axioms ResidualLoss20261106.Statlib.Imported.sv_zero_eq_opNorm

