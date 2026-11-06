import Lean
import ProverJobs.ResidualE2ESupport20261106.M_e8f30da990e4e55e8aa7

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

namespace ResidualMaskRepair20261106.Assembly

theorem mask_bridge_error_le_twenty_four (alpha0 p : ℝ) (m n : ℕ)
    (halpha0 : 15 < alpha0) (hm : 3 ≤ m) (hn1 : 1 ≤ n) (hnm : n ≤ m)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hgrowth : (m : ℝ) * p ≥ Real.rpow (Real.log (m : ℝ)) alpha0) :
    Real.sqrt ((1-p)/(m:ℝ)) * Real.sqrt (6 * Real.log (n:ℝ)) +
      (1 / Real.sqrt ((m:ℝ)*p)) ^ ((1:ℝ)/3) *
        (Real.sqrt (1-p)) ^ ((2:ℝ)/3) * (6 * Real.log (n:ℝ)) ^ ((2:ℝ)/3) +
      (1 / Real.sqrt ((m:ℝ)*p)) * (6 * Real.log (n:ℝ)) ≤ 24 := by
  have hold := statopia_math_node_321355006_cfdd7f53 alpha0 p m n halpha0 hm hn1 hnm hp0 hp1 hgrowth
  let R0 : ℝ := max p (1-p) / Real.sqrt ((m:ℝ)*p)
  let R1 : ℝ := 1 / Real.sqrt ((m:ℝ)*p)
  let t : ℝ := 6 * Real.log (n:ℝ)
  let b : ℝ := (Real.sqrt (1-p)) ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3)
  have ht : 0 ≤ t := mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hn1))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  have hR1 : 0 ≤ R1 := by dsimp [R1]; positivity
  have hmax : (1:ℝ) ≤ 2 * max p (1-p) := by
    linarith [le_max_left p (1-p), le_max_right p (1-p)]
  have hR : R1 ≤ 2 * R0 := by
    dsimp [R1, R0]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hmax (Real.sqrt_nonneg _)
  have htwo : (2:ℝ) ^ ((1:ℝ)/3) ≤ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (1:ℝ)/3 ≤ 1)
    simpa using hh
  have hRp : R1 ^ ((1:ℝ)/3) ≤ 2 * R0 ^ ((1:ℝ)/3) := by
    calc
      _ ≤ (2 * R0) ^ ((1:ℝ)/3) := Real.rpow_le_rpow hR1 hR (by norm_num)
      _ = (2:ℝ) ^ ((1:ℝ)/3) * R0 ^ ((1:ℝ)/3) := Real.mul_rpow (by norm_num) hR0
      _ ≤ 2 * R0 ^ ((1:ℝ)/3) := mul_le_mul_of_nonneg_right htwo (by positivity)
  have hmid := mul_le_mul_of_nonneg_right hRp hb
  have hend := mul_le_mul_of_nonneg_right hR ht
  change Real.sqrt ((1-p)/(m:ℝ)) * Real.sqrt t + R0 ^ ((1:ℝ)/3) *
    (Real.sqrt (1-p)) ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) + R0 * t ≤ 12 at hold
  change Real.sqrt ((1-p)/(m:ℝ)) * Real.sqrt t + R1 ^ ((1:ℝ)/3) *
    (Real.sqrt (1-p)) ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) + R1 * t ≤ 24
  dsimp [b] at hmid
  nlinarith [mul_nonneg (Real.sqrt_nonneg ((1-p)/(m:ℝ))) (Real.sqrt_nonneg t)]

end ResidualMaskRepair20261106.Assembly

#print axioms ResidualMaskRepair20261106.Assembly.mask_bridge_error_le_twenty_four

