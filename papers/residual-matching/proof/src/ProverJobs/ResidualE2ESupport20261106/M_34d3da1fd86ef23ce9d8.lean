import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1231859466_c0d9b055 : ∀ (m n r D : ℕ) (p mu0 Cth : ℝ)
    (hD1 : D ≤ r * (m + n))
    (hm : 3 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hr : 12 * r ≤ n)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hmu0 : 0 < mu0 * (r : ℝ))
    (hCth : 12 ≤ Cth)
    (hnp : (n : ℝ) * p ≥ Cth ^ 2 * mu0 * (r : ℝ) * Real.log (m : ℝ)),
    let theta : ℝ := Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
    let sigma2 : ℝ := 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p)
    ENNReal.ofReal (2 * (D : ℝ) *
        Real.exp (-(theta ^ 2 / 2) / (sigma2 + sigma2 * theta / 3)))
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4) := by
  /- @proof-region region.target-node.session.30584d87566d2704 begin -/
  intro m n r D p mu0 Cth hD1 hm hn hnm hr hp hp1 hmu0 hCth hnp
  dsimp only
  set theta : ℝ := Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) with htheta
  set sigma2 : ℝ := 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p) with hsigma2
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hm1R : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hrne : r ≠ 0 := by rintro rfl; simp at hmu0
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hrne)
  have hmu0pos : 0 < mu0 := by
    have h := hmu0
    rw [mul_comm] at h
    exact pos_of_mul_pos_right h (le_of_lt hrR)
  have hCthpos : 0 < Cth := by linarith only [hCth]
  have hLpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1R
  have hnp_pos : 0 < (n : ℝ) * p := mul_pos hnR hp
  have hnpne : ((n : ℝ) * p) ≠ 0 := ne_of_gt hnp_pos
  have hS_pos : 0 < mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p) :=
    div_pos (mul_pos (mul_pos hmu0pos hrR) hLpos) hnp_pos
  have htheta_nonneg : 0 ≤ theta := by
    rw [htheta]
    exact mul_nonneg (le_of_lt hCthpos) (Real.sqrt_nonneg _)
  have htheta_sq : theta ^ 2 = Cth ^ 2 * (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) := by
    rw [htheta, mul_pow, Real.sq_sqrt (le_of_lt hS_pos)]
  have htheta_sq_le : theta ^ 2 ≤ 1 := by
    have heq : theta ^ 2 = Cth ^ 2 * (mu0 * (r : ℝ) * Real.log (m : ℝ)) / ((n : ℝ) * p) := by
      rw [htheta_sq]
      field_simp
    rw [heq, div_le_one hnp_pos]
    nlinarith only [hnp]
  have htheta_le_one : theta ≤ 1 := by
    nlinarith only [htheta_nonneg, htheta_sq_le, sq_nonneg (theta - 1)]
  have hsigma2_pos : 0 < sigma2 := by
    rw [hsigma2]
    exact div_pos (by linarith only [hmu0] : (0 : ℝ) < 4 * (mu0 * (r : ℝ))) hnp_pos
  have hden_pos : 0 < sigma2 + sigma2 * theta / 3 := by
    nlinarith only [hsigma2_pos, htheta_nonneg]
  have hK : theta ^ 2 = (Cth ^ 2 * Real.log (m : ℝ) / 4) * sigma2 := by
    rw [htheta_sq, hsigma2]
    field_simp
  have hkey : 6 * Real.log (m : ℝ) * (sigma2 + sigma2 * theta / 3) ≤ theta ^ 2 / 2 := by
    have hmulθ : sigma2 * theta ≤ sigma2 * 1 :=
      mul_le_mul_of_nonneg_left htheta_le_one (le_of_lt hsigma2_pos)
    have hDbound : sigma2 + sigma2 * theta / 3 ≤ (4 / 3) * sigma2 := by linarith only [hmulθ]
    have hLnn : (0 : ℝ) ≤ 6 * Real.log (m : ℝ) := by linarith only [hLpos]
    have h1 : 6 * Real.log (m : ℝ) * (sigma2 + sigma2 * theta / 3)
        ≤ 6 * Real.log (m : ℝ) * ((4 / 3) * sigma2) :=
      mul_le_mul_of_nonneg_left hDbound hLnn
    have h2 : 6 * Real.log (m : ℝ) * ((4 / 3) * sigma2) = 8 * Real.log (m : ℝ) * sigma2 := by ring
    have h64 : (64 : ℝ) ≤ Cth ^ 2 := by
      have h := mul_le_mul hCth hCth (by norm_num : (0 : ℝ) ≤ 12) (le_of_lt hCthpos)
      have h144 : (144 : ℝ) ≤ Cth ^ 2 := by nlinarith only [h]
      linarith only [h144]
    have h64mul : (64 : ℝ) * Real.log (m : ℝ) ≤ Cth ^ 2 * Real.log (m : ℝ) :=
      mul_le_mul_of_nonneg_right h64 (le_of_lt hLpos)
    have h8 : 8 * Real.log (m : ℝ) ≤ Cth ^ 2 * Real.log (m : ℝ) / 8 := by linarith only [h64mul]
    have h3a : 8 * Real.log (m : ℝ) * sigma2 ≤ (Cth ^ 2 * Real.log (m : ℝ) / 8) * sigma2 :=
      mul_le_mul_of_nonneg_right h8 (le_of_lt hsigma2_pos)
    have h3 : 8 * Real.log (m : ℝ) * sigma2 ≤ theta ^ 2 / 2 := by
      rw [hK]
      have hfin : (Cth ^ 2 * Real.log (m : ℝ) / 8) * sigma2
          = (Cth ^ 2 * Real.log (m : ℝ) / 4) * sigma2 / 2 := by ring
      linarith only [h3a, hfin]
    calc 6 * Real.log (m : ℝ) * (sigma2 + sigma2 * theta / 3)
        ≤ 6 * Real.log (m : ℝ) * ((4 / 3) * sigma2) := h1
      _ = 8 * Real.log (m : ℝ) * sigma2 := h2
      _ ≤ theta ^ 2 / 2 := h3
  have htD : -(theta ^ 2 / 2) / (sigma2 + sigma2 * theta / 3) * (sigma2 + sigma2 * theta / 3)
      = -(theta ^ 2 / 2) := by
    field_simp
  have hexparg : -(theta ^ 2 / 2) / (sigma2 + sigma2 * theta / 3) ≤ -(6 * Real.log (m : ℝ)) := by
    by_contra hcon
    rw [not_le] at hcon
    have hpos1 : 0 < -(theta ^ 2 / 2) / (sigma2 + sigma2 * theta / 3) + 6 * Real.log (m : ℝ) := by
      linarith only [hcon]
    have hmul : 0 < (-(theta ^ 2 / 2) / (sigma2 + sigma2 * theta / 3) + 6 * Real.log (m : ℝ))
        * (sigma2 + sigma2 * theta / 3) := mul_pos hpos1 hden_pos
    have hexp : (-(theta ^ 2 / 2) / (sigma2 + sigma2 * theta / 3) + 6 * Real.log (m : ℝ))
        * (sigma2 + sigma2 * theta / 3)
        = -(theta ^ 2 / 2) + 6 * Real.log (m : ℝ) * (sigma2 + sigma2 * theta / 3) := by
      rw [add_mul, htD]
    nlinarith only [hmul, hexp, hkey]
  have hexp_le : Real.exp (-(theta ^ 2 / 2) / (sigma2 + sigma2 * theta / 3)) ≤ 1 / (m : ℝ) ^ 6 := by
    have h1 : Real.exp (-(theta ^ 2 / 2) / (sigma2 + sigma2 * theta / 3))
        ≤ Real.exp (-(6 * Real.log (m : ℝ))) := Real.exp_le_exp.mpr hexparg
    have h2 : Real.exp (-(6 * Real.log (m : ℝ))) = 1 / (m : ℝ) ^ 6 := by
      have hcast : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
      rw [hcast, Real.exp_neg, Real.exp_nat_mul (Real.log (m : ℝ)) 6, Real.exp_log hmR, one_div]
    rw [h2] at h1
    exact h1
  have hDle : 2 * (D : ℝ) ≤ (n : ℝ) * (m : ℝ) / 3 := by
    have hDcast : (D : ℝ) ≤ (r : ℝ) * ((m : ℝ) + (n : ℝ)) := by exact_mod_cast hD1
    have hs1 : (r : ℝ) * ((m : ℝ) + (n : ℝ)) ≤ (r : ℝ) * (2 * (m : ℝ)) := by
      have h2m : (m : ℝ) + (n : ℝ) ≤ 2 * (m : ℝ) := by linarith only [hnmR]
      exact mul_le_mul_of_nonneg_left h2m (le_of_lt hrR)
    have hrle : (r : ℝ) ≤ (n : ℝ) / 12 := by
      have h12 : 12 * (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
      linarith only [h12]
    have hs2 : (r : ℝ) * (2 * (m : ℝ)) ≤ ((n : ℝ) / 12) * (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hrle (by linarith only [hmR] : (0 : ℝ) ≤ 2 * (m : ℝ))
    have hs3 : ((n : ℝ) / 12) * (2 * (m : ℝ)) = (n : ℝ) * (m : ℝ) / 6 := by ring
    have hD6 : (D : ℝ) ≤ (n : ℝ) * (m : ℝ) / 6 := by
      have hchain : (D : ℝ) ≤ ((n : ℝ) / 12) * (2 * (m : ℝ)) :=
        le_trans hDcast (le_trans hs1 hs2)
      linarith only [hchain, hs3]
    linarith only [hD6]
  have hprod : 2 * (D : ℝ) * Real.exp (-(theta ^ 2 / 2) / (sigma2 + sigma2 * theta / 3))
      ≤ ((n : ℝ) * (m : ℝ) / 3) * (1 / (m : ℝ) ^ 6) :=
    mul_le_mul hDle hexp_le (le_of_lt (Real.exp_pos _)) (by positivity : (0 : ℝ) ≤ (n : ℝ) * (m : ℝ) / 3)
  have hfinal : ((n : ℝ) * (m : ℝ) / 3) * (1 / (m : ℝ) ^ 6) ≤ (1 / 2 : ℝ) / (n : ℝ) ^ 4 := by
    have hn2 : (n : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
      have h := mul_le_mul hnmR hnmR (le_of_lt hnR) (le_of_lt hmR)
      nlinarith only [h]
    have hn4 : (n : ℝ) ^ 4 ≤ (m : ℝ) ^ 4 := by
      have h := mul_le_mul hn2 hn2 (le_of_lt (pow_pos hnR 2)) (le_of_lt (pow_pos hmR 2))
      nlinarith only [h]
    have hn5m5 : (n : ℝ) ^ 5 ≤ (m : ℝ) ^ 5 := by
      have h := mul_le_mul hn4 hnmR (le_of_lt hnR) (le_of_lt (pow_pos hmR 4))
      nlinarith only [h]
    have h2n5 : 2 * (n : ℝ) ^ 5 ≤ 3 * (m : ℝ) ^ 5 := by
      have hp5 : (0 : ℝ) < (n : ℝ) ^ 5 := pow_pos hnR 5
      have hb : 3 * (n : ℝ) ^ 5 ≤ 3 * (m : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left hn5m5 (by norm_num : (0 : ℝ) ≤ 3)
      linarith only [hp5, hb]
    field_simp
    nlinarith only [h2n5]
  exact ENNReal.ofReal_le_ofReal (le_trans hprod hfinal)
  /- @proof-region region.target-node.session.30584d87566d2704 end -/

end

end Statlib.Imported

