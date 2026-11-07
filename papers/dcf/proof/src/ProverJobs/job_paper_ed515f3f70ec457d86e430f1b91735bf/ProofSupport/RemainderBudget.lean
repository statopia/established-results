import Lean
import Mathlib

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
set_option maxHeartbeats 300000
namespace DCFManualBudget
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `DCFManualBudget then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.DCFManualBudget))
lemma remainder_budget
    (phi phi2 ell S L rho M C1 C3 C2 Cb : ℝ)
    (hphi : 1 ≤ phi) (hphi2 : phi ≤ phi2) (hell : (1/2 : ℝ) ≤ ell)
    (hS : 0 ≤ S) (hL : 0 ≤ L) (hrho : 0 ≤ rho) (hM : 0 ≤ M)
    (hC1 : 1 ≤ C1) (hC3 : 1 ≤ C3) (hC2 : 0 ≤ C2) (hCb : 0 < Cb) :
    C3^2 * ((153/2 : ℝ) * S * L) * (C1*C2*phi*(phi*ell)^2) *
      (2*rho + Cb*(phi⁻¹+2*(phi*ell)⁻¹)*Real.sqrt ell) +
      81*(C1*C2*phi*(phi*ell)^2)*S*M ≤
    1000000*((C1+C3+C2+1)*(Cb+1))^4*S*
      (phi^2*ell^2*(phi2*(L*rho)+L*Real.sqrt ell+phi*M)) := by
  have hp : 0 < phi := by linarith
  have hphi20 : 0 ≤ phi2 := by linarith only [hp, hphi2]
  have he : 0 < ell := by linarith
  have hroot := Real.sqrt_nonneg ell
  have hinv : ell⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ he).2 (by linarith only [hell])
  have hD : 2*rho + Cb*(phi⁻¹+2*(phi*ell)⁻¹)*Real.sqrt ell ≤
      2*rho + 5*Cb*phi⁻¹*Real.sqrt ell := by
    have hinner : phi⁻¹+2*(phi*ell)⁻¹ ≤ 5*phi⁻¹ := by
      rw [mul_inv_rev]
      calc phi⁻¹+2*(ell⁻¹*phi⁻¹) = (1+2*ell⁻¹)*phi⁻¹ := by ring
           _ ≤ 5*phi⁻¹ := mul_le_mul_of_nonneg_right (by linarith only [hinv])
             (inv_nonneg.mpr hp.le)
    have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinner hCb.le) hroot
    convert add_le_add_left H (2*rho) using 1 <;> ring
  let A := C1+C3+C2+1
  let E := Cb+1
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hA0 : 0 ≤ A := by linarith
  have hE : 1 ≤ E := by dsimp [E]; linarith
  have hE0 : 0 ≤ E := by linarith
  have hC1A : C1 ≤ A := by dsimp [A]; linarith
  have hC3A : C3 ≤ A := by dsimp [A]; linarith
  have hC2A : C2 ≤ A := by dsimp [A]; linarith
  have hprod : C3^2*C1*C2 ≤ A^4 := by
    calc C3^2*C1*C2 ≤ A^2*A*A := by gcongr <;> linarith
         _ = A^4 := by ring
  have hprod2 : C1*C2 ≤ A^4 := by
    calc C1*C2 ≤ A*A := by gcongr <;> linarith
         _ ≤ A^4 := by
           have hA2 : 1 ≤ A^2 := one_le_pow₀ hA
           nlinarith only [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr hA2)]
  have hE4 : 1 ≤ E^4 := one_le_pow₀ hE
  have hCbE4 : Cb ≤ E^4 := by
    have hEE : E ≤ E^4 := by
      calc E = E*1 := (mul_one E).symm
           _ ≤ E*E^3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hE) hE0
           _ = E^4 := by ring
    have hCE : Cb ≤ E := by dsimp [E]; linarith only [hCb]
    exact hCE.trans hEE
  have hprodE : 0 ≤ A^4*E^4 := mul_nonneg (pow_nonneg hA0 4) (pow_nonneg hE0 4)
  have hcoef1 : 153*A^4 ≤ 1000000*(A*E)^4 := by
    rw [mul_pow]
    nlinarith only [mul_le_mul_of_nonneg_left hE4 (pow_nonneg hA0 4),hprodE]
  have hcoef2 : (765/2 : ℝ)*A^4*Cb ≤ 1000000*(A*E)^4 := by
    rw [mul_pow]
    nlinarith only [mul_le_mul_of_nonneg_left hCbE4 (pow_nonneg hA0 4),hprodE]
  have hcoef3 : 81*A^4 ≤ 1000000*(A*E)^4 := by
    rw [mul_pow]
    nlinarith only [mul_le_mul_of_nonneg_left hE4 (pow_nonneg hA0 4),hprodE]
  calc
    _ ≤ C3^2*((153/2 : ℝ)*S*L)*(C1*C2*phi*(phi*ell)^2)*
        (2*rho+5*Cb*phi⁻¹*Real.sqrt ell) +
        81*(C1*C2*phi*(phi*ell)^2)*S*M := by gcongr <;> positivity
    _ = 153*(C3^2*C1*C2)*S*phi^2*ell^2*(phi*(L*rho)) +
        (765/2 : ℝ)*(C3^2*C1*C2)*Cb*S*phi^2*ell^2*(L*Real.sqrt ell) +
        81*(C1*C2)*S*phi^2*ell^2*(phi*M) := by
      field_simp [ne_of_gt hp]
      <;> ring
    _ ≤ 153*A^4*S*phi^2*ell^2*(phi2*(L*rho)) +
        (765/2 : ℝ)*A^4*Cb*S*phi^2*ell^2*(L*Real.sqrt ell) +
        81*A^4*S*phi^2*ell^2*(phi*M) := by gcongr <;> positivity
    _ ≤ (1000000*(A*E)^4)*S*phi^2*ell^2*(phi2*(L*rho)) +
        (1000000*(A*E)^4)*S*phi^2*ell^2*(L*Real.sqrt ell) +
        (1000000*(A*E)^4)*S*phi^2*ell^2*(phi*M) := by gcongr <;> positivity
    _ = _ := by dsimp [A,E]; ring
end DCFManualBudget

