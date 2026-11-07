import Lean
import ProverJobs.job_paper_2d165b9668ee43088292ee6f2129e2cd.Vocabulary
import ProverJobs.job_paper_2d165b9668ee43088292ee6f2129e2cd.Base

namespace PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported.XuYaoL4 then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported.XuYaoL4))
open _root_.PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4
open XuYaoL4

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported.XuYaoL4 then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported.XuYaoL4))
open _root_.PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4

set_option autoImplicit false in
theorem statopia_math_node_1192201732_5ae35332 : ∀ (K1 L t c s : ℝ)
    (hK1 : 0 < K1) (hL : 0 < L) (ht : 0 < t) (hc : 0 < c) (hs : 0 < s),
    let phi : ℝ := K1 * ((L ^ 2 * t ^ 4 * c ^ 2 / s) ^ (-(1 / 6 : ℝ)))
    s ^ (-(1 / 2 : ℝ)) * phi ^ 3 * t ^ 2 * L * c = K1 ^ 3 ∧
      s ^ (-(1 / 2 : ℝ)) * phi ^ 2 * t ^ (5 / 2 : ℝ) * L * c
        = K1 ^ 2 * ((L ^ 2 * t ^ 7 * c ^ 2 / s) ^ (1 / 6 : ℝ)) ∧
      s ^ (-(1 / 2 : ℝ)) * phi ^ 3 * t ^ 2 * c = K1 ^ 3 / L ∧
      phi⁻¹ * t ^ (1 / 2 : ℝ) = K1⁻¹ * ((L ^ 2 * t ^ 7 * c ^ 2 / s) ^ (1 / 6 : ℝ)) := by
  /- @proof-region region.target-node.session.410df83eec424ff2 begin -/
  intro K1 L t c s hK1 hL ht hc hs
  dsimp only
  set D : ℝ := L ^ 2 * t ^ 4 * c ^ 2 / s with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  set phi : ℝ := K1 * D ^ (-(1 / 6 : ℝ)) with hphidef
  have hsne : s ≠ 0 := ne_of_gt hs
  have hLne : L ≠ 0 := ne_of_gt hL
  have hLhalf : (L ^ 2 : ℝ) ^ (1 / 2 : ℝ) = L := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_mul (le_of_lt hL) ((2 : ℕ) : ℝ) (1 / 2 : ℝ),
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
  have hthalf : (t ^ 4 : ℝ) ^ (1 / 2 : ℝ) = t ^ 2 := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_mul (le_of_lt ht) ((4 : ℕ) : ℝ) (1 / 2 : ℝ),
      show ((4 : ℕ) : ℝ) * (1 / 2) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hchalf : (c ^ 2 : ℝ) ^ (1 / 2 : ℝ) = c := by
    rw [← Real.rpow_natCast c 2, ← Real.rpow_mul (le_of_lt hc) ((2 : ℕ) : ℝ) (1 / 2 : ℝ),
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
  have hnum : (L ^ 2 * t ^ 4 * c ^ 2 : ℝ) ^ (1 / 2 : ℝ) = L * t ^ 2 * c := by
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ L ^ 2 * t ^ 4) (by positivity : (0:ℝ) ≤ c ^ 2),
      Real.mul_rpow (by positivity : (0:ℝ) ≤ L ^ 2) (by positivity : (0:ℝ) ≤ t ^ 4),
      hLhalf, hthalf, hchalf]
  have hsqrt : D ^ (1 / 2 : ℝ) = L * t ^ 2 * c * s ^ (-(1 / 2 : ℝ)) := by
    rw [hDdef,
      Real.div_rpow (by positivity : (0:ℝ) ≤ L ^ 2 * t ^ 4 * c ^ 2) (le_of_lt hs) (1 / 2),
      hnum, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs) (1 / 2)]
  have hCube : (D ^ (-(1 / 6 : ℝ))) ^ 3 = D ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_mul_natCast (le_of_lt hDpos) (-(1 / 6 : ℝ)) 3
    rw [show -(1 / 6 : ℝ) * ((3:ℕ) : ℝ) = -(1 / 2) by norm_num] at h
    exact h.symm
  have hSq : (D ^ (-(1 / 6 : ℝ))) ^ 2 = D ^ (-(1 / 3 : ℝ)) := by
    have h := Real.rpow_mul_natCast (le_of_lt hDpos) (-(1 / 6 : ℝ)) 2
    rw [show -(1 / 6 : ℝ) * ((2:ℕ) : ℝ) = -(1 / 3) by norm_num] at h
    exact h.symm
  have hkey : s ^ (-(1 / 2 : ℝ)) * D ^ (-(1 / 2 : ℝ)) * t ^ 2 * L * c = 1 := by
    have hm : s ^ (-(1 / 2 : ℝ)) * D ^ (-(1 / 2 : ℝ)) = (L * t ^ 2 * c)⁻¹ := by
      rw [← Real.mul_rpow (le_of_lt hs) (le_of_lt hDpos)]
      rw [show s * D = L ^ 2 * t ^ 4 * c ^ 2 by
        rw [hDdef]
        field_simp]
      rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ L ^ 2 * t ^ 4 * c ^ 2) (1 / 2), hnum]
    rw [hm]
    have hc0 : (L * t ^ 2 * c)⁻¹ * (L * t ^ 2 * c) = 1 :=
      inv_mul_cancel₀ (by positivity : (L * t ^ 2 * c) ≠ 0)
    rw [← hc0]
    ring
  have h1 : s ^ (-(1 / 2 : ℝ)) * phi ^ 3 * t ^ 2 * L * c = K1 ^ 3 := by
    calc s ^ (-(1 / 2 : ℝ)) * phi ^ 3 * t ^ 2 * L * c
        = K1 ^ 3 * (s ^ (-(1 / 2 : ℝ)) * D ^ (-(1 / 2 : ℝ)) * t ^ 2 * L * c) := by
          rw [hphidef, mul_pow, hCube]
          ring
      _ = K1 ^ 3 := by rw [hkey, mul_one]
  have ht52 : t ^ (5 / 2 : ℝ) = t ^ 2 * t ^ (1 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = ((2 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add ht,
      Real.rpow_natCast]
  have ht3 : (t ^ 3 : ℝ) ^ (1 / 6 : ℝ) = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast t 3, ← Real.rpow_mul (le_of_lt ht) ((3 : ℕ) : ℝ) (1 / 6 : ℝ),
      show ((3 : ℕ) : ℝ) * (1 / 6) = 1 / 2 by norm_num]
  have hsix : D ^ (1 / 6 : ℝ) = D ^ (1 / 2 : ℝ) * D ^ (-(1 / 3) : ℝ) := by
    rw [← Real.rpow_add hDpos (1 / 2 : ℝ) (-(1 / 3) : ℝ),
      show (1 / 2 : ℝ) + -(1 / 3) = 1 / 6 by norm_num]
  have hV6 : (L ^ 2 * t ^ 7 * c ^ 2 / s) ^ (1 / 6 : ℝ) = D ^ (1 / 6 : ℝ) * t ^ (1 / 2 : ℝ) := by
    rw [show L ^ 2 * t ^ 7 * c ^ 2 / s = D * t ^ 3 by
      rw [hDdef]
      field_simp]
    rw [Real.mul_rpow (le_of_lt hDpos) (by positivity : (0:ℝ) ≤ t ^ 3), ht3]
  have h2 : s ^ (-(1 / 2 : ℝ)) * phi ^ 2 * t ^ (5 / 2 : ℝ) * L * c
      = K1 ^ 2 * ((L ^ 2 * t ^ 7 * c ^ 2 / s) ^ (1 / 6 : ℝ)) := by
    rw [hV6, hsix, hsqrt, ht52, hphidef, mul_pow, hSq]
    ring
  have h3 : s ^ (-(1 / 2 : ℝ)) * phi ^ 3 * t ^ 2 * c = K1 ^ 3 / L := by
    rw [eq_div_iff hLne, ← h1]
    ring
  have hK1inv : K1 * K1⁻¹ = 1 := by
    rw [mul_comm]
    exact inv_mul_cancel₀ (ne_of_gt hK1)
  have hD1 : D ^ (-(1 / 6) : ℝ) * D ^ (1 / 6 : ℝ) = 1 := by
    rw [← Real.rpow_add hDpos (-(1 / 6) : ℝ) (1 / 6 : ℝ),
      show -(1 / 6 : ℝ) + 1 / 6 = 0 by norm_num, Real.rpow_zero]
  have hphipos : 0 < phi := by rw [hphidef]; positivity
  have hX : phi * (K1⁻¹ * D ^ (1 / 6 : ℝ)) = 1 := by
    rw [hphidef]
    calc K1 * D ^ (-(1 / 6) : ℝ) * (K1⁻¹ * D ^ (1 / 6 : ℝ))
        = K1 * K1⁻¹ * (D ^ (-(1 / 6) : ℝ) * D ^ (1 / 6 : ℝ)) := by ring
      _ = 1 := by rw [hK1inv, hD1, mul_one]
  have hInv : phi⁻¹ = K1⁻¹ * D ^ (1 / 6 : ℝ) := by
    have step : phi⁻¹ * (phi * (K1⁻¹ * D ^ (1 / 6 : ℝ))) = K1⁻¹ * D ^ (1 / 6 : ℝ) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hphipos), one_mul]
    rw [← step, hX, mul_one]
  have h4 : phi⁻¹ * t ^ (1 / 2 : ℝ) = K1⁻¹ * ((L ^ 2 * t ^ 7 * c ^ 2 / s) ^ (1 / 6 : ℝ)) := by
    rw [hInv, hV6]
    ring

  exact ⟨h1, h2, h3, h4⟩

  /- @proof-region region.target-node.session.410df83eec424ff2 end -/

end Statlib.Imported

