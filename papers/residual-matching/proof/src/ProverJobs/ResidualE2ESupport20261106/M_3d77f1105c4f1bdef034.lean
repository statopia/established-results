import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_3dccff77fe1d02cb5326

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
theorem statopia_math_node_2486598710_e2ce0d5f : ∀ (rhoMin : ℝ) (hrhoMin : 0 < rhoMin)
    (m n : ℕ) (hn : 2 ≤ n) (hnm : n ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (gam lamHat : Fin n → ℝ)
    (hgam : ∀ i ∈ indexSet n, Real.pi * rhoMin / 12 ≤ gam i)
    (C1 : ℝ) (hC1 : 0 < C1)
    (hlam : ∀ i : Fin n,
      |lamHat i - Real.sqrt p * gam i| ≤ C1 * Real.sqrt p * deltaM m)
    (hC1delta : C1 * deltaM m ≤ Real.pi * rhoMin / 12 / 2),
    (∑ i ∈ indexSet n, lamHat i ≥ (Real.pi * rhoMin / 12 / 22) * (n : ℝ) * Real.sqrt p) ∧
      (0 < ∑ i ∈ indexSet n, lamHat i) := by
  /- @proof-region region.target-node.session.1783b0e06fd974c4 begin -/
  intro rhoMin hrhoMin m n hn hnm p hp0 hp1 gam lamHat hgam C1 hC1 hlam hC1delta
  classical
  have hspos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hpoint : ∀ i ∈ indexSet n, Real.pi * rhoMin / 12 / 2 * Real.sqrt p ≤ lamHat i := by
    intro i hi
    have hsp : 0 ≤ Real.sqrt p := hspos.le
    have hstep1 : Real.sqrt p * (C1 * deltaM m) ≤ Real.sqrt p * (Real.pi * rhoMin / 12 / 2) :=
      mul_le_mul_of_nonneg_left hC1delta hsp
    have hstep2 : Real.sqrt p * (Real.pi * rhoMin / 12) ≤ Real.sqrt p * gam i :=
      mul_le_mul_of_nonneg_left (hgam i hi) hsp
    have hlo := (abs_le.mp (hlam i)).1
    nlinarith [hlo, hstep1, hstep2]

  have hcard : ((n : ℝ) / 11) ≤ ((indexSet n).card : ℝ) := by
    have hsub : (Finset.range (2 * n / 3 - ((n + 2) / 3 - 1))).image
        (fun k : ℕ => k + ((n + 2) / 3 - 1)) ⊆
        (indexSet n).image (fun i : Fin n => (i : ℕ)) := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      have hkd : k < 2 * n / 3 - ((n + 2) / 3 - 1) := Finset.mem_range.mp hk
      have hjn : k + ((n + 2) / 3 - 1) < n := by omega
      refine Finset.mem_image.mpr ⟨⟨k + ((n + 2) / 3 - 1), hjn⟩, ?_, rfl⟩
      simp only [indexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hJcard : ((Finset.range (2 * n / 3 - ((n + 2) / 3 - 1))).image
        (fun k : ℕ => k + ((n + 2) / 3 - 1))).card
        = 2 * n / 3 - ((n + 2) / 3 - 1) := by
      have hinj_add : ∀ t : ℕ, Function.Injective (fun k : ℕ => k + t) := by
        intro t a b hab
        have hab' : a + t = b + t := hab
        omega
      have himg := Finset.card_image_of_injective
        (s := Finset.range (2 * n / 3 - ((n + 2) / 3 - 1)))
        (f := fun k : ℕ => k + ((n + 2) / 3 - 1))
        (hinj_add ((n + 2) / 3 - 1))
      calc ((Finset.range (2 * n / 3 - ((n + 2) / 3 - 1))).image
            (fun k : ℕ => k + ((n + 2) / 3 - 1))).card
          = (Finset.range (2 * n / 3 - ((n + 2) / 3 - 1))).card := himg
        _ = 2 * n / 3 - ((n + 2) / 3 - 1) := Finset.card_range _
    have hd_le : 2 * n / 3 - ((n + 2) / 3 - 1) ≤ (indexSet n).card := by
      calc 2 * n / 3 - ((n + 2) / 3 - 1)
          = ((Finset.range (2 * n / 3 - ((n + 2) / 3 - 1))).image
              (fun k : ℕ => k + ((n + 2) / 3 - 1))).card := hJcard.symm
        _ ≤ ((indexSet n).image (fun i : Fin n => (i : ℕ))).card := Finset.card_le_card hsub
        _ ≤ (indexSet n).card := Finset.card_image_le
    have harith : n ≤ 11 * (2 * n / 3 - ((n + 2) / 3 - 1)) := by omega
    have h1 : ((2 * n / 3 - ((n + 2) / 3 - 1) : ℕ) : ℝ) ≤ ((indexSet n).card : ℝ) :=
      Nat.cast_le.mpr hd_le
    have h2 : (n : ℝ) ≤ 11 * ((2 * n / 3 - ((n + 2) / 3 - 1) : ℕ) : ℝ) := by
      exact_mod_cast harith
    linarith
  have hsum : ((indexSet n).card : ℝ) * (Real.pi * rhoMin / 12 / 2 * Real.sqrt p) ≤
      ∑ i ∈ indexSet n, lamHat i := by
    have h1 : ∑ i ∈ indexSet n, (Real.pi * rhoMin / 12 / 2 * Real.sqrt p) ≤
        ∑ i ∈ indexSet n, lamHat i := Finset.sum_le_sum hpoint
    rwa [Finset.sum_const, nsmul_eq_mul] at h1
  constructor
  · have h2 : Real.pi * rhoMin / 12 / 22 * (n : ℝ) * Real.sqrt p =
        ((n : ℝ) / 11) * (Real.pi * rhoMin / 12 / 2 * Real.sqrt p) := by ring
    rw [h2]
    exact le_trans (mul_le_mul_of_nonneg_right hcard (by positivity)) hsum
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (2 : ℝ) / 11 ≤ (n : ℝ) / 11 := by linarith [hn2]
    have hcardpos : (0 : ℝ) < ((indexSet n).card : ℝ) :=
      lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 / 11) (le_trans h2 hcard)
    have hpos : 0 < ((indexSet n).card : ℝ) * (Real.pi * rhoMin / 12 / 2 * Real.sqrt p) :=
      mul_pos hcardpos (by positivity)
    linarith [hsum]
  /- @proof-region region.target-node.session.1783b0e06fd974c4 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_2486598710_e2ce0d5f


