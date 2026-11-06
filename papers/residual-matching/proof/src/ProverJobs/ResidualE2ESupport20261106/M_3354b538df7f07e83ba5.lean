import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_9d21f75727525c382485
import ProverJobs.ResidualE2ESupport20261106.M_b1b781dde679316b27eb
import ProverJobs.ResidualE2ESupport20261106.M_9ee6587ba5cc9395f31f

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1148821130_ff99be46 : ∀ (D0 Kt alpha0 CD : ℝ) (hD0 : 0 < D0) (hKt : 0 < Kt) (halpha0 : 15 < alpha0)
    (hCD : Kt * (D0 + 12) ≤ CD),
    ∃ M0 : ℕ, ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → n ≤ m → M0 ≤ m →
      ∀ (p : ℝ), 0 < p → p ≤ 1 →
        Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p →
        ∀ (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν],
          (∀ (i : Fin m) (j : Fin n), ∫ x, (x i j) ^ 2 ∂ν = 1) →
          (∀ (i : Fin m) (j : Fin n), ∫ x, x i j ∂ν = 0) →
          (∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
            ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} ≤
              ENNReal.ofReal (2 * Real.exp (-t / Kt))) →
          ∀ (b c : Fin m → Fin n → ℝ)
            (XT : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ),
            (∀ (i : Fin m) (j : Fin n),
              b i j = ∫ x, x i j * (if |x i j| ≤
                  CD * Real.log ((m : ℝ) * (n : ℝ)) +
                    (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4
                then (1 : ℝ) else 0) ∂ν) →
            (∀ (i : Fin m) (j : Fin n),
              c i j = Real.sqrt (∫ x,
                (x i j * (if |x i j| ≤
                    CD * Real.log ((m : ℝ) * (n : ℝ)) +
                      (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4
                  then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν)) →
            (∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
              XT x i j = (x i j * (if |x i j| ≤
                  CD * Real.log ((m : ℝ) * (n : ℝ)) +
                    (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4
                then (1 : ℝ) else 0) - b i j) / c i j) →
            ∀ (M : Matrix (Fin m) (Fin n) ℝ),
              (∀ (i : Fin m) (j : Fin n), M i j = 0 ∨ M i j = 1) →
              ∀ (x : Matrix (Fin m) (Fin n) ℝ),
                (∀ (i : Fin m) (j : Fin n), |x i j| ≤
                  CD * Real.log ((m : ℝ) * (n : ℝ)) +
                    (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) →
                @norm (Matrix (Fin m) (Fin n) ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm
                  (maskedScaled p x M - maskedScaled p (XT x) M) ≤
                  Real.rpow (n : ℝ) (-(D0 + 5)) := by
  /- @proof-region region.target-node.session.c3b4b0656d5b0ec1 begin -/
  classical
  intro D0 Kt alpha0 CD hD0 hKt halpha0 hCD

  have hA : ∀ (m n : ℕ) (L : ℝ), 1 ≤ m → 1 ≤ n →
      L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
        (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 →
      ∀ (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν],
      (∀ (i : Fin m) (j : Fin n), ∫ x, (x i j) ^ 2 ∂ν = 1) →
      (∀ (i : Fin m) (j : Fin n), ∫ x, x i j ∂ν = 0) →
      (∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
        ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} ≤
          ENNReal.ofReal (2 * Real.exp (-t / Kt))) →
      ∀ (b c : Fin m → Fin n → ℝ)
        (XT : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ),
      (∀ (i : Fin m) (j : Fin n),
        b i j = ∫ x, x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) ∂ν) →
      (∀ (i : Fin m) (j : Fin n),
        c i j = Real.sqrt
          (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν)) →
      (∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
        XT x i j = (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j) →
      ∀ (x : Matrix (Fin m) (Fin n) ℝ), (∀ (i : Fin m) (j : Fin n), |x i j| ≤ L) →
      ∀ (i : Fin m) (j : Fin n),
        |x i j - XT x i j| ≤ 64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
    intro m n L hm hn hL ν instν h_var h_mean h_tail b c XT hb hc hXT x hx i j
    exact statopia_math_node_1590920294_08da72e6 Kt D0 alpha0 CD hKt hD0 (by linarith) hCD
      m n hm hn L hL ν h_var h_mean h_tail b c XT hb hc hXT x hx i j

  have hB : ∃ M0 : ℕ, ∀ (m n : ℕ) (L : ℝ), 1 ≤ m → 1 ≤ n → n ≤ m → M0 ≤ m →
      L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
        (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 →
      ∀ (p : ℝ), 0 < p → p ≤ 1 →
      Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p →
      Real.sqrt ((n : ℝ) / p) * (64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt)) ≤
        Real.rpow (n : ℝ) (-(D0 + 5)) := by
    exact statopia_math_node_4055001358_e7cf4d8e D0 Kt alpha0 CD hD0 hKt halpha0 hCD

  obtain ⟨M0, hM0⟩ := hB
  refine ⟨M0, ?_⟩
  intro m n hm hn hnm hM0'
  set L : ℝ := CD * Real.log ((m : ℝ) * (n : ℝ)) +
      (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 with hL
  intro p hp0 hp1 hsparse ν instν h_var h_mean h_tail b c XT hb hc hXT M hM x hx
  have hCDpos : 0 < CD := by
    have h : 0 < Kt * (D0 + 12) := mul_pos hKt (by linarith)
    linarith
  have hlog : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := by
    apply Real.log_nonneg
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hLpos : 0 < L := by
    have h1 : (0 : ℝ) < Kt + 1 := by linarith
    have h2 : (0 : ℝ) < D0 + 1 := by linarith
    have h3 : (0 : ℝ) < alpha0 + 1 := by linarith
    have hT : 0 < (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 :=
      mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) 6) (pow_pos h1 4)) (pow_pos h2 4))
        (pow_pos h3 4)
    have hcl : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_nonneg (le_of_lt hCDpos) hlog
    rw [hL]
    linarith
  have hBnn : (0 : ℝ) ≤ 64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (le_of_lt hLpos))
        (sq_nonneg _))
      (le_of_lt (Real.exp_pos _))

  have hsplit : maskedScaled p x M - maskedScaled p (XT x) M =
      maskedScaled p (x - XT x) M := by
    ext i j
    simp [maskedScaled, mul_sub]
    ring

  rw [hsplit]
  have hbnd : ∀ (i : Fin m) (j : Fin n),
      |(x - XT x) i j| ≤ 64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
    intro i j
    exact hA m n L hm hn rfl ν h_var h_mean h_tail b c XT hb hc hXT x hx i j
  have hnorm : ‖maskedScaled p (x - XT x) M‖ ≤
      Real.sqrt ((n : ℝ) / p) * (64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt)) := by
    simpa only [maskedScaled] using
      statopia_math_node_270675543_d5eed0a7 m n p
        (64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt)) hp0 hBnn
        M (x - XT x) hM hbnd
  have hnum : Real.sqrt ((n : ℝ) / p) *
        (64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt)) ≤
      (n : ℝ).rpow (-(D0 + 5)) :=
    hM0 m n L hm hn hnm hM0' rfl p hp0 hp1 hsparse

  exact le_trans hnorm hnum



  /- @proof-region region.target-node.session.c3b4b0656d5b0ec1 end -/

end Statlib.Imported

#print axioms Statlib.Imported.statopia_math_node_1148821130_ff99be46

