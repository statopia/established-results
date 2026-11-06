import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_3354b538df7f07e83ba5
import ProverJobs.ResidualE2ESupport20261106.M_2e445e9d131a16ed6935
import ProverJobs.ResidualE2ESupport20261106.M_5d525b55b78541bec184

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
theorem statopia_math_node_790018995_867172dc : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : Kt * (D0 + 12) ≤ CD),
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ M1 : ℕ,
      ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM1 : M1 ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p),
        ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0) →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1) →
          (∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
            μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt))) →
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
          (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
          (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
          IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
            (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
          ∃ G : Set Ω, MeasurableSet G ∧
            μ Gᶜ ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 2))) ∧
            (∀ ω ∈ G,
              svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ ≤
                1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + Ce * deltaM m ∧
              1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - Ce * deltaM m ≤
                svals (maskedScaled p (Xi ω) (Mask ω)) ⟨n - 1, by omega⟩ ∧
                @norm (Matrix (Fin m) (Fin n) ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm
                  (maskedScaled p (Xi ω) (Mask ω)) ≤ 4) ∧
              μ {ω | 4 < @norm (Matrix (Fin m) (Fin n) ℝ)
                  Matrix.instL2OpNormedAddCommGroup.toNorm
                  (maskedScaled p (Xi ω) (Mask ω))} ≤
              ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 2))) := by
  /- @proof-region region.target-node.session.aa262d1694585ad2 begin -/
  intro D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le_one Kt hKt alpha0 halpha0 CD hCD
  classical
  have hcoordGen : ∀ (m n : ℕ) (i : Fin m) (j : Fin n),
      Measurable fun x : Matrix (Fin m) (Fin n) ℝ => x i j := by
    intro m n i j
    exact ((measurable_pi_iff.mp measurable_id :
      ∀ j' : Fin n, Measurable fun z : Fin n → ℝ => z j') j).comp
      ((measurable_pi_iff.mp measurable_id :
        ∀ i' : Fin m, Measurable fun y : Matrix (Fin m) (Fin n) ℝ => y i') i)
  have hintGen : ∀ (m n : ℕ) (i : Fin m) (j : Fin n) (c : ℝ),
      Measurable fun x : Matrix (Fin m) (Fin n) ℝ => (if |x i j| ≤ c then (1 : ℝ) else 0) := by
    intro m n i j c
    have hS : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | |x i j| ≤ c} :=
      measurableSet_le (Measurable.abs (hcoordGen m n i j)) measurable_const
    simpa using Measurable.indicator (s := {x : Matrix (Fin m) (Fin n) ℝ | |x i j| ≤ c})
      measurable_const hS
  have trunc : ∃ M0 : ℕ, ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM0 : M0 ≤ m)
      (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
      (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
      (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
      (h_var : ∀ (i : Fin m) (j : Fin n), ∫ x, (x i j) ^ 2 ∂ν = 1)
      (h_xmean : ∀ (i : Fin m) (j : Fin n), ∫ x, x i j ∂ν = 0)
      (h_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
        ν {x | t < |x i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt))),
      ∃ b : Fin m → Fin n → ℝ, ∃ c : Fin m → Fin n → ℝ,
        ∃ XT : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ,
        (∀ (i : Fin m) (j : Fin n), b i j = ∫ x, x i j * (if |x i j| ≤
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) ∂ν) ∧
        (∀ (i : Fin m) (j : Fin n), c i j = Real.sqrt (∫ x, (x i j * (if |x i j| ≤
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν)) ∧
        (∀ (i : Fin m) (j : Fin n), 0 < c i j) ∧
        (∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
          XT x i j = (x i j * (if |x i j| ≤
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) / c i j) ∧
        (∀ (i : Fin m) (j : Fin n), ∫ x, XT x i j ∂ν = 0) ∧
        (∀ (i : Fin m) (j : Fin n), ∫ x, (XT x i j) ^ 2 ∂ν = 1) ∧
        (∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n), |XT x i j| ≤ 3 *
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)) ∧
        (ν {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n),
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) < |x i j|} ≤
          ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10)))) ∧
        (∀ (M : Matrix (Fin m) (Fin n) ℝ), (∀ (i : Fin m) (j : Fin n), M i j = 0 ∨ M i j = 1) →
          ∀ (x : Matrix (Fin m) (Fin n) ℝ), (∀ (i : Fin m) (j : Fin n),
            |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)) →
          ‖maskedScaled p x M - maskedScaled p (XT x) M‖ ≤ Real.rpow (n : ℝ) (-(D0 + 5))) := by
    obtain ⟨M0, hcore⟩ : ∃ M0 : ℕ,
        ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM0 : M0 ≤ m)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
        (h_var : ∀ (i : Fin m) (j : Fin n), ∫ x, (x i j) ^ 2 ∂ν = 1)
        (h_xmean : ∀ (i : Fin m) (j : Fin n), ∫ x, x i j ∂ν = 0)
        (h_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
          ν {x | t < |x i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
        (b : Fin m → Fin n → ℝ) (c : Fin m → Fin n → ℝ)
        (XT : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
        (hb : ∀ (i : Fin m) (j : Fin n), b i j = ∫ x, x i j * (if |x i j| ≤
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) ∂ν)
        (hc : ∀ (i : Fin m) (j : Fin n), c i j = Real.sqrt (∫ x, (x i j * (if |x i j| ≤
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν))
        (hXT : ∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
          XT x i j = (x i j * (if |x i j| ≤
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) / c i j),
        (∀ (i : Fin m) (j : Fin n), 0 < c i j) ∧
        (∀ (i : Fin m) (j : Fin n), ∫ x, XT x i j ∂ν = 0) ∧
        (∀ (i : Fin m) (j : Fin n), ∫ x, (XT x i j) ^ 2 ∂ν = 1) ∧
        (∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n), |XT x i j| ≤ 3 *
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)) ∧
        (ν {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n),
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) < |x i j|} ≤
          ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10)))) ∧
        (∀ (M : Matrix (Fin m) (Fin n) ℝ), (∀ (i : Fin m) (j : Fin n), M i j = 0 ∨ M i j = 1) →
          ∀ (x : Matrix (Fin m) (Fin n) ℝ), (∀ (i : Fin m) (j : Fin n),
            |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)) →
          ‖maskedScaled p x M - maskedScaled p (XT x) M‖ ≤ Real.rpow (n : ℝ) (-(D0 + 5))) := by
      obtain ⟨M0a, hcore⟩ :=
        statopia_math_node_69799842_f5d4fc65 D0 Kt alpha0 CD hD0 hKt halpha0 hCD
      obtain ⟨M0b, htransferAll⟩ :=
        statopia_math_node_1148821130_ff99be46 D0 Kt alpha0 CD hD0 hKt halpha0 hCD
      refine ⟨max M0a M0b, ?_⟩
      intro m n hm hn hnm hM0 p hp0 hp1 hsparse ν hν h_var h_xmean h_tail b c XT hb hc hXT
      obtain ⟨h1, h2, h3, _⟩ :=
        hcore m n hm hn hnm (le_trans (le_max_left M0a M0b) hM0) p hp0 hp1 hsparse ν
          h_var h_xmean h_tail b c XT hb hc hXT
      have hcoordm : ∀ (i : Fin m) (j : Fin n), Measurable fun x : Matrix (Fin m) (Fin n) ℝ => x i j :=
        hcoordGen m n
      have hmean : ∀ (i : Fin m) (j : Fin n), ∫ x, XT x i j ∂ν = 0 := by
        intro i j
        have hf_int : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ =>
            x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0)) ν := by
          have hind : Measurable fun x : Matrix (Fin m) (Fin n) ℝ =>
              (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) :=
            hintGen m n i j _
          refine MeasureTheory.Integrable.of_bound
            ((hcoordm i j).mul hind).aemeasurable.aestronglyMeasurable
            |(CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)| ?_
          filter_upwards with x
          by_cases hx : (|x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4))
          · rw [if_pos hx, mul_one, Real.norm_eq_abs]
            exact le_trans hx (le_abs_self _)
          · rw [if_neg hx, mul_zero, norm_zero]
            exact abs_nonneg _
        have hnum : ∫ x, (x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ∂ν = 0 := by
          rw [MeasureTheory.integral_sub hf_int (MeasureTheory.integrable_const (b i j)), (hb i j).symm]
          simp
        have hfun : (fun x : Matrix (Fin m) (Fin n) ℝ => XT x i j) = fun x =>
            (x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) / c i j :=
          funext fun x => hXT x i j
        rw [hfun, MeasureTheory.integral_div, hnum, zero_div]
      have hvar : ∀ (i : Fin m) (j : Fin n), ∫ x, (XT x i j) ^ 2 ∂ν = 1 := by
        intro i j
        have hIpos : 0 < ∫ x, (x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν := by
          have h : 0 < Real.sqrt (∫ x, (x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν) := by
            rw [← hc i j]
            exact h1 i j
          exact Real.sqrt_pos.mp h
        have hI : (c i j) ^ 2 = ∫ x, (x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν := by
          rw [hc i j]
          exact Real.sq_sqrt (le_of_lt hIpos)
        have hfun : (fun x : Matrix (Fin m) (Fin n) ℝ => (XT x i j) ^ 2) = fun x =>
            (x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 / (c i j) ^ 2 := by
          funext x
          rw [hXT x i j, div_pow]
        rw [hfun, MeasureTheory.integral_div, ← hI]
        exact div_self (ne_of_gt (pow_pos (h1 i j) 2))
      exact ⟨h1, hmean, hvar, h2, h3,
        htransferAll m n hm hn hnm (le_trans (le_max_right M0a M0b) hM0) p hp0 hp1 hsparse
          ν h_var h_xmean h_tail b c XT hb hc hXT⟩
    refine ⟨M0, ?_⟩
    intro m n hm hn hnm hM0 p hp0 hp1 hsparse ν hν h_var h_xmean h_tail
    let b : Fin m → Fin n → ℝ := fun i j => ∫ x, x i j * (if |x i j| ≤
      (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) ∂ν
    let c : Fin m → Fin n → ℝ := fun i j => Real.sqrt (∫ x, (x i j * (if |x i j| ≤
      (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν)
    let XT : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ := fun x i j =>
      (x i j * (if |x i j| ≤
        (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) / c i j
    have hb : ∀ (i : Fin m) (j : Fin n), b i j = ∫ x, x i j * (if |x i j| ≤
        (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) ∂ν :=
      fun i j => rfl
    have hc : ∀ (i : Fin m) (j : Fin n), c i j = Real.sqrt (∫ x, (x i j * (if |x i j| ≤
        (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν) :=
      fun i j => rfl
    have hXT : ∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
        XT x i j = (x i j * (if |x i j| ≤
          (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) / c i j :=
      fun x i j => rfl
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      hcore m n hm hn hnm hM0 p hp0 hp1 hsparse ν h_var h_xmean h_tail b c XT hb hc hXT
    exact ⟨b, c, XT, hb, hc, h1, hXT, h2, h3, h4, h5, h6⟩
  obtain ⟨M0, htrunc⟩ := trunc
  obtain ⟨Ce, hCe, M1', hM1'⟩ :=
    statopia_math_node_387310739_6591aef4 D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le_one
      Kt hKt alpha0 halpha0 CD hCD
  refine ⟨Ce, hCe, max M1' M0, ?_⟩
  intro m n hm hn hnm hM1 rho_lo rho_hi p hp0 hp1 hsparse Ω hΩ μ hμ Xi Mask
    hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val
    hMask_law hMask_indep hIndep
  have hXmeas : Measurable fun ω => Xi ω :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hXi_meas i j
  let ν : Measure (Matrix (Fin m) (Fin n) ℝ) := μ.map (fun ω => Xi ω)
  haveI hν : IsProbabilityMeasure ν :=
    MeasureTheory.Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  have hcoord : ∀ (i : Fin m) (j : Fin n), Measurable fun x : Matrix (Fin m) (Fin n) ℝ => x i j :=
    hcoordGen m n
  obtain ⟨b, c, XT, hb, hc, hc_pos, hXT, hXT_mean, hXT_var, hXT_bound, htail, htransfer⟩ :=
    htrunc m n hm hn hnm (le_trans (le_max_right M1' M0) hM1) p hp0 hp1 hsparse ν
      (fun i j => by
        have hmeas : Measurable fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2 := by
          simpa [pow_two] using (hcoord i j).mul (hcoord i j)
        rw [MeasureTheory.integral_map hXmeas.aemeasurable
          (f := fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2)
          hmeas.aemeasurable.aestronglyMeasurable]
        exact hXi_var i j)
      (fun i j => by
        rw [MeasureTheory.integral_map hXmeas.aemeasurable
          (f := fun x : Matrix (Fin m) (Fin n) ℝ => x i j)
          (hcoord i j).aemeasurable.aestronglyMeasurable]
        exact hXi_mean i j)
      (fun i j t ht => by
        have hcont : Measurable fun x : Matrix (Fin m) (Fin n) ℝ => |x i j| :=
          Measurable.abs (hcoord i j)
        have hset : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} :=
          measurableSet_lt measurable_const hcont
        rw [MeasureTheory.Measure.map_apply hXmeas hset]
        exact hXi_tail i j t ht)
  have hbμ : ∀ (i : Fin m) (j : Fin n), b i j = ∫ ω, Xi ω i j * (if |Xi ω i j| ≤
      (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) ∂μ := by
    intro i j
    have hind : Measurable fun x : Matrix (Fin m) (Fin n) ℝ =>
        (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) :=
      hintGen m n i j _
    rw [hb i j, MeasureTheory.integral_map hXmeas.aemeasurable
      (f := fun x : Matrix (Fin m) (Fin n) ℝ => x i j * (if |x i j| ≤
        (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0))
      ((hcoord i j).mul hind).aemeasurable.aestronglyMeasurable]
  have hcμ : ∀ (i : Fin m) (j : Fin n), c i j = Real.sqrt (∫ ω, (Xi ω i j * (if |Xi ω i j| ≤
      (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ) := by
    intro i j
    have hind : Measurable fun x : Matrix (Fin m) (Fin n) ℝ =>
        (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) :=
      hintGen m n i j _
    have hg : Measurable fun x : Matrix (Fin m) (Fin n) ℝ =>
        x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) :=
      (hcoord i j).mul hind
    have hsq : Measurable fun x : Matrix (Fin m) (Fin n) ℝ =>
        (x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2 := by
      have h : Measurable fun x : Matrix (Fin m) (Fin n) ℝ =>
          x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j :=
        hg.sub measurable_const
      simpa [pow_two] using h.mul h
    rw [hc i j, MeasureTheory.integral_map hXmeas.aemeasurable
      (f := fun x : Matrix (Fin m) (Fin n) ℝ =>
        (x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) ^ 2)
      hsq.aemeasurable.aestronglyMeasurable]
  have hXT_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun x : Matrix (Fin m) (Fin n) ℝ => XT x i j := by
    intro i j
    have hind : Measurable fun x : Matrix (Fin m) (Fin n) ℝ =>
        (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) :=
      hintGen m n i j _
    have hg : Measurable fun x : Matrix (Fin m) (Fin n) ℝ =>
        x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) :=
      (hcoord i j).mul hind
    have hfun : (fun x : Matrix (Fin m) (Fin n) ℝ => XT x i j) = fun x =>
        (x i j * (if |x i j| ≤ (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) then (1 : ℝ) else 0) - b i j) / c i j :=
      funext fun x => hXT x i j
    rw [hfun]
    exact (hg.sub measurable_const).div measurable_const
  have hmeanμ : ∀ (i : Fin m) (j : Fin n), ∫ ω, XT (Xi ω) i j ∂μ = 0 := by
    intro i j
    rw [← MeasureTheory.integral_map hXmeas.aemeasurable
      (f := fun x : Matrix (Fin m) (Fin n) ℝ => XT x i j)
      (hXT_meas i j).aemeasurable.aestronglyMeasurable]
    exact hXT_mean i j
  have hvarμ : ∀ (i : Fin m) (j : Fin n), ∫ ω, (XT (Xi ω) i j) ^ 2 ∂μ = 1 := by
    intro i j
    have hs : Measurable fun x : Matrix (Fin m) (Fin n) ℝ => (XT x i j) ^ 2 := by
      simpa [pow_two] using (hXT_meas i j).mul (hXT_meas i j)
    rw [← MeasureTheory.integral_map hXmeas.aemeasurable
      (f := fun x : Matrix (Fin m) (Fin n) ℝ => (XT x i j) ^ 2)
      hs.aemeasurable.aestronglyMeasurable]
    exact hXT_var i j
  have htailμ : μ {ω : Ω | ∃ (i : Fin m) (j : Fin n),
      (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) < |Xi ω i j|} ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10))) := by
    have hset : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n),
        (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) < |x i j|} := by
      have h : MeasurableSet (⋃ (i : Fin m) (j : Fin n), {x : Matrix (Fin m) (Fin n) ℝ |
          (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) < |x i j|}) :=
        MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
          measurableSet_lt measurable_const (Measurable.abs (hcoord i j))
      have hsetEq : (⋃ (i : Fin m) (j : Fin n), {x : Matrix (Fin m) (Fin n) ℝ |
          (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) < |x i j|}) =
          {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n),
            (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) < |x i j|} := by
        ext x
        simp [Set.mem_iUnion]
      rw [hsetEq] at h
      exact h
    have hEq : ν {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n),
        (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) < |x i j|} =
        μ {ω : Ω | ∃ (i : Fin m) (j : Fin n),
          (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) < |Xi ω i j|} :=
      MeasureTheory.Measure.map_apply hXmeas hset
    rw [← hEq]
    exact htail
  obtain ⟨G, hGmeas, hGμ, hGbound⟩ :=
    hM1' m n hm hn hnm (le_trans (le_max_left M1' M0) hM1) rho_lo rho_hi p hp0 hp1 hsparse
      (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) rfl
      μ Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
      hMask_meas hMask_val hMask_law hMask_indep hIndep
      b c hbμ hcμ hc_pos (fun ω => XT (Xi ω)) (fun ω i j => hXT (Xi ω) i j) hmeanμ hvarμ
      (fun ω i j => hXT_bound (Xi ω) i j) htailμ
      (fun ω hω => htransfer (Mask ω) (fun i j => hMask_val i j ω) (Xi ω) hω)
  refine ⟨G, hGmeas, hGμ, hGbound, ?_⟩
  · have hsub : {ω : Ω | 4 < ‖maskedScaled p (Xi ω) (Mask ω)‖} ⊆ Gᶜ := by
      intro ω hω
      simp only [Set.mem_compl_iff]
      intro hG
      exact absurd (hGbound ω hG).2.2 (not_le.mpr hω)
    exact le_trans (MeasureTheory.measure_mono hsub) hGμ
  /- @proof-region region.target-node.session.aa262d1694585ad2 end -/

#print axioms statopia_math_node_790018995_867172dc
end Statlib.Imported

