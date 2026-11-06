import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_655541399eba6e711ce1
import ProverJobs.ResidualE2ESupport20261106.M_4de8442c71140ee396a1
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5
import ProverJobs.ResidualE2ESupport20261106.M_24e4399710401de9771f

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_784642610_04ca9caa : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : max (Kt * (D0 + 12)) (D0 + 20) ≤ CD),
    ∃ Ce : ℝ, 0 < Ce ∧
      ∃ M1 : ℕ,
        ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM1 : M1 ≤ m)
          (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
          (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
          (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
          (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p),
        ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (XT Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => XT ω i j) →
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
          (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
          (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => XT ω ij.1 ij.2) μ →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
          IndepFun (fun ω (ij : Fin m × Fin n) => XT ω ij.1 ij.2)
            (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, XT ω i j ∂μ = 0) →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1) →
          (let L : ℝ := CD * Real.log ((m : ℝ) * (n : ℝ)) +
              (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4;
            ∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L) →
          ∃ G : Set Ω, MeasurableSet G ∧
            μ Gᶜ ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 4))) ∧
            ∀ ω ∈ G,
              svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩ ≤
                1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + Ce * deltaM m ∧
              1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - Ce * deltaM m ≤
                svals (maskedScaled p (XT ω) (Mask ω)) ⟨n - 1, by omega⟩ := by
  /- @proof-region region.target-node.session.493c3706cd9395e0 begin -/
  intro D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le Kt hKt alpha0 halpha0 CD hCD
  classical
  obtain ⟨M1, hconc⟩ :=
    statopia_math_node_2003834469_81c5daa0 D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le Kt hKt
      alpha0 halpha0 CD hCD
  refine ⟨1, by norm_num, M1, ?_⟩
  intro m n hm hn hnm hM1 hrho_lo hrho_hi p hp0 hp1 hsparse
  intro Ω _ μ _ XT Mask hXTmeas hMaskmeas hMask01 hMaskprob hXTindep hMaskindep
    hIndep hXTmean hXT2
  intro hXTbound0
  let L : ℝ := CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4
  have hXTbound : ∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L := by
    intro ω i j
    exact hXTbound0 ω i j
  have hXTint : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => XT ω i j) μ := by
    intro i j
    refine MeasureTheory.Integrable.of_bound (hXTmeas i j).aestronglyMeasurable (3 * L) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hXTbound ω i j
  have hXTint2 : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (XT ω i j) ^ 2) μ := by
    intro i j
    refine (MeasureTheory.memLp_two_iff_integrable_sq (hXTmeas i j).aestronglyMeasurable).1 ?_
    exact MeasureTheory.MemLp.of_bound (hXTmeas i j).aestronglyMeasurable (3 * L) (by
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact hXTbound ω i j)

  let G : Set Ω := {ω | svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩
        ≤ 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m ∧
      1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - 1 * deltaM m
        ≤ svals (maskedScaled p (XT ω) (Mask ω)) ⟨n - 1, by omega⟩}
  have hGcompl : Gᶜ = {ω | 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m
          < svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩} ∪
        {ω | svals (maskedScaled p (XT ω) (Mask ω)) ⟨n - 1, by omega⟩
          < 1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - 1 * deltaM m} := by
    ext ω
    simp only [G, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_union, not_and_or, not_le]
  refine ⟨G, ?_, ?_, ?_⟩
  · have hsvals_meas : ∀ i : Fin n,
        Measurable (fun ω : Ω => svals (maskedScaled p (XT ω) (Mask ω)) i) :=
      statopia_math_node_760072556_5eef0e48 m n (fun ω => maskedScaled p (XT ω) (Mask ω))
        (fun i j => ((hMaskmeas i j).mul (hXTmeas i j)).div_const (Real.sqrt ((m : ℝ) * p)))
    exact (measurableSet_le (hsvals_meas ⟨0, by omega⟩) measurable_const).inter
      (measurableSet_le measurable_const (hsvals_meas ⟨n - 1, by omega⟩))
  · rw [hGcompl]
    refine le_trans (measure_union_le _ _) ?_
    exact hconc m n hm hn hnm hM1 hrho_lo hrho_hi p hp0 hp1 hsparse μ XT Mask
      hXTmeas hXTint hXTint2 hMaskmeas hMask01 hMaskprob hXTindep hMaskindep hIndep hXTmean hXT2
      hXTbound
  · intro ω hω
    exact hω
  /- @proof-region region.target-node.session.493c3706cd9395e0 end -/

#print axioms statopia_math_node_784642610_04ca9caa
end Statlib.Imported

