import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_204015260_c65710ba_ef38b55c
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_4215527874_039d8d35_ee5a4db7

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_143024508_b4549bff : ∀ (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m p : ℕ) (hp : 0 < p)
    (muY : Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (i : Fin m) (j k : Fin p),
    Integrable (fun ω : Ω => (G i ω j - muY j) * (G i ω k - muY k)) P
      ∧ ∫ ω, ((G i ω j - muY j) * (G i ω k - muY k)) ∂P = covY P muY Y i j k := by
  /- @proof-region region.target-node.session.2fd6a90b538af4c1 begin -/
  intro Ω _ P _ m p hp muY Y G hGm hGcov i j k
  set Z : Ω → Fin p → ℝ := fun ω l => G i ω l - muY l with hZdef
  have hZmeas : ∀ l : Fin p, Measurable (fun ω => Z ω l) := by
    intro l
    have h1 : Measurable (fun ω => G i ω l) := (measurable_pi_apply l).comp (hGm i)
    have h2 : Measurable (fun _ : Ω => muY l) := measurable_const
    have h3 : Measurable (fun ω => G i ω l - muY l) := h1.sub h2
    simpa only [hZdef] using h3
  have hZcov : IsCenteredGaussianVector P Z (covY P muY Y i) := hGcov i
  have hmem : ∀ l : Fin p, MemLp (fun ω => Z ω l) 2 P := fun l =>
    (statopia_math_node_204015260_c65710ba P p hp Z hZmeas (covY P muY Y i) hZcov l).2.1
  have hsym : (covY P muY Y i).transpose = covY P muY Y i := by
    ext a b
    simp only [Matrix.transpose_apply, covY]
    apply integral_congr_ae
    filter_upwards with ω
    ring
  refine ⟨?_, ?_⟩
  · exact MemLp.integrable_mul (hmem j) (hmem k)
  · have hbridge : ∀ u : Fin p → ℝ,
        ∫ ω, (∑ l, u l * Z ω l) ^ 2 ∂P
          = ∑ a, ∑ b,
              u a * ((2 : ℝ)⁻¹ • (covY P muY Y i + (covY P muY Y i).transpose)) a b * u b :=
      fun u => statopia_math_node_4215527874_039d8d35 P (covY P muY Y i) Z hZmeas hZcov hp u
    set S : Matrix (Fin p) (Fin p) ℝ :=
      (2 : ℝ)⁻¹ • (covY P muY Y i + (covY P muY Y i).transpose) with hS
    set up : Fin p → ℝ :=
      fun l => (if l = j then (1 : ℝ) else 0) + (if l = k then 1 else 0) with hup
    set um : Fin p → ℝ :=
      fun l => (if l = j then (1 : ℝ) else 0) + (if l = k then (-1 : ℝ) else 0) with hum
    have hsumup : ∀ ω, (∑ l, up l * Z ω l) = Z ω j + Z ω k := by
      intro ω
      simp [hup, add_mul, Finset.sum_add_distrib]
    have hsumum : ∀ ω, (∑ l, um l * Z ω l) = Z ω j - Z ω k := by
      intro ω
      simp [hum, add_mul, Finset.sum_add_distrib, sub_eq_add_neg]
    have hSeq : S = covY P muY Y i := by
      have h2 : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by norm_num
      rw [hS, hsym, smul_add, ← add_smul, h2, one_smul]
    have hcross : ∀ a₁ b₁ : Fin p,
        (∑ a, ∑ b, (if a = a₁ then (1 : ℝ) else 0) * S a b * (if b = b₁ then (1 : ℝ) else 0))
          = S a₁ b₁ := by
      intro a₁ b₁
      have hb : ∀ a : Fin p, (∑ b, S a b * (if b = b₁ then (1 : ℝ) else 0)) = S a b₁ := by
        intro a
        simp
      calc (∑ a, ∑ b, (if a = a₁ then (1 : ℝ) else 0) * S a b * (if b = b₁ then (1 : ℝ) else 0))
          = ∑ a, (if a = a₁ then (1 : ℝ) else 0)
              * (∑ b, S a b * (if b = b₁ then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
        _ = ∑ a, (if a = a₁ then (1 : ℝ) else 0) * S a b₁ := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hb a]
        _ = S a₁ b₁ := by
            simp
    set vj : Fin p → ℝ := fun l => if l = j then (1 : ℝ) else 0 with hvj
    set vk : Fin p → ℝ := fun l => if l = k then (1 : ℝ) else 0 with hvk
    have hsumj : ∀ ω, (∑ l, vj l * Z ω l) = Z ω j := by
      intro ω
      simp [hvj]
    have hsumk : ∀ ω, (∑ l, vk l * Z ω l) = Z ω k := by
      intro ω
      simp [hvk]
    have hvalj : (∑ a, ∑ b, vj a * S a b * vj b) = S j j := by
      simpa only [hvj] using hcross j j
    have hvalk : (∑ a, ∑ b, vk a * S a b * vk b) = S k k := by
      simpa only [hvk] using hcross k k
    have hvalup : (∑ a, ∑ b, up a * S a b * up b) = S j j + S j k + S k j + S k k := by
      have hexp : ∀ a b : Fin p,
          up a * S a b * up b
            = (if a = j then (1 : ℝ) else 0) * S a b * (if b = j then (1 : ℝ) else 0)
              + (if a = j then (1 : ℝ) else 0) * S a b * (if b = k then (1 : ℝ) else 0)
              + (if a = k then (1 : ℝ) else 0) * S a b * (if b = j then (1 : ℝ) else 0)
              + (if a = k then (1 : ℝ) else 0) * S a b * (if b = k then (1 : ℝ) else 0) := by
        intro a b
        simp only [hup]
        ring
      simp only [hexp, Finset.sum_add_distrib]
      rw [hcross j j, hcross j k, hcross k j, hcross k k]
    have hJJ : ∫ ω, Z ω j ^ 2 ∂P = S j j := by
      have h1 : ∫ ω, (∑ l, vj l * Z ω l) ^ 2 ∂P = ∑ a, ∑ b, vj a * S a b * vj b :=
        hbridge vj
      rw [hvalj] at h1
      simpa only [hsumj] using h1
    have hKK : ∫ ω, Z ω k ^ 2 ∂P = S k k := by
      have h1 : ∫ ω, (∑ l, vk l * Z ω l) ^ 2 ∂P = ∑ a, ∑ b, vk a * S a b * vk b :=
        hbridge vk
      rw [hvalk] at h1
      simpa only [hsumk] using h1
    have hSum : ∫ ω, (Z ω j + Z ω k) ^ 2 ∂P = S j j + S j k + S k j + S k k := by
      have h1 : ∫ ω, (∑ l, up l * Z ω l) ^ 2 ∂P = ∑ a, ∑ b, up a * S a b * up b := hbridge up
      rw [hvalup] at h1
      simpa only [hsumup] using h1
    have hJJint : Integrable (fun ω => Z ω j ^ 2) P := MemLp.integrable_sq (hmem j)
    have hKKint : Integrable (fun ω => Z ω k ^ 2) P := MemLp.integrable_sq (hmem k)
    have hSumint : Integrable (fun ω => (Z ω j + Z ω k) ^ 2) P :=
      MemLp.integrable_sq ((hmem j).add (hmem k))
    have hpair : S j k + S k j = 2 * covY P muY Y i j k := by
      have hsymjk : covY P muY Y i k j = covY P muY Y i j k := by
        have h := congrFun (congrFun hsym j) k
        simpa using h
      rw [hSeq, hsymjk]
      ring
    have hKint : Integrable (fun ω => Z ω j ^ 2 + Z ω k ^ 2) P := hJJint.add hKKint
    have hA :
        ∫ ω, ((Z ω j + Z ω k) ^ 2 - (Z ω j ^ 2 + Z ω k ^ 2)) ∂P
          = (S j j + S j k + S k j + S k k) - (S j j + S k k) := by
      rw [integral_sub hSumint hKint, hSum, integral_add hJJint hKKint, hJJ, hKK]
    have hpoly :
        ∫ ω, 2 * (Z ω j * Z ω k) ∂P
          = (S j j + S j k + S k j + S k k) - (S j j + S k k) := by
      rw [← hA]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    have h2 :
        2 * ∫ ω, Z ω j * Z ω k ∂P
          = (S j j + S j k + S k j + S k k) - (S j j + S k k) := by
      rwa [integral_const_mul] at hpoly
    have hX : ∫ ω, Z ω j * Z ω k ∂P = covY P muY Y i j k := by
      have hlin : (S j j + S j k + S k j + S k k) - (S j j + S k k)
          = 2 * covY P muY Y i j k := by
        linarith [hpair]
      have h4 : 2 * ∫ ω, Z ω j * Z ω k ∂P = 2 * covY P muY Y i j k := by
        rw [h2, hlin]
      linarith
    exact hX
  /- @proof-region region.target-node.session.2fd6a90b538af4c1 end -/

end

end Statlib.Imported

