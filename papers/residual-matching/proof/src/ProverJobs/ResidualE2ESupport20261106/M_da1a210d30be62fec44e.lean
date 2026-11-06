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
theorem statopia_math_node_318634017_8ba2f28f : ∀ (m n : ℕ) (hm : 0 < m) (p : ℝ) (hp : p ≤ 1)
    (u v : Fin m × Fin n),
    ∫ z : (Fin m × Fin n) → ℝ, z u * z v
      ∂(MeasureTheory.Measure.pi (fun _ : Fin m × Fin n =>
          ProbabilityTheory.gaussianReal 0 ((1 - p) / (m : ℝ)).toNNReal))
      = if u = v then (1 - p) / (m : ℝ) else 0 := by
  /- @proof-region region.target-node.session.1250752b7633c9fe begin -/
  intro m n hm p hp u v
  set κ : ℝ := (1 - p) / (m : ℝ) with hκdef
  set v₀ : NNReal := κ.toNNReal with hv₀def
  set μ : Fin m × Fin n → Measure ℝ := fun _ => gaussianReal 0 v₀ with hμdef
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hκ_nn : 0 ≤ κ := by
    rw [hκdef]; exact div_nonneg (by linarith) (le_of_lt hmR)
  have hcast : (v₀ : ℝ) = κ := by
    rw [hv₀def]; exact Real.coe_toNNReal κ hκ_nn
  have h_id : ∫ y : ℝ, y ∂(gaussianReal 0 v₀) = 0 := by
    simpa using (ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := v₀))
  have h_one : ∫ y : ℝ, (1 : ℝ) ∂(gaussianReal 0 v₀) = 1 := by
    simp
  have h_sq : ∫ y : ℝ, y * y ∂(gaussianReal 0 v₀) = κ := by
    have h1 : (v₀ : ℝ) = ∫ y : ℝ, y * y ∂(gaussianReal 0 v₀) := by
      have h2 := ProbabilityTheory.variance_eq_integral (X := fun y : ℝ => y) (μ := gaussianReal 0 v₀) measurable_id.aemeasurable
      rw [ProbabilityTheory.variance_fun_id_gaussianReal] at h2
      simpa [h_id, pow_two] using h2
    rw [← hcast, ← h1]
  have hfac : ∀ i : Fin m × Fin n, (∫ y : ℝ, (if i = u then y * y else (1:ℝ)) ∂(gaussianReal 0 v₀)) = (if i = u then κ else 1) := by
    intro i
    by_cases hi : i = u
    · have hR : (if i = u then κ else (1:ℝ)) = κ := if_pos hi
      rw [hR]
      rw [show (fun y : ℝ => (if i = u then y * y else (1:ℝ))) = (fun y : ℝ => y * y) from by
        funext y; simp only [if_pos hi]]
      exact h_sq
    · have hR : (if i = u then κ else (1:ℝ)) = 1 := if_neg hi
      rw [hR]
      rw [show (fun y : ℝ => (if i = u then y * y else (1:ℝ))) = (fun _ => (1:ℝ)) from by
        funext y; simp only [if_neg hi]]
      exact h_one
  by_cases huv : u = v
  · rw [if_pos huv, ← huv]
    calc ∫ z : Fin m × Fin n → ℝ, z u * z u ∂(Measure.pi μ)
        = ∫ z : Fin m × Fin n → ℝ, (∏ i, (if i = u then z i * z i else (1:ℝ))) ∂(Measure.pi μ) := by
            rw [show (fun z : (Fin m × Fin n) → ℝ => z u * z u) = (fun z => ∏ i, (if i = u then z i * z i else (1:ℝ))) from by
              funext z
              rw [Finset.prod_eq_single (s := Finset.univ) (f := fun i => if i = u then z i * z i else (1:ℝ)) u (fun b _ hbu => by simp [hbu]) (fun hmem => absurd (Finset.mem_univ u) hmem)]
              simp]
      _ = ∏ i, ∫ y : ℝ, (if i = u then y * y else (1:ℝ)) ∂(gaussianReal 0 v₀) := MeasureTheory.integral_fintype_prod_eq_prod (μ := μ) (f := fun (i : Fin m × Fin n) (y : ℝ) => if i = u then y * y else (1:ℝ))
      _ = κ := by
            simp only [hfac]
            rw [Finset.prod_eq_single (s := Finset.univ) (f := fun i => if i = u then κ else (1:ℝ)) u (fun b _ hbu => by simp [hbu]) (fun hmem => absurd (Finset.mem_univ u) hmem)]
            simp
  · rw [if_neg huv]
    have hfv : ∀ i : Fin m × Fin n, (∫ y : ℝ, ((if i = u then y else (1:ℝ)) * (if i = v then y else (1:ℝ))) ∂(gaussianReal 0 v₀)) = (if i = u then 0 else if i = v then 0 else 1) := by
      intro i
      by_cases hiu : i = u
      · have hiv : i ≠ v := by rw [hiu]; exact huv
        have hfun : (fun y : ℝ => ((if i = u then y else (1:ℝ)) * (if i = v then y else (1:ℝ)))) = (fun y : ℝ => y) := by
          funext y
          rw [if_pos hiu, if_neg hiv]
          simp
        rw [hfun]
        rw [if_pos hiu]
        exact h_id
      · by_cases hiv : i = v
        · have hfun : (fun y : ℝ => ((if i = u then y else (1:ℝ)) * (if i = v then y else (1:ℝ)))) = (fun y : ℝ => y) := by
            funext y
            rw [if_neg hiu, if_pos hiv]
            simp
          rw [hfun]
          rw [if_neg hiu, if_pos hiv]
          exact h_id
        · have hfun : (fun y : ℝ => ((if i = u then y else (1:ℝ)) * (if i = v then y else (1:ℝ)))) = (fun _ => (1:ℝ)) := by
            funext y
            rw [if_neg hiu, if_neg hiv]
            simp
          rw [hfun]
          rw [if_neg hiu, if_neg hiv]
          exact h_one
    calc ∫ z : Fin m × Fin n → ℝ, z u * z v ∂(Measure.pi μ)
        = ∫ z : Fin m × Fin n → ℝ, (∏ i, ((if i = u then z i else (1:ℝ)) * (if i = v then z i else (1:ℝ)))) ∂(Measure.pi μ) := by
            rw [show (fun z : (Fin m × Fin n) → ℝ => z u * z v) = (fun z => ∏ i, ((if i = u then z i else (1:ℝ)) * (if i = v then z i else (1:ℝ)))) from by
              funext z
              rw [Finset.prod_mul_distrib]
              rw [Finset.prod_eq_single (s := Finset.univ) (f := fun i => if i = u then z i else (1:ℝ)) u (fun b _ hbu => by simp [hbu]) (fun hmem => absurd (Finset.mem_univ u) hmem)]
              rw [Finset.prod_eq_single (s := Finset.univ) (f := fun i => if i = v then z i else (1:ℝ)) v (fun b _ hbv => by simp [hbv]) (fun hmem => absurd (Finset.mem_univ v) hmem)]
              simp]
      _ = ∏ i, ∫ y : ℝ, ((if i = u then y else (1:ℝ)) * (if i = v then y else (1:ℝ))) ∂(gaussianReal 0 v₀) := MeasureTheory.integral_fintype_prod_eq_prod (μ := μ) (f := fun (i : Fin m × Fin n) (y : ℝ) => (if i = u then y else (1:ℝ)) * (if i = v then y else (1:ℝ)))
      _ = 0 := by
            simp only [hfv]
            rw [Finset.prod_eq_zero (s := Finset.univ) (f := fun i => if i = u then 0 else if i = v then 0 else (1:ℝ)) (Finset.mem_univ u) (by simp)]
  /- @proof-region region.target-node.session.1250752b7633c9fe end -/

end

end Statlib.Imported

