import Statlib.HighDim.Geometry.CoveringNumbers
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_b34aa34a4b446c8039a4
import ProverJobs.ResidualE2ESupport20261106.M_9688f84b736e5558a979

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
theorem statopia_math_node_2221798330_49ffe8bf : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 4),
    ∃ (N : ℕ) (_hN : 1 ≤ N) (x : Fin N → Fin m → ℝ) (y : Fin N → Fin n → ℝ),
      (∀ k : Fin N, (∑ i : Fin m, (x k i) ^ 2) = 1) ∧
      (∀ k : Fin N, (∑ j : Fin n, (y k j) ^ 2) = 1) ∧
      (∀ (u : Fin m → ℝ) (v : Fin n → ℝ),
        (∑ i : Fin m, (u i) ^ 2) = 1 → (∑ j : Fin n, (v j) ^ 2) = 1 →
        ∃ k : Fin N,
          (∑ i : Fin m, (x k i - u i) ^ 2) ≤ δ ^ 2 ∧
          (∑ j : Fin n, (y k j - v j) ^ 2) ≤ δ ^ 2) ∧
      (∀ A : Matrix (Fin m) (Fin n) ℝ,
        ‖A‖ ≤ (1 - 2 * δ)⁻¹ *
          (⨆ k : Fin N, ∑ i : Fin m, ∑ j : Fin n, x k i * A i j * y k j)) := by
  /- @proof-region region.target-node.session.c32bbf8765bcda56 begin -/
  intro m n hm hn δ hδ_pos hδ_lt
  obtain ⟨Nx, Tx, hTx_unit, hTx_cov, _hTx_card⟩ :=
    Statlib.HighDim.Geometry.exists_euclidean_unit_sphere_net_card_le_three_div
      (s := m) (by omega) δ hδ_pos (by linarith)
  obtain ⟨Ny, Ty, hTy_unit, hTy_cov, _hTy_card⟩ :=
    Statlib.HighDim.Geometry.exists_euclidean_unit_sphere_net_card_le_three_div
      (s := n) (by omega) δ hδ_pos (by linarith)
  have hterm : ∀ r : ℝ, ‖r‖ ^ 2 = r ^ 2 := by
    intro r
    rw [Real.norm_eq_abs, sq_abs]
  have hnorm_sq : ∀ (s : ℕ) (z : EuclideanSpace ℝ (Fin s)),
      ‖z‖ ^ 2 = ∑ i, (z.ofLp i) ^ 2 := by
    intro s z
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => hterm (z.ofLp i)
  have htoLp_norm : ∀ (s : ℕ) (w : Fin s → ℝ),
      ‖WithLp.toLp (p := 2) w‖ = Real.sqrt (∑ i, (w i) ^ 2) := by
    intro s w
    have hsq : ‖WithLp.toLp (p := 2) w‖ ^ 2 = ∑ i, (w i) ^ 2 := by
      rw [hnorm_sq]
    have hnn : 0 ≤ ∑ i, (w i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [eq_comm, Real.sqrt_eq_iff_eq_sq hnn (norm_nonneg _)]
    exact hsq.symm
  have hunit_nonempty : ∀ (s : ℕ), 1 ≤ s → ∃ w : Fin s → ℝ, ∑ i, (w i) ^ 2 = 1 := by
    intro s hs
    refine ⟨fun i => if i = (⟨0, by omega⟩ : Fin s) then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin s)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hNx : 1 ≤ Nx := by
    obtain ⟨w, hw⟩ := hunit_nonempty m hm
    have hU : ‖WithLp.toLp (p := 2) w‖ = 1 := by rw [htoLp_norm, hw, Real.sqrt_one]
    obtain ⟨q, _⟩ := hTx_cov _ hU
    have := q.isLt; omega
  have hNy : 1 ≤ Ny := by
    obtain ⟨w, hw⟩ := hunit_nonempty n hn
    have hU : ‖WithLp.toLp (p := 2) w‖ = 1 := by rw [htoLp_norm, hw, Real.sqrt_one]
    obtain ⟨q, _⟩ := hTy_cov _ hU
    have := q.isLt; omega
  have hN : 1 ≤ Nx * Ny := by
    have := Nat.mul_le_mul hNx hNy; simpa using this
  set e : Fin Nx × Fin Ny ≃ Fin (Nx * Ny) := finProdFinEquiv (m := Nx) (n := Ny) with he
  set x : Fin (Nx * Ny) → Fin m → ℝ :=
    fun k => (Tx (e.symm k).1).ofLp with hx_def
  set y : Fin (Nx * Ny) → Fin n → ℝ :=
    fun k => (Ty (e.symm k).2).ofLp with hy_def
  have hcov : ∀ (u : Fin m → ℝ) (v : Fin n → ℝ),
      (∑ i, (u i) ^ 2 = 1) → (∑ j, (v j) ^ 2 = 1) →
      ∃ k, (∑ i, (x k i - u i) ^ 2) ≤ δ ^ 2 ∧ (∑ j, (y k j - v j) ^ 2) ≤ δ ^ 2 := by
    intro u v hu hv
    have hU : ‖WithLp.toLp (p := 2) u‖ = 1 := by rw [htoLp_norm, hu, Real.sqrt_one]
    have hV : ‖WithLp.toLp (p := 2) v‖ = 1 := by rw [htoLp_norm, hv, Real.sqrt_one]
    obtain ⟨q1, hq1⟩ := hTx_cov (WithLp.toLp (p := 2) u) hU
    obtain ⟨q2, hq2⟩ := hTy_cov (WithLp.toLp (p := 2) v) hV
    refine ⟨e (q1, q2), ?_, ?_⟩
    · have heq : dist (Tx q1) (WithLp.toLp (p := 2) u) ^ 2
          = ∑ i, ((Tx q1).ofLp i - u i) ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq]
        apply Finset.sum_congr rfl; intro i _
        rw [dist_eq_norm, Real.norm_eq_abs, sq_abs]
      simp only [hx_def, Equiv.symm_apply_apply]
      rw [← heq]
      have hd : dist (Tx q1) (WithLp.toLp (p := 2) u) ≤ δ := by
        rw [dist_eq_norm]; exact hq1
      have h1 : (0:ℝ) ≤ δ - dist (Tx q1) (WithLp.toLp (p := 2) u) := by linarith
      have h2 : (0:ℝ) ≤ δ + dist (Tx q1) (WithLp.toLp (p := 2) u) := by
        linarith [dist_nonneg (x := Tx q1) (y := WithLp.toLp (p := 2) u)]
      nlinarith [mul_nonneg h1 h2]
    · have heq : dist (Ty q2) (WithLp.toLp (p := 2) v) ^ 2
          = ∑ j, ((Ty q2).ofLp j - v j) ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq]
        apply Finset.sum_congr rfl; intro j _
        rw [dist_eq_norm, Real.norm_eq_abs, sq_abs]
      simp only [hy_def, Equiv.symm_apply_apply]
      rw [← heq]
      have hd : dist (Ty q2) (WithLp.toLp (p := 2) v) ≤ δ := by
        rw [dist_eq_norm]; exact hq2
      have h1 : (0:ℝ) ≤ δ - dist (Ty q2) (WithLp.toLp (p := 2) v) := by linarith
      have h2 : (0:ℝ) ≤ δ + dist (Ty q2) (WithLp.toLp (p := 2) v) := by
        linarith [dist_nonneg (x := Ty q2) (y := WithLp.toLp (p := 2) v)]
      nlinarith [mul_nonneg h1 h2]
  refine ⟨Nx * Ny, hN, x, y, ?_, ?_, ?_, ?_⟩
  · intro k
    simp only [hx_def]
    rw [← hnorm_sq m (Tx (e.symm k).1), hTx_unit (e.symm k).1, one_pow]
  · intro k
    simp only [hy_def]
    rw [← hnorm_sq n (Ty (e.symm k).2), hTy_unit (e.symm k).2, one_pow]
  · exact hcov
  · intro A
    set M : ℝ := ⨆ k : Fin (Nx * Ny), ∑ i, ∑ j, x k i * A i j * y k j with hM_def
    set S : Set ℝ := {r : ℝ | ∃ u : Fin m → ℝ, ∃ v : Fin n → ℝ,
        (∑ i, (u i) ^ 2 = 1) ∧ (∑ j, (v j) ^ 2 = 1) ∧
          r = ∑ i, ∑ j, u i * A i j * v j} with hS_def
    have hAsup : ‖A‖ = sSup S := statopia_math_node_2162631172_eb3a62ea m n hm hn A
    have hpos : (0:ℝ) < 1 - 2 * δ := by linarith
    have hM_bound : ∀ (u : Fin m → ℝ) (v : Fin n → ℝ), (∑ i, (u i) ^ 2 = 1) →
        (∑ j, (v j) ^ 2 = 1) →
        ∑ i, ∑ j, u i * A i j * v j ≤ M + 2 * δ * ‖A‖ := by
      intro u v hu hv
      obtain ⟨k, hkx, hky⟩ := hcov u v hu hv
      have hxunit : (∑ i, (x k i) ^ 2) = 1 := by
        simp only [hx_def]
        rw [← hnorm_sq m (Tx (e.symm k).1), hTx_unit (e.symm k).1, one_pow]
      have hMk : (∑ i, ∑ j, x k i * A i j * y k j) ≤ M := by
        rw [hM_def]
        exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self k)
      have hsqrtx : Real.sqrt (∑ i, (u i - x k i) ^ 2) ≤ δ := by
        have h1 : (∑ i, (u i - x k i) ^ 2) ≤ δ ^ 2 := by
          rw [show (∑ i, (u i - x k i) ^ 2) = ∑ i, (x k i - u i) ^ 2 from by
            apply Finset.sum_congr rfl; intro i _; ring]
          exact hkx
        calc Real.sqrt (∑ i, (u i - x k i) ^ 2) ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt h1
          _ = δ := Real.sqrt_sq hδ_pos.le
      have hsqrty : Real.sqrt (∑ j, (v j - y k j) ^ 2) ≤ δ := by
        have h1 : (∑ j, (v j - y k j) ^ 2) ≤ δ ^ 2 := by
          rw [show (∑ j, (v j - y k j) ^ 2) = ∑ j, (y k j - v j) ^ 2 from by
            apply Finset.sum_congr rfl; intro j _; ring]
          exact hky
        calc Real.sqrt (∑ j, (v j - y k j) ^ 2) ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt h1
          _ = δ := Real.sqrt_sq hδ_pos.le
      have hc1 : (∑ i, ∑ j, (u i - x k i) * A i j * v j) ≤ δ * ‖A‖ := by
        have h := statopia_math_node_2970505295_46650432 m n A (fun i => u i - x k i) v
        have hv1 : Real.sqrt (∑ j, (v j) ^ 2) = 1 := by rw [hv, Real.sqrt_one]
        calc (∑ i, ∑ j, (u i - x k i) * A i j * v j)
            ≤ Real.sqrt (∑ i, (u i - x k i) ^ 2) * ‖A‖ * Real.sqrt (∑ j, (v j) ^ 2) := h
          _ = Real.sqrt (∑ i, (u i - x k i) ^ 2) * ‖A‖ := by rw [hv1, mul_one]
          _ ≤ δ * ‖A‖ := mul_le_mul_of_nonneg_right hsqrtx (norm_nonneg _)
      have hc2 : (∑ i, ∑ j, x k i * A i j * (v j - y k j)) ≤ δ * ‖A‖ := by
        have h := statopia_math_node_2970505295_46650432 m n A (x k) (fun j => v j - y k j)
        have hx1 : Real.sqrt (∑ i, (x k i) ^ 2) = 1 := by rw [hxunit, Real.sqrt_one]
        calc (∑ i, ∑ j, x k i * A i j * (v j - y k j))
            ≤ Real.sqrt (∑ i, (x k i) ^ 2) * ‖A‖ * Real.sqrt (∑ j, (v j - y k j) ^ 2) := h
          _ = ‖A‖ * Real.sqrt (∑ j, (v j - y k j) ^ 2) := by rw [hx1, one_mul]
          _ ≤ ‖A‖ * δ := mul_le_mul_of_nonneg_left hsqrty (norm_nonneg _)
          _ = δ * ‖A‖ := by ring
      have hdec : (∑ i, ∑ j, u i * A i j * v j)
          = (∑ i, ∑ j, x k i * A i j * y k j)
            + (∑ i, ∑ j, (u i - x k i) * A i j * v j)
            + (∑ i, ∑ j, x k i * A i j * (v j - y k j)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _
        ring
      rw [hdec]
      linarith [hMk, hc1, hc2]
    have hSne : S.Nonempty := by
      obtain ⟨u, hu⟩ := hunit_nonempty m hm
      obtain ⟨v, hv⟩ := hunit_nonempty n hn
      exact ⟨_, u, v, hu, hv, rfl⟩
    have hSup_le : sSup S ≤ M + 2 * δ * ‖A‖ := by
      apply csSup_le hSne
      rintro r ⟨u, v, hu, hv, rfl⟩
      exact hM_bound u v hu hv
    have hsup : ‖A‖ ≤ M + 2 * δ * ‖A‖ := by
      calc ‖A‖ = sSup S := hAsup
        _ ≤ M + 2 * δ * ‖A‖ := hSup_le
    have h1 : ‖A‖ - 2 * δ * ‖A‖ ≤ M := by linarith [hsup]
    have h2 : (1 - 2 * δ) * ‖A‖ ≤ M := by nlinarith [h1]
    calc ‖A‖ = (1 - 2 * δ)⁻¹ * ((1 - 2 * δ) * ‖A‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      _ ≤ (1 - 2 * δ)⁻¹ * M :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hpos))
  /- @proof-region region.target-node.session.c32bbf8765bcda56 end -/

end Statlib.Imported

