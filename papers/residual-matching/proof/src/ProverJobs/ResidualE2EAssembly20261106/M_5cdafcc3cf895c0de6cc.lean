import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_897344607_f43704b9 : ∀ (n r : ℕ) (hr : 0 < r)
    (U X : Matrix (Fin n) (Fin r) ℝ),
    ∃ R : Matrix (Fin r) (Fin r) ℝ,
      Matrix.transpose R * R = 1 ∧
        frob (U - X * R) =
          ⨅ (Rq : {R' : Matrix (Fin r) (Fin r) ℝ // Matrix.transpose R' * R' = 1}),
            frob (U - X * Rq.1) := by
  /- @proof-region region.target-node.session.15d9e6df078ca052 begin -/
  intro n r hr U X
  set S : Set (Matrix (Fin r) (Fin r) ℝ) := {R | Matrix.transpose R * R = 1} with hS
  have hcoord : ∀ {a b : ℕ} (i : Fin a) (j : Fin b),
      Continuous fun M : Matrix (Fin a) (Fin b) ℝ => M i j := by
    intro a b i j
    have h1 : Continuous fun M : Matrix (Fin a) (Fin b) ℝ => M i := continuous_apply i
    have h2 : Continuous fun (h : Fin b → ℝ) => h j := continuous_apply j
    exact Continuous.comp h2 h1
  have hcont : Continuous fun R : Matrix (Fin r) (Fin r) ℝ => frob (U - X * R) := by
    have hsub : Continuous fun R : Matrix (Fin r) (Fin r) ℝ => U - X * R := by
      have hmul : Continuous fun R : Matrix (Fin r) (Fin r) ℝ => X * R :=
        (continuous_const : Continuous fun _ : Matrix (Fin r) (Fin r) ℝ => X).matrix_mul
          continuous_id
      exact continuous_const.sub hmul
    unfold frob
    refine Continuous.sqrt ?_
    unfold frobSq
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact Continuous.pow ((hcoord i j).comp hsub) 2
  have htrans : Continuous fun R : Matrix (Fin r) (Fin r) ℝ => Matrix.transpose R := by
    refine continuous_pi fun i => ?_
    refine continuous_pi fun j => ?_
    simp only [Matrix.transpose_apply]
    exact hcoord j i
  have hclosed : IsClosed S := by
    have hsig : Continuous fun R : Matrix (Fin r) (Fin r) ℝ => Matrix.transpose R * R :=
      htrans.matrix_mul continuous_id
    rw [hS]
    exact isClosed_eq hsig continuous_const
  have hcol : ∀ (R : Matrix (Fin r) (Fin r) ℝ), R ∈ S → ∀ j : Fin r,
      ∑ k : Fin r, R k j ^ 2 = 1 := by
    intro R hR j
    have hRt : Matrix.transpose R * R = 1 := by
      have h' := hR
      rw [hS] at h'
      simpa using h'
    have h := congrFun (congrFun hRt j) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have hSsub : S ⊆ Set.univ.pi (fun _ : Fin r => Set.univ.pi (fun _ : Fin r => Set.Icc (-1:ℝ) 1)) := by
    intro R hR
    rw [Set.mem_univ_pi]
    intro i
    rw [Set.mem_univ_pi]
    intro j
    have h1 : R i j ^ 2 ≤ 1 := by
      calc R i j ^ 2 ≤ ∑ k : Fin r, R k j ^ 2 := by
              simpa using Finset.single_le_sum (fun k _ => sq_nonneg (R k j)) (Finset.mem_univ i)
        _ = 1 := hcol R hR j
    exact ⟨by nlinarith [h1], by nlinarith [h1]⟩
  have hambient : IsCompact (Set.univ.pi (fun _ : Fin r => Set.univ.pi (fun _ : Fin r => Set.Icc (-1:ℝ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hcompact : IsCompact S := hambient.of_isClosed_subset hclosed hSsub
  have hne : S.Nonempty := ⟨1, by simp [hS]⟩
  obtain ⟨R₀, hR₀S, hR₀min⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  have hR₀ : Matrix.transpose R₀ * R₀ = 1 := by
    have h' := hR₀S
    rw [hS] at h'
    simpa using h'
  have hmin : ∀ R ∈ S, frob (U - X * R₀) ≤ frob (U - X * R) := fun R hR => hR₀min hR
  refine ⟨R₀, hR₀, ?_⟩
  haveI : Nonempty {M : Matrix (Fin r) (Fin r) ℝ // Matrix.transpose M * M = 1} :=
    ⟨⟨1, by simp⟩⟩
  have hle : frob (U - X * R₀) ≤
      ⨅ Rk : {M : Matrix (Fin r) (Fin r) ℝ // Matrix.transpose M * M = 1}, frob (U - X * Rk.1) := by
    refine le_ciInf
      (f := fun Rk : {M : Matrix (Fin r) (Fin r) ℝ // Matrix.transpose M * M = 1} =>
        frob (U - X * Rk.1)) ?_
    intro Rk
    exact hmin Rk.1 (by rw [hS]; simpa using Rk.2)
  have hge : (⨅ Rk : {M : Matrix (Fin r) (Fin r) ℝ // Matrix.transpose M * M = 1},
        frob (U - X * Rk.1)) ≤ frob (U - X * R₀) := by
    have hbdd : BddBelow (Set.range fun Rk : {M : Matrix (Fin r) (Fin r) ℝ // Matrix.transpose M * M = 1} =>
        frob (U - X * Rk.1)) :=
      ⟨0, by rintro _ ⟨x, rfl⟩; exact Real.sqrt_nonneg _⟩
    exact ciInf_le
      (f := fun Rk : {M : Matrix (Fin r) (Fin r) ℝ // Matrix.transpose M * M = 1} =>
        frob (U - X * Rk.1)) hbdd ⟨R₀, hR₀⟩
  exact le_antisymm hle hge
  /- @proof-region region.target-node.session.15d9e6df078ca052 end -/

end

end Statlib.Imported

