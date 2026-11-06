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
theorem statopia_math_node_4153628898_515516f4 : ∀ (N : ℕ) (D : Matrix (Fin N) (Fin N) ℝ)
    (hD : D.IsHermitian)
    (H : (Matrix.of (fun a b : Fin N => ((D a b : ℝ) : ℂ))).IsHermitian),
    (⨆ a : Fin N, |(Matrix.IsHermitian.eigenvalues H a)|) =
      ⨆ a : Fin N, |(Matrix.IsHermitian.eigenvalues hD a)| := by
  /- @proof-region region.target-node.session.12ab226900cd7d79 begin -/
  intro N D hD H
  let f : ℝ →+* ℂ := algebraMap ℝ ℂ
  have hf_inj : Function.Injective f := by
    intro x y h
    have h' : (x : ℂ) = (y : ℂ) := by simpa [f] using h
    exact Complex.ofReal_injective h'
  have hM_eq : (Matrix.of (fun a b : Fin N => ((D a b : ℝ) : ℂ))) = D.map f := by
    ext i j
    simp [f, Matrix.map_apply]
  have hspec_eq : spectrum ℝ (D.map f) = spectrum ℝ D := by
    ext r
    let A : Matrix (Fin N) (Fin N) ℝ := algebraMap ℝ (Matrix (Fin N) (Fin N) ℝ) r - D
    have hcast : algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) r - D.map f = A.map f := by
      dsimp [A]
      ext i j
      by_cases hij : i = j <;>
        simp [f, Matrix.map_apply, Algebra.algebraMap_eq_smul_one, hij]
    have hdet : (A.map f).det = f A.det := by
      simpa using (RingHom.map_det f A).symm
    have hf_det : f A.det = 0 ↔ A.det = 0 := by
      constructor
      · intro h
        exact hf_inj (by simpa using h)
      · intro h
        simp [h]
    have hunit : IsUnit (A.map f) ↔ IsUnit A := by
      calc
        IsUnit (A.map f) ↔ IsUnit (A.map f).det := Matrix.isUnit_iff_isUnit_det _
        _ ↔ (A.map f).det ≠ 0 := isUnit_iff_ne_zero
        _ ↔ f A.det ≠ 0 := by rw [hdet]
        _ ↔ A.det ≠ 0 := not_congr hf_det
        _ ↔ IsUnit A.det := isUnit_iff_ne_zero.symm
        _ ↔ IsUnit A := (Matrix.isUnit_iff_isUnit_det A).symm
    rw [spectrum.mem_iff, spectrum.mem_iff]
    rw [hcast]
    exact not_congr hunit
  have hrange : Set.range H.eigenvalues = Set.range hD.eigenvalues := by
    have hHspec := Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues H
    have hDspec := Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hD
    rw [← hHspec, ← hDspec, hM_eq]
    exact hspec_eq
  have habs : Set.range (fun a : Fin N => |H.eigenvalues a|)
      = Set.range (fun a : Fin N => |hD.eigenvalues a|) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      have ha : H.eigenvalues a ∈ Set.range hD.eigenvalues := by
        rw [← hrange]
        exact Set.mem_range_self a
      rcases ha with ⟨b, hb⟩
      exact ⟨b, by simpa using congrArg (fun x => |x|) hb⟩
    · rintro ⟨a, rfl⟩
      have ha : hD.eigenvalues a ∈ Set.range H.eigenvalues := by
        rw [hrange]
        exact Set.mem_range_self a
      rcases ha with ⟨b, hb⟩
      exact ⟨b, by simpa using congrArg (fun x => |x|) hb⟩
  change sSup (Set.range (fun a : Fin N => |H.eigenvalues a|))
      = sSup (Set.range (fun a : Fin N => |hD.eigenvalues a|))
  rw [habs]
  /- @proof-region region.target-node.session.12ab226900cd7d79 end -/

end

end Statlib.Imported

