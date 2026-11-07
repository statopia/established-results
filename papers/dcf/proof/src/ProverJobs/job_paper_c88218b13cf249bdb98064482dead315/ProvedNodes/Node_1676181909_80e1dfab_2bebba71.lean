import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ProvedNodes.Node_436922874_8ad414b4_4d515167

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1676181909_80e1dfab : ∀ (n m p : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (μX μY : Fin p → ℝ) (d : ℝ)
    (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
    (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ))
    (hXm : ∀ i, Measurable (X i))
    (hYm : ∀ i, Measurable (Y i))
    (hFm : ∀ i, Measurable (F i))
    (hGm : ∀ i, Measurable (G i))
    (hindep : iIndepFun (allVec X Y F G) μ)
    (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂μ = μX j)
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂μ = μY j)
    (hXint : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => X i ω j) μ)
    (hYint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => Y i ω j) μ)
    (hFint : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => F i ω j) μ)
    (hGint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j) μ)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - μX j| ^ 3) μ)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - μY j| ^ 3) μ)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - μX j| ^ 3) μ)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - μY j| ^ 3) μ)
    (hXprod : ∀ (i : Fin n) (j k : Fin p),
      Integrable (fun ω => (X i ω j - μX j) * (X i ω k - μX k)) μ)
    (hYprod : ∀ (i : Fin m) (j k : Fin p),
      Integrable (fun ω => (Y i ω j - μY j) * (Y i ω k - μY k)) μ)
    (hFprod : ∀ (i : Fin n) (j k : Fin p),
      Integrable (fun ω => (F i ω j - μX j) * (F i ω k - μX k)) μ)
    (hGprod : ∀ (i : Fin m) (j k : Fin p),
      Integrable (fun ω => (G i ω j - μY j) * (G i ω k - μY k)) μ)
    (hFgauss : ∀ i : Fin n, IsGaussian (μ.map (F i)))
    (hFmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, F i ω j ∂μ = μX j)
    (hFcov : ∀ (i : Fin n) (j k : Fin p),
      ∫ ω, (F i ω j - μX j) * (F i ω k - μX k) ∂μ
        = ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂μ)
    (hGgauss : ∀ i : Fin m, IsGaussian (μ.map (G i)))
    (hGmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, G i ω j ∂μ = μY j)
    (hGcov : ∀ (i : Fin m) (j k : Fin p),
      ∫ ω, (G i ω j - μY j) * (G i ω k - μY k) ∂μ
        = ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂μ),
    let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
      if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
      else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩;
    (∀ i : Fin n, Measurable (T ∘ X i)) ∧
    (∀ i : Fin m, Measurable (T ∘ Y i)) ∧
    (∀ i : Fin n, Measurable (T ∘ F i)) ∧
    (∀ i : Fin m, Measurable (T ∘ G i)) ∧
    iIndepFun (allVec (fun i => T ∘ X i) (fun i => T ∘ Y i)
      (fun i => T ∘ F i) (fun i => T ∘ G i)) μ ∧
    (∀ (i : Fin n) (j : Fin (p + p)), ∫ ω, (T ∘ X i) ω j ∂μ = T μX j) ∧
    (∀ (i : Fin n) (j : Fin (p + p)), ∫ ω, (T ∘ F i) ω j ∂μ = T μX j) ∧
    (∀ (i : Fin m) (j : Fin (p + p)), ∫ ω, (T ∘ Y i) ω j ∂μ = T μY j) ∧
    (∀ (i : Fin m) (j : Fin (p + p)), ∫ ω, (T ∘ G i) ω j ∂μ = T μY j) ∧
    (∀ (i : Fin n) (j : Fin (p + p)), Integrable (fun ω => (T ∘ X i) ω j) μ) ∧
    (∀ (i : Fin m) (j : Fin (p + p)), Integrable (fun ω => (T ∘ Y i) ω j) μ) ∧
    (∀ (i : Fin n) (j : Fin (p + p)), Integrable (fun ω => (T ∘ F i) ω j) μ) ∧
    (∀ (i : Fin m) (j : Fin (p + p)), Integrable (fun ω => (T ∘ G i) ω j) μ) ∧
    (∀ (i : Fin n) (j : Fin (p + p)),
      Integrable (fun ω => |(T ∘ X i) ω j - T μX j| ^ 3) μ) ∧
    (∀ (i : Fin m) (j : Fin (p + p)),
      Integrable (fun ω => |(T ∘ Y i) ω j - T μY j| ^ 3) μ) ∧
    (∀ (i : Fin n) (j : Fin (p + p)),
      Integrable (fun ω => |(T ∘ F i) ω j - T μX j| ^ 3) μ) ∧
    (∀ (i : Fin m) (j : Fin (p + p)),
      Integrable (fun ω => |(T ∘ G i) ω j - T μY j| ^ 3) μ) ∧
    (∀ (i : Fin n) (j k : Fin (p + p)),
      Integrable (fun ω => ((T ∘ X i) ω j - T μX j) * ((T ∘ X i) ω k - T μX k)) μ) ∧
    (∀ (i : Fin m) (j k : Fin (p + p)),
      Integrable (fun ω => ((T ∘ Y i) ω j - T μY j) * ((T ∘ Y i) ω k - T μY k)) μ) ∧
    (∀ (i : Fin n) (j k : Fin (p + p)),
      Integrable (fun ω => ((T ∘ F i) ω j - T μX j) * ((T ∘ F i) ω k - T μX k)) μ) ∧
    (∀ (i : Fin m) (j k : Fin (p + p)),
      Integrable (fun ω => ((T ∘ G i) ω j - T μY j) * ((T ∘ G i) ω k - T μY k)) μ) ∧
    (∀ i : Fin n, IsGaussian (μ.map (T ∘ F i))) ∧
    (∀ i : Fin m, IsGaussian (μ.map (T ∘ G i))) ∧
    (∀ (i : Fin n) (j k : Fin (p + p)),
      ∫ ω, ((T ∘ F i) ω j - T μX j) * ((T ∘ F i) ω k - T μX k) ∂μ
        = ∫ ω, ((T ∘ X i) ω j - T μX j) * ((T ∘ X i) ω k - T μX k) ∂μ) ∧
    (∀ (i : Fin m) (j k : Fin (p + p)),
      ∫ ω, ((T ∘ G i) ω j - T μY j) * ((T ∘ G i) ω k - T μY k) ∂μ
        = ∫ ω, ((T ∘ Y i) ω j - T μY j) * ((T ∘ Y i) ω k - T μY k) ∂μ) := by
  /- @proof-region region.target-node.session.6935bdcdc5bb3ac1 begin -/
  intro n m p hn hm hp Ω _ μ _ μX μY d X Y F G
    hXm hYm hFm hGm hindep hXmean hYmean hXint hYint hFint hGint
    hX3 hY3 hF3 hG3 hXprod hYprod hFprod hGprod
    hFgauss hFmean hFcov hGgauss hGmean hGcov T
  obtain ⟨hadd, hsmul, hcont, hinj, hrange, hnormU, hpartXYU, hpartFGU, hmixU,
    hpartFGU', hcoord1, hcoord2, hcoord3, hcoord4⟩ :=
    statopia_math_node_436922874_8ad414b4 n m p hp Unit
  have hmean_gen : ∀ (Z : Ω → (Fin p → ℝ)) (c : Fin p → ℝ),
      (∀ j : Fin p, ∫ ω, Z ω j ∂μ = c j) →
      ∀ j : Fin (p + p), ∫ ω, T (Z ω) j ∂μ = T c j := by
    intro Z c hZ j
    by_cases hj : (j : ℕ) < p
    · have h1 : (fun ω => T (Z ω) j) = fun ω => Z ω ⟨(j : ℕ), hj⟩ := by
        funext ω; exact hcoord1 (Z ω) j hj
      rw [h1]
      have h2 : T c j = c ⟨(j : ℕ), hj⟩ := hcoord1 c j hj
      rw [h2, hZ ⟨(j : ℕ), hj⟩]
    · have hj' : p ≤ (j : ℕ) := by omega
      have h1 : (fun ω => T (Z ω) j) = fun ω => -Z ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := by
        funext ω; exact hcoord2 (Z ω) j hj'
      rw [h1, integral_neg]
      have h2 : T c j = -c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 c j hj'
      rw [h2, hZ ⟨(j : ℕ) - p, by have := j.isLt; omega⟩]
  have hinteg_gen : ∀ (Z : Ω → (Fin p → ℝ)),
      (∀ j : Fin p, Integrable (fun ω => Z ω j) μ) →
      ∀ j : Fin (p + p), Integrable (fun ω => T (Z ω) j) μ := by
    intro Z hZ j
    by_cases hj : (j : ℕ) < p
    · have h1 : (fun ω => T (Z ω) j) = fun ω => Z ω ⟨(j : ℕ), hj⟩ := by
        funext ω; exact hcoord1 (Z ω) j hj
      rw [h1]; exact hZ _
    · have hj' : p ≤ (j : ℕ) := by omega
      have h1 : (fun ω => T (Z ω) j) = fun ω => -Z ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := by
        funext ω; exact hcoord2 (Z ω) j hj'
      rw [h1]; exact (hZ _).neg
  have hcube_gen : ∀ (Z : Ω → (Fin p → ℝ)) (c : Fin p → ℝ),
      (∀ j : Fin p, Integrable (fun ω => |Z ω j - c j| ^ 3) μ) →
      ∀ j : Fin (p + p), Integrable (fun ω => |T (Z ω) j - T c j| ^ 3) μ := by
    intro Z c hZ j
    by_cases hj : (j : ℕ) < p
    · have h1 : (fun ω => |T (Z ω) j - T c j| ^ 3) = fun ω => |Z ω ⟨(j : ℕ), hj⟩ - c ⟨(j : ℕ), hj⟩| ^ 3 := by
        funext ω
        have e1 : T (Z ω) j = Z ω ⟨(j : ℕ), hj⟩ := hcoord1 (Z ω) j hj
        have e2 : T c j = c ⟨(j : ℕ), hj⟩ := hcoord1 c j hj
        rw [e1, e2]
      rw [h1]; exact hZ _
    · have hj' : p ≤ (j : ℕ) := by omega
      have h1 : (fun ω => |T (Z ω) j - T c j| ^ 3)
          = fun ω => |Z ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ - c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩| ^ 3 := by
        funext ω
        have e1 : T (Z ω) j = -Z ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 (Z ω) j hj'
        have e2 : T c j = -c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 c j hj'
        rw [e1, e2]
        have key : ∀ u v : ℝ, |-u - -v| ^ 3 = |u - v| ^ 3 := by
          intro u v
          rw [show -u - -v = -(u - v) by ring, abs_neg]
        exact key _ _
      rw [h1]; exact hZ _
  have hprod_gen : ∀ (Z : Ω → (Fin p → ℝ)) (c : Fin p → ℝ),
      (∀ j k : Fin p, Integrable (fun ω => (Z ω j - c j) * (Z ω k - c k)) μ) →
      ∀ j k : Fin (p + p),
        Integrable (fun ω => (T (Z ω) j - T c j) * (T (Z ω) k - T c k)) μ := by
    intro Z c hZ j k
    by_cases hj : (j : ℕ) < p
    · by_cases hk : (k : ℕ) < p
      · have e : (fun ω => (T (Z ω) j - T c j) * (T (Z ω) k - T c k))
            = fun ω => (Z ω ⟨(j : ℕ), hj⟩ - c ⟨(j : ℕ), hj⟩) * (Z ω ⟨(k : ℕ), hk⟩ - c ⟨(k : ℕ), hk⟩) := by
          funext ω
          have e1 : T (Z ω) j = Z ω ⟨(j : ℕ), hj⟩ := hcoord1 (Z ω) j hj
          have e2 : T c j = c ⟨(j : ℕ), hj⟩ := hcoord1 c j hj
          have e3 : T (Z ω) k = Z ω ⟨(k : ℕ), hk⟩ := hcoord1 (Z ω) k hk
          have e4 : T c k = c ⟨(k : ℕ), hk⟩ := hcoord1 c k hk
          rw [e1, e2, e3, e4]
        rw [e]; exact hZ _ _
      · have hk' : p ≤ (k : ℕ) := by omega
        have e : (fun ω => (T (Z ω) j - T c j) * (T (Z ω) k - T c k))
            = fun ω => -((Z ω ⟨(j : ℕ), hj⟩ - c ⟨(j : ℕ), hj⟩) * (Z ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ - c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩)) := by
          funext ω
          have e1 : T (Z ω) j = Z ω ⟨(j : ℕ), hj⟩ := hcoord1 (Z ω) j hj
          have e2 : T c j = c ⟨(j : ℕ), hj⟩ := hcoord1 c j hj
          have e3 : T (Z ω) k = -Z ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 (Z ω) k hk'
          have e4 : T c k = -c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 c k hk'
          rw [e1, e2, e3, e4]
          have key : ∀ u v w x : ℝ, (u - v) * (-w - -x) = -((u - v) * (w - x)) := by
            intro u v w x; ring
          exact key _ _ _ _
        rw [e]; exact (hZ _ _).neg
    · have hj' : p ≤ (j : ℕ) := by omega
      by_cases hk : (k : ℕ) < p
      · have e : (fun ω => (T (Z ω) j - T c j) * (T (Z ω) k - T c k))
            = fun ω => -((Z ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ - c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩) * (Z ω ⟨(k : ℕ), hk⟩ - c ⟨(k : ℕ), hk⟩)) := by
          funext ω
          have e1 : T (Z ω) j = -Z ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 (Z ω) j hj'
          have e2 : T c j = -c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 c j hj'
          have e3 : T (Z ω) k = Z ω ⟨(k : ℕ), hk⟩ := hcoord1 (Z ω) k hk
          have e4 : T c k = c ⟨(k : ℕ), hk⟩ := hcoord1 c k hk
          rw [e1, e2, e3, e4]
          have key : ∀ u v w x : ℝ, (-u - -v) * (w - x) = -((u - v) * (w - x)) := by
            intro u v w x; ring
          exact key _ _ _ _
        rw [e]; exact (hZ _ _).neg
      · have hk' : p ≤ (k : ℕ) := by omega
        have e : (fun ω => (T (Z ω) j - T c j) * (T (Z ω) k - T c k))
            = fun ω => (Z ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ - c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩) * (Z ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ - c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩) := by
          funext ω
          have e1 : T (Z ω) j = -Z ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 (Z ω) j hj'
          have e2 : T c j = -c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 c j hj'
          have e3 : T (Z ω) k = -Z ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 (Z ω) k hk'
          have e4 : T c k = -c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 c k hk'
          rw [e1, e2, e3, e4]
          have key : ∀ u v w x : ℝ, (-u - -v) * (-w - -x) = (u - v) * (w - x) := by
            intro u v w x; ring
          exact key _ _ _ _
        rw [e]; exact hZ _ _
  have Tclm : (Fin p → ℝ) →L[ℝ] (Fin (p + p) → ℝ) :=
    { toFun := T, map_add' := hadd, map_smul' := hsmul, cont := hcont }
  have hcov_gen : ∀ (A B : Ω → (Fin p → ℝ)) (c : Fin p → ℝ),
      (∀ j k : Fin p, ∫ ω, (A ω j - c j) * (A ω k - c k) ∂μ
        = ∫ ω, (B ω j - c j) * (B ω k - c k) ∂μ) →
      ∀ j k : Fin (p + p),
        ∫ ω, (T (A ω) j - T c j) * (T (A ω) k - T c k) ∂μ
          = ∫ ω, (T (B ω) j - T c j) * (T (B ω) k - T c k) ∂μ := by
    intro A B c hAB j k
    by_cases hj : (j : ℕ) < p
    · by_cases hk : (k : ℕ) < p
      · have eA : (fun ω => (T (A ω) j - T c j) * (T (A ω) k - T c k))
            = fun ω => (A ω ⟨(j : ℕ), hj⟩ - c ⟨(j : ℕ), hj⟩) * (A ω ⟨(k : ℕ), hk⟩ - c ⟨(k : ℕ), hk⟩) := by
          funext ω
          have a1 : T (A ω) j = A ω ⟨(j : ℕ), hj⟩ := hcoord1 (A ω) j hj
          have a2 : T c j = c ⟨(j : ℕ), hj⟩ := hcoord1 c j hj
          have a3 : T (A ω) k = A ω ⟨(k : ℕ), hk⟩ := hcoord1 (A ω) k hk
          have a4 : T c k = c ⟨(k : ℕ), hk⟩ := hcoord1 c k hk
          rw [a1, a2, a3, a4]
        have eB : (fun ω => (T (B ω) j - T c j) * (T (B ω) k - T c k))
            = fun ω => (B ω ⟨(j : ℕ), hj⟩ - c ⟨(j : ℕ), hj⟩) * (B ω ⟨(k : ℕ), hk⟩ - c ⟨(k : ℕ), hk⟩) := by
          funext ω
          have a1 : T (B ω) j = B ω ⟨(j : ℕ), hj⟩ := hcoord1 (B ω) j hj
          have a2 : T c j = c ⟨(j : ℕ), hj⟩ := hcoord1 c j hj
          have a3 : T (B ω) k = B ω ⟨(k : ℕ), hk⟩ := hcoord1 (B ω) k hk
          have a4 : T c k = c ⟨(k : ℕ), hk⟩ := hcoord1 c k hk
          rw [a1, a2, a3, a4]
        rw [eA, eB]; exact hAB _ _
      · have hk' : p ≤ (k : ℕ) := by omega
        have eA : (fun ω => (T (A ω) j - T c j) * (T (A ω) k - T c k))
            = fun ω => -((A ω ⟨(j : ℕ), hj⟩ - c ⟨(j : ℕ), hj⟩) * (A ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ - c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩)) := by
          funext ω
          have a1 : T (A ω) j = A ω ⟨(j : ℕ), hj⟩ := hcoord1 (A ω) j hj
          have a2 : T c j = c ⟨(j : ℕ), hj⟩ := hcoord1 c j hj
          have a3 : T (A ω) k = -A ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 (A ω) k hk'
          have a4 : T c k = -c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 c k hk'
          rw [a1, a2, a3, a4]
          have key : ∀ u v w x : ℝ, (u - v) * (-w - -x) = -((u - v) * (w - x)) := by
            intro u v w x; ring
          exact key _ _ _ _
        have eB : (fun ω => (T (B ω) j - T c j) * (T (B ω) k - T c k))
            = fun ω => -((B ω ⟨(j : ℕ), hj⟩ - c ⟨(j : ℕ), hj⟩) * (B ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ - c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩)) := by
          funext ω
          have a1 : T (B ω) j = B ω ⟨(j : ℕ), hj⟩ := hcoord1 (B ω) j hj
          have a2 : T c j = c ⟨(j : ℕ), hj⟩ := hcoord1 c j hj
          have a3 : T (B ω) k = -B ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 (B ω) k hk'
          have a4 : T c k = -c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 c k hk'
          rw [a1, a2, a3, a4]
          have key : ∀ u v w x : ℝ, (u - v) * (-w - -x) = -((u - v) * (w - x)) := by
            intro u v w x; ring
          exact key _ _ _ _
        rw [eA, eB]; simp only [integral_neg]; exact congrArg Neg.neg (hAB _ _)
    · have hj' : p ≤ (j : ℕ) := by omega
      by_cases hk : (k : ℕ) < p
      · have eA : (fun ω => (T (A ω) j - T c j) * (T (A ω) k - T c k))
            = fun ω => -((A ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ - c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩) * (A ω ⟨(k : ℕ), hk⟩ - c ⟨(k : ℕ), hk⟩)) := by
          funext ω
          have a1 : T (A ω) j = -A ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 (A ω) j hj'
          have a2 : T c j = -c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 c j hj'
          have a3 : T (A ω) k = A ω ⟨(k : ℕ), hk⟩ := hcoord1 (A ω) k hk
          have a4 : T c k = c ⟨(k : ℕ), hk⟩ := hcoord1 c k hk
          rw [a1, a2, a3, a4]
          have key : ∀ u v w x : ℝ, (-u - -v) * (w - x) = -((u - v) * (w - x)) := by
            intro u v w x; ring
          exact key _ _ _ _
        have eB : (fun ω => (T (B ω) j - T c j) * (T (B ω) k - T c k))
            = fun ω => -((B ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ - c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩) * (B ω ⟨(k : ℕ), hk⟩ - c ⟨(k : ℕ), hk⟩)) := by
          funext ω
          have a1 : T (B ω) j = -B ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 (B ω) j hj'
          have a2 : T c j = -c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 c j hj'
          have a3 : T (B ω) k = B ω ⟨(k : ℕ), hk⟩ := hcoord1 (B ω) k hk
          have a4 : T c k = c ⟨(k : ℕ), hk⟩ := hcoord1 c k hk
          rw [a1, a2, a3, a4]
          have key : ∀ u v w x : ℝ, (-u - -v) * (w - x) = -((u - v) * (w - x)) := by
            intro u v w x; ring
          exact key _ _ _ _
        rw [eA, eB]; simp only [integral_neg]; exact congrArg Neg.neg (hAB _ _)
      · have hk' : p ≤ (k : ℕ) := by omega
        have eA : (fun ω => (T (A ω) j - T c j) * (T (A ω) k - T c k))
            = fun ω => (A ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ - c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩) * (A ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ - c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩) := by
          funext ω
          have a1 : T (A ω) j = -A ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 (A ω) j hj'
          have a2 : T c j = -c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 c j hj'
          have a3 : T (A ω) k = -A ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 (A ω) k hk'
          have a4 : T c k = -c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 c k hk'
          rw [a1, a2, a3, a4]
          have key : ∀ u v w x : ℝ, (-u - -v) * (-w - -x) = (u - v) * (w - x) := by
            intro u v w x; ring
          exact key _ _ _ _
        have eB : (fun ω => (T (B ω) j - T c j) * (T (B ω) k - T c k))
            = fun ω => (B ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ - c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩) * (B ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ - c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩) := by
          funext ω
          have a1 : T (B ω) j = -B ω ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 (B ω) j hj'
          have a2 : T c j = -c ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ := hcoord2 c j hj'
          have a3 : T (B ω) k = -B ω ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 (B ω) k hk'
          have a4 : T c k = -c ⟨(k : ℕ) - p, by have := k.isLt; omega⟩ := hcoord2 c k hk'
          rw [a1, a2, a3, a4]
          have key : ∀ u v w x : ℝ, (-u - -v) * (-w - -x) = (u - v) * (w - x) := by
            intro u v w x; ring
          exact key _ _ _ _
        rw [eA, eB]; exact hAB _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hcont.measurable.comp (hXm i)
  · exact fun i => hcont.measurable.comp (hYm i)
  · exact fun i => hcont.measurable.comp (hFm i)
  · exact fun i => hcont.measurable.comp (hGm i)
  · have hcomp : allVec (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i)
        = fun t => T ∘ (allVec X Y F G t) := by
      funext t
      cases t with
      | inl i => rfl
      | inr t1 =>
        cases t1 with
        | inl j => rfl
        | inr t2 =>
          cases t2 with
          | inl i => rfl
          | inr j => rfl
    rw [hcomp]
    exact iIndepFun.comp hindep (fun _ => T) (fun _ => hcont.measurable)
  · exact fun i j => by simpa only [Function.comp_apply] using hmean_gen (X i) μX (hXmean i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hmean_gen (F i) μX (hFmean i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hmean_gen (Y i) μY (hYmean i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hmean_gen (G i) μY (hGmean i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hinteg_gen (X i) (hXint i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hinteg_gen (Y i) (hYint i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hinteg_gen (F i) (hFint i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hinteg_gen (G i) (hGint i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hcube_gen (X i) μX (hX3 i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hcube_gen (Y i) μY (hY3 i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hcube_gen (F i) μX (hF3 i) j
  · exact fun i j => by simpa only [Function.comp_apply] using hcube_gen (G i) μY (hG3 i) j
  · exact fun i j k => by simpa only [Function.comp_apply] using hprod_gen (X i) μX (hXprod i) j k
  · exact fun i j k => by simpa only [Function.comp_apply] using hprod_gen (Y i) μY (hYprod i) j k
  · exact fun i j k => by simpa only [Function.comp_apply] using hprod_gen (F i) μX (hFprod i) j k
  · exact fun i j k => by simpa only [Function.comp_apply] using hprod_gen (G i) μY (hGprod i) j k
  · intro i
    have hmap : μ.map (T ∘ F i) = (μ.map (F i)).map T := (Measure.map_map hcont.measurable (hFm i)).symm
    rw [hmap]
    haveI : IsGaussian (μ.map (F i)) := hFgauss i
    let hlin : (Fin p → ℝ) →ₗ[ℝ] (Fin (p + p) → ℝ) :=
      { toFun := T, map_add' := hadd, map_smul' := hsmul }
    let hclin : (Fin p → ℝ) →L[ℝ] (Fin (p + p) → ℝ) :=
      { toLinearMap := hlin, cont := hcont }
    have hc2 : (⇑hlin : (Fin p → ℝ) → (Fin (p + p) → ℝ)) = T := rfl
    have hc1 : (⇑hclin : (Fin p → ℝ) → (Fin (p + p) → ℝ)) = ⇑hlin := ContinuousLinearMap.coe_mk' hlin hcont
    have hc : (⇑hclin : (Fin p → ℝ) → (Fin (p + p) → ℝ)) = T := hc1.trans hc2
    rw [← hc]
    exact isGaussian_map (μ := μ.map (F i)) hclin
  · intro i
    have hmap : μ.map (T ∘ G i) = (μ.map (G i)).map T := (Measure.map_map hcont.measurable (hGm i)).symm
    rw [hmap]
    haveI : IsGaussian (μ.map (G i)) := hGgauss i
    let hlin : (Fin p → ℝ) →ₗ[ℝ] (Fin (p + p) → ℝ) :=
      { toFun := T, map_add' := hadd, map_smul' := hsmul }
    let hclin : (Fin p → ℝ) →L[ℝ] (Fin (p + p) → ℝ) :=
      { toLinearMap := hlin, cont := hcont }
    have hc2 : (⇑hlin : (Fin p → ℝ) → (Fin (p + p) → ℝ)) = T := rfl
    have hc1 : (⇑hclin : (Fin p → ℝ) → (Fin (p + p) → ℝ)) = ⇑hlin := ContinuousLinearMap.coe_mk' hlin hcont
    have hc : (⇑hclin : (Fin p → ℝ) → (Fin (p + p) → ℝ)) = T := hc1.trans hc2
    rw [← hc]
    exact isGaussian_map (μ := μ.map (G i)) hclin
  · exact fun i j k => by simpa only [Function.comp_apply] using hcov_gen (F i) (X i) μX (hFcov i) j k
  · exact fun i j k => by simpa only [Function.comp_apply] using hcov_gen (G i) (Y i) μY (hGcov i) j k
  /- @proof-region region.target-node.session.6935bdcdc5bb3ac1 end -/

end Statlib.Imported

end

