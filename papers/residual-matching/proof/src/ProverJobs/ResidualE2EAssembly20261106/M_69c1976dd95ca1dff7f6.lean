import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548
import ProverJobs.ResidualE2EAssembly20261106.M_bdab2ccc03f99c8412b2
import ProverJobs.ResidualE2EAssembly20261106.M_7f3eea621b0d2e005d06

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching


run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_1023666064_4c15a721 : ∀ {m n r : ℕ} {Ωm : Type*} [MeasurableSpace Ωm]
    (p Lam th : ℝ) (Om : Ωm → Matrix (Fin m) (Fin n) ℝ)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (hOm : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Om ω i j),
    MeasurableSet {ω : Ωm |
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
        p Lam th (Om ω) U0 V0} := by
  /- @proof-region region.target-node.session.f4b94fed4cbdfbcc begin -/
  intro m n r OmType _ p Lam th Om U0 V0 hOm
  unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
  have hTmeas : ∀ A : Matrix (Fin m) (Fin n) ℝ, Measurable fun ω : OmType =>
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) A := by
    intro A
    rw [measurable_pi_iff]
    intro i
    rw [measurable_pi_iff]
    intro j
    have hpt : Measurable fun ω : OmType => (p⁻¹ * Om ω i j - 1) * A i j :=
      (((hOm i j).const_mul p⁻¹).sub measurable_const).mul measurable_const
    simpa only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask,
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Wmask] using hpt
  have htrans : ∀ (k : ℕ), Continuous fun A : Matrix (Fin n) (Fin k) ℝ => Aᵀ := by
    intro k
    rw [continuous_pi_iff]
    intro i
    rw [continuous_pi_iff]
    intro j
    exact (continuous_apply i).comp (continuous_apply j)
  have hmul : ∀ (k : ℕ), Continuous fun x : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin n) (Fin k) ℝ =>
      x.1 * x.2ᵀ := by
    intro k
    exact Continuous.matrix_mul continuous_fst ((htrans k).comp continuous_snd)
  have hTmcont : ∀ W : Matrix (Fin m) (Fin n) ℝ, Continuous fun A : Matrix (Fin m) (Fin n) ℝ =>
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p W A := by
    intro W
    rw [continuous_pi_iff]
    intro i
    rw [continuous_pi_iff]
    intro j
    have hpt : Continuous fun A : Matrix (Fin m) (Fin n) ℝ => (p⁻¹ * W i j - 1) * A i j :=
      continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
    simpa only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask,
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Wmask] using hpt
  have hfn : Continuous fun A : Matrix (Fin m) (Fin n) ℝ =>
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm A := by
    unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm
    have hsq : Continuous fun A : Matrix (Fin m) (Fin n) ℝ => ∑ i, ∑ j, (A i j) ^ 2 := by
      refine continuous_finset_sum Finset.univ ?_
      intro i _
      refine continuous_finset_sum Finset.univ ?_
      intro j _
      exact ((continuous_apply j).comp (continuous_apply i)).pow 2
    exact Real.continuous_sqrt.comp hsq
  have hfin : Continuous fun z : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ =>
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner z.1 z.2 := by
    unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
    refine continuous_finset_sum Finset.univ ?_
    intro i _
    refine continuous_finset_sum Finset.univ ?_
    intro j _
    exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).mul
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))
  have hPhi : Continuous fun u : Matrix (Fin n) (Fin r) ℝ × Matrix (Fin m) (Fin r) ℝ =>
      U0 * u.1ᵀ + u.2 * V0ᵀ :=
    (Continuous.matrix_mul continuous_const ((htrans r).comp continuous_fst)).add
      (Continuous.matrix_mul continuous_snd continuous_const)
  have test1 : ∀ a b : ℝ, a - b ≤ 0 ↔ a ≤ b := fun a b => sub_nonpos
  have hcls : ∀ {β : Type} [TopologicalSpace β] {u : ℕ → β}, DenseRange u →
      ∀ {φ : β → ℝ}, Continuous φ → (∀ n, φ (u n) ≤ 0) → ∀ x, φ x ≤ 0 := by
    intro β _ u hu φ hφ hle x
    have hsub : Set.range u ⊆ {y : β | φ y ≤ 0} := by
      rintro _ ⟨n, rfl⟩
      exact hle n
    have hclosed : IsClosed {y : β | φ y ≤ 0} := by
      have hle' : IsClosed {y : β | y ∈ (Set.univ : Set β) ∧ φ y ≤ (0 : ℝ)} :=
        IsClosed.isClosed_le isClosed_univ hφ.continuousOn continuousOn_const
      simpa only [Set.mem_univ, true_and] using hle'
    have hmono : closure (Set.range u) ⊆ {y : β | φ y ≤ 0} := by
      have h2 := closure_mono hsub
      rwa [hclosed.closure_eq] at h2
    have hxcl : ∀ y : β, y ∈ closure (Set.range u) := by
      simpa only [DenseRange] using hu
    exact hmono (hxcl x)
  have keyD2 : ∀ {β₁ β₂ : Type} [TopologicalSpace β₁] [TopologicalSpace β₂]
      {u₁ : ℕ → β₁} {u₂ : ℕ → β₂}, DenseRange u₁ → DenseRange u₂ →
      ∀ (g : OmType → β₁ → β₂ → ℝ), (∀ x y, Measurable fun ω => g ω x y) →
      (∀ ω y, Continuous fun x => g ω x y) → (∀ ω x, Continuous fun y => g ω x y) →
      MeasurableSet {ω : OmType | ∀ x y, g ω x y ≤ 0} := by
    intro β₁ β₂ _ _ u₁ u₂ hu₁ hu₂ g hgm hc₁ hc₂
    have hEq : {ω : OmType | ∀ x y, g ω x y ≤ 0}
        = ⋂ n₁ : ℕ, ⋂ n₂ : ℕ, {ω : OmType | g ω (u₁ n₁) (u₂ n₂) ≤ 0} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h n₁ n₂
        exact h _ _
      · intro h x y
        have s₁ : ∀ n₁ y, g ω (u₁ n₁) y ≤ 0 := by
          intro n₁ y
          exact hcls hu₂ (hc₂ ω (u₁ n₁)) (fun n₂ => h n₁ n₂) y
        exact hcls hu₁ (hc₁ ω y) (fun n₁ => s₁ n₁ y) x
    rw [hEq]
    exact MeasurableSet.iInter (fun n₁ => MeasurableSet.iInter (fun n₂ =>
      MeasureTheory.StronglyMeasurable.measurableSet_le (hgm _ _).stronglyMeasurable
        stronglyMeasurable_const))
  have keyD4 : ∀ {β₁ β₂ β₃ β₄ : Type} [TopologicalSpace β₁] [TopologicalSpace β₂]
      [TopologicalSpace β₃] [TopologicalSpace β₄]
      {u₁ : ℕ → β₁} {u₂ : ℕ → β₂} {u₃ : ℕ → β₃} {u₄ : ℕ → β₄},
      DenseRange u₁ → DenseRange u₂ → DenseRange u₃ → DenseRange u₄ →
      ∀ (g : OmType → β₁ → β₂ → β₃ → β₄ → ℝ),
      (∀ x₁ x₂ x₃ x₄, Measurable fun ω => g ω x₁ x₂ x₃ x₄) →
      (∀ ω x₂ x₃ x₄, Continuous fun x₁ => g ω x₁ x₂ x₃ x₄) →
      (∀ ω x₁ x₃ x₄, Continuous fun x₂ => g ω x₁ x₂ x₃ x₄) →
      (∀ ω x₁ x₂ x₄, Continuous fun x₃ => g ω x₁ x₂ x₃ x₄) →
      (∀ ω x₁ x₂ x₃, Continuous fun x₄ => g ω x₁ x₂ x₃ x₄) →
      MeasurableSet {ω : OmType | ∀ x₁ x₂ x₃ x₄, g ω x₁ x₂ x₃ x₄ ≤ 0} := by
    intro β₁ β₂ β₃ β₄ _ _ _ _ u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ g hgm hc₁ hc₂ hc₃ hc₄
    have hEq : {ω : OmType | ∀ x₁ x₂ x₃ x₄, g ω x₁ x₂ x₃ x₄ ≤ 0}
        = ⋂ n₁ : ℕ, ⋂ n₂ : ℕ, ⋂ n₃ : ℕ, ⋂ n₄ : ℕ,
            {ω : OmType | g ω (u₁ n₁) (u₂ n₂) (u₃ n₃) (u₄ n₄) ≤ 0} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h n₁ n₂ n₃ n₄
        exact h _ _ _ _
      · intro h x₁ x₂ x₃ x₄
        have s₄ : ∀ n₁ n₂ n₃ y, g ω (u₁ n₁) (u₂ n₂) (u₃ n₃) y ≤ 0 := by
          intro n₁ n₂ n₃ y
          exact hcls hu₄ (hc₄ ω (u₁ n₁) (u₂ n₂) (u₃ n₃)) (fun n₄ => h n₁ n₂ n₃ n₄) y
        have s₃ : ∀ n₁ n₂ y₃ y₄, g ω (u₁ n₁) (u₂ n₂) y₃ y₄ ≤ 0 := by
          intro n₁ n₂ y₃ y₄
          exact hcls hu₃ (hc₃ ω (u₁ n₁) (u₂ n₂) y₄) (fun n₃ => s₄ n₁ n₂ n₃ y₄) y₃
        have s₂ : ∀ n₁ y₂ y₃ y₄, g ω (u₁ n₁) y₂ y₃ y₄ ≤ 0 := by
          intro n₁ y₂ y₃ y₄
          exact hcls hu₂ (hc₂ ω (u₁ n₁) y₃ y₄) (fun n₂ => s₃ n₁ n₂ y₃ y₄) y₂
        exact hcls hu₁ (hc₁ ω x₂ x₃ x₄) (fun n₁ => s₂ n₁ x₂ x₃ x₄) x₁
    rw [hEq]
    exact MeasurableSet.iInter (fun n₁ => MeasurableSet.iInter (fun n₂ =>
      MeasurableSet.iInter (fun n₃ => MeasurableSet.iInter (fun n₄ =>
        MeasureTheory.StronglyMeasurable.measurableSet_le (hgm _ _ _ _).stronglyMeasurable
          stronglyMeasurable_const))))
  have hrow : ∀ (a b : ℕ), Continuous fun A : Matrix (Fin a) (Fin b) ℝ =>
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm A := by
    intro a b
    have hrr : ∀ i : Fin a, Continuous fun A : Matrix (Fin a) (Fin b) ℝ =>
        Real.sqrt (∑ j, (A i j) ^ 2) := by
      intro i
      refine Real.continuous_sqrt.comp ?_
      refine continuous_finset_sum Finset.univ ?_
      intro j _
      exact ((continuous_apply j).comp (continuous_apply i)).pow 2
    have hsup : Continuous fun A : Matrix (Fin a) (Fin b) ℝ =>
        ⨆ i : Fin a, Real.sqrt (∑ j, (A i j) ^ 2) := by
      by_cases ha : Nonempty (Fin a)
      · haveI := ha
        rw [continuous_iff_continuousAt]
        intro A₀
        have hbdA : ∀ A : Matrix (Fin a) (Fin b) ℝ,
            BddAbove (Set.range (fun i : Fin a => Real.sqrt (∑ j, (A i j) ^ 2))) := by
          intro A
          have hf : (Set.range (fun i : Fin a => Real.sqrt (∑ j, (A i j) ^ 2))).Finite := by
            simpa only [Set.image_univ] using
              (Set.finite_univ.image (fun i : Fin a => Real.sqrt (∑ j, (A i j) ^ 2)))
          exact hf.bddAbove
        have hD : Continuous fun A : Matrix (Fin a) (Fin b) ℝ =>
            ∑ i : Fin a, |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)| := by
          refine continuous_finset_sum Finset.univ ?_
          intro i _
          exact ((hrr i).sub continuous_const).abs
        have hD0 : (∑ i : Fin a,
            |Real.sqrt (∑ j, (A₀ i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)|) = 0 := by
          simp
        have hup : ∀ A : Matrix (Fin a) (Fin b) ℝ,
            (⨆ i : Fin a, Real.sqrt (∑ j, (A i j) ^ 2)) ≤
              (⨆ i : Fin a, Real.sqrt (∑ j, (A₀ i j) ^ 2)) +
                ∑ i : Fin a, |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)| := by
          intro A
          refine ciSup_le (fun i => ?_)
          have h1 : Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2) ≤
              |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)| := le_abs_self _
          have h2 : Real.sqrt (∑ j, (A₀ i j) ^ 2) ≤
              ⨆ i : Fin a, Real.sqrt (∑ j, (A₀ i j) ^ 2) := le_ciSup (hbdA A₀) i
          have h3 : |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)| ≤
              ∑ i : Fin a,
                |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)| :=
            Finset.single_le_sum
              (f := fun i => |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)|)
              (fun i _ => abs_nonneg _) (Finset.mem_univ i)
          linarith
        have hlow : ∀ A : Matrix (Fin a) (Fin b) ℝ,
            (⨆ i : Fin a, Real.sqrt (∑ j, (A₀ i j) ^ 2)) ≤
              (⨆ i : Fin a, Real.sqrt (∑ j, (A i j) ^ 2)) +
                ∑ i : Fin a, |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)| := by
          intro A
          refine ciSup_le (fun i => ?_)
          have h1 : -|Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)| ≤
              Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2) := neg_abs_le _
          have h2 : Real.sqrt (∑ j, (A i j) ^ 2) ≤
              ⨆ i : Fin a, Real.sqrt (∑ j, (A i j) ^ 2) := le_ciSup (hbdA A) i
          have h3 : |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)| ≤
              ∑ i : Fin a,
                |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)| :=
            Finset.single_le_sum
              (f := fun i => |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)|)
              (fun i _ => abs_nonneg _) (Finset.mem_univ i)
          linarith
        have hc : Continuous fun _ : Matrix (Fin a) (Fin b) ℝ =>
            (⨆ i : Fin a, Real.sqrt (∑ j, (A₀ i j) ^ 2)) := continuous_const
        have htg : Tendsto (fun A : Matrix (Fin a) (Fin b) ℝ =>
            (⨆ i : Fin a, Real.sqrt (∑ j, (A₀ i j) ^ 2)) -
              ∑ i : Fin a, |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)|)
            (nhds A₀) (nhds (⨆ i : Fin a, Real.sqrt (∑ j, (A₀ i j) ^ 2))) := by
          have h := (hc.sub hD).tendsto A₀
          simpa only [hD0, sub_zero] using h
        have hth : Tendsto (fun A : Matrix (Fin a) (Fin b) ℝ =>
            (⨆ i : Fin a, Real.sqrt (∑ j, (A₀ i j) ^ 2)) +
              ∑ i : Fin a, |Real.sqrt (∑ j, (A i j) ^ 2) - Real.sqrt (∑ j, (A₀ i j) ^ 2)|)
            (nhds A₀) (nhds (⨆ i : Fin a, Real.sqrt (∑ j, (A₀ i j) ^ 2))) := by
          have h := (hc.add hD).tendsto A₀
          simpa only [hD0, add_zero] using h
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le htg hth
          (fun A => by linarith [hlow A]) (fun A => hup A)
      · haveI hE : IsEmpty (Fin a) := ⟨fun i => ha ⟨i⟩⟩
        have hpt : ∀ A A' : Matrix (Fin a) (Fin b) ℝ, A = A' := by
          intro A A'
          funext i
          exact (hE.false i).elim
        obtain ⟨A₁⟩ : Nonempty (Matrix (Fin a) (Fin b) ℝ) := ⟨fun i => (hE.false i).elim⟩
        have hconst : (fun A : Matrix (Fin a) (Fin b) ℝ =>
            ⨆ i : Fin a, Real.sqrt (∑ j, (A i j) ^ 2))
            = fun _ => ⨆ i : Fin a, Real.sqrt (∑ j, (A₁ i j) ^ 2) := by
          funext A
          rw [hpt A A₁]
        rw [hconst]
        exact continuous_const
    have hrw : (fun A : Matrix (Fin a) (Fin b) ℝ =>
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm A)
        = fun A => ⨆ i : Fin a, Real.sqrt (∑ j, (A i j) ^ 2) := by
      funext A
      unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm
      rfl
    rw [hrw]
    exact hsup
  have h1 : MeasurableSet {ω : OmType |
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
        (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Wmask p (Om ω)) ≤ Lam} := by
    have hspec : Continuous fun A : Matrix (Fin m) (Fin n) ℝ =>
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm A := by
      have hlin : Continuous fun A : Matrix (Fin m) (Fin n) ℝ =>
          (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A :=
        LinearMap.continuous_of_finiteDimensional _
      simpa only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm]
        using hlin.norm
    have hW : Measurable fun ω : OmType =>
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Wmask p (Om ω) := by
      rw [measurable_pi_iff]
      intro i
      rw [measurable_pi_iff]
      intro j
      have hpt : Measurable fun ω : OmType => p⁻¹ * Om ω i j - 1 :=
        ((hOm i j).const_mul p⁻¹).sub measurable_const
      simpa only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Wmask]
        using hpt
    have hf : Measurable fun ω : OmType =>
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
          (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Wmask p (Om ω)) :=
      hspec.measurable.comp hW
    exact MeasureTheory.StronglyMeasurable.measurableSet_le hf.stronglyMeasurable
      stronglyMeasurable_const
  have h2 : MeasurableSet {ω : OmType |
      ∀ (A B : Matrix (Fin m) (Fin n) ℝ),
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 A →
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 B →
        |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
            (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) A) B| ≤
          th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm A *
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm B} := by
    have hfinG : ∀ {β : Type} [TopologicalSpace β]
        {F G : β → Matrix (Fin m) (Fin n) ℝ}, Continuous F → Continuous G →
        Continuous fun x => PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
          (F x) (G x) := by
      intro β _ F G hF hG
      unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
      refine continuous_finset_sum Finset.univ ?_
      intro i _
      refine continuous_finset_sum Finset.univ ?_
      intro j _
      exact ((continuous_apply j).comp ((continuous_apply i).comp hF)).mul
        ((continuous_apply j).comp ((continuous_apply i).comp hG))
    have hcT : Continuous fun A' : Matrix (Fin n) (Fin r) ℝ => U0 * A'ᵀ :=
      Continuous.matrix_mul (A := fun _ : Matrix (Fin n) (Fin r) ℝ => U0)
        (B := fun A' : Matrix (Fin n) (Fin r) ℝ => A'ᵀ) continuous_const (htrans r)
    have hcS : Continuous fun B' : Matrix (Fin m) (Fin r) ℝ => B' * V0ᵀ :=
      Continuous.matrix_mul (A := fun B' : Matrix (Fin m) (Fin r) ℝ => B')
        (B := fun _ : Matrix (Fin m) (Fin r) ℝ => V0ᵀ) continuous_id continuous_const
    obtain ⟨u1, hu1⟩ := statopia_math_node_1035201060_6a460451 n r
    obtain ⟨u2, hu2⟩ := statopia_math_node_1035201060_6a460451 m r
    have hgm : ∀ (A' : Matrix (Fin n) (Fin r) ℝ) (B' : Matrix (Fin m) (Fin r) ℝ)
        (C' : Matrix (Fin n) (Fin r) ℝ) (D' : Matrix (Fin m) (Fin r) ℝ),
        Measurable fun ω : OmType =>
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ))
              (U0 * C'ᵀ + D' * V0ᵀ)| -
            th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) := by
      intro A' B' C' D'
      have hcont : Continuous fun X : Matrix (Fin m) (Fin n) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner X (U0 * C'ᵀ + D' * V0ᵀ) :=
        hfinG (F := fun X : Matrix (Fin m) (Fin n) ℝ => X) (G := fun _ => U0 * C'ᵀ + D' * V0ᵀ)
          continuous_id continuous_const
      have h1c : Measurable fun ω : OmType =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
            (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ))
            (U0 * C'ᵀ + D' * V0ᵀ) :=
        hcont.measurable.comp (hTmeas (U0 * A'ᵀ + B' * V0ᵀ))
      exact h1c.abs.sub measurable_const
    have hc1 : ∀ (ω : OmType) (B' : Matrix (Fin m) (Fin r) ℝ)
        (C' : Matrix (Fin n) (Fin r) ℝ) (D' : Matrix (Fin m) (Fin r) ℝ),
        Continuous fun A' : Matrix (Fin n) (Fin r) ℝ =>
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ))
              (U0 * C'ᵀ + D' * V0ᵀ)| -
            th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) := by
      intro ω B' C' D'
      have hΦ : Continuous fun A' : Matrix (Fin n) (Fin r) ℝ => U0 * A'ᵀ + B' * V0ᵀ :=
        hcT.add continuous_const
      have hF : Continuous fun A' : Matrix (Fin n) (Fin r) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ) :=
        (hTmcont (Om ω)).comp hΦ
      have hG : Continuous fun _ : Matrix (Fin n) (Fin r) ℝ => U0 * C'ᵀ + D' * V0ᵀ := continuous_const
      have hin := hfinG hF hG
      have hb : Continuous fun A' : Matrix (Fin n) (Fin r) ℝ =>
          th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) := by
        have hth : Continuous fun _ : Matrix (Fin n) (Fin r) ℝ => th := continuous_const
        have hBc : Continuous fun _ : Matrix (Fin n) (Fin r) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) :=
          continuous_const
        exact (hth.mul (hfn.comp hΦ)).mul hBc
      exact hin.abs.sub hb
    have hc2 : ∀ (ω : OmType) (A' : Matrix (Fin n) (Fin r) ℝ)
        (C' : Matrix (Fin n) (Fin r) ℝ) (D' : Matrix (Fin m) (Fin r) ℝ),
        Continuous fun B' : Matrix (Fin m) (Fin r) ℝ =>
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ))
              (U0 * C'ᵀ + D' * V0ᵀ)| -
            th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) := by
      intro ω A' C' D'
      have hΦ : Continuous fun B' : Matrix (Fin m) (Fin r) ℝ => U0 * A'ᵀ + B' * V0ᵀ :=
        continuous_const.add hcS
      have hF : Continuous fun B' : Matrix (Fin m) (Fin r) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ) :=
        (hTmcont (Om ω)).comp hΦ
      have hG : Continuous fun _ : Matrix (Fin m) (Fin r) ℝ => U0 * C'ᵀ + D' * V0ᵀ := continuous_const
      have hin := hfinG hF hG
      have hb : Continuous fun B' : Matrix (Fin m) (Fin r) ℝ =>
          th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) := by
        have hth : Continuous fun _ : Matrix (Fin m) (Fin r) ℝ => th := continuous_const
        have hBc : Continuous fun _ : Matrix (Fin m) (Fin r) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) :=
          continuous_const
        exact (hth.mul (hfn.comp hΦ)).mul hBc
      exact hin.abs.sub hb
    have hc3 : ∀ (ω : OmType) (A' : Matrix (Fin n) (Fin r) ℝ)
        (B' : Matrix (Fin m) (Fin r) ℝ) (D' : Matrix (Fin m) (Fin r) ℝ),
        Continuous fun C' : Matrix (Fin n) (Fin r) ℝ =>
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ))
              (U0 * C'ᵀ + D' * V0ᵀ)| -
            th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) := by
      intro ω A' B' D'
      have hΦ : Continuous fun C' : Matrix (Fin n) (Fin r) ℝ => U0 * C'ᵀ + D' * V0ᵀ :=
        hcT.add continuous_const
      have hF : Continuous fun _ : Matrix (Fin n) (Fin r) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ) :=
        continuous_const
      have hin := hfinG hF hΦ
      have hb : Continuous fun C' : Matrix (Fin n) (Fin r) ℝ =>
          th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) := by
        have hth : Continuous fun _ : Matrix (Fin n) (Fin r) ℝ => th := continuous_const
        have hAc : Continuous fun _ : Matrix (Fin n) (Fin r) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) :=
          continuous_const
        exact (hth.mul hAc).mul (hfn.comp hΦ)
      exact hin.abs.sub hb
    have hc4 : ∀ (ω : OmType) (A' : Matrix (Fin n) (Fin r) ℝ)
        (B' : Matrix (Fin m) (Fin r) ℝ) (C' : Matrix (Fin n) (Fin r) ℝ),
        Continuous fun D' : Matrix (Fin m) (Fin r) ℝ =>
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ))
              (U0 * C'ᵀ + D' * V0ᵀ)| -
            th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) := by
      intro ω A' B' C'
      have hΦ : Continuous fun D' : Matrix (Fin m) (Fin r) ℝ => U0 * C'ᵀ + D' * V0ᵀ :=
        continuous_const.add hcS
      have hF : Continuous fun _ : Matrix (Fin m) (Fin r) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ) :=
        continuous_const
      have hin := hfinG hF hΦ
      have hb : Continuous fun D' : Matrix (Fin m) (Fin r) ℝ =>
          th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) := by
        have hth : Continuous fun _ : Matrix (Fin m) (Fin r) ℝ => th := continuous_const
        have hAc : Continuous fun _ : Matrix (Fin m) (Fin r) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) :=
          continuous_const
        exact (hth.mul hAc).mul (hfn.comp hΦ)
      exact hin.abs.sub hb
    have hmain : MeasurableSet {ω : OmType |
        ∀ (A' : Matrix (Fin n) (Fin r) ℝ) (B' : Matrix (Fin m) (Fin r) ℝ)
          (C' : Matrix (Fin n) (Fin r) ℝ) (D' : Matrix (Fin m) (Fin r) ℝ),
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ))
              (U0 * C'ᵀ + D' * V0ᵀ)| -
            th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) ≤ 0} :=
      keyD4 (u₁ := u1) (u₂ := u2) (u₃ := u1) (u₄ := u2) hu1 hu2 hu1 hu2
        (fun (ω : OmType) (A' : Matrix (Fin n) (Fin r) ℝ) (B' : Matrix (Fin m) (Fin r) ℝ)
          (C' : Matrix (Fin n) (Fin r) ℝ) (D' : Matrix (Fin m) (Fin r) ℝ) =>
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ))
              (U0 * C'ᵀ + D' * V0ᵀ)| -
            th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ))
        hgm hc1 hc2 hc3 hc4
    have hEq : {ω : OmType |
        ∀ (A' : Matrix (Fin n) (Fin r) ℝ) (B' : Matrix (Fin m) (Fin r) ℝ)
          (C' : Matrix (Fin n) (Fin r) ℝ) (D' : Matrix (Fin m) (Fin r) ℝ),
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (U0 * A'ᵀ + B' * V0ᵀ))
              (U0 * C'ᵀ + D' * V0ᵀ)| -
            th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * A'ᵀ + B' * V0ᵀ) *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm (U0 * C'ᵀ + D' * V0ᵀ) ≤ 0}
        = {ω : OmType |
        ∀ (A B : Matrix (Fin m) (Fin n) ℝ),
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 A →
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 B →
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) A) B| ≤
            th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm A *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm B} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h A B hA hB
        simp only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect] at hA hB
        obtain ⟨A', B', hAB⟩ := hA
        obtain ⟨C', D', hCD⟩ := hB
        have hg := h A' B' C' D'
        first
          | exact (test1 _ _).mp (by simpa only [hAB, hCD] using hg)
          | exact (test1 _ _).mp (by simpa only [← hAB, ← hCD] using hg)
      · intro h A' B' C' D'
        have hA : PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 (U0 * A'ᵀ + B' * V0ᵀ) := by
          simp only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect]
          exact ⟨A', B', rfl⟩
        have hB : PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 (U0 * C'ᵀ + D' * V0ᵀ) := by
          simp only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect]
          exact ⟨C', D', rfl⟩
        exact (test1 _ _).mpr (h _ _ hA hB)
    rw [← hEq]
    exact hmain
  have h3 : MeasurableSet {ω : OmType |
      ∀ (k l : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
        (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
        |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
            (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
            (C * Dᵀ)| ≤
          Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D} := by
    have hspec : Continuous fun A : Matrix (Fin m) (Fin n) ℝ =>
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm A := by
      have hlin : Continuous fun A : Matrix (Fin m) (Fin n) ℝ =>
          (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A :=
        LinearMap.continuous_of_finiteDimensional _
      simpa only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm]
        using hlin.norm
    have hfnG : ∀ (a b : ℕ), Continuous fun A : Matrix (Fin a) (Fin b) ℝ =>
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm A := by
      intro a b
      unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm
      have hsq : Continuous fun A : Matrix (Fin a) (Fin b) ℝ => ∑ i, ∑ j, (A i j) ^ 2 := by
        refine continuous_finset_sum Finset.univ ?_
        intro i _
        refine continuous_finset_sum Finset.univ ?_
        intro j _
        exact ((continuous_apply j).comp (continuous_apply i)).pow 2
      exact Real.continuous_sqrt.comp hsq
    have hfinG : ∀ {β : Type} [TopologicalSpace β] {a b : ℕ}
        {F G : β → Matrix (Fin a) (Fin b) ℝ}, Continuous F → Continuous G →
        Continuous fun x => PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
          (F x) (G x) := by
      intro β _ a b F G hF hG
      unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
      refine continuous_finset_sum Finset.univ ?_
      intro i _
      refine continuous_finset_sum Finset.univ ?_
      intro j _
      exact ((continuous_apply j).comp ((continuous_apply i).comp hF)).mul
        ((continuous_apply j).comp ((continuous_apply i).comp hG))
    have hbF1 : ∀ (k l : ℕ) (C : Matrix (Fin m) (Fin l) ℝ),
        Continuous fun A : Matrix (Fin m) (Fin k) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C := by
      intro k l C
      unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor
      have hC1 : Continuous fun _ : Matrix (Fin m) (Fin k) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm C := continuous_const
      have hC2 : Continuous fun _ : Matrix (Fin m) (Fin k) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm C := continuous_const
      exact Continuous.min ((hfnG m k).mul hC1) ((hrow m k).mul hC2)
    have hbF2 : ∀ (k l : ℕ) (A : Matrix (Fin m) (Fin k) ℝ),
        Continuous fun C : Matrix (Fin m) (Fin l) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C := by
      intro k l A
      unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor
      have hA1 : Continuous fun _ : Matrix (Fin m) (Fin l) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm A := continuous_const
      have hA2 : Continuous fun _ : Matrix (Fin m) (Fin l) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm A := continuous_const
      exact Continuous.min (hA1.mul (hrow m l)) (hA2.mul (hfnG m l))
    have hbF3 : ∀ (k l : ℕ) (D : Matrix (Fin n) (Fin l) ℝ),
        Continuous fun B : Matrix (Fin n) (Fin k) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
      intro k l D
      unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor
      have hD1 : Continuous fun _ : Matrix (Fin n) (Fin k) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm D := continuous_const
      have hD2 : Continuous fun _ : Matrix (Fin n) (Fin k) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm D := continuous_const
      exact Continuous.min ((hfnG n k).mul hD1) ((hrow n k).mul hD2)
    have hbF4 : ∀ (k l : ℕ) (B : Matrix (Fin n) (Fin k) ℝ),
        Continuous fun D : Matrix (Fin n) (Fin l) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
      intro k l B
      unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor
      have hB1 : Continuous fun _ : Matrix (Fin n) (Fin l) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm B := continuous_const
      have hB2 : Continuous fun _ : Matrix (Fin n) (Fin l) ℝ =>
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm B := continuous_const
      exact Continuous.min (hB1.mul (hrow n l)) (hB2.mul (hfnG n l))
    have hS : ∀ (k l : ℕ), MeasurableSet {ω : OmType |
        ∀ (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
          (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
              (C * Dᵀ)| ≤
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D} := by
      intro k l
      obtain ⟨uA, huA⟩ := statopia_math_node_1035201060_6a460451 m k
      obtain ⟨uB, huB⟩ := statopia_math_node_1035201060_6a460451 n k
      obtain ⟨uC, huC⟩ := statopia_math_node_1035201060_6a460451 m l
      obtain ⟨uD, huD⟩ := statopia_math_node_1035201060_6a460451 n l
      have hgm : ∀ (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
          (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
          Measurable fun ω : OmType =>
            |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
                (C * Dᵀ)| -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
        intro A B C D
        have hcont : Continuous fun X : Matrix (Fin m) (Fin n) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner X (C * Dᵀ) :=
          hfinG (F := fun X : Matrix (Fin m) (Fin n) ℝ => X) (G := fun _ => C * Dᵀ)
            continuous_id continuous_const
        have h1c : Measurable fun ω : OmType =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
              (C * Dᵀ) :=
          hcont.measurable.comp (hTmeas (A * Bᵀ))
        exact h1c.abs.sub measurable_const
      have hc1 : ∀ (ω : OmType) (B : Matrix (Fin n) (Fin k) ℝ) (C : Matrix (Fin m) (Fin l) ℝ)
          (D : Matrix (Fin n) (Fin l) ℝ),
          Continuous fun A : Matrix (Fin m) (Fin k) ℝ =>
            |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
                (C * Dᵀ)| -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
        intro ω B C D
        have hF : Continuous fun A : Matrix (Fin m) (Fin k) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ) :=
          (hTmcont (Om ω)).comp
            (Continuous.matrix_mul (A := fun A => A) (B := fun _ => Bᵀ) continuous_id continuous_const)
        have hG : Continuous fun _ : Matrix (Fin m) (Fin k) ℝ => C * Dᵀ := continuous_const
        have hin := hfinG hF hG
        have hb : Continuous fun A : Matrix (Fin m) (Fin k) ℝ =>
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
          have hL : Continuous fun _ : Matrix (Fin m) (Fin k) ℝ => Lam := continuous_const
          have hBd : Continuous fun _ : Matrix (Fin m) (Fin k) ℝ =>
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := continuous_const
          exact (hL.mul (hbF1 k l C)).mul hBd
        exact hin.abs.sub hb
      have hc2 : ∀ (ω : OmType) (A : Matrix (Fin m) (Fin k) ℝ) (C : Matrix (Fin m) (Fin l) ℝ)
          (D : Matrix (Fin n) (Fin l) ℝ),
          Continuous fun B : Matrix (Fin n) (Fin k) ℝ =>
            |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
                (C * Dᵀ)| -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
        intro ω A C D
        have hF : Continuous fun B : Matrix (Fin n) (Fin k) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ) :=
          (hTmcont (Om ω)).comp
            (Continuous.matrix_mul (A := fun _ => A) (B := fun B => Bᵀ) continuous_const (htrans k))
        have hG : Continuous fun _ : Matrix (Fin n) (Fin k) ℝ => C * Dᵀ := continuous_const
        have hin := hfinG hF hG
        have hb : Continuous fun B : Matrix (Fin n) (Fin k) ℝ =>
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
          have hL : Continuous fun _ : Matrix (Fin n) (Fin k) ℝ => Lam := continuous_const
          have hAC : Continuous fun _ : Matrix (Fin n) (Fin k) ℝ =>
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C := continuous_const
          exact (hL.mul hAC).mul (hbF3 k l D)
        exact hin.abs.sub hb
      have hc3 : ∀ (ω : OmType) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
          (D : Matrix (Fin n) (Fin l) ℝ),
          Continuous fun C : Matrix (Fin m) (Fin l) ℝ =>
            |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
                (C * Dᵀ)| -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
        intro ω A B D
        have hF : Continuous fun _ : Matrix (Fin m) (Fin l) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ) :=
          continuous_const
        have hG : Continuous fun C : Matrix (Fin m) (Fin l) ℝ => C * Dᵀ :=
          Continuous.matrix_mul (A := fun C => C) (B := fun _ => Dᵀ) continuous_id continuous_const
        have hin := hfinG hF hG
        have hb : Continuous fun C : Matrix (Fin m) (Fin l) ℝ =>
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
          have hL : Continuous fun _ : Matrix (Fin m) (Fin l) ℝ => Lam := continuous_const
          have hBd : Continuous fun _ : Matrix (Fin m) (Fin l) ℝ =>
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := continuous_const
          exact (hL.mul (hbF2 k l A)).mul hBd
        exact hin.abs.sub hb
      have hc4 : ∀ (ω : OmType) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
          (C : Matrix (Fin m) (Fin l) ℝ),
          Continuous fun D : Matrix (Fin n) (Fin l) ℝ =>
            |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
                (C * Dᵀ)| -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
        intro ω A B C
        have hF : Continuous fun _ : Matrix (Fin n) (Fin l) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ) :=
          continuous_const
        have hG : Continuous fun D : Matrix (Fin n) (Fin l) ℝ => C * Dᵀ :=
          Continuous.matrix_mul (A := fun _ => C) (B := fun D => Dᵀ) continuous_const (htrans l)
        have hin := hfinG hF hG
        have hb : Continuous fun D : Matrix (Fin n) (Fin l) ℝ =>
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D := by
          have hL : Continuous fun _ : Matrix (Fin n) (Fin l) ℝ => Lam := continuous_const
          have hAC : Continuous fun _ : Matrix (Fin n) (Fin l) ℝ =>
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C := continuous_const
          exact (hL.mul hAC).mul (hbF4 k l B)
        exact hin.abs.sub hb
      have hmain : MeasurableSet {ω : OmType |
          ∀ (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
            (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
            |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
                (C * Dᵀ)| -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D ≤ 0} :=
        keyD4 (u₁ := uA) (u₂ := uB) (u₃ := uC) (u₄ := uD) huA huB huC huD
          (fun (ω : OmType) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
            (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ) =>
            |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
                (C * Dᵀ)| -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D)
          hgm hc1 hc2 hc3 hc4
      have hEq : {ω : OmType |
          ∀ (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
            (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
            |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
                (C * Dᵀ)| -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D ≤ 0}
          = {ω : OmType |
          ∀ (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
            (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
            |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
                (C * Dᵀ)| ≤
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D} := by
        ext ω
        simp only [Set.mem_setOf_eq, test1]
      rw [← hEq]
      exact hmain
    rw [show {ω : OmType |
        ∀ (k l : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
          (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
              (C * Dᵀ)| ≤
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D}
        = ⋂ k : ℕ, ⋂ l : ℕ, {ω : OmType |
        ∀ (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
          (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
          |PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (A * Bᵀ))
              (C * Dᵀ)| ≤
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor A C *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.bFactor B D} from by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun l => hS k l))
  have h4 : MeasurableSet {ω : OmType |
      ∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
            (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) ≤
          Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R} := by
    have hspec : Continuous fun A : Matrix (Fin m) (Fin n) ℝ =>
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm A := by
      have hlin : Continuous fun A : Matrix (Fin m) (Fin n) ℝ =>
          (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A :=
        LinearMap.continuous_of_finiteDimensional _
      simpa only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm]
        using hlin.norm
    have hS : ∀ k : ℕ, MeasurableSet {ω : OmType |
        ∀ (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) ≤
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R} := by
      intro k
      obtain ⟨uL, huL⟩ := statopia_math_node_1035201060_6a460451 m k
      obtain ⟨uR, huR⟩ := statopia_math_node_1035201060_6a460451 n k
      have hgm : ∀ (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
          Measurable fun ω : OmType =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R := by
        intro L R
        have h1c : Measurable fun ω : OmType =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) :=
          hspec.measurable.comp (hTmeas (L * Rᵀ))
        exact h1c.sub measurable_const
      have hc1 : ∀ (ω : OmType) (R : Matrix (Fin n) (Fin k) ℝ),
          Continuous fun L : Matrix (Fin m) (Fin k) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R := by
        intro ω R
        have hTR : Continuous fun L : Matrix (Fin m) (Fin k) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ) :=
          (hTmcont (Om ω)).comp
            (Continuous.matrix_mul (A := fun L => L) (B := fun _ => Rᵀ) continuous_id continuous_const)
        have hLam : Continuous fun _ : Matrix (Fin m) (Fin k) ℝ => Lam := continuous_const
        have hRn : Continuous fun _ : Matrix (Fin m) (Fin k) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R := continuous_const
        exact (hspec.comp hTR).sub ((hLam.mul (hrow m k)).mul hRn)
      have hc2 : ∀ (ω : OmType) (L : Matrix (Fin m) (Fin k) ℝ),
          Continuous fun R : Matrix (Fin n) (Fin k) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R := by
        intro ω L
        have hTR : Continuous fun R : Matrix (Fin n) (Fin k) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ) :=
          (hTmcont (Om ω)).comp
            (Continuous.matrix_mul (A := fun _ => L) (B := fun R => Rᵀ) continuous_const (htrans k))
        have hLam : Continuous fun _ : Matrix (Fin n) (Fin k) ℝ => Lam := continuous_const
        have hLn : Continuous fun _ : Matrix (Fin n) (Fin k) ℝ =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L := continuous_const
        exact (hspec.comp hTR).sub ((hLam.mul hLn).mul (hrow n k))
      have hmain : MeasurableSet {ω : OmType |
          ∀ (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R ≤ 0} :=
        keyD2 (u₁ := uL) (u₂ := uR) huL huR
          (fun (ω : OmType) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ) =>
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R)
          hgm hc1 hc2
      have hEq : {ω : OmType |
          ∀ (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) -
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R ≤ 0}
          = {ω : OmType |
          ∀ (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
            PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
                (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) ≤
              Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R} := by
        ext ω
        simp only [Set.mem_setOf_eq, test1]
      rw [← hEq]
      exact hmain
    rw [show {ω : OmType |
        ∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) ≤
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R}
        = ⋂ k : ℕ, {ω : OmType |
        ∀ (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm
              (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p (Om ω) (L * Rᵀ)) ≤
            Lam * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm L *
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm R} from by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    exact MeasurableSet.iInter hS
  refine MeasurableSet.inter h1 ?_
  exact MeasurableSet.inter h2 (MeasurableSet.inter h3 h4)
  /- @proof-region region.target-node.session.f4b94fed4cbdfbcc end -/

end Statlib.Imported

