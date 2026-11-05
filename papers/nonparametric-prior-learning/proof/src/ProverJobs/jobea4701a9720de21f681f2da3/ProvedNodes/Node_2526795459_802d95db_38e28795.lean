import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_1339717380_bb4bcebe_ea83abde

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_2526795459_802d95db : ∀ {X Y U Θ V : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U] [MeasurableSpace Θ]
    [Zero X] [Zero Y]
    (M : Model X Y U Θ V)
    (HP Q : ProbabilityMeasure Θ)
    (n : ℕ) (hn : 0 < n)
    [MeasurableSpace.CountableOrCountablyGenerated Θ (Fin n → U)]
    (ω : Fin n → Block (X × Y))
    (hPrior_meas : ∀ i : Fin n, Measurable fun θ : Θ =>
      (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))
    (hPost_meas : ∀ i : Fin n, Measurable fun θ : Θ =>
      (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))
    (hKL_meas : ∀ i : Fin n, Measurable fun θ : Θ =>
      InformationTheory.klDiv (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
        (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)),
    ENNReal.toEReal
        (InformationTheory.klDiv
          ((Q : Measure Θ).bind fun θ =>
            Measure.map (fun u : Fin n → U => (θ, u))
              (Measure.pi fun i : Fin n =>
                (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)))
          ((HP : Measure Θ).bind fun θ =>
            Measure.map (fun u : Fin n → U => (θ, u))
              (Measure.pi fun i : Fin n =>
                (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))))
      = ENNReal.toEReal (InformationTheory.klDiv (Q : Measure Θ) (HP : Measure Θ))
        + baseKLSum M n Q ω := by
  /- @proof-region region.target-node.session.9b1307fcd42d51b8 begin -/
  intro X Y U Θ V
    _ _ _ _ _ _
    M HP Qpost n hn
    _ omega hPrior_meas hPost_meas hKL_meas
  have hKL_aemeas : ∀ i : Fin n, AEMeasurable (fun θ : Θ =>
      InformationTheory.klDiv
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)) (Qpost : Measure Θ) :=
    fun i => (hKL_meas i).aemeasurable
  have hTER_zero : ((0 : ENNReal)).toEReal = 0 := by simp [ENNReal.toEReal]
  have hTER_eq_top : ∀ a : ENNReal, ENNReal.toEReal a = ⊤ ↔ a = ⊤ := by
    intro a
    rcases a with _ | x <;> simp [ENNReal.toEReal]
  have hTER_add : ∀ a b : ENNReal,
      ENNReal.toEReal (a + b) = ENNReal.toEReal a + ENNReal.toEReal b := by
    intro a b
    rcases a with _ | x <;> rcases b with _ | y <;>
      simp [← ENNReal.coe_add, ENNReal.toEReal, EReal.coe_add]
  have hTER_sum : ∀ (s : Finset (Fin n)) (f : Fin n → ENNReal),
      ENNReal.toEReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.toEReal (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro f; simp [ENNReal.toEReal]
    | insert a s ha ih =>
      intro f
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hTER_add, ih f]
  have hklDiv_eq_top_of_not_ac : ∀ (μ ν : Measure U), ¬ μ ≪ ν →
      InformationTheory.klDiv μ ν = ⊤ := by
    intro μ ν h
    simp only [InformationTheory.klDiv]
    rw [if_neg (fun hc => h hc.1)]
  have hklDiv_eq_top_or_ofReal : ∀ (μ ν : Measure U),
      InformationTheory.klDiv μ ν = ⊤ ∨ ∃ r : ℝ, InformationTheory.klDiv μ ν = ENNReal.ofReal r := by
    intro μ ν
    simp only [InformationTheory.klDiv]
    split_ifs with h
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  have hAC_of_klDiv_ne_top : ∀ (μ ν : Measure U), InformationTheory.klDiv μ ν ≠ ⊤ → μ ≪ ν := by
    intro μ ν h
    by_contra hc
    exact h (hklDiv_eq_top_of_not_ac μ ν hc)
  have hklDiv_toEReal_eq_top : ∀ (μ ν : Measure U),
      ENNReal.toEReal (InformationTheory.klDiv μ ν) = ⊤ ↔ InformationTheory.klDiv μ ν = ⊤ :=
    fun μ ν => hTER_eq_top _
  have hTER_ne_top : ∀ a : ENNReal, a ≠ ⊤ → ENNReal.toEReal a ≠ ⊤ := by
    intro a ha h
    exact ha ((hTER_eq_top a).mp h)
  have hTER_eq_zero : ∀ a : ENNReal, ENNReal.toEReal a = 0 ↔ a = 0 := by
    intro a
    rcases a with _ | x <;> simp [ENNReal.toEReal]
  have hTER_coe_toReal : ∀ a : ENNReal, a ≠ ⊤ →
      ENNReal.toEReal a = ((a.toReal : ℝ) : EReal) := by
    intro a ha
    rcases a with _ | x
    · exact absurd rfl ha
    · simp [ENNReal.toEReal, ENNReal.coe_toReal]
  have hTER_add_eq_top : ∀ a b : ENNReal,
      ENNReal.toEReal a + ENNReal.toEReal b = ⊤ ↔ a + b = ⊤ := by
    intro a b
    rw [← hTER_add a b]
    exact hTER_eq_top (a + b)
  have hTER_sum_eq_top : ∀ (s : Finset (Fin n)) (f : Fin n → ENNReal),
      (∑ i ∈ s, ENNReal.toEReal (f i)) = ⊤ ↔ ∑ i ∈ s, f i = ⊤ := by
    intro s f
    rw [← hTER_sum s f]
    exact hTER_eq_top (∑ i ∈ s, f i)
  have hTER_ne_zero : ∀ a : ENNReal, a ≠ 0 → ENNReal.toEReal a ≠ 0 := by
    intro a ha h
    exact ha ((hTER_eq_zero a).mp h)
  have hAC_of_toEReal_ne_top : ∀ (μ ν : Measure U),
      ENNReal.toEReal (InformationTheory.klDiv μ ν) ≠ ⊤ → μ ≪ ν := by
    intro μ ν h
    exact hAC_of_klDiv_ne_top μ ν (fun hh => h ((hklDiv_toEReal_eq_top μ ν).mpr hh))
  have hTER_add_eq_zero : ∀ a b : ENNReal,
      ENNReal.toEReal a + ENNReal.toEReal b = 0 ↔ a + b = 0 := by
    intro a b
    rw [← hTER_add a b]
    exact hTER_eq_zero (a + b)
  have hTER_sum_eq_zero : ∀ (s : Finset (Fin n)) (f : Fin n → ENNReal),
      (∑ i ∈ s, ENNReal.toEReal (f i)) = 0 ↔ ∑ i ∈ s, f i = 0 := by
    intro s f
    rw [← hTER_sum s f]
    exact hTER_eq_zero (∑ i ∈ s, f i)
  have hklDiv_eq_ofReal_of_ne_top : ∀ (μ ν : Measure U), InformationTheory.klDiv μ ν ≠ ⊤ →
      ∃ r : ℝ, InformationTheory.klDiv μ ν = ENNReal.ofReal r := by
    intro μ ν h
    rcases hklDiv_eq_top_or_ofReal μ ν with htop | ⟨r, hr⟩
    · exact absurd htop h
    · exact ⟨r, hr⟩
  have hTER_add_ne_top : ∀ a b : ENNReal,
      ENNReal.toEReal a + ENNReal.toEReal b ≠ ⊤ ↔ a + b ≠ ⊤ := by
    intro a b
    rw [← hTER_add a b]
    exact not_congr (hTER_eq_top (a + b))
  have hTER_sum_ne_top : ∀ (s : Finset (Fin n)) (f : Fin n → ENNReal),
      (∑ i ∈ s, ENNReal.toEReal (f i)) ≠ ⊤ ↔ ∑ i ∈ s, f i ≠ ⊤ := by
    intro s f
    rw [← hTER_sum s f]
    exact not_congr (hTER_eq_top (∑ i ∈ s, f i))
  have hENNReal_add_ne_top : ∀ a b : ENNReal, a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ := by
    intro a b
    rcases a with _ | x <;> rcases b with _ | y <;> simp [← ENNReal.coe_add]
  have hENNReal_sum_ne_top : ∀ (s : Finset (Fin n)) (f : Fin n → ENNReal),
      (∑ i ∈ s, f i) ≠ ⊤ ↔ ∀ i ∈ s, f i ≠ ⊤ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro f; simp
    | insert a s ha ih =>
      intro f
      rw [Finset.sum_insert ha, hENNReal_add_ne_top, ih f]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hmem
        · exact h1
        · exact h2 i hmem
      · intro h
        exact ⟨h a (Finset.mem_insert_self a s),
          fun i hi => h i (Finset.mem_insert_of_mem hi)⟩
  have hTER_sum_ne_top_all : ∀ (s : Finset (Fin n)) (f : Fin n → ENNReal),
      (∑ i ∈ s, ENNReal.toEReal (f i)) ≠ ⊤ ↔ ∀ i ∈ s, f i ≠ ⊤ := by
    intro s f
    rw [← hTER_sum s f]
    exact (not_congr (hTER_eq_top (∑ i ∈ s, f i))).trans (hENNReal_sum_ne_top s f)
  have hbaseKLSum_ne_top : baseKLSum M n Qpost omega ≠ ⊤ ↔ ∀ i : Fin n,
      (∫⁻ θ, InformationTheory.klDiv
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ)) ≠ ⊤ := by
    simp only [baseKLSum]
    rw [hTER_sum_ne_top_all]
    simp
  have hENNReal_add_eq_zero : ∀ a b : ENNReal, a + b = 0 ↔ a = 0 ∧ b = 0 := by
    intro a b
    rcases a with _ | x <;> rcases b with _ | y <;> simp [← ENNReal.coe_add]
  have hENNReal_sum_eq_zero : ∀ (s : Finset (Fin n)) (f : Fin n → ENNReal),
      (∑ i ∈ s, f i) = 0 ↔ ∀ i ∈ s, f i = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro f; simp
    | insert a s ha ih =>
      intro f
      rw [Finset.sum_insert ha, hENNReal_add_eq_zero, ih f]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hmem
        · exact h1
        · exact h2 i hmem
      · intro h
        exact ⟨h a (Finset.mem_insert_self a s),
          fun i hi => h i (Finset.mem_insert_of_mem hi)⟩
  have hbaseKLSum_eq_zero : baseKLSum M n Qpost omega = 0 ↔ ∀ i : Fin n,
      (∫⁻ θ, InformationTheory.klDiv
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ)) = 0 := by
    simp only [baseKLSum]
    rw [hTER_sum_eq_zero, hENNReal_sum_eq_zero]
    simp
  have hENNReal_add_eq_top : ∀ a b : ENNReal, a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
    intro a b
    constructor
    · intro h
      by_contra hc
      exact (hENNReal_add_ne_top a b |>.mpr
        ⟨fun ha => hc (Or.inl ha), fun hb => hc (Or.inr hb)⟩) h
    · rintro (ha | hb)
      · rw [ha]; simp
      · rw [hb]; simp
  have hENNReal_sum_eq_top : ∀ (s : Finset (Fin n)) (f : Fin n → ENNReal),
      (∑ i ∈ s, f i) = ⊤ ↔ ∃ i ∈ s, f i = ⊤ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro f; simp
    | insert a s ha ih =>
      intro f
      rw [Finset.sum_insert ha, hENNReal_add_eq_top, ih f]
      constructor
      · rintro (h1 | ⟨i, hi, hfi⟩)
        · exact ⟨a, Finset.mem_insert_self a s, h1⟩
        · exact ⟨i, Finset.mem_insert_of_mem hi, hfi⟩
      · rintro ⟨i, hi, hfi⟩
        rcases Finset.mem_insert.mp hi with rfl | hmem
        · exact Or.inl hfi
        · exact Or.inr ⟨i, hmem, hfi⟩
  have hbaseKLSum_eq_top : baseKLSum M n Qpost omega = ⊤ ↔ ∃ i : Fin n,
      (∫⁻ θ, InformationTheory.klDiv
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ)) = ⊤ := by
    simp only [baseKLSum]
    rw [hTER_sum_eq_top, hENNReal_sum_eq_top]
    simp
  have hRHS_eq_top :
      ENNReal.toEReal (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
        + baseKLSum M n Qpost omega = ⊤ ↔
      InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ) = ⊤ ∨
      ∃ i : Fin n, (∫⁻ θ, InformationTheory.klDiv
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ)) = ⊤ := by
    simp only [baseKLSum]
    rw [← hTER_sum Finset.univ, hTER_add_eq_top, hENNReal_add_eq_top, hENNReal_sum_eq_top]
    simp
  have hLin : (∫⁻ θ, ∑ i : Fin n, InformationTheory.klDiv
      (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
      (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ))
      = ∑ i : Fin n, ∫⁻ θ, InformationTheory.klDiv
          (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
          (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ) :=
    lintegral_finset_sum Finset.univ (fun i _ => hKL_meas i)
  have hInt_sum_eq_top :
      (∫⁻ θ, ∑ i : Fin n, InformationTheory.klDiv
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ)) = ⊤ ↔
      ∃ i : Fin n, (∫⁻ θ, InformationTheory.klDiv
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ)) = ⊤ := by
    rw [hLin, hENNReal_sum_eq_top]
    simp
  have hInt_sum_ne_top :
      (∫⁻ θ, ∑ i : Fin n, InformationTheory.klDiv
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ)) ≠ ⊤ ↔
      ∀ i : Fin n, (∫⁻ θ, InformationTheory.klDiv
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ)) ≠ ⊤ := by
    rw [hLin, hENNReal_sum_ne_top]
    simp
  have hchain :
      ENNReal.toEReal
          (InformationTheory.klDiv
            ((Qpost : Measure Θ).bind fun θ =>
              (Measure.pi fun i : Fin n =>
                (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)).map
                (fun u : Fin n → U => (θ, u)))
            ((HP : Measure Θ).bind fun θ =>
              (Measure.pi fun i : Fin n =>
                (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)).map
                (fun u : Fin n → U => (θ, u))))
        = ENNReal.toEReal
            (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
          + ∑ i : Fin n, ENNReal.toEReal (∫⁻ θ, InformationTheory.klDiv
              (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
              (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ)) := by
    have hCR : InformationTheory.klDiv
            ((Qpost : Measure Θ).bind fun θ =>
              (Measure.pi fun i : Fin n =>
                (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)).map
                (fun u : Fin n → U => (θ, u)))
            ((HP : Measure Θ).bind fun θ =>
              (Measure.pi fun i : Fin n =>
                (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)).map
                (fun u : Fin n → U => (θ, u)))
        = InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ)
          + ∫⁻ θ, ∑ i : Fin n, InformationTheory.klDiv
              (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
              (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) ∂(Qpost : Measure Θ) :=
      statopia_math_node_1339717380_bb4bcebe (Theta := Θ) n hn Qpost HP
        (fun i θ => (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))
        (fun i θ => (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))
        (fun i θ => inferInstance) (fun i θ => inferInstance)
        hPost_meas hPrior_meas
        hKL_meas
    rw [hCR, hTER_add, hLin, hTER_sum Finset.univ]
  simpa only [baseKLSum] using hchain
  /- @proof-region region.target-node.session.9b1307fcd42d51b8 end -/

end
end Statlib.Imported
