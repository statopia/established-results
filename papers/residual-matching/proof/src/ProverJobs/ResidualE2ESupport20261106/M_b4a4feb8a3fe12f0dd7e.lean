import Statlib.HighDim.SpectralPerturbation.Eigenvalues
import Statlib.HighDim.Vocabulary.Spectral
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_9c23ebb40b1c7df8c1d6

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
theorem statopia_math_node_1534763445_28183d06 : ∀ (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (H : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hH_meas : ∀ a b : Fin n, Measurable fun ω : Ω => H ω a b)
    (hH : ∀ ω : Ω, (H ω).IsHermitian)
    (k : Fin (Fintype.card (Fin n))),
    Measurable fun ω : Ω => (hH ω).eigenvalues₀ k := by
  /- @proof-region region.target-node.session.3d376fc202a8c0c1 begin -/
  classical
  intro n Ω _ H hH_meas hH k
  have htrace : Measurable fun ω : Ω => ∑ j : Fin n, (hH ω).eigenvalues j := by
    have hfun : (fun ω : Ω => ∑ j : Fin n, (hH ω).eigenvalues j) = fun ω => (H ω).trace := by
      funext ω
      simpa using (Matrix.IsHermitian.trace_eq_sum_eigenvalues (hH ω)).symm
    rw [hfun]
    exact Finset.measurable_sum (s := Finset.univ) (f := fun i ω => H ω i i) (fun i _ => hH_meas i i)
  have hsorted : ∀ j : Fin n,
      Measurable fun ω : Ω => Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) j :=
    fun j => statopia_math_node_1536250861_1a8485ab n H hH_meas hH j
  have hsort_def : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (j : Fin n),
      Statlib.HighDim.Vocabulary.sortedEigenvalues A hA j
        = hA.eigenvalues (Tuple.sort hA.eigenvalues j) := by
    intro A hA j
    simp only [Statlib.HighDim.Vocabulary.sortedEigenvalues]
  have heig₀_form : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (j : Fin n),
      hA.eigenvalues j
        = hA.eigenvalues₀ ((Fintype.equivOfCardEq
            (Fintype.card_fin (Fintype.card (Fin n)))).symm j) := by
    intro A hA j
    simp only [Matrix.IsHermitian.eigenvalues]
  have heig₀_inv : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
      (i : Fin (Fintype.card (Fin n))),
      hA.eigenvalues₀ i
        = hA.eigenvalues (Fintype.equivOfCardEq
            (Fintype.card_fin (Fintype.card (Fin n))) i) := by
    intro A hA i
    have h := heig₀_form A hA (Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card (Fin n))) i)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hanti₀ : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
      {i j : Fin (Fintype.card (Fin n))}, i ≤ j → hA.eigenvalues₀ j ≤ hA.eigenvalues₀ i := by
    intro A hA i j hij
    simp only [Matrix.IsHermitian.eigenvalues₀]
    exact LinearMap.IsSymmetric.eigenvalues_antitone _ _ hij
  have hgoal_of_eig : (∀ j : Fin n, Measurable fun ω : Ω => (hH ω).eigenvalues j) →
      Measurable fun ω : Ω => (hH ω).eigenvalues₀ k := by
    intro he
    have hfun : (fun ω : Ω => (hH ω).eigenvalues₀ k)
        = fun ω : Ω => (hH ω).eigenvalues (Fintype.equivOfCardEq
            (Fintype.card_fin (Fintype.card (Fin n))) k) := by
      funext ω
      exact heig₀_inv (H ω) (hH ω) k
    rw [hfun]
    exact he (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))) k)
  have hsorted₀ : ∀ k : Fin (Fintype.card (Fin n)), Measurable fun ω : Ω =>
      Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
        (Fin.cast (Fintype.card_fin n) k) :=
    fun k => hsorted _
  have hev_one : ∀ (A : Matrix (Fin 1) (Fin 1) ℝ) (hA : A.IsHermitian) (j : Fin 1),
      hA.eigenvalues j = A 0 0 := by
    intro A hA j
    have h0 : j = 0 := Fin.ext (by have := j.isLt; omega)
    have h' : A.trace = hA.eigenvalues 0 := by
      simpa using Matrix.IsHermitian.trace_eq_sum_eigenvalues hA
    rw [h0, ← h', Matrix.trace_fin_one]
  have hsorted_one : ∀ (A : Matrix (Fin 1) (Fin 1) ℝ) (hA : A.IsHermitian) (j : Fin 1),
      Statlib.HighDim.Vocabulary.sortedEigenvalues A hA j = A 0 0 := by
    intro A hA j
    obtain ⟨σ, hσ⟩ := Statlib.HighDim.SpectralPerturbation.sortedEigenvalues_perm A hA
    rw [hσ j]
    exact hev_one A hA (σ j)
  have heig_one : ∀ (A : Ω → Matrix (Fin 1) (Fin 1) ℝ)
      (hA : ∀ ω : Ω, (A ω).IsHermitian)
      (hmeas : ∀ a b : Fin 1, Measurable fun ω : Ω => A ω a b) (j : Fin 1),
      Measurable fun ω : Ω => (hA ω).eigenvalues j := by
    intro A hA hmeas j
    have hfun : (fun ω : Ω => (hA ω).eigenvalues j) = fun ω : Ω => A ω 0 0 := by
      funext ω
      exact hev_one (A ω) (hA ω) j
    rw [hfun]
    exact hmeas 0 0
  have hcount : ∀ t : ℝ, Measurable fun ω : Ω =>
      (Finset.univ.filter (fun i : Fin n =>
        t < Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i)).card := by
    intro t
    have hfun : (fun ω : Ω => (Finset.univ.filter (fun i : Fin n =>
            t < Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i)).card)
        = fun ω => ∑ i : Fin n,
            (if t < Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i then (1 : ℕ) else 0) := by
      funext ω
      rw [Finset.card_filter]
    rw [hfun]
    refine Finset.measurable_sum (s := Finset.univ) (f := fun i ω =>
      if t < Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i then (1 : ℕ) else 0) ?_
    intro i _
    have hset : MeasurableSet {ω : Ω |
        t < Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i} :=
      (measurableSet_Ioi (a := t)).preimage (hsorted i)
    exact Measurable.ite hset measurable_const measurable_const
  have hsvals : ∀ i : Fin n, Measurable fun ω : Ω =>
      Real.sqrt (Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i) :=
    fun i => Real.continuous_sqrt.measurable.comp (hsorted i)
  have hsvals₀ : ∀ i : Fin (Fintype.card (Fin n)), Measurable fun ω : Ω =>
      Real.sqrt (Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
        (Fin.cast (Fintype.card_fin n) i)) :=
    fun i => Real.continuous_sqrt.measurable.comp (hsorted₀ i)
  have hsvals_shape : ∀ i : Fin n, Measurable fun ω : Ω =>
      Real.sqrt (Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
        (Fin.cast (Fintype.card_fin n) (Fin.cast (Fintype.card_fin n).symm i))) :=
    fun i => hsvals
      (Fin.cast (Fintype.card_fin n) (Fin.cast (Fintype.card_fin n).symm i))
  have hcount_le : ∀ t : ℝ, Measurable fun ω : Ω =>
      (Finset.univ.filter (fun i : Fin n =>
        Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i ≤ t)).card := by
    intro t
    have hfun : (fun ω : Ω => (Finset.univ.filter (fun i : Fin n =>
            Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i ≤ t)).card)
        = fun ω => ∑ i : Fin n,
            (if Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i ≤ t
              then (1 : ℕ) else 0) := by
      funext ω
      rw [Finset.card_filter]
    rw [hfun]
    refine Finset.measurable_sum (s := Finset.univ) (f := fun i ω =>
      if Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i ≤ t then (1 : ℕ) else 0) ?_
    intro i _
    have hset : MeasurableSet {ω : Ω |
        Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i ≤ t} :=
      (measurableSet_Iic (a := t)).preimage (hsorted i)
    exact Measurable.ite hset measurable_const measurable_const
  have hcard_eq : ∀ (t : ℝ) (ω : Ω),
      Fintype.card {i : Fin n // t < Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i}
        = Fintype.card {i : Fin n // t < (hH ω).eigenvalues i} := by
    intro t ω
    obtain ⟨σ, hσ⟩ := Statlib.HighDim.SpectralPerturbation.sortedEigenvalues_perm (H ω) (hH ω)
    refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨i, hi⟩
      exact ⟨σ i, by rw [← hσ i]; exact hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨σ.symm i, by rw [hσ (σ.symm i), Equiv.apply_symm_apply]; exact hi⟩
    · rintro ⟨i, hi⟩
      exact Subtype.ext (Equiv.symm_apply_apply σ i)
    · rintro ⟨i, hi⟩
      exact Subtype.ext (Equiv.apply_symm_apply σ i)
  have hcount_eig : ∀ t : ℝ, Measurable fun ω : Ω =>
      Fintype.card {i : Fin n // t < (hH ω).eigenvalues i} := by
    intro t
    have hfun : (fun ω : Ω => Fintype.card {i : Fin n // t < (hH ω).eigenvalues i})
        = fun ω : Ω => (Finset.univ.filter (fun i : Fin n =>
            t < Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i)).card := by
      funext ω
      rw [← hcard_eq t ω]
      exact Fintype.card_subtype _
    rw [hfun]
    exact hcount t
  have hcard_eq_le : ∀ (t : ℝ) (ω : Ω),
      Fintype.card {i : Fin n // Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i ≤ t}
        = Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ t} := by
    intro t ω
    obtain ⟨σ, hσ⟩ := Statlib.HighDim.SpectralPerturbation.sortedEigenvalues_perm (H ω) (hH ω)
    refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨i, hi⟩
      exact ⟨σ i, by rw [← hσ i]; exact hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨σ.symm i, by rw [hσ (σ.symm i), Equiv.apply_symm_apply]; exact hi⟩
    · rintro ⟨i, hi⟩
      exact Subtype.ext (Equiv.symm_apply_apply σ i)
    · rintro ⟨i, hi⟩
      exact Subtype.ext (Equiv.apply_symm_apply σ i)
  have hcount_eig_le : ∀ t : ℝ, Measurable fun ω : Ω =>
      Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ t} := by
    intro t
    have hfun : (fun ω : Ω => Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ t})
        = fun ω : Ω => (Finset.univ.filter (fun i : Fin n =>
            Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i ≤ t)).card := by
      funext ω
      rw [← hcard_eq_le t ω]
      exact Fintype.card_subtype _
    rw [hfun]
    exact hcount_le t
  have hcount₀ : ∀ t : ℝ, Measurable fun ω : Ω =>
      Fintype.card {i : Fin (Fintype.card (Fin n)) // (hH ω).eigenvalues₀ i ≤ t} := by
    intro t
    have hfun : (fun ω : Ω =>
          Fintype.card {i : Fin (Fintype.card (Fin n)) // (hH ω).eigenvalues₀ i ≤ t})
        = fun ω : Ω => Fintype.card {j : Fin n // (hH ω).eigenvalues j ≤ t} := by
      funext ω
      refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
      · rintro ⟨i, hi⟩
        exact ⟨Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))) i,
          by rw [← heig₀_inv (H ω) (hH ω) i]; exact hi⟩
      · rintro ⟨j, hj⟩
        exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm j,
          by
            rw [heig₀_inv (H ω) (hH ω) ((Fintype.equivOfCardEq
                (Fintype.card_fin (Fintype.card (Fin n)))).symm j), Equiv.apply_symm_apply]
            exact hj⟩
      · rintro ⟨i, hi⟩
        exact Subtype.ext (Equiv.symm_apply_apply
          (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))) i)
      · rintro ⟨j, hj⟩
        exact Subtype.ext (Equiv.apply_symm_apply
          (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))) j)
    rw [hfun]
    exact hcount_eig_le t
  have hcount_sum : ∀ (t : ℝ) (ω : Ω),
      Fintype.card {i : Fin n // t < (hH ω).eigenvalues i}
        + Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ t} = n := by
    intro t ω
    have hcongr : Fintype.card ({i : Fin n // t < (hH ω).eigenvalues i} ⊕
        {i : Fin n // (hH ω).eigenvalues i ≤ t}) = Fintype.card (Fin n) := by
      refine Fintype.card_congr ?_
      exact
        { toFun := Sum.elim (fun x => x.1) (fun y => y.1)
          invFun := fun i => if h : t < (hH ω).eigenvalues i then Sum.inl ⟨i, h⟩
            else Sum.inr ⟨i, not_lt.1 h⟩
          left_inv := by
            rintro (x | y)
            · simp [x.2]
            · simp [not_lt.2 y.2]
          right_inv := by
            intro i
            by_cases h : t < (hH ω).eigenvalues i
            · simp [h]
            · simp [h] }
    rwa [Fintype.card_sum, Fintype.card_fin] at hcongr
  have hcount_compl : ∀ (t : ℝ) (ω : Ω),
      Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ t}
        = n - Fintype.card {i : Fin n // t < (hH ω).eigenvalues i} := by
    intro t ω
    have h := hcount_sum t ω
    omega
  have hcount_iff : ∀ (j : ℕ) (ω : Ω) (q : ℚ),
      Fintype.card {i : Fin n // (q : ℝ) < (hH ω).eigenvalues i} ≤ j ↔
        n - j ≤ Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)} := by
    intro j ω q
    have hsum := hcount_sum (q : ℝ) ω
    have h := hcount_compl (q : ℝ) ω
    constructor <;> intro h' <;> omega
  have hstep3_strict_iff : ∀ (t : ℝ) (j : ℕ),
      {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
        Fintype.card {i : Fin n // (q : ℝ) < (hH ω).eigenvalues i} ≤ j}
        = {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
          n - j ≤ Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} := by
    intro t j
    ext ω
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h q hq => (hcount_iff j ω q).1 (h q hq),
      fun h q hq => (hcount_iff j ω q).2 (h q hq)⟩


  have hstep3 : ∀ (t : ℝ) (j : ℕ), MeasurableSet {ω : Ω |
      ∀ q : ℚ, t < (q : ℝ) →
        j < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} := by
    intro t j
    have himpl : ∀ q : ℚ, MeasurableSet {ω : Ω | t < (q : ℝ) →
        j < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} := by
      intro q
      by_cases hq : t < (q : ℝ)
      · have hEq : {ω : Ω | t < (q : ℝ) →
            j < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}}
            = {ω : Ω | j < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} := by
          ext ω
          simp [hq]
        rw [hEq]
        exact (measurableSet_Ioi (a := j)).preimage (hcount_eig_le (q : ℝ))
      · have hEq : {ω : Ω | t < (q : ℝ) →
            j < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} = Set.univ := by
          ext ω
          simp [hq]
        rw [hEq]
        exact MeasurableSet.univ
    have hEq : {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
          j < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}}
        = ⋂ q : ℚ, {ω : Ω | t < (q : ℝ) →
          j < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hEq]
    exact MeasurableSet.iInter himpl
  have hstep3_ge : ∀ (t : ℝ) (c : ℕ), MeasurableSet {ω : Ω |
      ∀ q : ℚ, t < (q : ℝ) →
        c ≤ Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} := by
    intro t c
    have hEq : {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
          c ≤ Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}}
        = ⋂ d : {d : ℕ // d < c}, {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
            (d : ℕ) < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h d q hq
        exact lt_of_lt_of_le d.2 (h q hq)
      · intro h q hq
        by_contra hc
        push_neg at hc
        exact absurd (h ⟨_, hc⟩ q hq) (lt_irrefl _)
    rw [hEq]
    exact MeasurableSet.iInter fun d => hstep3 t (d : ℕ)
  have hstep3_strict : ∀ (t : ℝ) (j : ℕ), MeasurableSet {ω : Ω |
      ∀ q : ℚ, t < (q : ℝ) →
        Fintype.card {i : Fin n // (q : ℝ) < (hH ω).eigenvalues i} ≤ j} := by
    intro t j
    rw [hstep3_strict_iff t j]
    exact hstep3_ge t (n - j)

  have hstep3_sound_all : ∀ (t : ℝ) (ω : Ω) (j : Fin n),
      Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) j ≤ t →
      ∀ q : ℚ, t < (q : ℝ) →
        j.val < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)} := by
    intro t ω j hj q hq
    have hle : Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) j ≤ (q : ℝ) :=
      le_trans hj (le_of_lt hq)
    have hbase := Statlib.HighDim.SpectralPerturbation.sortedEigenvalues_lt_card_eigen_le_sorted
      (H ω) (hH ω) j
    have hinj : Function.Injective
        (fun x : {i : Fin n // (hH ω).eigenvalues i ≤
            Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) j} =>
          (⟨x.1, le_trans x.2 hle⟩ : {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)})) := by
      intro x y hxy
      exact Subtype.ext (by simpa using congrArg (fun z => z.val) hxy)
    have hcard : Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤
          Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) j}
        ≤ Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)} :=
      Fintype.card_le_of_injective _ hinj
    exact lt_of_lt_of_le hbase hcard
  have hcard_lt_fin_all : ∀ j : Fin n, Fintype.card {i : Fin n // i < j} = j.val := by
    intro j
    refine (Fintype.card_congr ?_).trans (Fintype.card_fin _)
    exact
      { toFun := fun x => ⟨x.1.val, x.2⟩
        invFun := fun m => ⟨⟨m.val, lt_of_lt_of_le m.isLt j.isLt.le⟩, m.isLt⟩
        left_inv := fun x => Subtype.ext (Fin.ext rfl)
        right_inv := fun m => Fin.ext rfl }
  have hcard_succ : ∀ j : Fin n,
      Fintype.card {i : Fin n // j < i} + 1 = Fintype.card {i : Fin n // j ≤ i} := by
    intro j
    have h1 : Fintype.card {i : Fin n // j < i}
        = (Finset.univ.filter (fun i : Fin n => j < i)).card := Fintype.card_subtype _
    have h2 : Fintype.card {i : Fin n // j ≤ i}
        = (Finset.univ.filter (fun i : Fin n => j ≤ i)).card := Fintype.card_subtype _
    have hfil : Finset.univ.filter (fun i : Fin n => j ≤ i)
        = insert j (Finset.univ.filter (fun i : Fin n => j < i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases hij : i = j
        · exact Or.inl hij
        · exact Or.inr (lt_of_le_of_ne h (Ne.symm hij))
      · intro h
        rcases h with rfl | h
        · exact le_rfl
        · exact le_of_lt h
    have hnotmem : j ∉ Finset.univ.filter (fun i : Fin n => j < i) := by simp
    rw [h1, h2, hfil]
    simp [hnotmem]
  have hstep3_strict_eq_all : ∀ (t : ℝ) (j : Fin n),
      {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) j ≤ t}
        = {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
            Fintype.card {i : Fin n // (q : ℝ) < (hH ω).eigenvalues i}
              ≤ Fintype.card {i : Fin n // j < i}} := by
    intro t j
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hj q hq
      rw [← hcard_eq (q : ℝ) ω]
      refine Fintype.card_le_of_injective
        (fun x : {i : Fin n // (q : ℝ) <
            Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i} =>
          (⟨x.1, ?_⟩ : {i : Fin n // j < i})) ?_
      · by_contra hx
        have hxj : x.1 ≤ j := not_lt.1 hx
        have hmono := Statlib.HighDim.SpectralPerturbation.sortedEigenvalues_mono
          (H ω) (hH ω) hxj
        exact absurd x.2 (not_lt.2 (le_trans (le_trans hmono hj) (le_of_lt hq)))
      · intro x y hxy
        exact Subtype.ext (by simpa using congrArg (fun z => z.val) hxy)
    · intro hcond
      by_contra hcon
      push_neg at hcon
      obtain ⟨q, htq, hqj⟩ := exists_rat_btwn hcon
      have hkq := hcond q htq
      have hge_sorted : Fintype.card {i : Fin n // j ≤ i} ≤
          Fintype.card {i : Fin n // (q : ℝ) <
            Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i} := by
        refine Fintype.card_le_of_injective
          (fun x : {i : Fin n // j ≤ i} =>
            (⟨x.1, ?_⟩ : {i : Fin n // (q : ℝ) <
              Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i})) ?_
        · exact lt_of_lt_of_le hqj
            (Statlib.HighDim.SpectralPerturbation.sortedEigenvalues_mono (H ω) (hH ω) x.2)
        · intro x y hxy
          exact Subtype.ext (by simpa using congrArg (fun z => z.val) hxy)
      have hge : Fintype.card {i : Fin n // j ≤ i} ≤
          Fintype.card {i : Fin n // (q : ℝ) < (hH ω).eigenvalues i} := by
        rw [← hcard_eq (q : ℝ) ω]
        exact hge_sorted
      have hsucc := hcard_succ j
      omega
  have hsorted_ray : ∀ t : ℝ, MeasurableSet {ω : Ω |
      Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
        (Fin.cast (Fintype.card_fin n) k) ≤ t} := by
    intro t
    rw [hstep3_strict_eq_all t (Fin.cast (Fintype.card_fin n) k)]
    exact hstep3_strict t
      (Fintype.card {i : Fin n // Fin.cast (Fintype.card_fin n) k < i})
  have hsorted_meas_device : Measurable fun ω : Ω =>
      Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
        (Fin.cast (Fintype.card_fin n) k) := by
    refine measurable_of_Iic fun t => ?_
    have hEq : (fun ω : Ω => Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
          (Fin.cast (Fintype.card_fin n) k)) ⁻¹' Set.Iic t
        = {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
            (Fin.cast (Fintype.card_fin n) k) ≤ t} := by
      ext ω
      simp
    rw [hEq]
    exact hsorted_ray t
  have hstep3_complete_all : ∀ (t : ℝ) (ω : Ω) (j : Fin n),
      (∀ q : ℚ, t < (q : ℝ) →
        j.val < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}) →
      Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) j ≤ t := by
    intro t ω j hcond
    by_contra hcon
    push_neg at hcon
    obtain ⟨q, htq, hqfk⟩ := exists_rat_btwn hcon
    have hkq := hcond q htq
    have hNq_sorted : Fintype.card {i : Fin n //
        Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i ≤ (q : ℝ)}
        ≤ j.val := by
      have hinj : Function.Injective
          (fun x : {i : Fin n //
              Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) i ≤ (q : ℝ)} =>
            (⟨x.1, by
              by_contra hx
              have hxj : j ≤ x.1 := not_lt.1 hx
              have hmono := Statlib.HighDim.SpectralPerturbation.sortedEigenvalues_mono
                (H ω) (hH ω) hxj
              exact absurd (le_trans hmono x.2) (not_le.2 hqfk)⟩ :
              {i : Fin n // i < j})) := by
        intro x y hxy
        exact Subtype.ext (by simpa using congrArg (fun z => z.val) hxy)
      have hle := Fintype.card_le_of_injective _ hinj
      rwa [hcard_lt_fin_all j] at hle
    have hNq : Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}
        ≤ j.val := by
      rw [← hcard_eq_le (q : ℝ) ω]
      exact hNq_sorted
    exact absurd hkq (not_lt.2 hNq)
  have hstep3_eq_all : ∀ (t : ℝ) (j : Fin n),
      {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) j ≤ t}
        = {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
            j.val < Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} := by
    intro t j
    ext ω
    exact ⟨fun h => hstep3_sound_all t ω j h, fun h => hstep3_complete_all t ω j h⟩
  have hstep3_eq : ∀ t : ℝ,
      {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
          (Fin.cast (Fintype.card_fin n) k) ≤ t}
        = {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
            (Fin.cast (Fintype.card_fin n) k).val <
              Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} :=
    fun t => hstep3_eq_all t (Fin.cast (Fintype.card_fin n) k)
  have hRmeas : ∀ t : ℝ, MeasurableSet {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
      (Fin.cast (Fintype.card_fin n) k).val <
        Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}} :=
    fun t => hstep3 t (Fin.cast (Fintype.card_fin n) k).val
  have hcard_le_gen : ∀ {m : ℕ} (j : Fin m), Fintype.card {i : Fin m // i ≤ j} = j.val + 1 := by
    intro m j
    refine (Fintype.card_congr ?_).trans (Fintype.card_fin _)
    exact
      { toFun := fun x => ⟨x.1.val, by have h : x.1.val ≤ j.val := x.2; omega⟩
        invFun := fun q => ⟨⟨q.val, by have h : q.val < j.val + 1 := q.isLt; have h2 := j.isLt; omega⟩,
          Nat.le_of_lt_succ q.isLt⟩
        left_inv := fun x => Subtype.ext (Fin.ext rfl)
        right_inv := fun q => Fin.ext rfl }
  have hcard_succ_gen : ∀ {m : ℕ} (j : Fin m),
      Fintype.card {i : Fin m // j < i} + 1 = Fintype.card {i : Fin m // j ≤ i} := by
    intro m j
    have h1 : Fintype.card {i : Fin m // j < i}
        = (Finset.univ.filter (fun i : Fin m => j < i)).card := Fintype.card_subtype _
    have h2 : Fintype.card {i : Fin m // j ≤ i}
        = (Finset.univ.filter (fun i : Fin m => j ≤ i)).card := Fintype.card_subtype _
    have hfil : Finset.univ.filter (fun i : Fin m => j ≤ i)
        = insert j (Finset.univ.filter (fun i : Fin m => j < i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases hij : i = j
        · exact Or.inl hij
        · exact Or.inr (lt_of_le_of_ne h (Ne.symm hij))
      · intro h
        rcases h with rfl | h
        · exact le_rfl
        · exact le_of_lt h
    have hnotmem : j ∉ Finset.univ.filter (fun i : Fin m => j < i) := by simp
    rw [h1, h2, hfil]
    simp [hnotmem]
  have hcard_split : ∀ {m : ℕ} (j : Fin m),
      Fintype.card {i : Fin m // j < i} + Fintype.card {i : Fin m // i ≤ j} = m := by
    intro m j
    have hcongr : Fintype.card ({i : Fin m // j < i} ⊕ {i : Fin m // i ≤ j})
        = Fintype.card (Fin m) := by
      refine Fintype.card_congr ?_
      exact
        { toFun := Sum.elim (fun x => x.1) (fun y => y.1)
          invFun := fun i => if h : j < i then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i, not_lt.1 h⟩
          left_inv := by
            rintro (x | y)
            · simp [x.2]
            · simp [not_lt.2 y.2]
          right_inv := by
            intro i
            by_cases h : j < i
            · simp [h]
            · simp [h] }
    rwa [Fintype.card_sum, Fintype.card_fin] at hcongr
  have hchar₀ : ∀ (t : ℝ) (ω : Ω),
      (hH ω).eigenvalues₀ k ≤ t ↔
        Fintype.card (Fin n) - k.val ≤
          Fintype.card {i : Fin (Fintype.card (Fin n)) // (hH ω).eigenvalues₀ i ≤ t} := by
    intro t ω
    constructor
    · intro hk
      have hinj : Function.Injective
          (fun x : {i : Fin (Fintype.card (Fin n)) // k ≤ i} =>
            (⟨x.1, le_trans (hanti₀ (H ω) (hH ω) x.2) hk⟩ :
              {i : Fin (Fintype.card (Fin n)) // (hH ω).eigenvalues₀ i ≤ t})) := by
        intro x y hxy
        exact Subtype.ext (by simpa using congrArg (fun z => z.val) hxy)
      have hle := Fintype.card_le_of_injective _ hinj
      have hs := hcard_split k
      have hl := hcard_le_gen k
      have hsc := hcard_succ_gen k
      have hklt := k.isLt
      omega
    · intro hN
      by_contra hcon
      push_neg at hcon
      have hinj : Function.Injective
          (fun x : {i : Fin (Fintype.card (Fin n)) // (hH ω).eigenvalues₀ i ≤ t} =>
            (⟨x.1, by
              by_contra hik
              have hki : x.1 ≤ k := not_lt.1 hik
              exact absurd (le_trans (hanti₀ (H ω) (hH ω) hki) x.2) (not_le.2 hcon)⟩ :
              {i : Fin (Fintype.card (Fin n)) // k < i})) := by
        intro x y hxy
        exact Subtype.ext (by simpa using congrArg (fun z => z.val) hxy)
      have hle := Fintype.card_le_of_injective _ hinj
      have hs := hcard_split k
      have hl := hcard_le_gen k
      have hklt := k.isLt
      omega
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    exact absurd k.isLt (by simp)
  · have hray : (∀ t : ℝ, {ω : Ω | (hH ω).eigenvalues₀ k ≤ t}
        = {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
            (Fin.cast (Fintype.card_fin n) k) ≤ t}) →
        (fun ω : Ω => (hH ω).eigenvalues₀ k)
          = fun ω : Ω => Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
              (Fin.cast (Fintype.card_fin n) k) := by
      intro h
      funext ω
      have hiff : ∀ t : ℝ, ((hH ω).eigenvalues₀ k ≤ t ↔
          Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
            (Fin.cast (Fintype.card_fin n) k) ≤ t) := by
        intro t
        have hmem := Set.ext_iff.1 (h t) ω
        simpa using hmem
      refine le_antisymm ?_ ?_
      · by_contra hc
        exact absurd ((hiff _).2 le_rfl) hc
      · by_contra hc
        exact absurd ((hiff _).1 le_rfl) hc
    have hray_of_funext : ((fun ω : Ω => (hH ω).eigenvalues₀ k)
          = fun ω : Ω => Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
              (Fin.cast (Fintype.card_fin n) k)) →
        ∀ t : ℝ, {ω : Ω | (hH ω).eigenvalues₀ k ≤ t}
          = {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
              (Fin.cast (Fintype.card_fin n) k) ≤ t} := by
      intro h t
      ext ω
      have hω : (hH ω).eigenvalues₀ k =
          Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
            (Fin.cast (Fintype.card_fin n) k) := congrFun h ω
      simp only [Set.mem_setOf_eq, hω]
    have hray_iff : (∀ t : ℝ, {ω : Ω | (hH ω).eigenvalues₀ k ≤ t}
          = {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
              (Fin.cast (Fintype.card_fin n) k) ≤ t})
        ↔ ((fun ω : Ω => (hH ω).eigenvalues₀ k)
            = fun ω : Ω => Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
                (Fin.cast (Fintype.card_fin n) k)) :=
      ⟨hray, hray_of_funext⟩
    have hres_iff : (∀ q : ℚ, {ω : Ω | (hH ω).eigenvalues₀ k ≤ (q : ℝ)}
          = {ω : Ω | ∀ q' : ℚ, (q : ℝ) < (q' : ℝ) →
              (Fin.cast (Fintype.card_fin n) k).val <
                Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q' : ℝ)}})
        ↔ (∀ q : ℚ, {ω : Ω | (hH ω).eigenvalues₀ k ≤ (q : ℝ)}
          = {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
              (Fin.cast (Fintype.card_fin n) k) ≤ (q : ℝ)}) := by
      constructor
      · intro h q
        rw [h q, ← hstep3_eq (q : ℝ)]
      · intro h q
        rw [h q, hstep3_eq (q : ℝ)]
    have hrat_to_all : (∀ q : ℚ, {ω : Ω | (hH ω).eigenvalues₀ k ≤ (q : ℝ)}
          = {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
              (Fin.cast (Fintype.card_fin n) k) ≤ (q : ℝ)}) →
        ∀ t : ℝ, {ω : Ω | (hH ω).eigenvalues₀ k ≤ t}
          = {ω : Ω | Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
              (Fin.cast (Fintype.card_fin n) k) ≤ t} := by
      intro h t
      ext ω
      simp only [Set.mem_setOf_eq]
      have hiff : ∀ q : ℚ, ((hH ω).eigenvalues₀ k ≤ (q : ℝ) ↔
          Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
            (Fin.cast (Fintype.card_fin n) k) ≤ (q : ℝ)) := by
        intro q
        have hmem := Set.ext_iff.1 (h q) ω
        simpa only [Set.mem_setOf_eq] using hmem
      constructor
      · intro hx
        by_contra hy
        push_neg at hy
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hy
        exact absurd ((hiff q).1 (le_trans hx (le_of_lt hq1))) (not_le.2 hq2)
      · intro hy
        by_contra hx
        push_neg at hx
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx
        exact absurd ((hiff q).2 (le_trans hy (le_of_lt hq1))) (not_le.2 hq2)
    have hres_iff_fun : (∀ q : ℚ, {ω : Ω | (hH ω).eigenvalues₀ k ≤ (q : ℝ)}
          = {ω : Ω | ∀ q' : ℚ, (q : ℝ) < (q' : ℝ) →
              (Fin.cast (Fintype.card_fin n) k).val <
                Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q' : ℝ)}})
        ↔ ((fun ω : Ω => (hH ω).eigenvalues₀ k)
            = fun ω : Ω => Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
                (Fin.cast (Fintype.card_fin n) k)) := by
      constructor
      · intro h
        exact hray (hrat_to_all (hres_iff.1 h))
      · intro h
        exact hres_iff.2 (fun q => hray_iff.2 h (q : ℝ))
    have hresAll_iff_fun : (∀ t : ℝ, {ω : Ω | (hH ω).eigenvalues₀ k ≤ t}
          = {ω : Ω | ∀ q : ℚ, t < (q : ℝ) →
              (Fin.cast (Fintype.card_fin n) k).val <
                Fintype.card {i : Fin n // (hH ω).eigenvalues i ≤ (q : ℝ)}})
        ↔ ((fun ω : Ω => (hH ω).eigenvalues₀ k)
            = fun ω : Ω => Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω)
                (Fin.cast (Fintype.card_fin n) k)) := by
      constructor
      · intro h
        exact hres_iff_fun.1 (fun q => h (q : ℝ))
      · intro h t
        exact (hray_of_funext h t).trans (hstep3_eq t)
    have hLmeas_all : ∀ t : ℝ, MeasurableSet {ω : Ω | (hH ω).eigenvalues₀ k ≤ t} := by
      intro t
      have hEq : {ω : Ω | (hH ω).eigenvalues₀ k ≤ t}
          = {ω : Ω | Fintype.card (Fin n) - k.val ≤
              Fintype.card {i : Fin (Fintype.card (Fin n)) // (hH ω).eigenvalues₀ i ≤ t}} := by
        ext ω
        exact hchar₀ t ω
      rw [hEq]
      exact (measurableSet_Ici (a := Fintype.card (Fin n) - k.val)).preimage (hcount₀ t)
    refine measurable_of_Iic fun t => ?_
    have hEq : (fun ω : Ω => (hH ω).eigenvalues₀ k) ⁻¹' Set.Iic t
        = {ω : Ω | (hH ω).eigenvalues₀ k ≤ t} := by
      ext ω
      simp
    rw [hEq]
    exact hLmeas_all t
  /- @proof-region region.target-node.session.3d376fc202a8c0c1 end -/

end Statlib.Imported

