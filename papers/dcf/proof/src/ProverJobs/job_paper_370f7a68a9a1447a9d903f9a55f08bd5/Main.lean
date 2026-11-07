import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base

namespace PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5

noncomputable section
open scoped BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

theorem paper_370f7a68a9a1447a9d903f9a55f08bd5 :
    ∃ C2 : ℝ, 1 ≤ C2 ∧
      (∀ (p : ℕ), 0 < p → 0 < Real.log (p : ℝ) → ∀ φ : ℝ, 1 ≤ φ →
        φ ^ 3 + φ ^ 2 * (φ * Real.log (p : ℝ)) + φ * (φ * Real.log (p : ℝ)) ^ 2
          ≤ C2 * (φ * (φ * Real.log (p : ℝ)) ^ 2)) ∧
      (∀ (φ0 : ℝ → ℝ), (∀ z, φ0 z ∈ Set.Icc (0 : ℝ) 1) → ContDiff ℝ 3 φ0 →
        (∀ z, z ≤ 0 → φ0 z = 1) → (∀ z, 1 ≤ z → φ0 z = 0) →
        ∃ C1 : ℝ, ∃ C3 : ℝ, 1 ≤ C1 ∧ 1 ≤ C3 ∧
          ∀ (p : ℕ) (hp : 0 < p) (hlog : 0 < Real.log (p : ℝ))
            (φ : ℝ) (hφ : 1 ≤ φ) (y : Fin p → ℝ),
            ∃ Q : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ,
              (∀ (j k l : Fin p) (w : Fin p → ℝ), 0 ≤ Q j k l w) ∧
              (∀ (j k l : Fin p) (w : Fin p → ℝ),
                |kappaThird p φ y φ0 j k l w| ≤ Q j k l w) ∧
              (∀ w : Fin p → ℝ,
                (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, Q a b c w)
                  ≤ C1 * (φ ^ 3 + φ ^ 2 * (φ * Real.log (p : ℝ))
                      + φ * (φ * Real.log (p : ℝ)) ^ 2)) ∧
              (∀ w : Fin p → ℝ,
                (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, Q a b c w)
                  ≤ C1 * C2 * (φ * (φ * Real.log (p : ℝ)) ^ 2)) ∧
              (∀ (j k l : Fin p) (w w' : Fin p → ℝ),
                (∀ r : Fin p, |w' r| * (φ * Real.log (p : ℝ)) ≤ 1) →
                  (Q j k l w ≤ C3 * Q j k l (w + w') ∧
                    Q j k l (w + w') ≤ C3 * Q j k l w)))
:= by
  /- @proof-region region.root.b8201b127b44 begin -/
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC2ge : 1 ≤ ((Real.log 2) ^ 2)⁻¹ + (Real.log 2)⁻¹ + 1 := by
    have h1 : 0 < ((Real.log 2) ^ 2)⁻¹ := inv_pos.mpr (pow_pos hlog2pos 2)
    have h2 : 0 < (Real.log 2)⁻¹ := inv_pos.mpr hlog2pos
    linarith
  have hmainineq : ∀ (p : ℕ), 0 < p → 0 < Real.log (p : ℝ) → ∀ φ : ℝ, 1 ≤ φ →
      φ ^ 3 + φ ^ 2 * (φ * Real.log (p : ℝ)) + φ * (φ * Real.log (p : ℝ)) ^ 2
        ≤ (((Real.log 2) ^ 2)⁻¹ + (Real.log 2)⁻¹ + 1) * (φ * (φ * Real.log (p : ℝ)) ^ 2) := by
    intro p hp hlog φ hφ
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      by_contra hle
      push_neg at hle
      have hz : Real.log (p : ℝ) ≤ 0 := by
        have h := Real.log_le_log hp0 hle
        simpa using h
      linarith
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have h2 : 2 ≤ p := by
        have h1' : 1 < p := by exact_mod_cast hp1
        omega
      exact_mod_cast h2
    have hlogle : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp2
    have hinv : (Real.log (p : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ := (inv_le_inv₀ hlog hlog2pos).mpr hlogle
    have hinv2 : ((Real.log (p : ℝ)) ^ 2)⁻¹ ≤ ((Real.log 2) ^ 2)⁻¹ := by
      rw [inv_le_inv₀ (pow_pos hlog 2) (pow_pos hlog2pos 2)]
      have h1 : (0 : ℝ) ≤ Real.log (p : ℝ) - Real.log 2 := by linarith
      have h2 : (0 : ℝ) ≤ Real.log (p : ℝ) + Real.log 2 := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hkey : φ ^ 3 + φ ^ 2 * (φ * Real.log (p : ℝ)) + φ * (φ * Real.log (p : ℝ)) ^ 2
        = (φ * (φ * Real.log (p : ℝ)) ^ 2) *
            (((Real.log (p : ℝ)) ^ 2)⁻¹ + (Real.log (p : ℝ))⁻¹ + 1) := by
      have hne : Real.log (p : ℝ) ≠ 0 := ne_of_gt hlog
      field_simp
    rw [hkey]
    have hposM : (0 : ℝ) ≤ φ * (φ * Real.log (p : ℝ)) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    calc (φ * (φ * Real.log (p : ℝ)) ^ 2) *
          (((Real.log (p : ℝ)) ^ 2)⁻¹ + (Real.log (p : ℝ))⁻¹ + 1)
        ≤ (φ * (φ * Real.log (p : ℝ)) ^ 2) *
            (((Real.log 2) ^ 2)⁻¹ + (Real.log 2)⁻¹ + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hposM
          linarith
      _ = (((Real.log 2) ^ 2)⁻¹ + (Real.log 2)⁻¹ + 1) *
            (φ * (φ * Real.log (p : ℝ)) ^ 2) := by ring
  refine ⟨((Real.log 2) ^ 2)⁻¹ + (Real.log 2)⁻¹ + 1, hC2ge, hmainineq, ?_⟩
  intro φ0 hIcc hcont hleft hright
  have hvan : ∀ k : ℕ, ∀ (c : ℝ) (t : Set ℝ), IsOpen t → (∀ z ∈ t, φ0 z = c) →
      ∀ u ∈ t, iteratedDeriv (k + 1) φ0 u = 0 := by
    intro k
    induction k with
    | zero =>
      intro c t ht hc u hu
      have hev : φ0 =ᶠ[nhds u] (fun _ : ℝ => c) := by
        filter_upwards [ht.mem_nhds hu] with z hz
        exact hc z hz
      have hd : HasDerivAt φ0 0 u := (hasDerivAt_const u c).congr_of_eventuallyEq hev
      have h1 : iteratedDeriv 1 φ0 u = 0 := by
        rw [iteratedDeriv_one]
        exact hd.deriv
      simpa using h1
    | succ k ih =>
      intro c t ht hc u hu
      have hprev : ∀ z ∈ t, iteratedDeriv (k + 1) φ0 z = 0 := ih c t ht hc
      have hev : iteratedDeriv (k + 1) φ0 =ᶠ[nhds u] (fun _ : ℝ => 0) := by
        filter_upwards [ht.mem_nhds hu] with z hz
        exact hprev z hz
      rw [iteratedDeriv_succ]
      exact ((hasDerivAt_const u 0).congr_of_eventuallyEq hev).deriv
  have hc1 : Continuous (fun u : ℝ => |iteratedDeriv 1 φ0 u|) :=
    (hcont.continuous_iteratedDeriv 1 (by norm_num)).abs
  have hc2 : Continuous (fun u : ℝ => |iteratedDeriv 2 φ0 u|) :=
    (hcont.continuous_iteratedDeriv 2 (by norm_num)).abs
  have hc3 : Continuous (fun u : ℝ => |iteratedDeriv 3 φ0 u|) :=
    (hcont.continuous_iteratedDeriv 3 (by norm_num)).abs
  have hne0 : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by constructor <;> norm_num⟩
  obtain ⟨u1, hu1, hmax1⟩ := isCompact_Icc.exists_isMaxOn hne0 hc1.continuousOn
  obtain ⟨u2, hu2, hmax2⟩ := isCompact_Icc.exists_isMaxOn hne0 hc2.continuousOn
  obtain ⟨u3, hu3, hmax3⟩ := isCompact_Icc.exists_isMaxOn hne0 hc3.continuousOn
  set d1 : ℝ := |iteratedDeriv 1 φ0 u1| with hd1eq
  set d2 : ℝ := |iteratedDeriv 2 φ0 u2| with hd2eq
  set d3 : ℝ := |iteratedDeriv 3 φ0 u3| with hd3eq
  have hd1 : 0 ≤ d1 := by rw [hd1eq]; exact abs_nonneg _
  have hd2 : 0 ≤ d2 := by rw [hd2eq]; exact abs_nonneg _
  have hd3 : 0 ≤ d3 := by rw [hd3eq]; exact abs_nonneg _
  have hz1 : ∀ u : ℝ, (u < 0 ∨ 1 < u) → iteratedDeriv 1 φ0 u = 0 := by
    intro u hu
    rcases hu with h | h
    · exact hvan 0 1 (Set.Iio 0) isOpen_Iio (fun z hz => hleft z (le_of_lt hz)) u h
    · exact hvan 0 0 (Set.Ioi 1) isOpen_Ioi (fun z hz => hright z (le_of_lt hz)) u h
  have hz2 : ∀ u : ℝ, (u < 0 ∨ 1 < u) → iteratedDeriv 2 φ0 u = 0 := by
    intro u hu
    rcases hu with h | h
    · exact hvan 1 1 (Set.Iio 0) isOpen_Iio (fun z hz => hleft z (le_of_lt hz)) u h
    · exact hvan 1 0 (Set.Ioi 1) isOpen_Ioi (fun z hz => hright z (le_of_lt hz)) u h
  have hz3 : ∀ u : ℝ, (u < 0 ∨ 1 < u) → iteratedDeriv 3 φ0 u = 0 := by
    intro u hu
    rcases hu with h | h
    · exact hvan 2 1 (Set.Iio 0) isOpen_Iio (fun z hz => hleft z (le_of_lt hz)) u h
    · exact hvan 2 0 (Set.Ioi 1) isOpen_Ioi (fun z hz => hright z (le_of_lt hz)) u h
  have hb1 : ∀ u : ℝ, |iteratedDeriv 1 φ0 u| ≤ d1 := by
    intro u
    rcases lt_or_ge u 0 with h | h
    · rw [hz1 u (Or.inl h), abs_zero]
      exact hd1
    rcases lt_or_ge 1 u with h' | h'
    · rw [hz1 u (Or.inr h'), abs_zero]
      exact hd1
    · exact hmax1 ⟨h, h'⟩
  have hb2 : ∀ u : ℝ, |iteratedDeriv 2 φ0 u| ≤ d2 := by
    intro u
    rcases lt_or_ge u 0 with h | h
    · rw [hz2 u (Or.inl h), abs_zero]
      exact hd2
    rcases lt_or_ge 1 u with h' | h'
    · rw [hz2 u (Or.inr h'), abs_zero]
      exact hd2
    · exact hmax2 ⟨h, h'⟩
  have hb3 : ∀ u : ℝ, |iteratedDeriv 3 φ0 u| ≤ d3 := by
    intro u
    rcases lt_or_ge u 0 with h | h
    · rw [hz3 u (Or.inl h), abs_zero]
      exact hd3
    rcases lt_or_ge 1 u with h' | h'
    · rw [hz3 u (Or.inr h'), abs_zero]
      exact hd3
    · exact hmax3 ⟨h, h'⟩
  have hbound : ∀ u : ℝ, |iteratedDeriv 1 φ0 u| ≤ d1 ∧ |iteratedDeriv 2 φ0 u| ≤ d2 ∧
      |iteratedDeriv 3 φ0 u| ≤ d3 := fun u => ⟨hb1 u, hb2 u, hb3 u⟩
  refine ⟨max (max 1 d3) (max (6 * d2) (6 * d1)), Real.exp 6, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left 1 d3) (le_max_left _ _)
  · have h0 : Real.exp 0 ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
    simpa only [Real.exp_zero] using h0
  · intro p hp hlog φ hφ y
    have hφpos : 0 < φ := by linarith
    set β : ℝ := φ * Real.log (p : ℝ) with hβeq
    have hβpos : 0 < β := by rw [hβeq]; exact mul_pos hφpos hlog
    have hC2ineq : φ ^ 3 + φ ^ 2 * β + φ * β ^ 2
        ≤ (((Real.log 2) ^ 2)⁻¹ + (Real.log 2)⁻¹ + 1) * (φ * β ^ 2) :=
      hmainineq p hp hlog φ hφ
    have hgb1 : ∀ t : ℝ,
        |iteratedDeriv 1 (fun s : ℝ => φ0 (φ * s)) t| ≤ φ ^ (1 : ℕ) * d1 := by
      intro t
      rw [iteratedDeriv_comp_const_mul (n := 1) (hcont.of_le (by norm_num)) φ]
      simp only [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hφpos) 1)]
      exact mul_le_mul_of_nonneg_left (hb1 _) (pow_nonneg (le_of_lt hφpos) 1)
    have hgb2 : ∀ t : ℝ,
        |iteratedDeriv 2 (fun s : ℝ => φ0 (φ * s)) t| ≤ φ ^ (2 : ℕ) * d2 := by
      intro t
      rw [iteratedDeriv_comp_const_mul (n := 2) (hcont.of_le (by norm_num)) φ]
      simp only [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hφpos) 2)]
      exact mul_le_mul_of_nonneg_left (hb2 _) (pow_nonneg (le_of_lt hφpos) 2)
    have hgb3 : ∀ t : ℝ,
        |iteratedDeriv 3 (fun s : ℝ => φ0 (φ * s)) t| ≤ φ ^ (3 : ℕ) * d3 := by
      intro t
      rw [iteratedDeriv_comp_const_mul (n := 3) hcont φ]
      simp only [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hφpos) 3)]
      exact mul_le_mul_of_nonneg_left (hb3 _) (pow_nonneg (le_of_lt hφpos) 3)
    have hgbound : ∀ t : ℝ,
        |iteratedDeriv 1 (fun s : ℝ => φ0 (φ * s)) t| ≤ φ ^ (1 : ℕ) * d1 ∧
        |iteratedDeriv 2 (fun s : ℝ => φ0 (φ * s)) t| ≤ φ ^ (2 : ℕ) * d2 ∧
        |iteratedDeriv 3 (fun s : ℝ => φ0 (φ * s)) t| ≤ φ ^ (3 : ℕ) * d3 :=
      fun t => ⟨hgb1 t, hgb2 t, hgb3 t⟩
    let pi : (Fin p → ℝ) → Fin p → ℝ := fun w j =>
      Real.exp (β * (w j - y j)) / (∑ m : Fin p, Real.exp (β * (w m - y m)))
    let W : (Fin p → ℝ) → Fin p → Fin p → ℝ := fun w j k =>
      pi w j * (if j = k then (1 : ℝ) else 0) + pi w j * pi w k
    let Pp : (Fin p → ℝ) → Fin p → Fin p → Fin p → ℝ := fun w j k l =>
      pi w j * (if j = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)
      + pi w j * pi w l * (if j = k then (1 : ℝ) else 0)
      + pi w j * pi w k * (if j = l then (1 : ℝ) else 0)
      + pi w j * pi w k * (if k = l then (1 : ℝ) else 0)
      + 2 * pi w j * pi w k * pi w l
    let Qm : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ := fun j k l w =>
      φ ^ 3 * d3 * pi w j * pi w k * pi w l
      + φ ^ 2 * d2 * β * (W w j k * pi w l + W w j l * pi w k + W w k l * pi w j)
      + φ * d1 * β ^ 2 * Pp w j k l
    have hkt : ∀ (j k l : Fin p) (w : Fin p → ℝ),
        kappaThird p φ y φ0 j k l w
          = (iteratedFDeriv ℝ 3 (fun v : Fin p → ℝ =>
              φ0 (φ * (β⁻¹ * Real.log (∑ m : Fin p, Real.exp (β * (v m - y m)))))) w)
              (fun i : Fin 3 => Pi.single (![j, k, l] i) (1 : ℝ)) :=
      fun j k l w => rfl
    have hdep := statopia_math_node_2201401131_f578e354 p hp β hβpos φ hφpos y φ0 hcont
      d1 d2 d3 hd1 hd2 hd3 hbound hgbound
    refine ⟨Qm, ?_, ?_, ?_, ?_, ?_⟩
    · intro j k l w
      exact (hdep j k l w).1
    · intro j k l w
      rw [hkt j k l w]
      exact (hdep j k l w).2
    · intro w
      have htot := statopia_math_node_1216269461_011b141c p hp β hβpos φ hφ y
        d1 d2 d3 hd1 hd2 hd3 (((Real.log 2) ^ 2)⁻¹ + (Real.log 2)⁻¹ + 1) hC2ineq
      exact htot.2.2.1 w
    · intro w
      have htot := statopia_math_node_1216269461_011b141c p hp β hβpos φ hφ y
        d1 d2 d3 hd1 hd2 hd3 (((Real.log 2) ^ 2)⁻¹ + (Real.log 2)⁻¹ + 1) hC2ineq
      exact htot.2.2.2 w
    · intro j k l w w' hw
      exact statopia_math_node_4085384541_bfcefbca p hp β hβpos φ hφpos y
        d1 d2 d3 hd1 hd2 hd3 j k l w w' hw
  /- @proof-region region.root.b8201b127b44 end -/

end Statlib.Imported

