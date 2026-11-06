import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_943015288_0eb97663 : ∀ (m n : ℕ) (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (i : Fin m) (j : Fin n) (L Kt : ℝ)
    (hKt : 0 < Kt) (hL : 0 < L)
    (hmeas : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j))
    (htail : ∀ t : ℝ, 0 < t →
      ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} ≤
        ENNReal.ofReal (2 * Real.exp (-t / Kt))),
    (∫ x, |x i j| * (if |x i j| ≤ L then (0 : ℝ) else 1) ∂ν ≤
      2 * (L + Kt) * Real.exp (-L / Kt)) ∧
    (∫ x, (x i j) ^ 2 * (if |x i j| ≤ L then (0 : ℝ) else 1) ∂ν ≤
      (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt)) := by
  /- @proof-region region.target-node.session.497d953a2ab7b549 begin -/
  intro m n ν hν i j L Kt hKt hL hmeas htail
  have hKtne : Kt ≠ 0 := ne_of_gt hKt
  have hEpos : (0:ℝ) < Real.exp (-L / Kt) := Real.exp_pos _
  have hE0 : (0:ℝ) ≤ Real.exp (-L / Kt) := le_of_lt hEpos
  have hpiece1 : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)) ≤
      ENNReal.ofReal (2 * (L + Kt) * Real.exp (-L / Kt)) := by
    set ψ : ℝ → ℝ := fun t => 2 * Real.exp (-(max L t) / Kt) with hψdef
    have hψnn : ∀ t : ℝ, 0 ≤ ψ t := by
      intro t
      exact mul_nonneg (by norm_num) (Real.exp_pos _).le
    have hψcont : Continuous ψ := by
      have h1 : Continuous fun t : ℝ => max L t := continuous_const.max continuous_id
      have h2 : Continuous fun t : ℝ => -(max L t) / Kt := h1.neg.div_const Kt
      exact continuous_const.mul (Real.continuous_exp.comp h2)
    have hψmeas : Measurable fun t : ℝ => ENNReal.ofReal (ψ t) := hψcont.measurable.ennreal_ofReal
    have hpt : ∀ t : ℝ, Set.indicator (Set.Ioi (0:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) t
        = ⨆ n : ℕ, Set.indicator (Set.Ioc (0:ℝ) (n:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) t := by
      intro t
      by_cases ht : (0:ℝ) < t
      · obtain ⟨n, hn⟩ := exists_nat_gt t
        rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht)]
        refine le_antisymm ?_ (iSup_le fun m => ?_)
        · have hmem : t ∈ Set.Ioc (0:ℝ) ((n + 1 : ℕ) : ℝ) := ⟨ht, by push_cast; linarith⟩
          calc ENNReal.ofReal (ψ t)
              = Set.indicator (Set.Ioc (0:ℝ) ((n + 1 : ℕ) : ℝ))
                  (fun t : ℝ => ENNReal.ofReal (ψ t)) t := by
                rw [Set.indicator_of_mem hmem]
            _ ≤ ⨆ m : ℕ, Set.indicator (Set.Ioc (0:ℝ) (m:ℝ))
                  (fun t : ℝ => ENNReal.ofReal (ψ t)) t :=
                le_iSup (fun m : ℕ => Set.indicator (Set.Ioc (0:ℝ) (m:ℝ))
                  (fun t : ℝ => ENNReal.ofReal (ψ t)) t) (n + 1)
        · by_cases hm : t ∈ Set.Ioc (0:ℝ) (m:ℝ)
          · rw [Set.indicator_of_mem hm]
          · rw [Set.indicator_of_notMem hm]; exact zero_le _
      · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0:ℝ) from ht)]
        refine le_antisymm (zero_le _) (iSup_le fun m => ?_)
        rw [Set.indicator_of_notMem (show t ∉ Set.Ioc (0:ℝ) (m:ℝ) from fun hh => ht hh.1)]
    have key : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (ψ t)
        = ⨆ n : ℕ, ∫⁻ t in Set.Ioc (0:ℝ) (n:ℝ), ENNReal.ofReal (ψ t) := by
      have hsup : (fun a : ℝ => ⨆ n : ℕ, Set.indicator (Set.Ioc (0:ℝ) (n:ℝ))
            (fun t : ℝ => ENNReal.ofReal (ψ t)) a)
          = Set.indicator (Set.Ioi (0:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) := by
        funext t
        exact (hpt t).symm
      rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi
        (f := fun t : ℝ => ENNReal.ofReal (ψ t))]
      rw [← hsup]
      rw [MeasureTheory.lintegral_iSup (f := fun n : ℕ =>
        Set.indicator (Set.Ioc (0:ℝ) (n:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)))]
      · refine iSup_congr fun n => ?_
        exact MeasureTheory.lintegral_indicator measurableSet_Ioc (fun t : ℝ => ENNReal.ofReal (ψ t))
      · intro n
        have hone : Measurable
            (fun t : ℝ => if t ∈ Set.Ioc (0:ℝ) (n:ℝ) then ENNReal.ofReal (ψ t) else 0) :=
          Measurable.ite measurableSet_Ioc hψmeas measurable_const
        have heq : Set.indicator (Set.Ioc (0:ℝ) (n:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t))
            = fun t : ℝ => if t ∈ Set.Ioc (0:ℝ) (n:ℝ) then ENNReal.ofReal (ψ t) else 0 := by
          funext t
          by_cases h : t ∈ Set.Ioc (0:ℝ) (n:ℝ)
          · rw [Set.indicator_of_mem h, if_pos h]
          · rw [Set.indicator_of_notMem h, if_neg h]
        rw [heq]
        exact hone
      · intro a b hab t
        show Set.indicator (Set.Ioc (0:ℝ) (a:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) t
          ≤ Set.indicator (Set.Ioc (0:ℝ) (b:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) t
        by_cases h : t ∈ Set.Ioc (0:ℝ) (a:ℝ)
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem
            (show t ∈ Set.Ioc (0:ℝ) (b:ℝ) from ⟨h.1, le_trans h.2 (by exact_mod_cast hab)⟩)]
        · rw [Set.indicator_of_notMem h]; exact zero_le _
    have hstep : ∀ n : ℕ, ∫⁻ t in Set.Ioc (0:ℝ) (n:ℝ), ENNReal.ofReal (ψ t)
        = ENNReal.ofReal (∫ x in (0:ℝ)..(n:ℝ), ψ x) := by
      intro n
      have hIntble : Integrable ψ (volume.restrict (Set.Ioc (0:ℝ) (n:ℝ))) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp
          (hψcont.intervalIntegrable 0 (n:ℝ))
      rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict (Set.Ioc (0:ℝ) (n:ℝ))) hIntble
        (Filter.Eventually.of_forall hψnn)).symm
    have hcont2 : Continuous fun x : ℝ => 2 * Real.exp (-x / Kt) := by
      have h : Continuous fun x : ℝ => -x / Kt := continuous_id.neg.div_const Kt
      exact continuous_const.mul (Real.continuous_exp.comp h)
    have hreal : ∀ n : ℕ, ∫ x in (0:ℝ)..(n:ℝ), ψ x ≤ 2 * (L + Kt) * Real.exp (-L / Kt) := by
      intro n
      by_cases hn : (n:ℝ) ≤ L
      · have hmono : ∫ x in (0:ℝ)..(n:ℝ), ψ x
            ≤ ∫ x in (0:ℝ)..(n:ℝ), (fun _ => 2 * Real.exp (-L / Kt)) x := by
          refine intervalIntegral.integral_mono_on (Nat.cast_nonneg n)
            (hψcont.intervalIntegrable 0 (n:ℝ)) (continuous_const.intervalIntegrable 0 (n:ℝ)) ?_
          intro x hx
          show ψ x ≤ 2 * Real.exp (-L / Kt)
          simp only [hψdef]
          rw [max_eq_left (le_trans hx.2 hn)]
        have hval : ∫ x in (0:ℝ)..(n:ℝ), (fun _ => 2 * Real.exp (-L / Kt)) x
            = (n:ℝ) * (2 * Real.exp (-L / Kt)) := by
          rw [intervalIntegral.integral_const]
          simp
        rw [hval] at hmono
        have hLE : (n:ℝ) ≤ L + Kt := by linarith
        exact le_trans hmono (by nlinarith [mul_le_mul_of_nonneg_right hLE (le_of_lt hEpos)])
      · push_neg at hn
        have hsplit : ∫ x in (0:ℝ)..(n:ℝ), ψ x
            = (∫ x in (0:ℝ)..L, ψ x) + ∫ x in L..(n:ℝ), ψ x :=
          (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
            (hψcont.intervalIntegrable 0 L) (hψcont.intervalIntegrable L (n:ℝ))).symm
        have h1 : ∫ x in (0:ℝ)..L, ψ x ≤ 2 * L * Real.exp (-L / Kt) := by
          have hmono : ∫ x in (0:ℝ)..L, ψ x
              ≤ ∫ x in (0:ℝ)..L, (fun _ => 2 * Real.exp (-L / Kt)) x := by
            refine intervalIntegral.integral_mono_on (le_of_lt hL) (hψcont.intervalIntegrable 0 L)
              (continuous_const.intervalIntegrable 0 L) ?_
            intro x hx
            show ψ x ≤ 2 * Real.exp (-L / Kt)
            simp only [hψdef]
            rw [max_eq_left hx.2]
          have hval : ∫ x in (0:ℝ)..L, (fun _ => 2 * Real.exp (-L / Kt)) x
              = L * (2 * Real.exp (-L / Kt)) := by
            rw [intervalIntegral.integral_const]
            simp
          rw [hval] at hmono
          calc ∫ x in (0:ℝ)..L, ψ x ≤ L * (2 * Real.exp (-L / Kt)) := hmono
            _ = 2 * L * Real.exp (-L / Kt) := by ring
        have h2 : ∫ x in L..(n:ℝ), ψ x ≤ 2 * Kt * Real.exp (-L / Kt) := by
          have hmono : ∫ x in L..(n:ℝ), ψ x
              ≤ ∫ x in L..(n:ℝ), (fun x => 2 * Real.exp (-x / Kt)) x := by
            refine intervalIntegral.integral_mono_on hn.le (hψcont.intervalIntegrable L (n:ℝ))
              (hcont2.intervalIntegrable L (n:ℝ)) ?_
            intro x hx
            show ψ x ≤ 2 * Real.exp (-x / Kt)
            simp only [hψdef]
            rw [max_eq_right hx.1]
          have hFTC : ∫ x in L..(n:ℝ), (fun x => 2 * Real.exp (-x / Kt)) x
              = 2 * Kt * Real.exp (-L / Kt) - 2 * Kt * Real.exp (-(n:ℝ) / Kt) := by
            have hderiv : ∀ x ∈ Set.uIcc L (n:ℝ),
                HasDerivAt (fun x : ℝ => -(2 * Kt * Real.exp (-x / Kt)))
                  (2 * Real.exp (-x / Kt)) x := by
              intro x _
              have hbase : HasDerivAt (fun x : ℝ => -x / Kt) (-1 / Kt) x :=
                (hasDerivAt_id x).neg.div_const Kt
              have hexp : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp (-x / Kt)) (-x / Kt) :=
                Real.hasDerivAt_exp _
              have hexp2 : HasDerivAt (fun x : ℝ => Real.exp (-x / Kt))
                  (Real.exp (-x / Kt) * (-1 / Kt)) x := by
                simpa using hexp.comp x hbase
              have hmul : HasDerivAt (fun x : ℝ => 2 * Kt * Real.exp (-x / Kt))
                  ((2 * Kt) * (Real.exp (-x / Kt) * (-1 / Kt))) x := hexp2.const_mul (2 * Kt)
              have hneg : HasDerivAt (fun x : ℝ => -(2 * Kt * Real.exp (-x / Kt)))
                  (-((2 * Kt) * (Real.exp (-x / Kt) * (-1 / Kt)))) x := hmul.neg
              have heq : -((2 * Kt) * (Real.exp (-x / Kt) * (-1 / Kt)))
                  = 2 * Real.exp (-x / Kt) := by
                field_simp
              rw [heq] at hneg
              exact hneg
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
              (hcont2.intervalIntegrable L (n:ℝ))]
            ring
          rw [hFTC] at hmono
          have hpos : (0:ℝ) ≤ 2 * Kt * Real.exp (-(n:ℝ) / Kt) := by positivity
          linarith
        rw [hsplit]
        have hsum : (∫ x in (0:ℝ)..L, ψ x) + ∫ x in L..(n:ℝ), ψ x
            ≤ 2 * L * Real.exp (-L / Kt) + 2 * Kt * Real.exp (-L / Kt) := add_le_add h1 h2
        refine le_trans hsum ?_
        have hcalc : 2 * L * Real.exp (-L / Kt) + 2 * Kt * Real.exp (-L / Kt)
            = 2 * (L + Kt) * Real.exp (-L / Kt) := by ring
        rw [hcalc]
    rw [key]
    refine iSup_le fun n => ?_
    rw [hstep n]
    exact ENNReal.ofReal_le_ofReal (hreal n)
  constructor
  · have hset1 : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | |x i j| ≤ L} :=
      measurableSet_le hmeas.abs measurable_const
    have hg1meas : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1)) := by
      have h : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => if |x i j| ≤ L then (0:ℝ) else |x i j|) :=
        Measurable.ite hset1 measurable_const hmeas.abs
      simpa using h
    have hg1nn : ∀ x : Matrix (Fin m) (Fin n) ℝ, 0 ≤ |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1) := by
      intro x
      by_cases h : |x i j| ≤ L
      · rw [if_pos h, mul_zero]
      · rw [if_neg h, mul_one]; exact abs_nonneg _
    have hlc := MeasureTheory.lintegral_eq_lintegral_meas_lt (μ := ν)
      (f := fun x : Matrix (Fin m) (Fin n) ℝ => |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1))
      (Filter.Eventually.of_forall hg1nn) hg1meas.aemeasurable
    have hbound : ∀ t : ℝ, 0 < t → ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1)}
        ≤ ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)) := by
      intro t ht
      have hmaxpos : 0 < max L t := lt_of_lt_of_le hL (le_max_left L t)
      refine le_trans (measure_mono ?_) (htail (max L t) hmaxpos)
      intro x hx
      have hg1pos : 0 < |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1) := lt_trans ht hx
      have hgt : L < |x i j| := by
        by_contra hcon
        push_neg at hcon
        rw [if_pos hcon, mul_zero] at hg1pos
        exact lt_irrefl 0 hg1pos
      have hval : |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1) = |x i j| := by
        rw [if_neg (not_le.mpr hgt), mul_one]
      have hx' : t < |x i j| := by
        have h2 : t < |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1) := hx
        rwa [hval] at h2
      rcases le_total L t with h | h
      · rw [max_eq_right h]; exact hx'
      · rw [max_eq_left h]; exact hgt
    have hle : ∫⁻ t in Set.Ioi (0:ℝ), ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1)}
        ≤ ENNReal.ofReal (2 * (L + Kt) * Real.exp (-L / Kt)) := by
      refine le_trans ?_ hpiece1
      rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi
        (f := fun t => ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1)})]
      rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi
        (f := fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))]
      refine lintegral_mono (fun t => ?_)
      by_cases ht : (0:ℝ) < t
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht),
          Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht)]
        exact hbound t ht
      · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0:ℝ) from ht),
          Set.indicator_of_notMem (show t ∉ Set.Ioi (0:ℝ) from ht)]
    have hlin : ∫⁻ x, ENNReal.ofReal (|x i j| * (if |x i j| ≤ L then (0:ℝ) else 1)) ∂ν
        ≤ ENNReal.ofReal (2 * (L + Kt) * Real.exp (-L / Kt)) := by
      rw [hlc]; exact hle
    have hne : ∫⁻ x, ENNReal.ofReal (|x i j| * (if |x i j| ≤ L then (0:ℝ) else 1)) ∂ν < ⊤ :=
      lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
    have hfin : MeasureTheory.HasFiniteIntegral
        (fun x : Matrix (Fin m) (Fin n) ℝ => |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1)) ν :=
      (MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg1nn)).mpr hne
    have hint : Integrable
        (fun x : Matrix (Fin m) (Fin n) ℝ => |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1)) ν :=
      ⟨hg1meas.aestronglyMeasurable, hfin⟩
    have hbridge : ENNReal.ofReal (∫ x, |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1) ∂ν)
        = ∫⁻ x, ENNReal.ofReal (|x i j| * (if |x i j| ≤ L then (0:ℝ) else 1)) ∂ν :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hg1nn)
    have hC0 : (0:ℝ) ≤ 2 * (L + Kt) * Real.exp (-L / Kt) := by positivity
    calc ∫ x, |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1) ∂ν
        = (ENNReal.ofReal (∫ x, |x i j| * (if |x i j| ≤ L then (0:ℝ) else 1) ∂ν)).toReal := by
          rw [ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg hg1nn)]
      _ ≤ (ENNReal.ofReal (2 * (L + Kt) * Real.exp (-L / Kt))).toReal := by
          refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
          rw [hbridge]; exact hlin
      _ = 2 * (L + Kt) * Real.exp (-L / Kt) := ENNReal.toReal_ofReal hC0
  · have hset2 : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | |x i j| ≤ L} :=
      measurableSet_le hmeas.abs measurable_const
    have hsqmeas : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2) := by
      have h2' : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j * x i j) := hmeas.mul hmeas
      simpa only [sq] using h2'
    have hg2meas : Measurable
        (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1)) := by
      have h : Measurable
          (fun x : Matrix (Fin m) (Fin n) ℝ => if |x i j| ≤ L then (0:ℝ) else (x i j) ^ 2) :=
        Measurable.ite hset2 measurable_const hsqmeas
      simpa using h
    have hg2nn : ∀ x : Matrix (Fin m) (Fin n) ℝ,
        0 ≤ (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1) := by
      intro x
      by_cases h : |x i j| ≤ L
      · rw [if_pos h, mul_zero]
      · rw [if_neg h, mul_one]; exact sq_nonneg _
    have hsq : ∀ y : ℝ, y ^ 2 = |y| ^ 2 := by
      intro y
      rw [sq, sq, abs_mul_abs_self]
    have hlc2 := MeasureTheory.lintegral_eq_lintegral_meas_lt (μ := ν)
      (f := fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1))
      (Filter.Eventually.of_forall hg2nn) hg2meas.aemeasurable
    have hpiece2 : ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (2 * Real.exp (-(Real.sqrt (max (L^2) t)) / Kt)) ≤
        ENNReal.ofReal ((2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt)) := by
      set ψ : ℝ → ℝ := fun t => 2 * Real.exp (-(Real.sqrt (max (L^2) t)) / Kt) with hψdef
      have hψnn : ∀ t : ℝ, 0 ≤ ψ t := fun t => mul_nonneg (by norm_num) (Real.exp_pos _).le
      have hψcont : Continuous ψ := by
        have h1 : Continuous fun t : ℝ => max (L^2) t := continuous_const.max continuous_id
        have h2 : Continuous fun t : ℝ => Real.sqrt (max (L^2) t) := Real.continuous_sqrt.comp h1
        have h3 : Continuous fun t : ℝ => -(Real.sqrt (max (L^2) t)) / Kt := h2.neg.div_const Kt
        exact continuous_const.mul (Real.continuous_exp.comp h3)
      have hψmeas : Measurable fun t : ℝ => ENNReal.ofReal (ψ t) := hψcont.measurable.ennreal_ofReal
      have hpt : ∀ t : ℝ, Set.indicator (Set.Ioi (0:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) t
          = ⨆ n : ℕ, Set.indicator (Set.Ioc (0:ℝ) (n:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) t := by
        intro t
        by_cases ht : (0:ℝ) < t
        · obtain ⟨n, hn⟩ := exists_nat_gt t
          rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht)]
          refine le_antisymm ?_ (iSup_le fun m => ?_)
          · have hmem : t ∈ Set.Ioc (0:ℝ) ((n + 1 : ℕ) : ℝ) := ⟨ht, by push_cast; linarith⟩
            calc ENNReal.ofReal (ψ t)
                = Set.indicator (Set.Ioc (0:ℝ) ((n + 1 : ℕ) : ℝ))
                    (fun t : ℝ => ENNReal.ofReal (ψ t)) t := by
                  rw [Set.indicator_of_mem hmem]
              _ ≤ ⨆ m : ℕ, Set.indicator (Set.Ioc (0:ℝ) (m:ℝ))
                    (fun t : ℝ => ENNReal.ofReal (ψ t)) t :=
                  le_iSup (fun m : ℕ => Set.indicator (Set.Ioc (0:ℝ) (m:ℝ))
                    (fun t : ℝ => ENNReal.ofReal (ψ t)) t) (n + 1)
          · by_cases hm : t ∈ Set.Ioc (0:ℝ) (m:ℝ)
            · rw [Set.indicator_of_mem hm]
            · rw [Set.indicator_of_notMem hm]; exact zero_le _
        · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0:ℝ) from ht)]
          refine le_antisymm (zero_le _) (iSup_le fun m => ?_)
          rw [Set.indicator_of_notMem (show t ∉ Set.Ioc (0:ℝ) (m:ℝ) from fun hh => ht hh.1)]
      have key : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (ψ t)
          = ⨆ n : ℕ, ∫⁻ t in Set.Ioc (0:ℝ) (n:ℝ), ENNReal.ofReal (ψ t) := by
        have hsup : (fun a : ℝ => ⨆ n : ℕ, Set.indicator (Set.Ioc (0:ℝ) (n:ℝ))
              (fun t : ℝ => ENNReal.ofReal (ψ t)) a)
            = Set.indicator (Set.Ioi (0:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) := by
          funext t
          exact (hpt t).symm
        rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi
          (f := fun t : ℝ => ENNReal.ofReal (ψ t))]
        rw [← hsup]
        rw [MeasureTheory.lintegral_iSup (f := fun n : ℕ =>
          Set.indicator (Set.Ioc (0:ℝ) (n:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)))]
        · refine iSup_congr fun n => ?_
          exact MeasureTheory.lintegral_indicator measurableSet_Ioc
            (fun t : ℝ => ENNReal.ofReal (ψ t))
        · intro n
          have hone : Measurable
              (fun t : ℝ => if t ∈ Set.Ioc (0:ℝ) (n:ℝ) then ENNReal.ofReal (ψ t) else 0) :=
            Measurable.ite measurableSet_Ioc hψmeas measurable_const
          have heq : Set.indicator (Set.Ioc (0:ℝ) (n:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t))
              = fun t : ℝ => if t ∈ Set.Ioc (0:ℝ) (n:ℝ) then ENNReal.ofReal (ψ t) else 0 := by
            funext t
            by_cases h : t ∈ Set.Ioc (0:ℝ) (n:ℝ)
            · rw [Set.indicator_of_mem h, if_pos h]
            · rw [Set.indicator_of_notMem h, if_neg h]
          rw [heq]
          exact hone
        · intro a b hab t
          show Set.indicator (Set.Ioc (0:ℝ) (a:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) t
            ≤ Set.indicator (Set.Ioc (0:ℝ) (b:ℝ)) (fun t : ℝ => ENNReal.ofReal (ψ t)) t
          by_cases h : t ∈ Set.Ioc (0:ℝ) (a:ℝ)
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem
              (show t ∈ Set.Ioc (0:ℝ) (b:ℝ) from ⟨h.1, le_trans h.2 (by exact_mod_cast hab)⟩)]
          · rw [Set.indicator_of_notMem h]; exact zero_le _
      have hstep : ∀ n : ℕ, ∫⁻ t in Set.Ioc (0:ℝ) (n:ℝ), ENNReal.ofReal (ψ t)
          = ENNReal.ofReal (∫ x in (0:ℝ)..(n:ℝ), ψ x) := by
        intro n
        have hIntble : Integrable ψ (volume.restrict (Set.Ioc (0:ℝ) (n:ℝ))) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp
            (hψcont.intervalIntegrable 0 (n:ℝ))
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (μ := volume.restrict (Set.Ioc (0:ℝ) (n:ℝ))) hIntble
          (Filter.Eventually.of_forall hψnn)).symm
      have hcont3 : Continuous fun x : ℝ => 2 * Real.exp (-(Real.sqrt x) / Kt) := by
        have h : Continuous fun x : ℝ => -(Real.sqrt x) / Kt :=
          Real.continuous_sqrt.neg.div_const Kt
        exact continuous_const.mul (Real.continuous_exp.comp h)
      have hreal : ∀ n : ℕ,
          ∫ x in (0:ℝ)..(n:ℝ), ψ x ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := by
        intro n
        by_cases hn : (n:ℝ) ≤ L^2
        · have hmono : ∫ x in (0:ℝ)..(n:ℝ), ψ x
              ≤ ∫ x in (0:ℝ)..(n:ℝ), (fun _ => 2 * Real.exp (-L / Kt)) x := by
            refine intervalIntegral.integral_mono_on (Nat.cast_nonneg n)
              (hψcont.intervalIntegrable 0 (n:ℝ)) (continuous_const.intervalIntegrable 0 (n:ℝ)) ?_
            intro x hx
            show ψ x ≤ 2 * Real.exp (-L / Kt)
            simp only [hψdef]
            rw [max_eq_left (le_trans hx.2 hn), Real.sqrt_sq (le_of_lt hL)]
          have hval : ∫ x in (0:ℝ)..(n:ℝ), (fun _ => 2 * Real.exp (-L / Kt)) x
              = (n:ℝ) * (2 * Real.exp (-L / Kt)) := by
            rw [intervalIntegral.integral_const]
            simp
          rw [hval] at hmono
          refine le_trans hmono ?_
          have hA : (n:ℝ) * (2 * Real.exp (-L / Kt))
              ≤ (L^2) * (2 * Real.exp (-L / Kt)) :=
            mul_le_mul_of_nonneg_right hn (by positivity)
          have hB : (L^2) * (2 * Real.exp (-L / Kt))
              ≤ (2 * L^2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := by
            have h4 : (0:ℝ) ≤ 4 * Kt * (L + Kt) * Real.exp (-L / Kt) := by positivity
            nlinarith [h4]
          linarith
        · push_neg at hn
          have hsplit : ∫ x in (0:ℝ)..(n:ℝ), ψ x
              = (∫ x in (0:ℝ)..(L^2), ψ x) + ∫ x in (L^2)..(n:ℝ), ψ x :=
            (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
              (hψcont.intervalIntegrable 0 (L^2))
              (hψcont.intervalIntegrable (L^2) (n:ℝ))).symm
          have h1 : ∫ x in (0:ℝ)..(L^2), ψ x ≤ 2 * L^2 * Real.exp (-L / Kt) := by
            have hmono : ∫ x in (0:ℝ)..(L^2), ψ x
                ≤ ∫ x in (0:ℝ)..(L^2), (fun _ => 2 * Real.exp (-L / Kt)) x := by
              refine intervalIntegral.integral_mono_on (le_of_lt (pow_pos hL 2))
                (hψcont.intervalIntegrable 0 (L^2))
                (continuous_const.intervalIntegrable 0 (L^2)) ?_
              intro x hx
              show ψ x ≤ 2 * Real.exp (-L / Kt)
              simp only [hψdef]
              rw [max_eq_left hx.2, Real.sqrt_sq (le_of_lt hL)]
            have hval : ∫ x in (0:ℝ)..(L^2), (fun _ => 2 * Real.exp (-L / Kt)) x
                = (L^2) * (2 * Real.exp (-L / Kt)) := by
              rw [intervalIntegral.integral_const]
              simp
            rw [hval] at hmono
            calc ∫ x in (0:ℝ)..(L^2), ψ x ≤ (L^2) * (2 * Real.exp (-L / Kt)) := hmono
              _ = 2 * L^2 * Real.exp (-L / Kt) := by ring
          have h2 : ∫ x in (L^2)..(n:ℝ), ψ x ≤ 4 * Kt * (L + Kt) * Real.exp (-L / Kt) := by
            have hmono : ∫ x in (L^2)..(n:ℝ), ψ x
                ≤ ∫ x in (L^2)..(n:ℝ), (fun x => 2 * Real.exp (-(Real.sqrt x) / Kt)) x := by
              refine intervalIntegral.integral_mono_on hn.le
                (hψcont.intervalIntegrable (L^2) (n:ℝ))
                (hcont3.intervalIntegrable (L^2) (n:ℝ)) ?_
              intro x hx
              show ψ x ≤ 2 * Real.exp (-(Real.sqrt x) / Kt)
              simp only [hψdef]
              rw [max_eq_right hx.1]
            have hFTC : ∫ x in (L^2)..(n:ℝ), (fun x => 2 * Real.exp (-(Real.sqrt x) / Kt)) x
                = 4 * Kt * (L + Kt) * Real.exp (-L / Kt)
                  - 4 * Kt * (Real.sqrt (n:ℝ) + Kt) * Real.exp (-(Real.sqrt (n:ℝ)) / Kt) := by
              have hderiv : ∀ x ∈ Set.uIcc (L^2) (n:ℝ),
                  HasDerivAt
                    (fun x : ℝ => -(4 * Kt * ((Real.sqrt x + Kt) * Real.exp (-(Real.sqrt x) / Kt))))
                    (2 * Real.exp (-(Real.sqrt x) / Kt)) x := by
                intro x hx
                have hxge : L^2 ≤ x := by
                  have hmin : min (L^2) (n:ℝ) = L^2 := min_eq_left hn.le
                  calc L^2 = min (L^2) (n:ℝ) := hmin.symm
                    _ ≤ x := hx.1
                have hxpos : (0:ℝ) < x := lt_of_lt_of_le (pow_pos hL 2) hxge
                have hsne : Real.sqrt x ≠ 0 := by
                  intro h0
                  have hx0 : x = 0 := by
                    rw [← Real.sq_sqrt (le_of_lt hxpos), h0]
                    ring
                  linarith
                have hbase : HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * Real.sqrt x)) x :=
                  Real.hasDerivAt_sqrt hxpos.ne'
                have hsK : HasDerivAt (fun x : ℝ => Real.sqrt x + Kt)
                    (1 / (2 * Real.sqrt x)) x := hbase.add_const Kt
                have hsneg : HasDerivAt (fun x : ℝ => -(Real.sqrt x) / Kt)
                    ((-(1 / (2 * Real.sqrt x))) / Kt) x := hbase.neg.div_const Kt
                have hexp : HasDerivAt (fun y : ℝ => Real.exp y)
                    (Real.exp (-(Real.sqrt x) / Kt)) (-(Real.sqrt x) / Kt) := Real.hasDerivAt_exp _
                have hexp2 : HasDerivAt (fun x : ℝ => Real.exp (-(Real.sqrt x) / Kt))
                    (Real.exp (-(Real.sqrt x) / Kt) * ((-(1 / (2 * Real.sqrt x))) / Kt)) x := by
                  simpa using hexp.comp x hsneg
                have hmul : HasDerivAt
                    (fun x : ℝ => (Real.sqrt x + Kt) * Real.exp (-(Real.sqrt x) / Kt))
                    ((1 / (2 * Real.sqrt x)) * Real.exp (-(Real.sqrt x) / Kt)
                      + (Real.sqrt x + Kt) * (Real.exp (-(Real.sqrt x) / Kt)
                        * ((-(1 / (2 * Real.sqrt x))) / Kt))) x := hsK.mul hexp2
                have hcm := hmul.const_mul (4 * Kt)
                have hneg := hcm.neg
                have heq : -((4 * Kt) * ((1 / (2 * Real.sqrt x)) * Real.exp (-(Real.sqrt x) / Kt)
                      + (Real.sqrt x + Kt) * (Real.exp (-(Real.sqrt x) / Kt)
                        * ((-(1 / (2 * Real.sqrt x))) / Kt))))
                    = 2 * Real.exp (-(Real.sqrt x) / Kt) := by
                  field_simp
                  ring
                rw [heq] at hneg
                exact hneg
              rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
                (hcont3.intervalIntegrable (L^2) (n:ℝ))]
              rw [Real.sqrt_sq (le_of_lt hL)]
              ring
            rw [hFTC] at hmono
            have hpos : (0:ℝ) ≤ 4 * Kt * (Real.sqrt (n:ℝ) + Kt)
                * Real.exp (-(Real.sqrt (n:ℝ)) / Kt) := by positivity
            linarith
          rw [hsplit]
          have hsum : (∫ x in (0:ℝ)..(L^2), ψ x) + ∫ x in (L^2)..(n:ℝ), ψ x
              ≤ 2 * L^2 * Real.exp (-L / Kt) + 4 * Kt * (L + Kt) * Real.exp (-L / Kt) :=
            add_le_add h1 h2
          refine le_trans hsum ?_
          have hcalc : 2 * L^2 * Real.exp (-L / Kt) + 4 * Kt * (L + Kt) * Real.exp (-L / Kt)
              = (2 * L^2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := by ring
          rw [hcalc]
      rw [key]
      refine iSup_le fun n => ?_
      rw [hstep n]
      exact ENNReal.ofReal_le_ofReal (hreal n)
    have hbound2 : ∀ t : ℝ, 0 < t →
        ν {x : Matrix (Fin m) (Fin n) ℝ | t < (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1)}
          ≤ ENNReal.ofReal (2 * Real.exp (-(Real.sqrt (max (L^2) t)) / Kt)) := by
      intro t ht
      have hmaxpos : 0 < max (L^2) t := lt_of_lt_of_le (pow_pos hL 2) (le_max_left _ _)
      refine le_trans (measure_mono ?_) (htail (Real.sqrt (max (L^2) t)) (Real.sqrt_pos.mpr hmaxpos))
      intro x hx
      have hg2pos : 0 < (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1) := lt_trans ht hx
      have hgt : L < |x i j| := by
        by_contra hcon
        push_neg at hcon
        rw [if_pos hcon, mul_zero] at hg2pos
        exact lt_irrefl 0 hg2pos
      have hval : (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1) = (x i j) ^ 2 := by
        rw [if_neg (not_le.mpr hgt), mul_one]
      have hx2 : t < |x i j| ^ 2 := by
        have h2 : t < (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1) := hx
        rw [hval, hsq] at h2
        exact h2
      have hsqrt : Real.sqrt t < |x i j| := by
        by_contra hcon
        push_neg at hcon
        have h3 : |x i j| * |x i j| ≤ Real.sqrt t * Real.sqrt t :=
          mul_le_mul hcon hcon (abs_nonneg _) (Real.sqrt_nonneg t)
        have h4 : Real.sqrt t * Real.sqrt t = t := by
          have h6 := Real.sq_sqrt (le_of_lt ht)
          rwa [sq] at h6
        have h7 : |x i j| * |x i j| = |x i j| ^ 2 := by rw [sq]
        linarith
      rcases le_total (L^2) t with h | h
      · rw [max_eq_right h]; exact hsqrt
      · rw [max_eq_left h, Real.sqrt_sq (le_of_lt hL)]; exact hgt
    have hle2 : ∫⁻ t in Set.Ioi (0:ℝ),
        ν {x : Matrix (Fin m) (Fin n) ℝ | t < (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1)}
        ≤ ENNReal.ofReal ((2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt)) := by
      refine le_trans ?_ hpiece2
      rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi
        (f := fun t => ν {x : Matrix (Fin m) (Fin n) ℝ |
          t < (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1)})]
      rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi
        (f := fun t => ENNReal.ofReal (2 * Real.exp (-(Real.sqrt (max (L^2) t)) / Kt)))]
      refine lintegral_mono (fun t => ?_)
      by_cases ht : (0:ℝ) < t
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht),
          Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht)]
        exact hbound2 t ht
      · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0:ℝ) from ht),
          Set.indicator_of_notMem (show t ∉ Set.Ioi (0:ℝ) from ht)]
    have hlin2 : ∫⁻ x, ENNReal.ofReal ((x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1)) ∂ν
        ≤ ENNReal.ofReal ((2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt)) := by
      rw [hlc2]; exact hle2
    have hne2 : ∫⁻ x, ENNReal.ofReal ((x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1)) ∂ν < ⊤ :=
      lt_of_le_of_lt hlin2 ENNReal.ofReal_lt_top
    have hfin2 : MeasureTheory.HasFiniteIntegral
        (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1)) ν :=
      (MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg2nn)).mpr hne2
    have hint2 : Integrable
        (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1)) ν :=
      ⟨hg2meas.aestronglyMeasurable, hfin2⟩
    have hbridge2 : ENNReal.ofReal
        (∫ x, (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1) ∂ν)
        = ∫⁻ x, ENNReal.ofReal ((x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1)) ∂ν :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall hg2nn)
    have hC2 : (0:ℝ) ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := by positivity
    calc ∫ x, (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1) ∂ν
        = (ENNReal.ofReal
            (∫ x, (x i j) ^ 2 * (if |x i j| ≤ L then (0:ℝ) else 1) ∂ν)).toReal := by
          rw [ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg hg2nn)]
      _ ≤ (ENNReal.ofReal ((2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt))).toReal := by
          refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
          rw [hbridge2]; exact hlin2
      _ = (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := ENNReal.toReal_ofReal hC2
  /- @proof-region region.target-node.session.497d953a2ab7b549 end -/

end Statlib.Imported

