import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_1d297aff76277b66ad8f
import ProverJobs.ResidualE2ESupport20261106.M_2ca6b2fa3059121c3609
import ProverJobs.ResidualE2ESupport20261106.M_6593d2a70db14ade2913

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
theorem statopia_math_node_3352644490_9c3ad106 : ∀ (Kt D0 alpha0 CD : ℝ)
    (hKt : 0 < Kt) (hD0 : 0 < D0) (halpha0 : 0 < alpha0)
    (hCD : Kt * (D0 + 12) ≤ CD)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (L : ℝ)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ))
      + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
    (ν : MeasureTheory.Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (h_var : ∀ (i : Fin m) (j : Fin n), ∫ x, (x i j) ^ 2 ∂ν = 1)
    (h_mean : ∀ (i : Fin m) (j : Fin n), ∫ x, x i j ∂ν = 0)
    (h_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
      ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|}
        ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (b c : Fin m → Fin n → ℝ)
    (hb : ∀ (i : Fin m) (j : Fin n),
      b i j = ∫ x, x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) ∂ν)
    (hc : ∀ (i : Fin m) (j : Fin n),
      c i j = Real.sqrt (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν)),
    ∀ (i : Fin m) (j : Fin n),
      (|b i j| ≤ 2 * (L + Kt) * Real.exp (-L / Kt))
      ∧ ((1 / 2 : ℝ) ≤ c i j)
      ∧ (c i j ≤ 1)
      ∧ (1 - (c i j) ^ 2 ≤ 8 * (L + Kt) ^ 2 * Real.exp (-L / Kt)) := by
  /- @proof-region region.target-node.session.b2bd232c1fbdf0e3 begin -/
  intro Kt D0 alpha0 CD hKt hD0 halpha0 hCD m n hm hn L hL ν hν h_var h_mean h_tail b c hb hc i j
  haveI : IsProbabilityMeasure ν := hν
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmn : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by nlinarith
  have hCDpos : 0 < CD := by nlinarith [hKt, hD0, hCD]
  have hlog : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := Real.log_nonneg hmn
  have hp1 : (1 : ℝ) ≤ (Kt + 1) ^ 4 := by
    have h : (1 : ℝ) ^ 4 ≤ (Kt + 1) ^ 4 := by
      gcongr
      linarith
    simpa using h
  have hp2 : (1 : ℝ) ≤ (D0 + 1) ^ 4 := by
    have h : (1 : ℝ) ^ 4 ≤ (D0 + 1) ^ 4 := by
      gcongr
      linarith
    simpa using h
  have hp3 : (1 : ℝ) ≤ (alpha0 + 1) ^ 4 := by
    have h : (1 : ℝ) ^ 4 ≤ (alpha0 + 1) ^ 4 := by
      gcongr
      linarith
    simpa using h
  have hpA : (0 : ℝ) ≤ (Kt + 1) ^ 4 := by positivity
  have hprod1 : (1 : ℝ) ≤ (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
    have h : (1 : ℝ) * 1 * 1 ≤ (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
      gcongr <;> first | exact hp1 | exact hp2 | exact hp3 | norm_num | positivity
    simpa using h
  have hT1' : (1 : ℝ) ≤ (10 : ℝ) ^ 6 * ((Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) := by
    have h := mul_le_mul (show (1 : ℝ) ≤ (10 : ℝ) ^ 6 by norm_num) hprod1
      (show (0 : ℝ) ≤ 1 by norm_num) (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 6)
    simpa using h
  have hT1 : (1 : ℝ) ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
    simpa [mul_assoc] using hT1'
  have hLge : (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 ≤ L := by
    rw [hL]
    have hc0 : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_nonneg hCDpos.le hlog
    linarith
  have hL1 : (1 : ℝ) ≤ L := le_trans hT1 hLge
  have hLpos : 0 < L := by linarith
  have hK4 : Kt ≤ (Kt + 1) ^ 4 := by
    have hring : (Kt + 1) ^ 4 = Kt ^ 4 + 4 * Kt ^ 3 + 6 * Kt ^ 2 + 4 * Kt + 1 := by ring
    have hnn : (0 : ℝ) ≤ Kt ^ 4 + 4 * Kt ^ 3 + 6 * Kt ^ 2 + 3 * Kt + 1 := by positivity
    linarith
  have hstep1 : (Kt + 1) ^ 4 ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 := by
    have h := mul_le_mul (show (1 : ℝ) ≤ (10 : ℝ) ^ 6 by norm_num)
      (le_refl ((Kt + 1) ^ 4)) hpA (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 6)
    simpa using h
  have hstep2 : (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 := by
    have h := mul_le_mul (le_refl ((10 : ℝ) ^ 6 * (Kt + 1) ^ 4)) hp2
      (show (0 : ℝ) ≤ 1 by norm_num) (by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4)
    simpa using h
  have hstep3 : (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4
      ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
    have h := mul_le_mul (le_refl ((10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4)) hp3
      (show (0 : ℝ) ≤ 1 by norm_num)
      (by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4)
    simpa using h
  have hKtT : Kt ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 :=
    le_trans hK4 (le_trans hstep1 (le_trans hstep2 hstep3))
  have hKL : Kt ≤ L := le_trans hKtT hLge
  have hLK : L + Kt ≤ 2 * L := by linarith
  have h10a : 10 * (Kt + 1) ^ 4 ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 := by
    have h := mul_le_mul (show (10 : ℝ) ≤ (10 : ℝ) ^ 6 by norm_num)
      (le_refl ((Kt + 1) ^ 4)) hpA (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 6)
    exact h
  have ha10 : 10 ≤ L / Kt := by
    rw [le_div_iff₀ hKt]
    have h1 : 10 * Kt ≤ 10 * (Kt + 1) ^ 4 := by linarith
    linarith [h1, h10a, hstep2, hstep3, hLge]
  have hmY : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j) := by fun_prop
  have hmYabs : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => |x i j|) := hmY.abs
  have hvar' : ∫ x, (x i j) ^ 2 ∂ν = 1 := h_var i j
  have hIntY2 : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2) ν := by
    by_contra hcon
    rw [MeasureTheory.integral_undef hcon] at hvar'
    norm_num at hvar'
  have hpt : ∀ y : ℝ, |y| ≤ y ^ 2 + 1 := by
    intro y
    have hsq : (0 : ℝ) ≤ (|y| - 1 / 2) ^ 2 := sq_nonneg _
    have hexp : (|y| - 1 / 2) ^ 2 = |y| ^ 2 - |y| + 1 / 4 := by ring
    have h1 : |y| ≤ |y| ^ 2 + 1 := by linarith [hsq, hexp]
    rwa [sq_abs] at h1
  have hIntY : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j) ν := by
    have hg : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2 + 1) ν :=
      hIntY2.add (integrable_const (1 : ℝ))
    refine hg.mono hmY.aestronglyMeasurable ?_
    filter_upwards with x
    have h1 := hpt (x i j)
    have h2 : |x i j ^ 2 + 1| = x i j ^ 2 + 1 := abs_of_nonneg (by positivity)
    simpa [Real.norm_eq_abs, h2] using h1
  have hmeasT : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|} :=
    measurableSet_lt measurable_const hmYabs
  have hmeasTc : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | |x i j| ≤ L} :=
    measurableSet_le hmYabs measurable_const
  have habs : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => |x i j|) ν := hIntY.abs
  have hmφ : Measurable fun x : Matrix (Fin m) (Fin n) ℝ => x i j * (if |x i j| ≤ L then 1 else 0) := by
    have hind : Measurable fun x : Matrix (Fin m) (Fin n) ℝ => if |x i j| ≤ L then (1 : ℝ) else 0 :=
      Measurable.ite hmeasTc measurable_const measurable_const
    exact hmY.mul hind
  have hmη : Measurable fun x : Matrix (Fin m) (Fin n) ℝ => x i j * (if L < |x i j| then 1 else 0) := by
    have hind : Measurable fun x : Matrix (Fin m) (Fin n) ℝ => if L < |x i j| then (1 : ℝ) else 0 :=
      Measurable.ite hmeasT measurable_const measurable_const
    exact hmY.mul hind

  have hIntφ : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j * (if |x i j| ≤ L then 1 else 0)) ν := by
    refine habs.mono hmφ.aestronglyMeasurable ?_
    filter_upwards with x
    have h1 : |x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)| ≤ |x i j| := by
      by_cases hx : |x i j| ≤ L
      · simp [hx]
      · simp [hx]
    simpa [Real.norm_eq_abs] using h1
  have hIntη : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j * (if L < |x i j| then 1 else 0)) ν := by
    refine habs.mono hmη.aestronglyMeasurable ?_
    filter_upwards with x
    have h1 : |x i j * (if L < |x i j| then (1 : ℝ) else 0)| ≤ |x i j| := by
      by_cases hx : L < |x i j|
      · simp [hx]
      · simp [hx]
    simpa [Real.norm_eq_abs] using h1

  have hφη : ∀ x : Matrix (Fin m) (Fin n) ℝ,
      x i j * (if |x i j| ≤ L then 1 else 0) + x i j * (if L < |x i j| then 1 else 0) = x i j := by
    intro x
    by_cases hx : (|x i j| ≤ L)
    · have hx2 : ¬ L < |x i j| := by linarith
      simp [hx, hx2]
    · have hx2 : L < |x i j| := by linarith
      simp [hx, hx2]
  have hsplit : ∫ x, x i j ∂ν
      = ∫ x, x i j * (if |x i j| ≤ L then 1 else 0) ∂ν
        + ∫ x, x i j * (if L < |x i j| then 1 else 0) ∂ν := by
    have h := integral_add hIntφ hIntη
    simp only [hφη] at h
    exact h
  have hηint : ∫ x, x i j * (if L < |x i j| then 1 else 0) ∂ν = -b i j := by
    have h := hsplit
    rw [h_mean i j, ← hb i j] at h
    linarith
  have habsη : ∀ x : Matrix (Fin m) (Fin n) ℝ,
      |x i j * (if L < |x i j| then (1 : ℝ) else 0)| = |x i j| * (if L < |x i j| then 1 else 0) := by
    intro x
    rw [abs_mul]
    by_cases hx : (L < |x i j|)
    · simp [hx]
    · simp [hx]
  have hTail1 : ∫ x, |x i j| * (if L < |x i j| then 1 else 0) ∂ν
      ≤ 2 * (L + Kt) * Real.exp (-L / Kt) :=
    statopia_math_node_983993472_4468443a m n ν Kt L hKt (by linarith) i j
      (fun t ht => h_tail i j t ht) (h_var i j)
  have hb1 : |b i j| ≤ ∫ x, |x i j| * (if L < |x i j| then 1 else 0) ∂ν := by
    have h1 : b i j = -∫ x, x i j * (if L < |x i j| then 1 else 0) ∂ν := by
      rw [hηint]
      ring
    have h2 := norm_integral_le_integral_norm (μ := ν)
      (f := fun x : Matrix (Fin m) (Fin n) ℝ => x i j * (if L < |x i j| then 1 else 0))
    simp only [Real.norm_eq_abs] at h2
    rw [h1, abs_neg]
    refine le_trans h2 (le_of_eq ?_)
    simp only [habsη]
  have hbconcl : |b i j| ≤ 2 * (L + Kt) * Real.exp (-L / Kt) := le_trans hb1 hTail1
  have hζ_nonneg : (0 : ℝ) ≤ ∫ x, (x i j) ^ 2 * (if L < |x i j| then 1 else 0) ∂ν := by
    refine integral_nonneg ?_
    intro x
    by_cases hx : L < |x i j|
    · simpa [hx] using sq_nonneg (x i j)
    · simp [hx]
  have hTail2 : ∫ x, (x i j) ^ 2 * (if L < |x i j| then 1 else 0) ∂ν
      ≤ 4 * (L + Kt) ^ 2 * Real.exp (-L / Kt) :=
    statopia_math_node_1249221228_c96b816c m n ν Kt L hKt (by linarith) hKL i j
      (fun t ht => h_tail i j t ht) (h_var i j)
  have hnum : 4 * (L + Kt) ^ 2 * Real.exp (-L / Kt) + 4 * (L + Kt) ^ 2 * (Real.exp (-L / Kt)) ^ 2 ≤ 3 / 4 := by
    exact statopia_math_node_3407536053_46f66794 Kt L hKt hL1
      (le_trans hstep2 (le_trans hstep3 hLge))
  have hexp0 : (0 : ℝ) ≤ Real.exp (-L / Kt) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-L / Kt) ≤ 1 := by
    have hle : (0 : ℝ) ≤ L / Kt := by linarith [ha10]
    have harg : -L / Kt ≤ 0 := by
      rw [neg_div]
      linarith
    have h := Real.exp_le_exp.mpr harg
    simpa using h
  have hexpsq : Real.exp (-L / Kt) ^ 2 ≤ Real.exp (-L / Kt) := by
    have h1 : Real.exp (-L / Kt) * Real.exp (-L / Kt) ≤ Real.exp (-L / Kt) := by
      have h2 := mul_le_mul (le_refl (Real.exp (-L / Kt))) hexp1 hexp0 hexp0
      simpa using h2
    calc Real.exp (-L / Kt) ^ 2 = Real.exp (-L / Kt) * Real.exp (-L / Kt) := pow_two _
      _ ≤ Real.exp (-L / Kt) := h1
  have hc2 : (c i j) ^ 2
      = 1 - (∫ x, (x i j) ^ 2 * (if L < |x i j| then 1 else 0) ∂ν) - (b i j) ^ 2 := by
    have hIntφ2 : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ =>
        (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) ^ 2) ν := by
      convert hIntY2.indicator hmeasTc using 1
      funext x
      by_cases hx : |x i j| ≤ L <;> simp [Set.indicator, hx]
    have hIntζ : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ =>
        (x i j) ^ 2 * (if L < |x i j| then (1 : ℝ) else 0)) ν := by
      convert hIntY2.indicator hmeasT using 1
      funext x
      by_cases hx : L < |x i j| <;> simp [Set.indicator, hx]
    have hsplit2 : (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) ^ 2 ∂ν)
        + (∫ x, (x i j) ^ 2 * (if L < |x i j| then (1 : ℝ) else 0) ∂ν) = 1 := by
      rw [← integral_add hIntφ2 hIntζ]
      calc
        _ = ∫ x, (x i j) ^ 2 ∂ν := by
          apply integral_congr_ae
          filter_upwards with x
          by_cases hx : |x i j| ≤ L
          · simp [hx, not_lt.mpr hx]
          · simp [hx, lt_of_not_ge hx]
        _ = 1 := h_var i j
    have hexpand : (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν)
        = (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) ^ 2 ∂ν)
          - (b i j) ^ 2 := by
      have hfun : (fun x : Matrix (Fin m) (Fin n) ℝ =>
          (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2) =
          (fun x => ((x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) ^ 2
            - (2 * b i j) * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)))
            + (b i j) ^ 2) := by
        funext x
        ring
      have hadd := integral_add (hIntφ2.sub (hIntφ.const_mul (2 * b i j)))
        (integrable_const ((b i j) ^ 2) (μ := ν))
      have hsub := integral_sub hIntφ2 (hIntφ.const_mul (2 * b i j))
      simp only [Pi.sub_apply, integral_const, probReal_univ, one_smul] at hadd hsub
      rw [hfun, hadd, hsub, integral_const_mul, ← hb i j]
      ring
    rw [hc i j, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _)), hexpand]
    linarith
  have hc_nonneg : (0 : ℝ) ≤ c i j := by
    rw [hc i j]
    exact Real.sqrt_nonneg _
  have hc_le_one : c i j ≤ 1 := by
    have hI : (0 : ℝ) ≤ ∫ x, (x i j * (if |x i j| ≤ L then 1 else 0) - b i j) ^ 2 ∂ν := by
      refine integral_nonneg ?_
      intro x
      exact sq_nonneg _
    have hsq_le : (c i j) ^ 2 ≤ 1 := by
      rw [hc2]
      linarith [hζ_nonneg, sq_nonneg (b i j)]
    have hIsq : (∫ x, (x i j * (if |x i j| ≤ L then 1 else 0) - b i j) ^ 2 ∂ν) = (c i j) ^ 2 := by
      rw [hc i j, Real.sq_sqrt hI]
    calc c i j = Real.sqrt (∫ x, (x i j * (if |x i j| ≤ L then 1 else 0) - b i j) ^ 2 ∂ν) := hc i j
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by rw [hIsq]; exact hsq_le)
      _ = 1 := Real.sqrt_one
  have hb_sq : (b i j) ^ 2 ≤ 4 * (L + Kt) ^ 2 * (Real.exp (-L / Kt)) ^ 2 := by
    have hK0 : (0 : ℝ) ≤ 2 * (L + Kt) * Real.exp (-L / Kt) := by positivity
    have h1 : |b i j| * |b i j|
        ≤ (2 * (L + Kt) * Real.exp (-L / Kt)) * (2 * (L + Kt) * Real.exp (-L / Kt)) :=
      mul_le_mul hbconcl hbconcl (abs_nonneg _) hK0
    have h2 : |b i j| * |b i j| = (b i j) ^ 2 := by
      rw [← pow_two, sq_abs]
    have h3 : (2 * (L + Kt) * Real.exp (-L / Kt)) * (2 * (L + Kt) * Real.exp (-L / Kt))
        = 4 * (L + Kt) ^ 2 * (Real.exp (-L / Kt)) ^ 2 := by
      ring
    rw [h2, h3] at h1
    exact h1
  have hfour : 1 - (c i j) ^ 2 ≤ 8 * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
    have h1 : 1 - (c i j) ^ 2
        = (∫ x, (x i j) ^ 2 * (if L < |x i j| then 1 else 0) ∂ν) + (b i j) ^ 2 := by
      rw [hc2]
      ring
    have h7 : 4 * (L + Kt) ^ 2 * (Real.exp (-L / Kt)) ^ 2
        ≤ 4 * (L + Kt) ^ 2 * Real.exp (-L / Kt) :=
      mul_le_mul (le_refl (4 * (L + Kt) ^ 2)) hexpsq (by positivity) (by positivity)
    linarith [h1, hTail2, hb_sq, h7]
  have hc_ge : (1 / 2 : ℝ) ≤ c i j := by
    have hone : 1 - (c i j) ^ 2 ≤ 3 / 4 := by
      have h1 : 1 - (c i j) ^ 2
          = (∫ x, (x i j) ^ 2 * (if L < |x i j| then 1 else 0) ∂ν) + (b i j) ^ 2 := by
        rw [hc2]
        ring
      linarith [h1, hTail2, hb_sq, hnum]
    have hsq : (1 / 4 : ℝ) ≤ (c i j) ^ 2 := by linarith
    calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt ((c i j) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = c i j := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc_nonneg]
  exact ⟨hbconcl, hc_ge, hc_le_one, hfour⟩
  /- @proof-region region.target-node.session.b2bd232c1fbdf0e3 end -/

#print axioms statopia_math_node_3352644490_9c3ad106
end Statlib.Imported

