import Lean
import ProverJobs.ResidualE2ESupport20261106.M_3dccff77fe1d02cb5326
import ProverJobs.ResidualE2ESupport20261106.M_fa8bbc31a4e4e2df874d

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace ResidualLoss20261106.Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2169097838_d24405fa : ∀ (rho : ℝ) (h_rho_pos : 0 < rho)
    (h_rho_le : rho ≤ 1) (n : ℕ) (gamma : Fin n → ℝ)
    (hquant : ∀ i : Fin n,
      (∫ x, nuRho rho x ∂(volume.restrict (Set.Icc (gamma i) (lambdaPlus rho))))
        = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ)),
    ∀ i : Fin n,
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpQuantile rho n i
        = gamma i := by
  /- @proof-region region.target-node.session.00fb34d32e80c52e begin -/
  intro rho hrho_pos hrho_le n gamma hgamma i
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have h : 0 < n := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact absurd i.isLt (Nat.not_lt_zero _))
    exact_mod_cast h
  have hi_lt : ((i : ℕ) : ℝ) + 1 / 2 < (n : ℝ) := by
    have h1 : (i : ℕ) + 1 ≤ n := i.isLt
    have h2 : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hlev_pos : 0 < (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) := by
    have h1 : 0 < ((i : ℕ) : ℝ) + 1 / 2 := by positivity
    exact div_pos h1 hn_pos
  have hlev_lt_one : (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) < 1 := by
    have h := div_lt_div_of_pos_right hi_lt hn_pos
    rwa [div_self (ne_of_gt hn_pos)] at h
  have hlev_eq : (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) = (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) := by
    ring
  have hν : ∀ x : ℝ, nuRho rho x = _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x := by
    intro x
    rw [nuRho, lambdaMinus, lambdaPlus,
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity,
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaPlus,
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaMinus]
    by_cases hx : 1 - Real.sqrt rho ≤ x ∧ x ≤ 1 + Real.sqrt rho
    · rw [if_pos hx, if_pos hx, mul_one]
      have key : ∀ a b c : ℝ, a / (Real.pi * b * c) = (1 / Real.pi * a) / (b * c) := by
        intro a b c
        rw [show Real.pi * b * c = Real.pi * (b * c) by ring, ← div_div,
          show a / Real.pi = 1 / Real.pi * a by rw [div_eq_inv_mul, one_div]]
      exact key _ _ _
    · rw [if_neg hx, if_neg hx, mul_zero]
  have hgam_le : gamma i ≤ lambdaPlus rho := by
    by_contra hle
    have hlt : lambdaPlus rho < gamma i := lt_of_not_ge hle
    have hempty : Set.Icc (gamma i) (lambdaPlus rho) = ∅ := by
      ext y
      simp only [Set.mem_Icc, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      linarith
    have hzero : (∫ x, nuRho rho x ∂(volume.restrict (Set.Icc (gamma i) (lambdaPlus rho)))) = 0 := by
      rw [hempty]
      simp
    have hq := hgamma i
    rw [hzero] at hq
    rw [hlev_eq] at hq
    linarith [hlev_pos]
  have htail_gamma : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail rho (gamma i) = (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) := by
    rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail]
    have hq := hgamma i
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, hlev_eq] at hq
    rw [← intervalIntegral.integral_of_le hgam_le] at hq
    rw [intervalIntegral.integral_congr (fun x _ => hν x)] at hq
    exact hq
  have hmpL : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaPlus rho = lambdaPlus rho := rfl
  have htail_ge : ∀ t : ℝ, lambdaPlus rho ≤ t → _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail rho t = 0 := by
    intro t ht
    rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail]
    rw [hmpL]
    have hzero : ∀ x ∈ Set.uIcc t (lambdaPlus rho),
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x = 0 := by
      intro x hx
      rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaPlus,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaMinus]
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · by_cases hc : 1 - Real.sqrt rho ≤ x ∧ x ≤ 1 + Real.sqrt rho
        · rw [if_pos hc]
          rw [show x = 1 + Real.sqrt rho from le_antisymm h2 (le_trans ht h1)]
          simp
        · rw [if_neg hc, mul_zero]
      · by_cases hc : 1 - Real.sqrt rho ≤ x ∧ x ≤ 1 + Real.sqrt rho
        · rw [if_pos hc]
          rw [show x = 1 + Real.sqrt rho from le_antisymm hc.2 h1]
          simp
        · rw [if_neg hc, mul_zero]
    calc (∫ x in t..lambdaPlus rho,
          _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
        = ∫ x in t..lambdaPlus rho, (0 : ℝ) := intervalIntegral.integral_congr hzero
      _ = 0 := by simp
  have hlam_nonneg : 0 ≤ lambdaMinus rho := by
    have hs : Real.sqrt rho ≤ 1 := by
      have h1 : Real.sqrt rho ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      simpa using h1
    rw [lambdaMinus]
    linarith
  have hplus_pos : 0 < lambdaPlus rho := by
    rw [lambdaPlus]
    positivity
  have hplus_eq : lambdaPlus rho = 1 + Real.sqrt rho := rfl
  have hminus_eq : lambdaMinus rho = 1 - Real.sqrt rho := rfl
  have hlam_le : lambdaMinus rho ≤ lambdaPlus rho := by
    rw [lambdaMinus, lambdaPlus]
    have hs := Real.sqrt_nonneg rho
    linarith
  have hmeas : Measurable (fun x : ℝ =>
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x) := by
    have h1 : Measurable (fun x : ℝ =>
        (1 / Real.pi) * Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2))
          / (rho * x)) := by
      measurability
    have h2 : Measurable (fun x : ℝ =>
        if lambdaMinus rho ≤ x ∧ x ≤ lambdaPlus rho then (1 : ℝ) else 0) := by
      have hms : MeasurableSet {x : ℝ | lambdaMinus rho ≤ x ∧ x ≤ lambdaPlus rho} :=
        (measurableSet_le (f := fun _ : ℝ => lambdaMinus rho) (g := fun x : ℝ => x)
            measurable_const measurable_id).inter
          (measurableSet_le (f := fun x : ℝ => x) (g := fun _ : ℝ => lambdaPlus rho)
            measurable_id measurable_const)
      exact Measurable.ite (f := fun _ : ℝ => (1 : ℝ)) (g := fun _ : ℝ => 0)
        hms measurable_const measurable_const
    exact h1.mul h2
  have hbound : ∀ x : ℝ, ‖_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x‖
      ≤ lambdaPlus rho / (Real.pi * rho) := by
    intro x
    rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity,
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaPlus,
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaMinus]
    by_cases hc : 1 - Real.sqrt rho ≤ x ∧ x ≤ 1 + Real.sqrt rho
    · rw [if_pos hc, mul_one]
      have hx0 : 0 ≤ x := le_trans hlam_nonneg hc.1
      by_cases hxzero : x = 0
      · rw [hxzero, mul_zero, div_zero, norm_zero]
        exact div_nonneg (le_of_lt hplus_pos) (le_of_lt (mul_pos Real.pi_pos hrho_pos))
      · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
        have hA' : 0 ≤ lambdaPlus rho ^ 2 - x ^ 2 := by
          have h1 : 0 ≤ lambdaPlus rho - x := by linarith [hplus_eq, hc.2]
          have h2 : 0 ≤ lambdaPlus rho + x := by linarith [hplus_pos, hx0]
          nlinarith [mul_nonneg h1 h2]
        have hB' : 0 ≤ x ^ 2 - lambdaMinus rho ^ 2 := by
          have h1 : 0 ≤ x - lambdaMinus rho := by linarith [hminus_eq, hc.1]
          have h2 : 0 ≤ x + lambdaMinus rho := by linarith [hlam_nonneg, hx0]
          nlinarith [mul_nonneg h1 h2]
        have hsqle : (lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)
            ≤ (lambdaPlus rho * x) ^ 2 := by
          have hx2 : x ^ 2 - lambdaMinus rho ^ 2 ≤ x ^ 2 := by nlinarith [hlam_nonneg, hx0]
          have step1 : (lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)
              ≤ (lambdaPlus rho ^ 2 - x ^ 2) * x ^ 2 := mul_le_mul_of_nonneg_left hx2 hA'
          have step2 : (lambdaPlus rho ^ 2 - x ^ 2) * x ^ 2 ≤ lambdaPlus rho ^ 2 * x ^ 2 := by
            have h : lambdaPlus rho ^ 2 - x ^ 2 ≤ lambdaPlus rho ^ 2 := by nlinarith [sq_nonneg x]
            exact mul_le_mul_of_nonneg_right h (sq_nonneg x)
          calc (lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)
              ≤ (lambdaPlus rho ^ 2 - x ^ 2) * x ^ 2 := step1
            _ ≤ lambdaPlus rho ^ 2 * x ^ 2 := step2
            _ = (lambdaPlus rho * x) ^ 2 := by ring
        have hNle : Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2))
            ≤ lambdaPlus rho * x := by
          calc Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2))
              ≤ Real.sqrt ((lambdaPlus rho * x) ^ 2) := Real.sqrt_le_sqrt hsqle
            _ = lambdaPlus rho * x := Real.sqrt_sq (by positivity)
        have hnn : ‖(1 / Real.pi) * Real.sqrt (((1 + Real.sqrt rho) ^ 2 - x ^ 2) * (x ^ 2 - (1 - Real.sqrt rho) ^ 2)) / (rho * x)‖
            = (1 / Real.pi) * Real.sqrt (((1 + Real.sqrt rho) ^ 2 - x ^ 2) * (x ^ 2 - (1 - Real.sqrt rho) ^ 2)) / (rho * x) := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          have hpi : (0 : ℝ) < 1 / Real.pi := by positivity
          exact div_nonneg (mul_nonneg (le_of_lt hpi) (Real.sqrt_nonneg _))
            (le_of_lt (mul_pos hrho_pos hxpos))
        rw [hnn, div_le_iff₀ (mul_pos hrho_pos hxpos)]
        have h1 : (1 / Real.pi) * Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2))
            ≤ (1 / Real.pi) * (lambdaPlus rho * x) :=
          mul_le_mul_of_nonneg_left hNle (by positivity)
        have h2 : (lambdaPlus rho / (Real.pi * rho)) * (rho * x) = (1 / Real.pi) * (lambdaPlus rho * x) := by
          field_simp
        rw [h2]
        exact h1
    · rw [if_neg hc, mul_zero, norm_zero]
      exact div_nonneg (le_of_lt hplus_pos) (le_of_lt (mul_pos Real.pi_pos hrho_pos))
  have hInt : ∀ p q : ℝ, p ≤ q → IntervalIntegrable (fun x : ℝ =>
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x) volume p q := by
    intro p q hpq
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
    have hvol : volume (Set.Ioc p q) < ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have haesm : AEStronglyMeasurable (fun x : ℝ =>
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
        (volume.restrict (Set.Ioc p q)) := hmeas.aestronglyMeasurable
    have hbnd : ∀ᵐ x ∂(volume.restrict (Set.Ioc p q)),
        ‖(fun y : ℝ => _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho y) x‖
          ≤ lambdaPlus rho / (Real.pi * rho) := Filter.Eventually.of_forall hbound
    exact MeasureTheory.IntegrableOn.of_bound hvol haesm _ hbnd
  have htail_le : ∀ t : ℝ, t ≤ lambdaMinus rho → _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail rho t = 1 := by
    intro t ht
    have hzero : ∀ x ∈ Set.uIcc t (lambdaMinus rho),
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x = 0 := by
      intro x hx
      have hxle : x ≤ 1 - Real.sqrt rho := by
        rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact le_trans h2 ht
      rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaPlus,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaMinus]
      by_cases hc : 1 - Real.sqrt rho ≤ x ∧ x ≤ 1 + Real.sqrt rho
      · rw [if_pos hc]
        rw [show x = 1 - Real.sqrt rho from le_antisymm hxle hc.1]
        simp
      · rw [if_neg hc, mul_zero]
    have hleft : (∫ x in t..lambdaMinus rho,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x) = 0 := by
      calc (∫ x in t..lambdaMinus rho,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
          = ∫ x in t..lambdaMinus rho, (0 : ℝ) := intervalIntegral.integral_congr hzero
        _ = 0 := by simp
    have hdiag : (∫ x in lambdaMinus rho..lambdaMinus rho,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x) = 0 := by
      simp
    have hnorm : (∫ x in lambdaMinus rho..lambdaPlus rho,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x) = 1 := by
      have hdep := (statopia_math_node_2262828856_34ee8798 rho rho hrho_pos le_rfl hrho_le).1
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc] at hdep
      rw [← intervalIntegral.integral_of_le hlam_le] at hdep
      rw [intervalIntegral.integral_congr (fun x _ => hν x)] at hdep
      exact hdep
    have hadd : (∫ x in t..lambdaMinus rho,
          _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
        + (∫ x in lambdaMinus rho..lambdaPlus rho,
          _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
        = (∫ x in t..lambdaPlus rho,
          _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
        + (∫ x in lambdaMinus rho..lambdaMinus rho,
          _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x) :=
      intervalIntegral.integral_interval_add_interval_comm
        (f := fun x : ℝ => _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
        (hInt t (lambdaMinus rho) ht)
        (hInt (lambdaMinus rho) (lambdaPlus rho) hlam_le)
        (hInt t (lambdaMinus rho) ht)
    have hsplit : (∫ x in t..lambdaPlus rho,
          _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
        = (∫ x in t..lambdaMinus rho,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
          + (∫ x in lambdaMinus rho..lambdaPlus rho,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
          - (∫ x in lambdaMinus rho..lambdaMinus rho,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x) := by
      linarith [hadd]
    rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail,
      hmpL]
    rw [hsplit, hleft, hnorm, hdiag]
    norm_num
  have hstrict : ∀ a b : ℝ, lambdaMinus rho ≤ a → a < b → b ≤ lambdaPlus rho →
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail rho b
        < _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail rho a := by
    intro a b ha hab hb
    have hPB : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail rho b
        = (∫ x in a..lambdaPlus rho,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
          - (∫ x in a..b,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x) := by
      rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail,
        hmpL]
      have hKey : (∫ x in a..lambdaPlus rho,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
          - (∫ x in a..b,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
          = ∫ x in b..lambdaPlus rho,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x :=
        intervalIntegral.integral_interval_sub_left
          (f := fun x : ℝ =>
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x)
          (hInt a (lambdaPlus rho) (le_of_lt (lt_of_lt_of_le hab hb)))
          (hInt a b (le_of_lt hab))
      rw [← hKey]
    have hPA : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail rho a
        = ∫ x in a..lambdaPlus rho,
            _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x := by
      rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail,
        hmpL]
    have hpos : 0 < ∫ x in a..b,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity rho x := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on (hInt a b (le_of_lt hab)) ?_ hab
      intro x hx
      have hx1 : lambdaMinus rho ≤ x := le_trans ha (le_of_lt hx.1)
      have hx2 : x ≤ lambdaPlus rho := le_trans (le_of_lt hx.2) hb
      have hxpos : 0 < x := lt_of_le_of_lt (le_trans hlam_nonneg ha) hx.1
      rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rootedMPDensity,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaPlus,
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpLambdaMinus,
        if_pos ⟨hx1, hx2⟩, mul_one]
      have hA : 0 < lambdaPlus rho ^ 2 - x ^ 2 := by
        have h1 : 0 < lambdaPlus rho - x := by linarith [hx.2]
        have h2 : 0 < lambdaPlus rho + x := by linarith [hplus_pos, hxpos]
        nlinarith [mul_pos h1 h2]
      have hB : 0 < x ^ 2 - lambdaMinus rho ^ 2 := by
        have h1 : 0 < x - lambdaMinus rho := by linarith [lt_of_le_of_lt ha hx.1]
        have h2 : 0 < x + lambdaMinus rho := by linarith [hlam_nonneg, hxpos]
        nlinarith [mul_pos h1 h2]
      have hsq : 0 < Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) :=
        Real.sqrt_pos_of_pos (mul_pos hA hB)
      have hpi : (0 : ℝ) < 1 / Real.pi := by positivity
      exact div_pos (mul_pos hpi hsq) (mul_pos hrho_pos hxpos)
    rw [hPB, hPA]
    linarith
  have hgam_ge : lambdaMinus rho ≤ gamma i := by
    by_contra hc
    have hlt : gamma i < lambdaMinus rho := lt_of_not_ge hc
    have h1 := htail_le (gamma i) (le_of_lt hlt)
    rw [htail_gamma] at h1
    linarith [hlev_lt_one]
  rw [_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpQuantile]
  apply le_antisymm
  · apply csSup_le
    · exact ⟨gamma i, by simp [htail_gamma]⟩
    · intro x hx
      have hx' : (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) ≤ _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail rho x := hx
      by_contra hc
      have hxgt : gamma i < x := lt_of_not_ge hc
      by_cases hxlt : x < lambdaPlus rho
      · have hstr := hstrict (gamma i) x hgam_ge hxgt (le_of_lt hxlt)
        rw [htail_gamma] at hstr
        linarith
      · have h0 := htail_ge x (le_of_not_gt hxlt)
        linarith [hlev_pos]
  · apply le_csSup
    · refine ⟨lambdaPlus rho, ?_⟩
      intro x hx
      have hx' : (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) ≤ _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.mpTail rho x := hx
      by_contra hc
      have hxt : lambdaPlus rho < x := lt_of_not_ge hc
      have h0 := htail_ge x (le_of_lt hxt)
      linarith [hlev_pos]
    · simp [htail_gamma]
  /- @proof-region region.target-node.session.00fb34d32e80c52e end -/

end ResidualLoss20261106.Statlib.Imported

end

#print axioms ResidualLoss20261106.Statlib.Imported.statopia_math_node_2169097838_d24405fa

