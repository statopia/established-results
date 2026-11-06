import Lean
import ProverJobs.ResidualE2ESupport20261106.M_d004fbb4a25718027e28
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5
import ProverJobs.ResidualE2ESupport20261106.M_502c198e09a942a29fc0
import ProverJobs.ResidualE2ESupport20261106.M_5d8a316db71815ae22a4
import ProverJobs.ResidualE2ESupport20261106.M_16393836de1500c0c075

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
theorem statopia_math_node_1642389212_296f47d2 : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : max (Kt * (D0 + 12)) (D0 + 20) ≤ CD),
    ∃ M1 : ℕ,
      ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM1 : M1 ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (XT Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
        (hXT_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => XT ω i j)
        (hXT_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => XT ω i j) μ)
        (hXT_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (XT ω i j) ^ 2) μ)
        (hXT_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => XT ω ij.1 ij.2) μ)
        (hXT_mean : ∀ (i : Fin m) (j : Fin n), ∫ ω, XT ω i j ∂μ = 0)
        (hXT_var : ∀ (i : Fin m) (j : Fin n), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1)
        (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
        (hMask_val : ∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
        (hMask_law : ∀ (i : Fin m) (j : Fin n),
          μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
        (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
        (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => XT ω ij.1 ij.2)
          (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ)
        (hXT_bound : let L : ℝ := CD * Real.log ((m : ℝ) * (n : ℝ)) +
            10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4;
          ∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L),
        μ {ω | svals (maskedScaled p (XT ω) (Mask ω)) ⟨n - 1, by omega⟩ <
              1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - 1 * deltaM m} ≤
          ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 4)) / 2) := by
  /- @proof-region region.target-node.session.9690fe998d596e5e begin -/
  intro D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le Kt hKt alpha0 halpha0 CD hCD
  obtain ⟨M1low, hlow⟩ :=
    statopia_math_node_3749303560_8ce7b7f3 D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le
      Kt hKt alpha0 halpha0 CD hCD
  obtain ⟨M1he, c, hc, hhe⟩ :=
    statopia_math_node_1024439655_0419b336 D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le
      Kt hKt alpha0 halpha0 CD hCD (D0 + 5) (by linarith)
  obtain ⟨Mnum, hnum⟩ :=
    statopia_math_node_1358304067_3215dc50 1 1 D0 (by norm_num) (by norm_num) hD0
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * c / rhoMinus)
  refine ⟨max (max M1low M1he) (max Mnum (N + 1)), ?_⟩
  intro m n hm hn hnm hM1 hrho_lo hrho_hi p hp0 hp1 hsparse Ω _ μ _ XT Mask
    hXT_meas hXT_int hXT_sq_int hXT_indep hXT_mean hXT_var hMask_meas hMask_val
    hMask_law hMask_indep hIndep hXT_bound
  have hentry : ∀ (h h' : Fin m × Fin n),
      Integrable (fun ω => maskedScaled p (XT ω) (Mask ω) h.1 h.2) μ ∧
      (∫ ω, maskedScaled p (XT ω) (Mask ω) h.1 h.2 ∂μ = 0) ∧
      Integrable (fun ω => maskedScaled p (XT ω) (Mask ω) h.1 h.2
        * maskedScaled p (XT ω) (Mask ω) h'.1 h'.2) μ ∧
      (∫ ω, maskedScaled p (XT ω) (Mask ω) h.1 h.2
          * maskedScaled p (XT ω) (Mask ω) h'.1 h'.2 ∂μ
        = if h = h' then 1 / (m : ℝ) else 0) := by
    intro h h'
    exact statopia_math_node_3553486712_c6cf8bba m n (by omega) hn p hp0 hp1
      μ XT Mask hXT_meas hXT_int hXT_sq_int hXT_indep hXT_mean hXT_var
      hMask_meas hMask_val hMask_law hMask_indep hIndep h h'
  have hrowvar : ∀ (i : Fin m),
      ∑ j : Fin n, ∫ ω, (maskedScaled p (XT ω) (Mask ω) i j) ^ 2 ∂μ
        = (n : ℝ) / (m : ℝ) := by
    intro i
    have hterm : ∀ j : Fin n,
        ∫ ω, (maskedScaled p (XT ω) (Mask ω) i j) ^ 2 ∂μ = 1 / (m : ℝ) := by
      intro j
      have h := (hentry (i, j) (i, j)).2.2.2
      simpa [pow_two] using h
    calc ∑ j : Fin n, ∫ ω, (maskedScaled p (XT ω) (Mask ω) i j) ^ 2 ∂μ
        = ∑ _j : Fin n, 1 / (m : ℝ) := Finset.sum_congr rfl (fun j _ => hterm j)
      _ = (n : ℝ) * (1 / (m : ℝ)) := by simp
      _ = (n : ℝ) / (m : ℝ) := by ring
  have hcov : ∀ (i i' : Fin m),
      ∑ j : Fin n, ∫ ω, maskedScaled p (XT ω) (Mask ω) i j
          * maskedScaled p (XT ω) (Mask ω) i' j ∂μ
        = if i = i' then (n : ℝ) / (m : ℝ) else 0 := by
    intro i i'
    have hterm : ∀ j : Fin n,
        ∫ ω, maskedScaled p (XT ω) (Mask ω) i j
          * maskedScaled p (XT ω) (Mask ω) i' j ∂μ
          = if ((i, j) : Fin m × Fin n) = (i', j) then 1 / (m : ℝ) else 0 :=
      fun j => (hentry (i, j) (i', j)).2.2.2
    have hconst : (∑ _j : Fin n, (1 / (m : ℝ))) = (n : ℝ) / (m : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    calc ∑ j : Fin n, ∫ ω, maskedScaled p (XT ω) (Mask ω) i j
          * maskedScaled p (XT ω) (Mask ω) i' j ∂μ
        = ∑ j : Fin n,
            (if ((i, j) : Fin m × Fin n) = (i', j) then 1 / (m : ℝ) else 0) :=
            Finset.sum_congr rfl (fun j _ => hterm j)
      _ = if i = i' then (n : ℝ) / (m : ℝ) else 0 := by
            by_cases h : i = i'
            · subst h
              have hc : (∑ j : Fin n,
                    (if ((i, j) : Fin m × Fin n) = (i, j) then 1 / (m : ℝ) else 0))
                  = ∑ _j : Fin n, (1 / (m : ℝ)) :=
                Finset.sum_congr rfl (fun j _ => by simp)
              rw [hc, if_pos rfl]
              exact hconst
            · have hne : ∀ j : Fin n, ¬ ((i, j) : Fin m × Fin n) = (i', j) := by
                intro j hij
                exact h (congrArg Prod.fst hij)
              rw [if_neg h]
              refine Finset.sum_eq_zero ?_
              intro j _
              rw [if_neg (hne j)]


  set L : ℝ := CD * Real.log ((m : ℝ) * (n : ℝ)) +
      10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 with hL
  have hXb : ∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L := by
    intro ω i j
    have h := hXT_bound ω i j
    simpa [hL] using h
  have hscale : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
      |maskedScaled p (XT ω) (Mask ω) i j| ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := by
    intro ω i j
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hmp : (0 : ℝ) < (m : ℝ) * p := mul_pos hmpos hp0
    have hsq : (0 : ℝ) < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.mpr hmp
    have hmask1 : |Mask ω i j| ≤ 1 := by
      rcases hMask_val i j ω with h | h <;> rw [h] <;> norm_num
    have hmul : |Mask ω i j * XT ω i j| ≤ 3 * L := by
      rw [abs_mul]
      calc |Mask ω i j| * |XT ω i j| ≤ 1 * (3 * L) :=
            mul_le_mul hmask1 (hXb ω i j) (abs_nonneg _) (by norm_num)
        _ = 3 * L := by ring
    calc |maskedScaled p (XT ω) (Mask ω) i j|
        = |Mask ω i j * XT ω i j| / Real.sqrt ((m : ℝ) * p) := by
          simp only [maskedScaled, abs_div, abs_of_pos hsq]
      _ ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := by
          gcongr

  have hsv_nonneg : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n), 0 ≤ svals A i :=
    fun A i => Real.sqrt_nonneg _
  by_cases hthr : 1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - 1 * deltaM m ≤ 0
  · have hnull : μ {ω | svals (maskedScaled p (XT ω) (Mask ω)) ⟨n - 1, by omega⟩ <
        1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - 1 * deltaM m} = 0 := by
      apply measure_mono_null _ measure_empty
      intro ω hω
      simp only [Set.mem_empty_iff_false]
      exact absurd hω (not_lt.mpr (le_trans hthr (hsv_nonneg _ _)))
    exact le_trans (le_of_eq hnull) (zero_le _)
  · by_cases hn1 : n = 1
    · subst hn1
      have hM1low : M1low ≤ m :=
        le_trans (le_trans (le_max_left M1low M1he)
          (le_max_left (max M1low M1he) (max Mnum (N + 1)))) hM1
      have h1 := hlow m hm hM1low (by simpa using hrho_lo) (by simpa using hrho_hi)
        p hp0 hp1 hsparse μ XT Mask hXT_meas hXT_int hXT_sq_int hXT_indep hXT_mean
        hXT_var hMask_meas hMask_val hMask_law hMask_indep hIndep hXT_bound
      simpa using h1
    · have hM1he : M1he ≤ m :=
        le_trans (le_trans (le_max_right M1low M1he)
          (le_max_left (max M1low M1he) (max Mnum (N + 1)))) hM1
      have hMnum : Mnum ≤ m :=
        le_trans (le_trans (le_max_left Mnum (N + 1))
          (le_max_right (max M1low M1he) (max Mnum (N + 1)))) hM1
      have hNle : N + 1 ≤ m :=
        le_trans (le_trans (le_max_right Mnum (N + 1))
          (le_max_right (max M1low M1he) (max Mnum (N + 1)))) hM1
      obtain ⟨_, hεquarter, _⟩ := hnum m hMnum
      have hlogpos : 0 < Real.log (m : ℝ) := by
        have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        exact Real.log_pos hm1
      have hn2 : 2 ≤ n := by omega
      have hAm : ∀ (i : Fin m) (j : Fin n),
          Measurable fun ω => maskedScaled p (XT ω) (Mask ω) i j := by
        intro i j
        show Measurable fun ω => Mask ω i j * XT ω i j / Real.sqrt ((m : ℝ) * p)
        exact Measurable.div ((hMask_meas i j).mul (hXT_meas i j)) measurable_const
      have hAint : ∀ (i : Fin m) (j : Fin n),
          Integrable (fun ω => maskedScaled p (XT ω) (Mask ω) i j) μ :=
        fun i j => (hentry (i, j) (i, j)).1
      have hAsq : ∀ (i : Fin m) (j : Fin n),
          Integrable (fun ω => (maskedScaled p (XT ω) (Mask ω) i j) ^ 2) μ :=
        fun i j => by simpa [pow_two] using (hentry (i, j) (i, j)).2.2.1
      have hpair : iIndepFun
          (fun (ij : Fin m × Fin n) (ω : Ω) => (XT ω ij.1 ij.2, Mask ω ij.1 ij.2)) μ :=
        statopia_math_node_2156877478_7316b341
          (fun (ij : Fin m × Fin n) => fun ω => XT ω ij.1 ij.2)
          (fun (ij : Fin m × Fin n) => fun ω => Mask ω ij.1 ij.2)
          (fun q : ℝ × ℝ => q) hXT_indep hMask_indep hIndep
          (fun ij => (hXT_meas ij.1 ij.2).aemeasurable)
          (fun ij => (hMask_meas ij.1 ij.2).aemeasurable)
          measurable_id
      have hAind : iIndepFun
          (fun (ij : Fin m × Fin n) (ω : Ω) => maskedScaled p (XT ω) (Mask ω) ij.1 ij.2) μ :=
        hpair.comp (fun (_ : Fin m × Fin n) (q : ℝ × ℝ) =>
            q.2 * q.1 / Real.sqrt ((m : ℝ) * p))
          (fun _ => (measurable_snd.mul measurable_fst).div measurable_const)
      have hAmean : ∀ (i : Fin m) (j : Fin n),
          ∫ ω, maskedScaled p (XT ω) (Mask ω) i j ∂μ = 0 :=
        fun i j => (hentry (i, j) (i, j)).2.1
      have hAvar : ∀ (i : Fin m) (j : Fin n),
          ∫ ω, (maskedScaled p (XT ω) (Mask ω) i j) ^ 2 ∂μ = 1 / (m : ℝ) := by
        intro i j
        have h := (hentry (i, j) (i, j)).2.2.2
        simpa [pow_two] using h
      have hmR : (0 : ℝ) < (m : ℝ) := by
        have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith only [h2]
      have hnR : (0 : ℝ) < (n : ℝ) := by
        have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hnmR' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hlog1 : (1 : ℝ) ≤ Real.log (m : ℝ) := by
        have h4 : (0 : ℝ) < 2 * Real.log (m : ℝ) := by positivity
        have hkey : (2 * Real.log (m : ℝ)) * (1 / (2 * Real.log (m : ℝ))) = 1 := by
          have hne : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlogpos
          field_simp
        have hmul := mul_le_mul_of_nonneg_left hεquarter (le_of_lt h4)
        rw [hkey] at hmul
        nlinarith [hmul]
      obtain ⟨T, hT⟩ : ∃ T : ℝ,
          T = 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := ⟨_, rfl⟩
      have hcapT : (0 : ℝ) ≤ T := by
        rw [hT]
        positivity
      have hCDnn : (0 : ℝ) ≤ CD := by
        have h1 : (0 : ℝ) < D0 + 20 := by linarith
        have h2 : D0 + 20 ≤ CD :=
          le_trans (le_max_right (Kt * (D0 + 12)) (D0 + 20)) hCD
        linarith
      have hmnle : Real.log ((m : ℝ) * (n : ℝ)) ≤ 2 * Real.log (m : ℝ) := by
        have hle : (m : ℝ) * (n : ℝ) ≤ (m : ℝ) * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hnmR' (le_of_lt hmR)
        calc Real.log ((m : ℝ) * (n : ℝ)) ≤ Real.log ((m : ℝ) * (m : ℝ)) :=
              Real.log_le_log (mul_pos hmR hnR) hle
          _ = Real.log ((m : ℝ) ^ 2) := by rw [pow_two]
          _ = 2 * Real.log (m : ℝ) := by
              rw [Real.log_pow]
              norm_num
      have hLb : L ≤ (2 * CD + T) * Real.log (m : ℝ) := by
        have hs1 : CD * Real.log ((m : ℝ) * (n : ℝ)) ≤ CD * (2 * Real.log (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hmnle hCDnn
        have hs2 : T ≤ T * Real.log (m : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hlog1 hcapT
          rwa [mul_one] at h
        have hsum := add_le_add hs1 hs2
        rw [hL, ← hT]
        calc CD * Real.log ((m : ℝ) * (n : ℝ)) + T
            ≤ CD * (2 * Real.log (m : ℝ)) + T * Real.log (m : ℝ) := hsum
          _ = (2 * CD + T) * Real.log (m : ℝ) := by ring
      have hsqrpow : (Real.rpow (Real.log (m : ℝ)) (alpha0 / 2)) ^ 2 =
          Real.rpow (Real.log (m : ℝ)) alpha0 := by
        have hsum : alpha0 / 2 + alpha0 / 2 = alpha0 := by ring
        have hadd : Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) *
            Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) =
            Real.rpow (Real.log (m : ℝ)) (alpha0 / 2 + alpha0 / 2) :=
          (Real.rpow_add hlogpos (alpha0 / 2) (alpha0 / 2)).symm
        rw [hsum] at hadd
        rw [pow_two]
        exact hadd
      have hsqrtle : Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) ≤
          Real.sqrt ((m : ℝ) * p) := by
        have hx0 : (0 : ℝ) ≤ Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) :=
          le_of_lt (Real.rpow_pos_of_pos hlogpos _)
        have h2 : (Real.rpow (Real.log (m : ℝ)) (alpha0 / 2)) ^ 2 ≤ (m : ℝ) * p := by
          rw [hsqrpow]
          exact hsparse
        have hmono : Real.sqrt ((Real.rpow (Real.log (m : ℝ)) (alpha0 / 2)) ^ 2) ≤
            Real.sqrt ((m : ℝ) * p) := Real.sqrt_le_sqrt h2
        rwa [Real.sqrt_sq hx0] at hmono
      have hquot : Real.log (m : ℝ) / Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) =
          Real.rpow (Real.log (m : ℝ)) (1 - alpha0 / 2) := by
        have h := Real.rpow_sub hlogpos 1 (alpha0 / 2)
        rw [Real.rpow_one] at h
        exact h.symm
      have hrpowpos : (0 : ℝ) < Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) :=
        Real.rpow_pos_of_pos hlogpos _
      have hAampT : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
          |maskedScaled p (XT ω) (Mask ω) i j| ≤
            3 * (2 * CD + T) *
              (Real.log (m : ℝ) / Real.rpow (Real.log (m : ℝ)) (alpha0 / 2)) := by
        intro ω i j
        have hbase := hscale ω i j
        calc |maskedScaled p (XT ω) (Mask ω) i j|
            ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := hbase
          _ ≤ 3 * ((2 * CD + T) * Real.log (m : ℝ)) /
                Real.sqrt ((m : ℝ) * p) := by gcongr
          _ ≤ 3 * ((2 * CD + T) * Real.log (m : ℝ)) /
                Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) := by gcongr
          _ = 3 * (2 * CD + T) *
                (Real.log (m : ℝ) / Real.rpow (Real.log (m : ℝ)) (alpha0 / 2)) := by ring
      have hAamp : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
          |maskedScaled p (XT ω) (Mask ω) i j| ≤
            3 * (2 * CD + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) *
              Real.rpow (Real.log (m : ℝ)) (1 - alpha0 / 2) := by
        intro ω i j
        have h := hAampT ω i j
        rw [hquot, hT] at h
        exact h
      have hn2c : 2 * c ≤ (n : ℝ) := by
        have hone : rhoMinus * (2 * c / rhoMinus) = 2 * c := by
          have hne : rhoMinus ≠ 0 := ne_of_gt hrhoMinus_pos
          field_simp
        have hstep1 : 2 * c ≤ rhoMinus * (N : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hN (le_of_lt hrhoMinus_pos)
          rwa [hone] at h
        have hNm : (N : ℝ) ≤ (m : ℝ) := by
          have h' : ((N + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hNle
          push_cast at h'
          linarith only [h']
        have hstep2 : rhoMinus * (N : ℝ) ≤ rhoMinus * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hNm (le_of_lt hrhoMinus_pos)
        have hstep3 : rhoMinus * (m : ℝ) ≤ (n : ℝ) := by
          have h := mul_le_mul_of_nonneg_right hrho_lo (le_of_lt hmR)
          have h2 : (n : ℝ) / (m : ℝ) * (m : ℝ) = (n : ℝ) := by
            have hne : (m : ℝ) ≠ 0 := ne_of_gt hmR
            field_simp
          rwa [h2] at h
        linarith only [hstep1, hstep2, hstep3]
      have hsplit : Real.rpow (n : ℝ) (-(D0 + 4)) =
          (n : ℝ) * Real.rpow (n : ℝ) (-(D0 + 5)) := by
        have h := Real.rpow_add hnR (1 : ℝ) (-(D0 + 5))
        rw [Real.rpow_one] at h
        have hexp : (1 : ℝ) + (-(D0 + 5)) = -(D0 + 4) := by ring
        rw [hexp] at h
        exact h
      have hcmul : c * Real.rpow (n : ℝ) (-(D0 + 5)) ≤
          ((n : ℝ) / 2) * Real.rpow (n : ℝ) (-(D0 + 5)) := by
        have hrpowle : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-(D0 + 5)) :=
          le_of_lt (Real.rpow_pos_of_pos hnR _)
        apply mul_le_mul_of_nonneg_right _ hrpowle
        linarith only [hn2c]
      refine le_trans (hhe m n hm hn2 hnm hM1he hrho_lo hrho_hi μ
        (fun ω => maskedScaled p (XT ω) (Mask ω)) hAm
        (fun i j => ⟨hAint i j, hAsq i j⟩) hAind hAmean hAvar hAamp)
        (ENNReal.ofReal_le_ofReal ?_)
      calc c * Real.rpow (n : ℝ) (-(D0 + 5))
          ≤ ((n : ℝ) / 2) * Real.rpow (n : ℝ) (-(D0 + 5)) := hcmul
        _ = Real.rpow (n : ℝ) (-(D0 + 4)) / 2 := by
            rw [hsplit]
            ring
  /- @proof-region region.target-node.session.9690fe998d596e5e end -/

#print axioms statopia_math_node_1642389212_296f47d2
end Statlib.Imported
