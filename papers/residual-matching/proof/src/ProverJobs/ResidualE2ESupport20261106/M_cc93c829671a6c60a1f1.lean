import Lean
import ProverJobs.ResidualE2ESupport20261106.M_c2f636835ffa610ac933
import ProverJobs.ResidualE2ESupport20261106.M_768d89edee376a3171f4

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported
universe u

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace ResidualLoss20261106.Statlib.Imported

set_option autoImplicit false in
theorem ideal_noise_from_actual_rigidity : ∀ (K rhoMin : ℝ) (hK : 0 < K) (hrhoMin : 0 < rhoMin)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CR cR : ℝ) (hCR : 0 < CR) (hcR : 0 < cR) (m0att : ℕ)
    (hRig : ∀ (m n : ℕ) (hnm : n ≤ m) (hn : 0 < n) (p : ℝ) (γ : Fin n → ℝ)
        (hp0 : 0 < p) (hp1 : p ≤ 1) (hrho_lo : rhoMin ≤ (rho m n)) (hrho_hi : (rho m n) ≤ 1)
        (hm : m0att ≤ m)
        (hmp : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (hgamma : ∀ i : Fin n,
          (∫ x, nuRho (rho m n) x ∂(volume.restrict (Set.Icc (γ i) (lambdaPlus (rho m n)))))
            = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ))
        {Ωs : Type u} [MeasurableSpace Ωs] (μ : Measure Ωs) [IsProbabilityMeasure μ]
        (Om : Ωs → Matrix (Fin m) (Fin n) ℝ) (Xi : Ωs → Matrix (Fin m) (Fin n) ℝ)
        (hOm_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Om s i j)
        (hOm_bin : ∀ (s : Ωs) (i : Fin m) (j : Fin n), Om s i j = 0 ∨ Om s i j = 1)
        (hOm_prob : ∀ (i : Fin m) (j : Fin n), μ {s : Ωs | Om s i j = 1} = ENNReal.ofReal p)
        (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Xi s i j)
        (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => Xi s i j) μ)
        (hXi_mean : ∀ (i : Fin m) (j : Fin n), (∫ s, Xi s i j ∂μ) = 0)
        (hXi_int2 : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => (Xi s i j) ^ 2) μ)
        (hXi_var : ∀ (i : Fin m) (j : Fin n), (∫ s, (Xi s i j) ^ 2 ∂μ) = 1)
        (hXi_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
          μ {s : Ωs | t < |Xi s i j|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / K))))
        (hindep : iIndepFun (fun (x : (Fin m × Fin n) ⊕ (Fin m × Fin n)) => fun s : Ωs =>
          match x with
          | Sum.inl q => Om s q.1 q.2
          | Sum.inr q => Xi s q.1 q.2) μ),
        μ {s : Ωs | ∃ i : Fin n,
              CR * deltaM m
                < |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|}
            ≤ ENNReal.ofReal (cR * Real.rpow (n : ℝ) (-4 : ℝ)) ∧
        (∀ s : Ωs, ¬ (∃ i : Fin n,
              CR * deltaM m
                < |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|) →
          sv hnm (maskOp (Om s) (Xi s)) ⟨0, hn⟩
              / Real.sqrt ((m : ℝ) * p)
            ≤ 1 + Real.sqrt (rho m n) + CR * deltaM m)),
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (p sigma : ℝ) (n m : ℕ) (γ : Fin n → ℝ)
        {Ωs : Type u} [MeasurableSpace Ωs] (μ : Measure Ωs) [IsProbabilityMeasure μ]
        (Om Hm : Ωs → Matrix (Fin m) (Fin n) ℝ)
        (hm : m0att ≤ m) (hn : 2 ≤ n) (hnm : n ≤ m) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hrho_lo : rhoMin ≤ (rho m n)) (hrho_hi : (rho m n) ≤ 1) (hsigma : 0 < sigma)
        (hmp : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (hgamma : ∀ i : Fin n,
          (∫ x, nuRho (rho m n) x ∂(volume.restrict (Set.Icc (γ i) (lambdaPlus (rho m n)))))
            = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ))
        (hOm_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Om s i j)
        (hOm_bin : ∀ (s : Ωs) (i : Fin m) (j : Fin n), Om s i j = 0 ∨ Om s i j = 1)
        (hOm_prob : ∀ (i : Fin m) (j : Fin n), μ {s : Ωs | Om s i j = 1} = ENNReal.ofReal p)
        (hHm_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Hm s i j)
        (hHm_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => Hm s i j) μ)
        (hHm_mean : ∀ (i : Fin m) (j : Fin n), (∫ s, Hm s i j ∂μ) = 0)
        (hHm_int2 : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => (Hm s i j) ^ 2) μ)
        (hHm_var : ∀ (i : Fin m) (j : Fin n), (∫ s, (Hm s i j) ^ 2 ∂μ) = sigma ^ 2)
        (hHm_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
          μ {s : Ωs | t * sigma < |Hm s i j|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / K))))
        (hindep : iIndepFun (fun (x : (Fin m × Fin n) ⊕ (Fin m × Fin n)) => fun s : Ωs =>
          match x with
          | Sum.inl q => Om s q.1 q.2
          | Sum.inr q => Hm s q.1 q.2) μ),
        μ {s : Ωs |
              (∀ i : Fin n,
                |sv hnm (maskOp (Om s) (Hm s)) i / (sigma * Real.sqrt (m : ℝ))
                    - Real.sqrt p * γ i|
                  ≤ C * Real.sqrt p * deltaM m) ∧
              sv hnm (maskOp (Om s) (Hm s)) ⟨0, Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn⟩
                  / (sigma * Real.sqrt (m : ℝ))
                ≤ Real.sqrt p * (1 + Real.sqrt (rho m n) + C * deltaM m)}
          ≥ ENNReal.ofReal (1 - c * Real.rpow (n : ℝ) (-4 : ℝ)) := by
  /- @proof-region region.target-node.session.dc48f4cff39dc673 begin -/
  intro K rhoMin hK hrhoMin alpha0 halpha0 CR cR hCR hcR m0att hRig
  refine ⟨CR, cR, hCR, hcR, ?_⟩
  intro p sigma n m γ
  intro Ωs _ μ _
  intro Om Hm
  intro hm hn hnm hp hp1 hrhoMinm hrhom hsigma hlog hγ
  intro hOmm hOmb hOmp hmeas hint hmean hsqint hsq htail hind
  set Xi : Ωs → Matrix (Fin m) (Fin n) ℝ := fun s i j => Hm s i j / sigma with hXi
  have hmeasXi : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Xi s i j := by
    intro i j
    simpa only [hXi] using (hmeas i j).div_const sigma
  have hintXi : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => Xi s i j) μ := by
    intro i j
    simpa only [hXi] using (hint i j).div_const sigma
  have hmeanXi : ∀ (i : Fin m) (j : Fin n), ∫ s, Xi s i j ∂μ = 0 := by
    intro i j
    have hpoint : ∀ s : Ωs, Xi s i j = Hm s i j * sigma⁻¹ := by
      intro s
      change Hm s i j / sigma = Hm s i j * sigma⁻¹
      rw [div_eq_mul_inv]
    calc ∫ s, Xi s i j ∂μ = ∫ s, Hm s i j * sigma⁻¹ ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
      _ = (∫ s, Hm s i j ∂μ) * sigma⁻¹ := by rw [integral_mul_const]
      _ = 0 * sigma⁻¹ := by rw [hmean i j]
      _ = 0 := zero_mul _
  have hsqintXi : ∀ (i : Fin m) (j : Fin n), Integrable (fun s : Ωs => (Xi s i j) ^ 2) μ := by
    intro i j
    have hfun : (fun s : Ωs => (Xi s i j) ^ 2) = fun s => (Hm s i j) ^ 2 / sigma ^ 2 := by
      funext s
      change (Hm s i j / sigma) ^ 2 = (Hm s i j) ^ 2 / sigma ^ 2
      rw [div_pow]
    rw [hfun]
    exact (hsqint i j).div_const (sigma ^ 2)
  have hsqXi : ∀ (i : Fin m) (j : Fin n), ∫ s, (Xi s i j) ^ 2 ∂μ = 1 := by
    intro i j
    have hσ2 : sigma ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hsigma)
    have hpoint : ∀ s : Ωs, (Xi s i j) ^ 2 = (Hm s i j) ^ 2 * (sigma ^ 2)⁻¹ := by
      intro s
      change (Hm s i j / sigma) ^ 2 = (Hm s i j) ^ 2 * (sigma ^ 2)⁻¹
      rw [div_pow, div_eq_mul_inv]
    calc ∫ s, (Xi s i j) ^ 2 ∂μ = ∫ s, (Hm s i j) ^ 2 * (sigma ^ 2)⁻¹ ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
      _ = (∫ s, (Hm s i j) ^ 2 ∂μ) * (sigma ^ 2)⁻¹ := by rw [integral_mul_const]
      _ = sigma ^ 2 * (sigma ^ 2)⁻¹ := by rw [hsq i j]
      _ = 1 := by rw [mul_inv_cancel₀ hσ2]
  have htailXi : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
      μ {s : Ωs | t < |Xi s i j|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / K))) := by
    intro i j t ht
    have hset : {s : Ωs | t < |Xi s i j|} = {s : Ωs | t * sigma < |Hm s i j|} := by
      ext s
      simp only [Set.mem_setOf_eq]
      change (t < |Hm s i j / sigma| ↔ t * sigma < |Hm s i j|)
      rw [abs_div, abs_of_pos hsigma]
      exact lt_div_iff₀ hsigma
    rw [hset]
    exact htail i j t ht
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have happ :=
    hRig m n hnm hn0 p γ hp hp1 hrhoMinm hrhom hm hlog hγ μ Om Xi hOmm hOmb hOmp
      hmeasXi hintXi hmeanXi hsqintXi hsqXi htailXi (by
        have hg : ∀ x : (Fin m × Fin n) ⊕ (Fin m × Fin n),
            Measurable (fun y : ℝ => match x with
              | Sum.inl _ => y
              | Sum.inr _ => y / sigma) := by
          rintro (q | q) <;> simp only
          · exact measurable_id
          · exact measurable_id.div_const sigma
        convert iIndepFun.comp hind
          (fun (x : (Fin m × Fin n) ⊕ (Fin m × Fin n)) (y : ℝ) => match x with
            | Sum.inl _ => y
            | Sum.inr _ => y / sigma) hg using 1
        funext x s
        cases x with
        | inl q => rfl
        | inr q => rfl)
  obtain ⟨hBadle, hEdge⟩ := happ
  have hmaskid : ∀ (s : Ωs),
      maskOp (Om s) (Xi s) = fun a b => sigma⁻¹ * maskOp (Om s) (Hm s) a b := by
    intro s
    funext a b
    show Om s a b * Xi s a b = sigma⁻¹ * (Om s a b * Hm s a b)
    change Om s a b * (Hm s a b / sigma) = sigma⁻¹ * (Om s a b * Hm s a b)
    rw [div_eq_mul_inv]
    ring
  have hsvXi : ∀ (s : Ωs) (i : Fin n),
      sv hnm (maskOp (Om s) (Xi s)) i = sigma⁻¹ * sv hnm (maskOp (Om s) (Hm s)) i := by
    intro s i
    have hc : (0 : ℝ) ≤ sigma⁻¹ := inv_nonneg.mpr (le_of_lt hsigma)
    simpa only [hmaskid s] using
      statopia_math_node_3402644224_aa9fa448 m n hnm (sigma⁻¹) hc (maskOp (Om s) (Hm s)) i
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) (le_trans hn hnm)
  have hmp : Real.sqrt ((m : ℝ) * p) = Real.sqrt (m : ℝ) * Real.sqrt p :=
    Real.sqrt_mul (Nat.cast_nonneg m) p
  have hkey : ∀ (s : Ωs) (i : Fin n),
      sv hnm (maskOp (Om s) (Hm s)) i / (sigma * Real.sqrt (m : ℝ)) - Real.sqrt p * γ i
        = Real.sqrt p *
          (sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i) := by
    intro s i
    rw [hsvXi s i, hmp]
    have hσ : sigma ≠ 0 := ne_of_gt hsigma
    have hsm : Real.sqrt (m : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hmpos))
    have hsp : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
    have h1 : sigma * Real.sqrt (m : ℝ) ≠ 0 := mul_ne_zero hσ hsm
    have h2 : Real.sqrt (m : ℝ) * Real.sqrt p ≠ 0 := mul_ne_zero hsm hsp
    field_simp
  have htopkey : ∀ (s : Ωs),
      sv hnm (maskOp (Om s) (Hm s)) ⟨0, hn0⟩ / (sigma * Real.sqrt (m : ℝ))
        = Real.sqrt p *
          (sv hnm (maskOp (Om s) (Xi s)) ⟨0, hn0⟩ / Real.sqrt ((m : ℝ) * p)) := by
    intro s
    rw [hsvXi s ⟨0, hn0⟩, hmp]
    have hσ : sigma ≠ 0 := ne_of_gt hsigma
    have hsm : Real.sqrt (m : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hmpos))
    have hsp : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
    have h1 : sigma * Real.sqrt (m : ℝ) ≠ 0 := mul_ne_zero hσ hsm
    have h2 : Real.sqrt (m : ℝ) * Real.sqrt p ≠ 0 := mul_ne_zero hsm hsp
    field_simp
  set B : Set Ωs := {s : Ωs | ∃ i : Fin n,
      CR * deltaM m
        < |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|} with hB
  have hBle : μ B ≤ ENNReal.ofReal (cR * Real.rpow (n : ℝ) (-4 : ℝ)) := by
    rw [hB]
    exact hBadle
  have hsvmeasi : ∀ i : Fin n, Measurable fun s : Ωs =>
      sv hnm (maskOp (Om s) (Xi s)) i := by
    intro i
    exact statopia_math_node_1703810688_a15f7ece m n hnm
      (fun s => maskOp (Om s) (Xi s))
      (fun i j => by
        simpa only [maskOp] using (hOmm i j).mul (hmeasXi i j)) i
  have hBmeas : MeasurableSet B := by
    rw [hB]
    have hset : {s : Ωs | ∃ i : Fin n,
          CR * deltaM m
            < |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|}
        = ⋃ i : Fin n, {s : Ωs |
            CR * deltaM m
              < |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|} := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [hset]
    refine MeasurableSet.iUnion (fun i => ?_)
    exact measurableSet_lt measurable_const
      (((hsvmeasi i).div_const (Real.sqrt ((m : ℝ) * p))).sub measurable_const).abs
  set G : Set Ωs := {s : Ωs |
      (∀ i : Fin n,
        |sv hnm (maskOp (Om s) (Hm s)) i / (sigma * Real.sqrt (m : ℝ))
          - Real.sqrt p * γ i| ≤ CR * Real.sqrt p * deltaM m) ∧
      sv hnm (maskOp (Om s) (Hm s))
          ⟨0, Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn⟩
        / (sigma * Real.sqrt (m : ℝ))
        ≤ Real.sqrt p * (1 + Real.sqrt (rho m n) + CR * deltaM m)} with hG
  have hBG : Bᶜ ⊆ G := by
    intro s hne
    have hbad : s ∉ {s : Ωs | ∃ i : Fin n,
        CR * deltaM m
          < |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|} := by
      rw [← hB]
      exact hne
    have hne' : ∀ i : Fin n,
        |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|
          ≤ CR * deltaM m := by
      intro i
      exact not_lt.mp (fun hlt => hbad ⟨i, hlt⟩)
    rw [hG]
    simp only [Set.mem_setOf_eq]
    refine ⟨fun i => ?_, ?_⟩
    · have h1i := hkey s i
      rw [h1i, abs_mul, abs_of_nonneg (le_of_lt (Real.sqrt_pos.2 hp))]
      calc Real.sqrt p *
            |sv hnm (maskOp (Om s) (Xi s)) i / Real.sqrt ((m : ℝ) * p) - γ i|
          ≤ Real.sqrt p * (CR * deltaM m) :=
            mul_le_mul_of_nonneg_left (hne' i) (le_of_lt (Real.sqrt_pos.2 hp))
        _ = CR * Real.sqrt p * deltaM m := by ring
    · calc sv hnm (maskOp (Om s) (Hm s))
            ⟨0, Nat.lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn⟩
            / (sigma * Real.sqrt (m : ℝ))
          = Real.sqrt p *
              (sv hnm (maskOp (Om s) (Xi s))
                ⟨0, Nat.lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn⟩
                / Real.sqrt ((m : ℝ) * p)) := htopkey s
        _ ≤ Real.sqrt p * (1 + Real.sqrt (rho m n) + CR * deltaM m) :=
            mul_le_mul_of_nonneg_left (hEdge s hbad) (le_of_lt (Real.sqrt_pos.2 hp))
  have hn4 : (0 : ℝ) ≤ cR * Real.rpow (n : ℝ) (-4 : ℝ) :=
    mul_nonneg (le_of_lt hcR) (Real.rpow_nonneg (Nat.cast_nonneg n) (-4))
  show ENNReal.ofReal (1 - cR * Real.rpow (n : ℝ) (-4 : ℝ)) ≤ μ G
  calc ENNReal.ofReal (1 - cR * Real.rpow (n : ℝ) (-4 : ℝ))
      = 1 - ENNReal.ofReal (cR * Real.rpow (n : ℝ) (-4 : ℝ)) := by
        rw [ENNReal.ofReal_sub 1 (q := cR * Real.rpow (n : ℝ) (-4 : ℝ)) hn4,
          ENNReal.ofReal_one]
    _ ≤ 1 - μ B := tsub_le_tsub_left hBle 1
    _ = μ Bᶜ := by
        rw [measure_compl hBmeas (measure_ne_top μ B), measure_univ]
    _ ≤ μ G := measure_mono hBG
  /- @proof-region region.target-node.session.dc48f4cff39dc673 end -/

end ResidualLoss20261106.Statlib.Imported

end

#print axioms ResidualLoss20261106.Statlib.Imported.ideal_noise_from_actual_rigidity

