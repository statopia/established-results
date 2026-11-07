import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_1960475459_46432c8a_a4a43fe7
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_283558168_72fffefb_dab35fce
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_3988397096_0cdbf9e6_62406218

namespace PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5



open scoped BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported

noncomputable section
open scoped BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2201401131_f578e354 : ∀ (p : ℕ) (hp : 0 < p) (beta : ℝ) (hbeta : 0 < beta)
    (phi : ℝ) (hphi : 0 < phi) (y : Fin p → ℝ)
    (phi0 : ℝ → ℝ) (hphi0 : ContDiff ℝ 3 phi0)
    (d1 d2 d3 : ℝ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (hbound : ∀ u : ℝ,
      |iteratedDeriv 1 phi0 u| ≤ d1 ∧ |iteratedDeriv 2 phi0 u| ≤ d2 ∧
        |iteratedDeriv 3 phi0 u| ≤ d3)
    (hgbound : ∀ t : ℝ,
      |iteratedDeriv 1 (fun s : ℝ => phi0 (phi * s)) t| ≤ phi ^ (1 : ℕ) * d1 ∧
        |iteratedDeriv 2 (fun s : ℝ => phi0 (phi * s)) t| ≤ phi ^ (2 : ℕ) * d2 ∧
          |iteratedDeriv 3 (fun s : ℝ => phi0 (phi * s)) t| ≤ phi ^ (3 : ℕ) * d3)
    (j k l : Fin p) (w : Fin p → ℝ),
    let Z : ℝ := ∑ m : Fin p, Real.exp (beta * (w m - y m))
    let pi : Fin p → ℝ := fun i => Real.exp (beta * (w i - y i)) / Z
    let W : Fin p → Fin p → ℝ := fun a b =>
      pi a * (if a = b then (1 : ℝ) else 0) + pi a * pi b
    let P : ℝ := pi j * (if j = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)
      + pi j * pi l * (if j = k then (1 : ℝ) else 0)
      + pi j * pi k * (if j = l then (1 : ℝ) else 0)
      + pi j * pi k * (if k = l then (1 : ℝ) else 0)
      + 2 * pi j * pi k * pi l
    let Q : ℝ := phi ^ 3 * d3 * pi j * pi k * pi l
      + phi ^ 2 * d2 * beta * (W j k * pi l + W j l * pi k + W k l * pi j)
      + phi * d1 * beta ^ 2 * P
    0 ≤ Q ∧
      |(iteratedFDeriv ℝ 3
          (fun v : Fin p → ℝ =>
            phi0 (phi * (beta⁻¹ * Real.log (∑ m : Fin p, Real.exp (beta * (v m - y m))))))
          w) (fun i : Fin 3 => Pi.single (![j, k, l] i) (1 : ℝ))| ≤ Q := by
  /- @proof-region region.target-node.session.5bd8359d5f91fab9 begin -/
  intro p hp beta hbeta phi hphi y phi0 hphi0 d1 d2 d3 hd1 hd2 hd3 hbound hgbound j k l w
  obtain ⟨_hC3kap, hformula⟩ :=
    statopia_math_node_3988397096_0cdbf9e6 p hp beta hbeta phi hphi y phi0 hphi0
  obtain ⟨_hC3F, hsw⟩ := statopia_math_node_283558168_72fffefb p hp beta hbeta y
  obtain ⟨_hZpos, hpipos, _hsum, _hfderiv⟩ := hsw w
  dsimp only
  set djk : ℝ := if j = k then (1:ℝ) else 0 with hdjkdef
  set djl : ℝ := if j = l then (1:ℝ) else 0 with hdjldef
  set dkl : ℝ := if k = l then (1:ℝ) else 0 with hdkldef
  set Z : ℝ := ∑ m : Fin p, Real.exp (beta * (w m - y m)) with hZdef
  set pj : ℝ := Real.exp (beta * (w j - y j)) / Z with hpjdef
  set pk : ℝ := Real.exp (beta * (w k - y k)) / Z with hpkdef
  set pl : ℝ := Real.exp (beta * (w l - y l)) / Z with hpldef
  set Wbr : ℝ := (pj * djk + pj * pk) * pl + (pj * djl + pj * pl) * pk + (pk * dkl + pk * pl) * pj with hWbrdef
  set Pq : ℝ := pj * djl * djk + pj * pl * djk + pj * pk * djl + pj * pk * dkl + 2 * pj * pk * pl with hPqdef
  have hpjpos : 0 < pj := by rw [hpjdef, hZdef]; exact hpipos j
  have hpkpos : 0 < pk := by rw [hpkdef, hZdef]; exact hpipos k
  have hplpos : 0 < pl := by rw [hpldef, hZdef]; exact hpipos l
  have hdjk : (0:ℝ) ≤ djk := by rw [hdjkdef]; by_cases h : j = k <;> simp [h]
  have hdjl : (0:ℝ) ≤ djl := by rw [hdjldef]; by_cases h : j = l <;> simp [h]
  have hdkl : (0:ℝ) ≤ dkl := by rw [hdkldef]; by_cases h : k = l <;> simp [h]
  have hformula_apply :
      (iteratedFDeriv ℝ 3
          (fun v : Fin p → ℝ =>
            phi0 (phi * (beta⁻¹ * Real.log (∑ m : Fin p, Real.exp (beta * (v m - y m))))))
          w) (fun i : Fin 3 => Pi.single (![j, k, l] i) (1 : ℝ))
        = iteratedDeriv 3 (fun t : ℝ => phi0 (phi * t)) (beta⁻¹ * Real.log Z) * pj * pk * pl
          + iteratedDeriv 2 (fun t : ℝ => phi0 (phi * t)) (beta⁻¹ * Real.log Z) * beta
              * (pj * pk * (djl - pl) + pj * pk * (dkl - pl) + pl * (pj * djk - pj * pk))
          + deriv (fun t : ℝ => phi0 (phi * t)) (beta⁻¹ * Real.log Z) * beta ^ 2
              * (pj * djk * djl - pj * pl * djk - pj * pk * djl - pj * pk * dkl + 2 * pj * pk * pl) := by
    have h := hformula w j k l
    simpa [Fbeta, hdjkdef, hdjldef, hdkldef, hZdef, hpjdef, hpkdef, hpldef] using h
  rw [hformula_apply]
  set Fw : ℝ := beta⁻¹ * Real.log Z with hFwdef
  set A3 : ℝ := iteratedDeriv 3 (fun t : ℝ => phi0 (phi * t)) Fw with hA3def
  set A2 : ℝ := iteratedDeriv 2 (fun t : ℝ => phi0 (phi * t)) Fw with hA2def
  set A1 : ℝ := deriv (fun t : ℝ => phi0 (phi * t)) Fw with hA1def
  set X2 : ℝ := pj * pk * (djl - pl) + pj * pk * (dkl - pl) + pl * (pj * djk - pj * pk) with hX2def
  set X1 : ℝ := pj * djk * djl - pj * pl * djk - pj * pk * djl - pj * pk * dkl + 2 * pj * pk * pl with hX1def
  have hA3 : |A3| ≤ phi ^ 3 * d3 := by rw [hA3def]; exact (hgbound Fw).2.2
  have hA2 : |A2| ≤ phi ^ 2 * d2 := by rw [hA2def]; exact (hgbound Fw).2.1
  have hA1 : |A1| ≤ phi * d1 := by
    rw [hA1def, ← iteratedDeriv_one]
    simpa [pow_one] using (hgbound Fw).1
  have hWbr : 0 ≤ Wbr := by
    rw [hWbrdef]
    have u1 : (0:ℝ) ≤ (pj * djk + pj * pk) * pl :=
      mul_nonneg (add_nonneg (mul_nonneg hpjpos.le hdjk) (mul_nonneg hpjpos.le hpkpos.le)) hplpos.le
    have u2 : (0:ℝ) ≤ (pj * djl + pj * pl) * pk :=
      mul_nonneg (add_nonneg (mul_nonneg hpjpos.le hdjl) (mul_nonneg hpjpos.le hplpos.le)) hpkpos.le
    have u3 : (0:ℝ) ≤ (pk * dkl + pk * pl) * pj :=
      mul_nonneg (add_nonneg (mul_nonneg hpkpos.le hdkl) (mul_nonneg hpkpos.le hplpos.le)) hpjpos.le
    linarith
  have hPq : 0 ≤ Pq := by
    rw [hPqdef]
    have t1 : (0:ℝ) ≤ pj * djl * djk := mul_nonneg (mul_nonneg hpjpos.le hdjl) hdjk
    have t2 : (0:ℝ) ≤ pj * pl * djk := mul_nonneg (mul_nonneg hpjpos.le hplpos.le) hdjk
    have t3 : (0:ℝ) ≤ pj * pk * djl := mul_nonneg (mul_nonneg hpjpos.le hpkpos.le) hdjl
    have t4 : (0:ℝ) ≤ pj * pk * dkl := mul_nonneg (mul_nonneg hpjpos.le hpkpos.le) hdkl
    have t5 : (0:ℝ) ≤ 2 * pj * pk * pl :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hpjpos.le) hpkpos.le) hplpos.le
    linarith
  constructor
  · have b1 : (0:ℝ) ≤ phi ^ 3 * d3 * pj * pk * pl :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hphi.le 3) hd3) hpjpos.le) hpkpos.le) hplpos.le
    have b2 : (0:ℝ) ≤ phi ^ 2 * d2 * beta * Wbr :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hphi.le 2) hd2) hbeta.le) hWbr
    have b3 : (0:ℝ) ≤ phi * d1 * beta ^ 2 * Pq :=
      mul_nonneg (mul_nonneg (mul_nonneg hphi.le hd1) (pow_nonneg hbeta.le 2)) hPq
    exact add_nonneg (add_nonneg b1 b2) b3
  · have hdjl_abs : |djl - pl| ≤ djl + pl := by rw [abs_le]; constructor <;> linarith [hdjl, hplpos.le]
    have hdkl_abs : |dkl - pl| ≤ dkl + pl := by rw [abs_le]; constructor <;> linarith [hdkl, hplpos.le]
    have hdjk_abs : |djk - pk| ≤ djk + pk := by rw [abs_le]; constructor <;> linarith [hdjk, hpkpos.le]
    have ht1 : |pj * pk * (djl - pl)| ≤ pj * pk * (djl + pl) := by
      simp only [abs_mul]
      rw [abs_of_pos hpjpos, abs_of_pos hpkpos]
      exact mul_le_mul_of_nonneg_left hdjl_abs (mul_nonneg hpjpos.le hpkpos.le)
    have ht2 : |pj * pk * (dkl - pl)| ≤ pj * pk * (dkl + pl) := by
      simp only [abs_mul]
      rw [abs_of_pos hpjpos, abs_of_pos hpkpos]
      exact mul_le_mul_of_nonneg_left hdkl_abs (mul_nonneg hpjpos.le hpkpos.le)
    have ht3 : |pl * (pj * djk - pj * pk)| ≤ pl * (pj * djk + pj * pk) := by
      have hfac : pj * djk - pj * pk = pj * (djk - pk) := by ring
      rw [hfac]
      simp only [abs_mul]
      rw [abs_of_pos hplpos, abs_of_pos hpjpos]
      have hinner : pj * |djk - pk| ≤ pj * djk + pj * pk := by
        have hh := mul_le_mul_of_nonneg_left hdjk_abs hpjpos.le
        have he : pj * (djk + pk) = pj * djk + pj * pk := by ring
        rw [he] at hh
        exact hh
      exact mul_le_mul_of_nonneg_left hinner hplpos.le
    have hX2 : |X2| ≤ Wbr := by
      rw [hX2def, hWbrdef]
      have htri : |pj * pk * (djl - pl) + pj * pk * (dkl - pl) + pl * (pj * djk - pj * pk)|
          ≤ |pj * pk * (djl - pl)| + |pj * pk * (dkl - pl)| + |pl * (pj * djk - pj * pk)| := by
        have h1 := abs_add_le (pj * pk * (djl - pl) + pj * pk * (dkl - pl)) (pl * (pj * djk - pj * pk))
        have h2 := abs_add_le (pj * pk * (djl - pl)) (pj * pk * (dkl - pl))
        linarith
      have hsum : |pj * pk * (djl - pl)| + |pj * pk * (dkl - pl)| + |pl * (pj * djk - pj * pk)|
          ≤ (pj * djk + pj * pk) * pl + (pj * djl + pj * pl) * pk + (pk * dkl + pk * pl) * pj := by
        have heq : pj * pk * (djl + pl) + pj * pk * (dkl + pl) + pl * (pj * djk + pj * pk)
            = (pj * djk + pj * pk) * pl + (pj * djl + pj * pl) * pk + (pk * dkl + pk * pl) * pj := by ring
        linarith [ht1, ht2, ht3, heq]
      linarith [htri, hsum]
    have hT3 : |A3 * pj * pk * pl| ≤ phi ^ 3 * d3 * pj * pk * pl := by
      simp only [abs_mul]
      rw [abs_of_pos hpjpos, abs_of_pos hpkpos, abs_of_pos hplpos]
      have s1 : |A3| * pj ≤ (phi ^ 3 * d3) * pj := mul_le_mul_of_nonneg_right hA3 hpjpos.le
      have s2 : |A3| * pj * pk ≤ (phi ^ 3 * d3) * pj * pk := mul_le_mul_of_nonneg_right s1 hpkpos.le
      have s3 : |A3| * pj * pk * pl ≤ (phi ^ 3 * d3) * pj * pk * pl := mul_le_mul_of_nonneg_right s2 hplpos.le
      exact s3
    have hT2 : |A2 * beta * X2| ≤ phi ^ 2 * d2 * beta * Wbr := by
      rw [abs_mul, abs_mul, abs_of_pos hbeta]
      have hb2 : (0:ℝ) ≤ phi ^ 2 * d2 := mul_nonneg (pow_nonneg hphi.le 2) hd2
      have step1 : |A2| * |X2| ≤ (phi ^ 2 * d2) * Wbr := mul_le_mul hA2 hX2 (abs_nonneg X2) hb2
      calc |A2| * beta * |X2| = (|A2| * |X2|) * beta := by ring
        _ ≤ ((phi ^ 2 * d2) * Wbr) * beta := mul_le_mul_of_nonneg_right step1 hbeta.le
        _ = phi ^ 2 * d2 * beta * Wbr := by ring
    have hX1 : |X1| ≤ Pq := by
      rw [abs_le]
      constructor
      · have hkey : (0:ℝ) ≤ X1 + Pq := by
          have hid : X1 + Pq = pj * djk * djl + pj * djl * djk + 4 * (pj * pk * pl) := by
            rw [hX1def, hPqdef]; ring
          rw [hid]
          have e1 : (0:ℝ) ≤ pj * djk * djl := mul_nonneg (mul_nonneg hpjpos.le hdjk) hdjl
          have e2 : (0:ℝ) ≤ pj * djl * djk := mul_nonneg (mul_nonneg hpjpos.le hdjl) hdjk
          have e3 : (0:ℝ) ≤ pj * pk * pl := mul_nonneg (mul_nonneg hpjpos.le hpkpos.le) hplpos.le
          linarith
        linarith [hkey]
      · have hkey : (0:ℝ) ≤ Pq - X1 := by
          have hid : Pq - X1 = 2 * (pj * pl * djk) + 2 * (pj * pk * djl) + 2 * (pj * pk * dkl) := by
            rw [hX1def, hPqdef]; ring
          rw [hid]
          have e1 : (0:ℝ) ≤ pj * pl * djk := mul_nonneg (mul_nonneg hpjpos.le hplpos.le) hdjk
          have e2 : (0:ℝ) ≤ pj * pk * djl := mul_nonneg (mul_nonneg hpjpos.le hpkpos.le) hdjl
          have e3 : (0:ℝ) ≤ pj * pk * dkl := mul_nonneg (mul_nonneg hpjpos.le hpkpos.le) hdkl
          linarith
        linarith [hkey]
    have hT1 : |A1 * beta ^ 2 * X1| ≤ phi * d1 * beta ^ 2 * Pq := by
      rw [abs_mul, abs_mul, abs_of_pos (pow_pos hbeta 2)]
      have hb1 : (0:ℝ) ≤ phi * d1 := mul_nonneg hphi.le hd1
      have step1 : |A1| * |X1| ≤ (phi * d1) * Pq := mul_le_mul hA1 hX1 (abs_nonneg X1) hb1
      calc |A1| * beta ^ 2 * |X1| = (|A1| * |X1|) * beta ^ 2 := by ring
        _ ≤ ((phi * d1) * Pq) * beta ^ 2 := mul_le_mul_of_nonneg_right step1 (pow_nonneg hbeta.le 2)
        _ = phi * d1 * beta ^ 2 * Pq := by ring
    have htri : |A3 * pj * pk * pl + A2 * beta * X2 + A1 * beta ^ 2 * X1|
        ≤ |A3 * pj * pk * pl| + |A2 * beta * X2| + |A1 * beta ^ 2 * X1| := by
      have h1 := abs_add_le (A3 * pj * pk * pl + A2 * beta * X2) (A1 * beta ^ 2 * X1)
      have h2 := abs_add_le (A3 * pj * pk * pl) (A2 * beta * X2)
      linarith
    linarith [htri, hT3, hT2, hT1]
  /- @proof-region region.target-node.session.5bd8359d5f91fab9 end -/

end Statlib.Imported
end

