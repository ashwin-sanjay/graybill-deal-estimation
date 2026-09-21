import GD.Module0314
import GD.Module0312





open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0232.N0720.N1384

open _root_.GD.N0232.N0720.N1377 _root_.GD.N0232.N0720.N1376
open _root_.GD.N0232.N0720.N1375 _root_.GD.N0232.N0720.N1385
open _root_.GD.N0232.N0720.N1383 _root_.GD.N0232.N0720.N1373

noncomputable section

variable {I : Type*} [Fintype I]

def d004684 (p : I → _root_.GD.N0232.N0720.N1373.d004629) (weight : I → ℝ) (x : _root_.GD.N0232.N0720.N1383.d004679) : ℝ :=
  (∑ i, weight i * _root_.GD.N0232.N0720.N1373.d004632 (p i) x) /
    (∑ i, weight i * _root_.GD.N0232.N0720.N1373.d004631 (p i) x)

def d004685 (p : _root_.GD.N0232.N0720.N1373.d004629) : _root_.GD.N0232.N0720.N1373.d004629 := (-p.1, p.2)

theorem d004686 (p : _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1383.d004679) :
    _root_.GD.N0232.N0720.N1373.d004631 (_root_.GD.N0232.N0720.N1384.d004685 p) x = _root_.GD.N0232.N0720.N1373.d004631 p (-x) := by
  have hA : _root_.GD.N0232.N0720.N1376.d002892 p.2.1 (-x 0) (-x 2) ((-x 1) ^ 2 / 2) ((-x 3) ^ 2 / 2) =
      _root_.GD.N0232.N0720.N1376.d002892 p.2.1 (x 0) (x 2) (x 1 ^ 2 / 2) (x 3 ^ 2 / 2) := by
    simp only [_root_.GD.N0232.N0720.N1376.d002892, neg_sq]
  have hB : _root_.GD.N0232.N0720.N1376.d002893 p.2.1 (-x 0) (-x 2) * p.1 =
      _root_.GD.N0232.N0720.N1376.d002893 p.2.1 (x 0) (x 2) * (-p.1) := by unfold _root_.GD.N0232.N0720.N1376.d002893; ring
  simp only [_root_.GD.N0232.N0720.N1373.d004631, _root_.GD.N0232.N0720.N1384.d004685, _root_.GD.N0232.N0720.N1376.d002894, PiLp.neg_apply, hA, hB]

theorem d004687 (p : _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1383.d004679) :
    _root_.GD.N0232.N0720.N1373.d004632 (_root_.GD.N0232.N0720.N1384.d004685 p) x = -_root_.GD.N0232.N0720.N1373.d004632 p (-x) := by
  have hA : _root_.GD.N0232.N0720.N1376.d002892 p.2.1 (-x 0) (-x 2) ((-x 1) ^ 2 / 2) ((-x 3) ^ 2 / 2) =
      _root_.GD.N0232.N0720.N1376.d002892 p.2.1 (x 0) (x 2) (x 1 ^ 2 / 2) (x 3 ^ 2 / 2) := by
    simp only [_root_.GD.N0232.N0720.N1376.d002892, neg_sq]
  have hB : _root_.GD.N0232.N0720.N1376.d002893 p.2.1 (-x 0) (-x 2) * p.1 =
      _root_.GD.N0232.N0720.N1376.d002893 p.2.1 (x 0) (x 2) * (-p.1) := by unfold _root_.GD.N0232.N0720.N1376.d002893; ring
  simp only [_root_.GD.N0232.N0720.N1373.d004632, _root_.GD.N0232.N0720.N1384.d004685, _root_.GD.N0232.N0720.N1376.d002895, PiLp.neg_apply, hA, hB,
    neg_mul, neg_div]

theorem d004688 (p : I → _root_.GD.N0232.N0720.N1373.d004629) (weight : I → ℝ)
    (x : _root_.GD.N0232.N0720.N1383.d004679) :
    _root_.GD.N0232.N0720.N1384.d004684 (fun i ↦ _root_.GD.N0232.N0720.N1384.d004685 (p i)) weight x = -_root_.GD.N0232.N0720.N1384.d004684 p weight (-x) := by
  simp only [_root_.GD.N0232.N0720.N1384.d004684, _root_.GD.N0232.N0720.N1384.d004686, _root_.GD.N0232.N0720.N1384.d004687,
    mul_neg, Finset.sum_neg_distrib, neg_div]

theorem d004689 (p : I → _root_.GD.N0232.N0720.N1373.d004629) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hprob : ∑ i, weight i = 1)
    {x : _root_.GD.N0232.N0720.N1383.d004679} (hR : x 1 ≠ 0) (hS : x 3 ≠ 0) :
    0 < ∑ i, weight i * _root_.GD.N0232.N0720.N1373.d004631 (p i) x := by
  have hp (i : I) : 0 < _root_.GD.N0232.N0720.N1373.d004631 (p i) x :=
    _root_.GD.N0232.N0720.N1376.d002900 _ (p i).2.2
      (div_pos (sq_pos_of_ne_zero hR) (by norm_num))
      (div_pos (sq_pos_of_ne_zero hS) (by norm_num)) _ _
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hw i)).1
    (show 0 < ∑ i, weight i by rw [hprob]; norm_num)
  exact Finset.sum_pos' (fun i _ ↦ mul_nonneg (hw i) (hp i).le)
    ⟨j, Finset.mem_univ j, mul_pos hj (hp j)⟩

theorem d004690 {Amax Bmin delta : ℝ}
    (hBmin : 0 < Bmin) (hdelta : 0 < delta) :
    ∃ cutoff : ℝ, 1 ≤ cutoff ∧
      8 * Amax ^ 2 ≤ delta * Bmin ^ 3 * cutoff ^ 2 := by
  let ratio : ℝ := 8 * Amax ^ 2 / (delta * Bmin ^ 3)
  have hden : 0 < delta * Bmin ^ 3 := mul_pos hdelta (pow_pos hBmin _)
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  refine ⟨max 1 (Real.sqrt ratio), le_max_left _ _, ?_⟩
  have hs : ratio ≤ max 1 (Real.sqrt ratio) ^ 2 := by
    calc
      ratio = Real.sqrt ratio ^ 2 := (Real.sq_sqrt hratio).symm
      _ ≤ max 1 (Real.sqrt ratio) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg ratio) (le_max_right 1 _) 2
  have h := mul_le_mul_of_nonneg_left hs hden.le
  have hcancel : (delta * Bmin ^ 3) * ratio = 8 * Amax ^ 2 := by
    dsimp [ratio]
    field_simp [hden.ne']
  rw [hcancel] at h
  exact h



theorem d004691 (p : I → _root_.GD.N0232.N0720.N1373.d004629) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hprob : ∑ i, weight i = 1)
    {lo hi level delta beta cutoff : ℝ}
    (hlo : 0 < lo) (hbeta : 0 ≤ beta) (hdelta : 0 ≤ delta)
    (hlevel : hi ≤ level + delta) (hmargin : (level + delta - lo) * hi ≤ 1)
    (hrate : 2 * beta * (hi ^ 2 + 4) ≤ lo ^ 2)
    (hcutoff : 1 ≤ cutoff)
    (hthreshold : 8 * (hi ^ 2 + 4) ^ 2 ≤ delta * lo ^ 3 * cutoff ^ 2)
    {x : _root_.GD.N0232.N0720.N1383.d004679} (hx : x ∈ _root_.GD.N0232.N0720.N1383.d004680 lo hi)
    (hposterior : _root_.GD.N0232.N0720.N1384.d004684 p weight x ≤ level) :
    (∑ i, weight i * (if cutoff ≤ (p i).1 then
      (delta / 2 * _root_.GD.N0232.N0720.N1375.d002935 (hi ^ 2 + 4) lo) *
        Real.exp (beta * (p i).1 ^ 2) else 0)) ≤
      _root_.GD.N0232.N0720.N1377.d002852 3 (lo ^ 2 + 1) (hi * cutoff) / (2 * lo) := by
  have hX := Ioo_subset_Icc_self hx.1
  have hY := Ioo_subset_Icc_self hx.2.1
  have hR := Ioo_subset_Icc_self hx.2.2.1
  have hS := Ioo_subset_Icc_self hx.2.2.2
  have hparameters (i : I) := _root_.GD.N0232.N0720.N1383.d004675 (p i).2.2 hlo.le hX hY hR hS
  have hden := _root_.GD.N0232.N0720.N1384.d004689 p weight hw hprob
    (by linarith [hx.2.2.1.1] : x 1 ≠ 0)
    (by linarith [hx.2.2.2.1] : x 3 ≠ 0)
  exact _root_.GD.N0232.N0720.N1385.d002944 weight
    (fun i ↦ _root_.GD.N0232.N0720.N1383.d004672 (p i).2.1 (x 0) (x 1) (x 2) (x 3))
    (fun i ↦ _root_.GD.N0232.N0720.N1376.d002893 (p i).2.1 (x 0) (x 2)) (fun i ↦ (p i).1)
    (by positivity) (fun i ↦ (hparameters i).2.1) (fun i ↦ (hparameters i).2.2)
    hlo (fun i ↦ (hparameters i).1.1) (fun i ↦ (hparameters i).1.2)
    hdelta hcutoff
    (fun i ↦ _root_.GD.N0232.N0720.N1383.d004676 (p i).2.2 hlo hX hY hR.1 hS.1 hlevel hmargin)
    (fun i ↦ _root_.GD.N0232.N0720.N1383.d004677 (p i).2.2 hlo hbeta hX hY hR hS hrate)
    hthreshold hw hprob hden hposterior

variable {Index : ℕ → Type*} [∀ n, Fintype (Index n)]

private theorem d004692 (p : I → _root_.GD.N0232.N0720.N1373.d004629) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hprob : ∑ i, weight i = 1)
    {beta cp cn Cp Cn Rp Rn : ℝ} (hbeta : 0 ≤ beta)
    (hcp : 0 < cp) (hcn : 0 < cn) (_hRp : 1 ≤ Rp) (_hRn : 1 ≤ Rn)
    (hp : (∑ i, weight i * (if Rp ≤ (p i).1 then
      cp * Real.exp (beta * (p i).1 ^ 2) else 0)) ≤ Cp)
    (hn : (∑ i, weight i * (if Rn ≤ -(p i).1 then
      cn * Real.exp (beta * (p i).1 ^ 2) else 0)) ≤ Cn) :
    (∑ i, weight i * Real.exp (beta * (p i).1 ^ 2)) ≤
      Cp / cp + Cn / cn + Real.exp (beta * (max Rp Rn) ^ 2) := by
  classical
  let P (i : I) : ℝ := if Rp ≤ (p i).1 then cp * Real.exp (beta * (p i).1 ^ 2) else 0
  let N (i : I) : ℝ := if Rn ≤ -(p i).1 then cn * Real.exp (beta * (p i).1 ^ 2) else 0
  let E : ℝ := Real.exp (beta * (max Rp Rn) ^ 2)
  have hP (i : I) : 0 ≤ P i := by dsimp [P]; split_ifs <;> positivity
  have hN (i : I) : 0 ≤ N i := by dsimp [N]; split_ifs <;> positivity
  have hpoint (i : I) : Real.exp (beta * (p i).1 ^ 2) ≤ P i / cp + N i / cn + E := by
    by_cases hpi : Rp ≤ (p i).1
    · have heq : P i / cp = Real.exp (beta * (p i).1 ^ 2) := by
        simp only [P, if_pos hpi, mul_div_cancel_left₀ _ hcp.ne']
      rw [heq]
      have hnn := div_nonneg (hN i) hcn.le
      have he : 0 ≤ E := (Real.exp_pos _).le
      linarith
    by_cases hni : Rn ≤ -(p i).1
    · have heq : N i / cn = Real.exp (beta * (p i).1 ^ 2) := by
        simp only [N, if_pos hni, mul_div_cancel_left₀ _ hcn.ne']
      rw [heq]
      have hpp := div_nonneg (hP i) hcp.le
      have he : 0 ≤ E := (Real.exp_pos _).le
      linarith
    have habs : |(p i).1| ≤ max Rp Rn := by
      apply abs_le.mpr
      constructor
      · have hleft := le_max_right Rp Rn
        linarith [lt_of_not_ge hni]
      · exact (le_of_not_ge hpi).trans (le_max_left _ _)
    have hsq : (p i).1 ^ 2 ≤ (max Rp Rn) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
    have he : Real.exp (beta * (p i).1 ^ 2) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq hbeta)
    exact he.trans (by linarith [div_nonneg (hP i) hcp.le, div_nonneg (hN i) hcn.le])
  calc
    (∑ i, weight i * Real.exp (beta * (p i).1 ^ 2)) ≤
        ∑ i, weight i * (P i / cp + N i / cn + E) :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hpoint i) (hw i))
    _ = (∑ i, weight i * P i) / cp + (∑ i, weight i * N i) / cn + E := by
      simp only [mul_add, ← mul_div_assoc, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.sum_mul, hprob, one_mul]
    _ ≤ _ := by
      simpa only [P, N, E, add_comm] using! add_le_add_right (add_le_add
        (div_le_div_of_nonneg_right hp hcp.le)
        (div_le_div_of_nonneg_right hn hcn.le)) E

private theorem d004693 (f : ℕ → ℝ) {C : ℝ}
    (h : ∀ᶠ n in atTop, f n ≤ C) : ∃ B : ℝ, ∀ n, f n ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max C (∑ j ∈ Finset.range N, |f j|), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_max_left _ _)
  · have hsingle : |f n| ≤ ∑ j ∈ Finset.range N, |f j| :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (f j))
        (Finset.mem_range.mpr (lt_of_not_ge hn))
    exact ((le_abs_self _).trans hsingle).trans (le_max_right _ _)



theorem d004694
    (p : ∀ n, Index n → _root_.GD.N0232.N0720.N1373.d004629) (weight : ∀ n, Index n → ℝ)
    (hw : ∀ n i, 0 ≤ weight n i) (hprob : ∀ n, ∑ i, weight n i = 1)
    (f : _root_.GD.N0232.N0720.N1383.d004679 → ℝ)
    (hlim : ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1383.d004679),
      Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1384.d004684 (p n) (weight n) x) atTop (𝓝 (f x)))
    (hbetween : ∀ x : _root_.GD.N0232.N0720.N1383.d004679, 0 < x 1 → 0 < x 3 → f x ≤ max (x 0) (x 2))
    {beta : ℝ} (hbeta : 0 ≤ beta) (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ c C cutoff : ℝ, 0 < c ∧ 1 ≤ cutoff ∧ ∀ᶠ n in atTop,
      (∑ i, weight n i * (if cutoff ≤ (p n i).1 then
        c * Real.exp (beta * (p n i).1 ^ 2) else 0)) ≤ C := by
  obtain ⟨lo, hi, level, delta, hlo, hwidth, hlevel, hdelta, hgap, hmargin, hrate⟩ :=
    _root_.GD.N0232.N0720.N1383.d004678 hbeta hhalf
  obtain ⟨cutoff, hcutoff, hthreshold⟩ :=
    _root_.GD.N0232.N0720.N1384.d004690 (Amax := hi ^ 2 + 4) hlo hdelta
  obtain ⟨x, hx, hxlim⟩ := _root_.GD.N0232.N0720.N1383.d004683 hwidth hlim
  have hf : f x < level := by
    have hb := hbetween x (by linarith [hx.2.2.1.1]) (by linarith [hx.2.2.2.1])
    have hm : max (x 0) (x 2) < hi := max_lt hx.1.2 hx.2.1.2
    exact hb.trans_lt (hm.trans hlevel)
  refine ⟨delta / 2 * _root_.GD.N0232.N0720.N1375.d002935 (hi ^ 2 + 4) lo,
    _root_.GD.N0232.N0720.N1377.d002852 3 (lo ^ 2 + 1) (hi * cutoff) / (2 * lo), cutoff,
    mul_pos (by positivity) (_root_.GD.N0232.N0720.N1375.d002936 (by positivity) hlo), hcutoff, ?_⟩
  filter_upwards [hxlim.eventually (gt_mem_nhds hf)] with n hn
  exact _root_.GD.N0232.N0720.N1384.d004691 (p n) (weight n) (hw n) (hprob n) hlo hbeta
    hdelta.le hgap hmargin hrate hcutoff hthreshold hx hn.le



theorem d004695
    (p : ∀ n, Index n → _root_.GD.N0232.N0720.N1373.d004629) (weight : ∀ n, Index n → ℝ)
    (hw : ∀ n i, 0 ≤ weight n i) (hprob : ∀ n, ∑ i, weight n i = 1)
    (f : _root_.GD.N0232.N0720.N1383.d004679 → ℝ)
    (hlim : ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1383.d004679),
      Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1384.d004684 (p n) (weight n) x) atTop (𝓝 (f x)))
    (hbetween : ∀ x : _root_.GD.N0232.N0720.N1383.d004679, min (x 0) (x 2) ≤ f x)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ c C cutoff : ℝ, 0 < c ∧ 1 ≤ cutoff ∧ ∀ᶠ n in atTop,
      (∑ i, weight n i * (if cutoff ≤ -(p n i).1 then
        c * Real.exp (beta * (p n i).1 ^ 2) else 0)) ≤ C := by
  have hreflect : ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1383.d004679),
      Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1384.d004684 (p n) (weight n) (-x)) atTop (𝓝 (f (-x))) :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae hlim
  have hlim' : ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1383.d004679),
      Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1384.d004684 (fun i ↦ _root_.GD.N0232.N0720.N1384.d004685 (p n i)) (weight n) x)
        atTop (𝓝 (-f (-x))) := by
    filter_upwards [hreflect] with x hx
    simpa only [_root_.GD.N0232.N0720.N1384.d004688] using hx.neg
  have hbound (x : _root_.GD.N0232.N0720.N1383.d004679) (_ : 0 < x 1) (_ : 0 < x 3) :
      -f (-x) ≤ max (x 0) (x 2) := by
    have h := neg_le_neg (hbetween (-x))
    simp only [PiLp.neg_apply] at h
    by_cases hxy : x 0 ≤ x 2
    · rw [min_eq_right (neg_le_neg hxy)] at h
      rw [max_eq_right hxy]
      linarith
    · have hyx := le_of_not_ge hxy
      rw [min_eq_left (neg_le_neg hyx)] at h
      rw [max_eq_left hyx]
      linarith
  obtain ⟨c, C, cutoff, hc, hcutoff, hbudget⟩ :=
    _root_.GD.N0232.N0720.N1384.d004694 (fun n i ↦ _root_.GD.N0232.N0720.N1384.d004685 (p n i))
      weight hw hprob (fun x ↦ -f (-x)) hlim' hbound hbeta hhalf
  exact ⟨c, C, cutoff, hc, hcutoff, by simpa only [_root_.GD.N0232.N0720.N1384.d004685, neg_sq] using hbudget⟩



theorem d004696
    (p : ∀ n, Index n → _root_.GD.N0232.N0720.N1373.d004629) (weight : ∀ n, Index n → ℝ)
    (hw : ∀ n i, 0 ≤ weight n i) (hprob : ∀ n, ∑ i, weight n i = 1)
    (f : _root_.GD.N0232.N0720.N1383.d004679 → ℝ)
    (hlim : ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1383.d004679),
      Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1384.d004684 (p n) (weight n) x) atTop (𝓝 (f x)))
    (hbetween : ∀ x : _root_.GD.N0232.N0720.N1383.d004679, f x ∈ Icc (min (x 0) (x 2)) (max (x 0) (x 2)))
    {beta : ℝ} (hbeta : 0 ≤ beta) (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ B : ℝ, ∀ n, (∑ i, weight n i * Real.exp (beta * (p n i).1 ^ 2)) ≤ B := by
  obtain ⟨cp, Cp, Rp, hcp, hRp, hp⟩ := _root_.GD.N0232.N0720.N1384.d004694
    p weight hw hprob f hlim (fun x _ _ ↦ (hbetween x).2) hbeta hhalf
  obtain ⟨cn, Cn, Rn, hcn, hRn, hn⟩ := _root_.GD.N0232.N0720.N1384.d004695
    p weight hw hprob f hlim (fun x ↦ (hbetween x).1) hbeta hhalf
  apply _root_.GD.N0232.N0720.N1384.d004693
  filter_upwards [hp, hn] with n hpn hnn
  exact _root_.GD.N0232.N0720.N1384.d004692 (p n) (weight n) (hw n) (hprob n)
    hbeta hcp hcn hRp hRn hpn hnn

end
end GD.N0232.N0720.N1384
