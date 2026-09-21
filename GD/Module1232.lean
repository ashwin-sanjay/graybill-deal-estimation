import GD.Module0214
import GD.Module1231
import GD.Module0197
import GD.Module1230




open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0232.N0720.N1321

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1329
open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1331
open _root_.GD.N0232.N0720.N1324 _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1376 _root_.GD.N0232.N0720.N1297

noncomputable section

variable {I : Type*} [Fintype I]

def d020059 (d : ℕ) (p : I → _root_.GD.N0232.N0720.N1315.d019832) (weight : I → ℝ) (x : _root_.GD.N0232.N0720.N1315.d019833) : ℝ :=
  (∑ i, weight i * _root_.GD.N0232.N0720.N1315.d019849 d (p i) x) / (∑ i, weight i * _root_.GD.N0232.N0720.N1315.d019848 d (p i) x)

def d020060 (p : _root_.GD.N0232.N0720.N1315.d019832) : _root_.GD.N0232.N0720.N1315.d019832 := (-p.1, p.2)

def d020061 (x : _root_.GD.N0232.N0720.N1315.d019833) : _root_.GD.N0232.N0720.N1315.d019833 := ![-x 0, -x 1, x 2, x 3]

theorem d020062 (d : ℕ) (p : _root_.GD.N0232.N0720.N1315.d019832) (x : _root_.GD.N0232.N0720.N1315.d019833) :
    _root_.GD.N0232.N0720.N1315.d019848 d (_root_.GD.N0232.N0720.N1321.d020060 p) x = _root_.GD.N0232.N0720.N1315.d019848 d p (_root_.GD.N0232.N0720.N1321.d020061 x) := by
  have hA : _root_.GD.N0232.N0720.N1376.d002892 p.2.1 (-x 0) (-x 1) (x 2) (x 3) =
      _root_.GD.N0232.N0720.N1376.d002892 p.2.1 (x 0) (x 1) (x 2) (x 3) := by simp only [_root_.GD.N0232.N0720.N1376.d002892, neg_sq]
  have hB : _root_.GD.N0232.N0720.N1376.d002893 p.2.1 (-x 0) (-x 1) * p.1 =
      _root_.GD.N0232.N0720.N1376.d002893 p.2.1 (x 0) (x 1) * (-p.1) := by unfold _root_.GD.N0232.N0720.N1376.d002893; ring
  change _root_.GD.N0232.N0720.N1377.d002852 (d + 2) (_root_.GD.N0232.N0720.N1376.d002892 p.2.1 (x 0) (x 1) (x 2) (x 3))
      (_root_.GD.N0232.N0720.N1376.d002893 p.2.1 (x 0) (x 1) * (-p.1)) =
    _root_.GD.N0232.N0720.N1377.d002852 (d + 2) (_root_.GD.N0232.N0720.N1376.d002892 p.2.1 (-x 0) (-x 1) (x 2) (x 3))
      (_root_.GD.N0232.N0720.N1376.d002893 p.2.1 (-x 0) (-x 1) * p.1)
  rw [hA, hB]

theorem d020063 (d : ℕ) (p : _root_.GD.N0232.N0720.N1315.d019832) (x : _root_.GD.N0232.N0720.N1315.d019833) :
    _root_.GD.N0232.N0720.N1315.d019849 d (_root_.GD.N0232.N0720.N1321.d020060 p) x = -_root_.GD.N0232.N0720.N1315.d019849 d p (_root_.GD.N0232.N0720.N1321.d020061 x) := by
  have hA : _root_.GD.N0232.N0720.N1376.d002892 p.2.1 (-x 0) (-x 1) (x 2) (x 3) =
      _root_.GD.N0232.N0720.N1376.d002892 p.2.1 (x 0) (x 1) (x 2) (x 3) := by simp only [_root_.GD.N0232.N0720.N1376.d002892, neg_sq]
  have hB : _root_.GD.N0232.N0720.N1376.d002893 p.2.1 (-x 0) (-x 1) * p.1 =
      _root_.GD.N0232.N0720.N1376.d002893 p.2.1 (x 0) (x 1) * (-p.1) := by unfold _root_.GD.N0232.N0720.N1376.d002893; ring
  change (-p.1) * _root_.GD.N0232.N0720.N1377.d002852 (d + 1)
      (_root_.GD.N0232.N0720.N1376.d002892 p.2.1 (x 0) (x 1) (x 2) (x 3))
      (_root_.GD.N0232.N0720.N1376.d002893 p.2.1 (x 0) (x 1) * (-p.1)) =
    -(p.1 * _root_.GD.N0232.N0720.N1377.d002852 (d + 1)
      (_root_.GD.N0232.N0720.N1376.d002892 p.2.1 (-x 0) (-x 1) (x 2) (x 3))
      (_root_.GD.N0232.N0720.N1376.d002893 p.2.1 (-x 0) (-x 1) * p.1))
  rw [hA, hB, neg_mul]

theorem d020064 (d : ℕ) (p : I → _root_.GD.N0232.N0720.N1315.d019832) (weight : I → ℝ) (x : _root_.GD.N0232.N0720.N1315.d019833) :
    _root_.GD.N0232.N0720.N1321.d020059 d (fun i ↦ _root_.GD.N0232.N0720.N1321.d020060 (p i)) weight x = -_root_.GD.N0232.N0720.N1321.d020059 d p weight (_root_.GD.N0232.N0720.N1321.d020061 x) := by
  simp only [_root_.GD.N0232.N0720.N1321.d020059, _root_.GD.N0232.N0720.N1321.d020062, _root_.GD.N0232.N0720.N1321.d020063,
    mul_neg, Finset.sum_neg_distrib, neg_div]

private theorem d020065 {m : ℕ} (x : _root_.GD.N0137.d008894 m) :
    _root_.GD.N0107.d009084 (-x) = -_root_.GD.N0107.d009084 x := by
  simp [_root_.GD.N0107.d009084, _root_.GD.N0126.d006420,
    Finset.sum_neg_distrib, neg_div]

private theorem d020066 {m : ℕ} (x : _root_.GD.N0137.d008894 m) :
    _root_.GD.N0126.d006422 (-x) = _root_.GD.N0126.d006422 x := by
  have hm : _root_.GD.N0126.d006420 (-x) = -_root_.GD.N0126.d006420 x := by
    simp [_root_.GD.N0126.d006420, Finset.sum_neg_distrib, neg_div]
  unfold _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
  rw [hm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.neg_apply]
  ring

theorem d020067 {m n d : ℕ} (hdim : m + n = d + 1) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1315.d019850 m n d hdim (-x) = _root_.GD.N0232.N0720.N1321.d020061 (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x) := by
  have hleft : ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm (-x)).1 = -((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).1 := by
    funext i
    rfl
  have hright : ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm (-x)).2 = -((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).2 := by
    funext i
    rfl
  unfold _root_.GD.N0232.N0720.N1315.d019850
  rw [hleft, hright]
  funext i
  fin_cases i <;> dsimp [_root_.GD.N0232.N0720.N1321.d020061] <;> simp only [_root_.GD.N0232.N0720.N1321.d020065, _root_.GD.N0232.N0720.N1321.d020066]

theorem d020068 (d : ℕ) (p : I → _root_.GD.N0232.N0720.N1315.d019832) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hprob : ∑ i, weight i = 1)
    {x : _root_.GD.N0232.N0720.N1315.d019833} (hz : 0 < x 2) (hw' : 0 < x 3) :
    0 < ∑ i, weight i * _root_.GD.N0232.N0720.N1315.d019848 d (p i) x := by
  have hp (i : I) : 0 < _root_.GD.N0232.N0720.N1315.d019848 d (p i) x :=
    _root_.GD.N0232.N0720.N1377.d002861 (d + 2) (_root_.GD.N0232.N0720.N1376.d002898 (p i).2.2 hz hw' (x 0) (x 1)) _
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hw i)).1
    (show 0 < ∑ i, weight i by rw [hprob]; norm_num)
  exact Finset.sum_pos' (fun i _ ↦ mul_nonneg (hw i) (hp i).le)
    ⟨j, Finset.mem_univ j, mul_pos hj (hp j)⟩

theorem d020069 (N : ℕ) {Amax Bmin delta : ℝ}
    (hBmin : 0 < Bmin) (hdelta : 0 < delta) :
    ∃ cutoff : ℝ, 1 ≤ cutoff ∧
      2 * (N : ℝ) * Amax ^ 2 ≤ delta * Bmin ^ 3 * cutoff ^ 2 := by
  let ratio : ℝ := 2 * (N : ℝ) * Amax ^ 2 / (delta * Bmin ^ 3)
  have hden : 0 < delta * Bmin ^ 3 := mul_pos hdelta (pow_pos hBmin _)
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  refine ⟨max 1 (Real.sqrt ratio), le_max_left _ _, ?_⟩
  have hs : ratio ≤ max 1 (Real.sqrt ratio) ^ 2 := by
    calc
      ratio = Real.sqrt ratio ^ 2 := (Real.sq_sqrt hratio).symm
      _ ≤ max 1 (Real.sqrt ratio) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg ratio) (le_max_right 1 _) 2
  have h := mul_le_mul_of_nonneg_left hs hden.le
  have hcancel : (delta * Bmin ^ 3) * ratio = 2 * (N : ℝ) * Amax ^ 2 := by
    dsimp [ratio]
    field_simp [hden.ne']
  rw [hcancel] at h
  exact h

theorem d020070 (d : ℕ) (hd : 1 ≤ d)
    (p : I → _root_.GD.N0232.N0720.N1315.d019832) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hprob : ∑ i, weight i = 1)
    {lo hi level delta beta cutoff : ℝ}
    (hlo : 0 < lo) (hbeta : 0 ≤ beta) (hdelta : 0 ≤ delta)
    (hlevel : hi ≤ level + delta) (hmargin : (level + delta - lo) * hi ≤ 1)
    (hrate : 2 * beta * (hi ^ 2 + 4) ≤ lo ^ 2) (hcutoff : 1 ≤ cutoff)
    (hthreshold : 2 * ((d + 1 : ℕ) : ℝ) * (hi ^ 2 + 4) ^ 2 ≤ delta * lo ^ 3 * cutoff ^ 2)
    {x : _root_.GD.N0232.N0720.N1315.d019833} (hx : x ∈ _root_.GD.N0232.N0720.N1331.d020050 lo hi)
    (hposterior : _root_.GD.N0232.N0720.N1321.d020059 d p weight x ≤ level) :
    (∑ i, weight i * (if cutoff ≤ (p i).1 then
      (delta / 2 * _root_.GD.N0232.N0720.N1324.d002946 (d + 1) (hi ^ 2 + 4) lo) *
        Real.exp (beta * (p i).1 ^ 2) else 0)) ≤
      ((d + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 d (lo ^ 2 + 1) (hi * cutoff) / lo := by
  have hparameters (i : I) := _root_.GD.N0232.N0720.N1331.d020056 (p i).2.2 hlo.le hx
  have hden := _root_.GD.N0232.N0720.N1321.d020068 d p weight hw hprob
    (by linarith [hx.2.2.1.1] : 0 < x 2) (by linarith [hx.2.2.2.1] : 0 < x 3)
  have h := _root_.GD.N0232.N0720.N1324.d002956 (d + 1) (by omega) weight
    (fun i ↦ _root_.GD.N0232.N0720.N1376.d002892 (p i).2.1 (x 0) (x 1) (x 2) (x 3))
    (fun i ↦ _root_.GD.N0232.N0720.N1376.d002893 (p i).2.1 (x 0) (x 1)) (fun i ↦ (p i).1)
    (by positivity) (fun i ↦ (hparameters i).2.1) (fun i ↦ (hparameters i).2.2)
    hlo (fun i ↦ (hparameters i).1.1) (fun i ↦ (hparameters i).1.2)
    hdelta hcutoff
    (fun i ↦ _root_.GD.N0232.N0720.N1331.d020057 (p i).2.2 hlo hx hlevel hmargin)
    (fun i ↦ _root_.GD.N0232.N0720.N1331.d020058 (p i).2.2 hlo hx hbeta hrate)
    hthreshold hw hprob
    (by simpa only [_root_.GD.N0232.N0720.N1315.d019848, Nat.add_assoc] using hden)
    (by simpa only [_root_.GD.N0232.N0720.N1321.d020059, _root_.GD.N0232.N0720.N1315.d019848, _root_.GD.N0232.N0720.N1315.d019849, Nat.add_assoc] using hposterior)
  simpa only [Nat.add_sub_cancel] using h

private theorem d020071 (p : I → _root_.GD.N0232.N0720.N1315.d019832) (weight : I → ℝ)
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

private theorem d020072 (f : ℕ → ℝ) {C : ℝ}
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

variable {Index : ℕ → Type*} [∀ j, Fintype (Index j)]

theorem d020073 {m n d : ℕ}
    (hdim : m + n = d + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p : ∀ j, Index j → _root_.GD.N0232.N0720.N1315.d019832) (weight : ∀ j, Index j → ℝ)
    (hw : ∀ j i, 0 ≤ weight j i) (hprob : ∀ j, ∑ i, weight j i = 1)
    (f : _root_.GD.N0232.N0720.N1341.d004414 d → ℝ)
    (hlim : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1321.d020059 d (p j) (weight j) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x))
        atTop (𝓝 (f x)))
    (hbetween : ∀ x, f x ≤ max (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0)
      (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1))
    {beta : ℝ} (hbeta : 0 ≤ beta) (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ c C cutoff : ℝ, 0 < c ∧ 1 ≤ cutoff ∧ ∀ᶠ j in atTop,
      (∑ i, weight j i * (if cutoff ≤ (p j i).1 then
        c * Real.exp (beta * (p j i).1 ^ 2) else 0)) ≤ C := by
  obtain ⟨lo, hi, level, delta, hlo, hwidth, hlevel, hdelta, hgap, hmargin, hrate⟩ :=
    _root_.GD.N0232.N0720.N1383.d004678 hbeta hhalf
  obtain ⟨cutoff, hcutoff, hthreshold⟩ :=
    _root_.GD.N0232.N0720.N1321.d020069 (d + 1) (Amax := hi ^ 2 + 4) hlo hdelta
  obtain ⟨x, hx, hxlim⟩ := _root_.GD.N0232.N0720.N1331.d020055 hdim hm hn hwidth hlim
  have hf : f x < level := by
    have hmax : max (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1) < hi :=
      max_lt hx.1.2 hx.2.1.2
    exact (hbetween x).trans_lt (hmax.trans hlevel)
  refine ⟨delta / 2 * _root_.GD.N0232.N0720.N1324.d002946 (d + 1) (hi ^ 2 + 4) lo,
    ((d + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 d (lo ^ 2 + 1) (hi * cutoff) / lo,
    cutoff, mul_pos (by positivity) (_root_.GD.N0232.N0720.N1324.d002947 _ (by positivity) hlo), hcutoff, ?_⟩
  filter_upwards [hxlim.eventually (gt_mem_nhds hf)] with j hj
  exact _root_.GD.N0232.N0720.N1321.d020070 d (by omega) (p j) (weight j) (hw j) (hprob j)
    hlo hbeta hdelta.le hgap hmargin hrate hcutoff hthreshold hx hj.le

theorem d020074 {m n d : ℕ}
    (hdim : m + n = d + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p : ∀ j, Index j → _root_.GD.N0232.N0720.N1315.d019832) (weight : ∀ j, Index j → ℝ)
    (hw : ∀ j i, 0 ≤ weight j i) (hprob : ∀ j, ∑ i, weight j i = 1)
    (f : _root_.GD.N0232.N0720.N1341.d004414 d → ℝ)
    (hlim : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1321.d020059 d (p j) (weight j) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x))
        atTop (𝓝 (f x)))
    (hbetween : ∀ x, min (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0)
      (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1) ≤ f x)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ c C cutoff : ℝ, 0 < c ∧ 1 ≤ cutoff ∧ ∀ᶠ j in atTop,
      (∑ i, weight j i * (if cutoff ≤ -(p j i).1 then
        c * Real.exp (beta * (p j i).1 ^ 2) else 0)) ≤ C := by
  have hreflect : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1321.d020059 d (p j) (weight j) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim (-x)))
        atTop (𝓝 (f (-x))) :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae hlim
  have hlim' : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1321.d020059 d (fun i ↦ _root_.GD.N0232.N0720.N1321.d020060 (p j i)) (weight j)
        (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x)) atTop (𝓝 (-f (-x))) := by
    filter_upwards [hreflect] with x hx
    simpa only [_root_.GD.N0232.N0720.N1321.d020064, ← _root_.GD.N0232.N0720.N1321.d020067 hdim] using! hx.neg
  have hbound (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
      -f (-x) ≤ max (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1) := by
    have h := neg_le_neg (hbetween (-x))
    rw [_root_.GD.N0232.N0720.N1321.d020067] at h
    dsimp [_root_.GD.N0232.N0720.N1321.d020061] at h
    by_cases hxy : _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0 ≤ _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1
    · rw [min_eq_right (neg_le_neg hxy)] at h
      rw [max_eq_right hxy]
      linarith
    · have hyx := le_of_not_ge hxy
      rw [min_eq_left (neg_le_neg hyx)] at h
      rw [max_eq_left hyx]
      linarith
  obtain ⟨c, C, cutoff, hc, hcutoff, hbudget⟩ := _root_.GD.N0232.N0720.N1321.d020073
    hdim hm hn (fun j i ↦ _root_.GD.N0232.N0720.N1321.d020060 (p j i)) weight hw hprob
    (fun x ↦ -f (-x)) hlim' hbound hbeta hhalf
  exact ⟨c, C, cutoff, hc, hcutoff, by simpa only [_root_.GD.N0232.N0720.N1321.d020060, neg_sq] using hbudget⟩

theorem d020075 {m n d : ℕ}
    (hdim : m + n = d + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p : ∀ j, Index j → _root_.GD.N0232.N0720.N1315.d019832) (weight : ∀ j, Index j → ℝ)
    (hw : ∀ j i, 0 ≤ weight j i) (hprob : ∀ j, ∑ i, weight j i = 1)
    (f : _root_.GD.N0232.N0720.N1341.d004414 d → ℝ)
    (hlim : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1321.d020059 d (p j) (weight j) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x))
        atTop (𝓝 (f x)))
    (hbetween : ∀ x, f x ∈ Icc (min (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1))
      (max (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1)))
    {beta : ℝ} (hbeta : 0 ≤ beta) (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ B : ℝ, ∀ j, (∑ i, weight j i * Real.exp (beta * (p j i).1 ^ 2)) ≤ B := by
  obtain ⟨cp, Cp, Rp, hcp, hRp, hp⟩ := _root_.GD.N0232.N0720.N1321.d020073
    hdim hm hn p weight hw hprob f hlim (fun x ↦ (hbetween x).2) hbeta hhalf
  obtain ⟨cn, Cn, Rn, hcn, hRn, hn'⟩ := _root_.GD.N0232.N0720.N1321.d020074
    hdim hm hn p weight hw hprob f hlim (fun x ↦ (hbetween x).1) hbeta hhalf
  apply _root_.GD.N0232.N0720.N1321.d020072
  filter_upwards [hp, hn'] with j hpj hnj
  exact _root_.GD.N0232.N0720.N1321.d020071 (p j) (weight j) (hw j) (hprob j)
    hbeta hcp hcn hRp hRn hpj hnj

theorem d020076 (p : I → _root_.GD.N0232.N0720.N1315.d019832) (weight : I → ℝ) (f : _root_.GD.N0232.N0720.N1315.d019832 → ℝ) :
    Integrable f (∑ i, ENNReal.ofReal (weight i) • Measure.dirac (p i)) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d020077 (p : I → _root_.GD.N0232.N0720.N1315.d019832) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (f : _root_.GD.N0232.N0720.N1315.d019832 → ℝ) :
    (∫ y, f y ∂(∑ i, ENNReal.ofReal (weight i) • Measure.dirac (p i))) =
      ∑ i, weight i * f (p i) := by
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d020078 {m n d : ℕ} (hdim : m + n = d + 1)
    (p : I → _root_.GD.N0232.N0720.N1315.d019832) (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1330.d020037 hdim
      (∑ i, ENNReal.ofReal (weight i) • Measure.dirac (p i)) x =
      _root_.GD.N0232.N0720.N1321.d020059 d p weight (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x) := by
  unfold _root_.GD.N0232.N0720.N1330.d020037 _root_.GD.N0232.N0720.N1321.d020059
  rw [_root_.GD.N0232.N0720.N1321.d020077 p weight hw, _root_.GD.N0232.N0720.N1321.d020077 p weight hw]



theorem d020079
    (m n d : ℕ) (hdim : m + n = d + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n δ) :
    ∃ (g : ℝ × ℝ → ℝ) (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1315.d019832),
      Measurable g ∧ (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        δ =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
          _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      (∀ beta : ℝ, 0 < beta → beta < 1 / 2 → ∃ B : ℝ, _root_.GD.N0232.N0720.N1297.d002706 ν beta B) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
        Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1330.d020037 hdim
          (ν j : Measure _root_.GD.N0232.N0720.N1315.d019832) x) atTop
            (𝓝 (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g x))) := by
  obtain ⟨g, ell, p, weight, ν, hg, hb, hrep, hw, hprob, hν, _hinterior, hlim, hbetween⟩ :=
    _root_.GD.N0232.N0720.N1330.d020041
      m n d hdim hm hn hd
  refine ⟨g, ν, hg, hb, hrep, ?_, hlim⟩
  intro beta hbeta hhalf
  have hlim' : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1321.d020059 d (p j) (weight j) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x)) atTop
        (𝓝 (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g x)) := by
    simpa only [hν, _root_.GD.N0232.N0720.N1321.d020078 _ _ _ (hw _)] using hlim
  obtain ⟨B, hB⟩ := _root_.GD.N0232.N0720.N1321.d020075 hdim hm hn p weight hw hprob
    (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g) hlim' hbetween hbeta.le hhalf
  refine ⟨B, ?_⟩
  intro j
  constructor
  · rw [hν]
    exact _root_.GD.N0232.N0720.N1321.d020076 (p j) (weight j) (_root_.GD.N0232.N0720.N1297.d002703 beta)
  · rw [hν, _root_.GD.N0232.N0720.N1321.d020077 (p j) (weight j) (hw j)]
    exact hB j

end
end GD.N0232.N0720.N1321

#print axioms _root_.GD.N0232.N0720.N1321.d020075
#print axioms _root_.GD.N0232.N0720.N1321.d020079
