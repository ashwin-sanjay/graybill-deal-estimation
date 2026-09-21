import GD.Module1763
import GD.Module1774
import GD.Module0383











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open MeasureTheory Set Filter Topology
open scoped FourierTransform BigOperators

namespace GD.N0106.N0428.N0765.N1517
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1652 _root_.GD.N0106.N0428.N0765.N1653
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1550
open _root_.GD.N0106.N0428.N0765.N1595 _root_.GD.N0106.N0428.N0765.N1594 _root_.GD.N0106.N0428.N0765.N1593
open _root_.GD.N0106.N0428.N0765.N1587 _root_.GD.N0106.N0428.N0765.N1602 _root_.GD.N0106.N0428.N0765.N1589
open _root_.GD.N0106.N0428.N0765.N1601



theorem d029364 {e dA dB : ℝ} (he : 0 ≤ e)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ) / 2) * (dA + dB) < Real.pi) (xi nu : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) xi nu‖ ≤
      (∫ p : ℝ × ℝ,
        ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e (if 0 ≤ xi then -dA else dA) (if 0 ≤ nu then -dB else dB) p‖) *
        Real.exp (-2 * Real.pi * dA * |xi|) * Real.exp (-2 * Real.pi * dB * |nu|) := by
  let α : ℝ := if 0 ≤ xi then -dA else dA
  let β : ℝ := if 0 ≤ nu then -dB else dB
  have hα : |α| ≤ dA := by simp only [α]; split <;> simp [abs_of_nonneg hdA]
  have hβ : |β| ≤ dB := by simp only [β]; split <;> simp [abs_of_nonneg hdB]
  have hphase : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi := by unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; nlinarith
  have hf : ∀ z : ℂ, |z.im| ≤ dA → DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 nu) z := by
    intro z hz
    apply (_root_.GD.N0106.N0428.N0765.N1595.d029339 he ?_).2.differentiableAt
    change ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 z.im 0 < Real.pi
    simp only [_root_.GD.N0106.N0428.N0765.N1538.d021192, abs_zero, add_zero]
    nlinarith
  obtain ⟨C, hC⟩ := _root_.GD.N0106.N0428.N0765.N1593.d029345 hdA hdB hd
  have hint := _root_.GD.N0106.N0428.N0765.N1593.d029346 he hdA hdB hd nu
  have hFourier := _root_.GD.N0106.N0428.N0765.N1550.d005490 (f := _root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 nu) (AL := C) (AR := C)
    hdA hf (hint 0 (by simpa using hdA))
    (hint (-dA) (by simp only [abs_neg, abs_of_nonneg hdA, le_refl]))
    (hint dA (by simp only [abs_of_nonneg hdA, le_refl]))
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 10)
    (by intro z hz hx; simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx] using hC e he nu z hz)
    (by
      intro z hz hx
      by_cases heq : z.re = 0
      · simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, heq, le_refl, if_true, mul_zero, Real.exp_zero, mul_one] using hC e he nu z hz
      · have hp : ¬ z.re ≤ 0 := not_le.mpr (lt_of_le_of_ne hx (Ne.symm heq))
        simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_neg hp] using hC e he nu z hz) xi
  have hi := _root_.GD.N0106.N0428.N0765.N1537.d021550 he hphase
  have hB : (∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 nu) α x‖) ≤
      Real.exp (-2 * Real.pi * dB * |nu|) * ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β p‖ := by
    calc (∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 nu) α x‖)
        ≤ ∫ x : ℝ, Real.exp (-2 * Real.pi * dB * |nu|) * ∫ y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β (x, y)‖ := by
          apply integral_mono_ae (hint α hα).norm (hi.integral_norm_prod_left.const_mul _)
          exact Filter.Eventually.of_forall fun x => by
            simpa only [_root_.GD.N0106.N0428.N0765.N1593.d029344, _root_.GD.N0106.N0428.N0765.N1537.d021525, _root_.GD.N0106.N0428.N0765.N1537.d021526, β] using
              _root_.GD.N0106.N0428.N0765.N1594.d029343 he hdA hdB hd
                (z := _root_.GD.N0106.N0428.N0765.N1537.d021524 x α) (by simpa only [_root_.GD.N0106.N0428.N0765.N1537.d021526] using hα) nu
      _ = _ := by
        rw [integral_const_mul, ← integral_prod _ hi.norm]
        rfl
  have h := hFourier.trans (mul_le_mul_of_nonneg_left hB (Real.exp_nonneg _))
  have hfun : _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 nu) 0 =
      fun x : ℝ => 𝓕 (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 (x, y)) nu := by
    funext x
    rw [_root_.GD.N0106.N0428.N0765.N1593.d029344, _root_.GD.N0106.N0428.N0765.N1594.d029340]
    simp only [_root_.GD.N0106.N0428.N0765.N1537.d021525, _root_.GD.N0106.N0428.N0765.N1537.d021526]
  rw [hfun] at h
  change ‖𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 (x, y)) nu) xi‖ ≤ _
  simpa only [α, β, mul_assoc, mul_left_comm, mul_comm] using h

def d029365 (eta : ℝ) : ℝ := (1 + eta) / 11 * (eta⁻¹) ^ 2

theorem d029366 {eta : ℝ} (heta : 0 < eta) : 0 < _root_.GD.N0106.N0428.N0765.N1517.d029365 eta := by
  unfold _root_.GD.N0106.N0428.N0765.N1517.d029365
  positivity

private theorem d029367 : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 0 0 < Real.pi := by
  simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos

theorem d029368 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β =
      fun p => _root_.GD.N0106.N0428.N0765.N1517.d029365 eta • _root_.GD.N0106.N0428.N0765.N1537.d021532 eta⁻¹ α β p := by
  funext p
  simpa only [_root_.GD.N0106.N0428.N0765.N1517.d029365, Complex.real_smul] using
    _root_.GD.N0106.N0428.N0765.N1516.d029241 heta hs p

theorem d029369 (f : ℝ × ℝ → ℂ) (r nu a : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005816 (fun p => r • f p) nu a = r • _root_.GD.N0106.N0428.N0765.N1652.d005816 f nu a :=
  _root_.GD.N0106.N0428.N0765.N1652.d005821 (fun b => f (a, b)) r nu

theorem d029370 (f : ℝ × ℝ → ℂ) (r xi nu : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (fun p => r • f p) xi nu = r • _root_.GD.N0106.N0428.N0765.N1652.d005817 f xi nu := by
  unfold _root_.GD.N0106.N0428.N0765.N1652.d005817 _root_.GD.N0106.N0428.N0765.N1652.d005816
  simp only [_root_.GD.N0106.N0428.N0765.N1652.d005821]

theorem d029371 (f : ℝ × ℝ → ℂ) (r h : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005822 (fun p => r • f p) h = fun p => r • _root_.GD.N0106.N0428.N0765.N1652.d005822 f h p := rfl

theorem d029372 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ p, ‖_root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β p‖) =
      _root_.GD.N0106.N0428.N0765.N1517.d029365 eta * ∫ p, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 eta⁻¹ α β p‖ := by
  rw [_root_.GD.N0106.N0428.N0765.N1517.d029368 heta hs]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (_root_.GD.N0106.N0428.N0765.N1517.d029366 heta)]
  exact integral_const_mul _ _


theorem d029373 (eta dA dB xi nu : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029223 eta (if 0 ≤ xi then -dA else dA) (if 0 ≤ nu then -dB else dB) =
      _root_.GD.N0106.N0428.N0765.N1516.d029223 eta dA dB := by
  split_ifs <;> simp only [_root_.GD.N0106.N0428.N0765.N1516.d029223, _root_.GD.N0106.N0428.N0765.N1516.d029221,
    _root_.GD.N0106.N0428.N0765.N1512.d029183, _root_.GD.N0106.N0428.N0765.N1538.d021231, _root_.GD.N0106.N0428.N0765.N1538.d021192, abs_neg, neg_div, Real.cos_neg]



theorem d029374 {eta dA dB : ℝ} (heta : 0 < eta)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ) / 2) * (dA + dB) < Real.pi) (xi nu : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0) xi nu‖ ≤
      _root_.GD.N0106.N0428.N0765.N1516.d029223 eta dA dB * Real.exp (-2 * Real.pi * dA * |xi|) *
        Real.exp (-2 * Real.pi * dB * |nu|) := by
  let α : ℝ := if 0 ≤ xi then -dA else dA
  let β : ℝ := if 0 ≤ nu then -dB else dB
  have hα : |α| ≤ dA := by simp only [α]; split <;> simp [abs_of_nonneg hdA]
  have hβ : |β| ≤ dB := by simp only [β]; split <;> simp [abs_of_nonneg hdB]
  have hphase : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi := by unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; nlinarith
  have hB := _root_.GD.N0106.N0428.N0765.N1516.d029233 heta hphase
  rw [_root_.GD.N0106.N0428.N0765.N1517.d029372 heta hphase] at hB
  have hW := _root_.GD.N0106.N0428.N0765.N1517.d029364 (inv_pos.mpr heta).le hdA hdB hd xi nu
  rw [_root_.GD.N0106.N0428.N0765.N1517.d029368 heta _root_.GD.N0106.N0428.N0765.N1517.d029367, _root_.GD.N0106.N0428.N0765.N1517.d029370,
    norm_smul, Real.norm_eq_abs, abs_of_pos (_root_.GD.N0106.N0428.N0765.N1517.d029366 heta)]
  calc
    _ ≤ _root_.GD.N0106.N0428.N0765.N1517.d029365 eta * ((∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 eta⁻¹ α β p‖) *
        Real.exp (-2 * Real.pi * dA * |xi|) * Real.exp (-2 * Real.pi * dB * |nu|)) :=
      mul_le_mul_of_nonneg_left hW (_root_.GD.N0106.N0428.N0765.N1517.d029366 heta).le
    _ = (_root_.GD.N0106.N0428.N0765.N1517.d029365 eta * ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 eta⁻¹ α β p‖) *
        Real.exp (-2 * Real.pi * dA * |xi|) * Real.exp (-2 * Real.pi * dB * |nu|) := by ring
    _ ≤ _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β * Real.exp (-2 * Real.pi * dA * |xi|) *
        Real.exp (-2 * Real.pi * dB * |nu|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = _ := by rw [show _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β = _root_.GD.N0106.N0428.N0765.N1516.d029223 eta dA dB from
        _root_.GD.N0106.N0428.N0765.N1517.d029373 eta dA dB xi nu]


theorem d029375 {eta h d : ℝ} (heta : 0 < eta) (hh : 0 < h)
    (hd : 0 < d) (hstrip : ((21 : ℝ) / 2) * d < Real.pi) (a : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0) h (a, b)) := by
  rw [_root_.GD.N0106.N0428.N0765.N1517.d029368 heta _root_.GD.N0106.N0428.N0765.N1517.d029367, _root_.GD.N0106.N0428.N0765.N1517.d029371]
  exact _root_.GD.N0106.N0428.N0765.N1601.d029268 (_root_.GD.N0106.N0428.N0765.N1601.d029270
    (_root_.GD.N0106.N0428.N0765.N1601.d029269 (_root_.GD.N0106.N0428.N0765.N1597.d029354 (inv_pos.mpr heta).le hd hstrip (h * a)) hh)
      (_root_.GD.N0106.N0428.N0765.N1517.d029365 eta))

theorem d029376 {eta h d : ℝ} (heta : 0 < eta) (hh : 0 < h)
    (hd : 0 < d) (hstrip : ((21 : ℝ) / 2) * (d + d) < Real.pi) (n : ℤ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0) h) n) := by
  have heq : _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0) h) n =
      fun a : ℝ => _root_.GD.N0106.N0428.N0765.N1517.d029365 eta •
        (h⁻¹ • _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1537.d021532 eta⁻¹ 0 0) (n / h) (h * a)) := by
    funext a
    rw [_root_.GD.N0106.N0428.N0765.N1517.d029368 heta _root_.GD.N0106.N0428.N0765.N1517.d029367, _root_.GD.N0106.N0428.N0765.N1517.d029371,
      _root_.GD.N0106.N0428.N0765.N1517.d029369, _root_.GD.N0106.N0428.N0765.N1652.d005823 _ hh]
  rw [heq]
  exact _root_.GD.N0106.N0428.N0765.N1601.d029268 (_root_.GD.N0106.N0428.N0765.N1601.d029270
    (_root_.GD.N0106.N0428.N0765.N1601.d029270 (_root_.GD.N0106.N0428.N0765.N1601.d029269
      (_root_.GD.N0106.N0428.N0765.N1597.d029355 (inv_pos.mpr heta).le hd hstrip (n / h)) hh) h⁻¹)
        (_root_.GD.N0106.N0428.N0765.N1517.d029365 eta))

theorem d029377 {eta h : ℝ} (heta : 0 < eta) (hh : 0 < h) (x y : ℝ) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0 (x + h * p.1, y + h * p.2)) := by
  rw [_root_.GD.N0106.N0428.N0765.N1517.d029368 heta _root_.GD.N0106.N0428.N0765.N1517.d029367]
  exact (_root_.GD.N0106.N0428.N0765.N1596.d029360 (inv_pos.mpr heta).le hh x y).const_smul (_root_.GD.N0106.N0428.N0765.N1517.d029365 eta)

theorem d029378 {eta h : ℝ} (heta : 0 < eta) (hh : 0 < h) (x y : ℝ) :
    Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0) h (x / h + p.1, y / h + p.2)) := by
  rw [_root_.GD.N0106.N0428.N0765.N1517.d029368 heta _root_.GD.N0106.N0428.N0765.N1517.d029367, _root_.GD.N0106.N0428.N0765.N1517.d029371]
  exact (_root_.GD.N0106.N0428.N0765.N1596.d029361 (inv_pos.mpr heta).le hh x y).const_smul
    (_root_.GD.N0106.N0428.N0765.N1517.d029365 eta)

theorem d029379 {eta h d : ℝ} (heta : 0 < eta) (hh : 0 < h)
    (hd : 0 < d) (hstrip : ((21 : ℝ) / 2) * d < Real.pi) (x : ℝ) :
    Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0) h) p.2 (x / h + p.1)) := by
  rw [_root_.GD.N0106.N0428.N0765.N1517.d029368 heta _root_.GD.N0106.N0428.N0765.N1517.d029367, _root_.GD.N0106.N0428.N0765.N1517.d029371]
  simp only [_root_.GD.N0106.N0428.N0765.N1517.d029369]
  exact (_root_.GD.N0106.N0428.N0765.N1596.d029362 (inv_pos.mpr heta).le hh hd hstrip x).const_smul
    (_root_.GD.N0106.N0428.N0765.N1517.d029365 eta)

theorem d029380 {eta h d : ℝ} (heta : 0 < eta) (hh : 0 < h)
    (hd : 0 < d) (hstrip : ((21 : ℝ) / 2) * (d + d) < Real.pi) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0) h) p.1 p.2) := by
  rw [_root_.GD.N0106.N0428.N0765.N1517.d029368 heta _root_.GD.N0106.N0428.N0765.N1517.d029367, _root_.GD.N0106.N0428.N0765.N1517.d029371]
  simp only [_root_.GD.N0106.N0428.N0765.N1517.d029370]
  exact (_root_.GD.N0106.N0428.N0765.N1596.d029363 (inv_pos.mpr heta).le hh hd hstrip).const_smul
    (_root_.GD.N0106.N0428.N0765.N1517.d029365 eta)



theorem d029381 {eta h d : ℝ} (heta : 0 < eta) (hh : 0 < h)
    (hd : 0 < d) (hstrip : ((21 : ℝ) / 2) * (d + d) < Real.pi) (x y : ℝ) :
    h ^ 2 • (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0 (x + h * p.1, y + h * p.2)) =
      ∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0) (p.1 / h) (p.2 / h) *
        fourier p.1 ((x / h : ℝ) : UnitAddCircle) * fourier p.2 ((y / h : ℝ) : UnitAddCircle) := by
  have hsmall : ((21 : ℝ) / 2) * d < Real.pi := by nlinarith
  exact _root_.GD.N0106.N0428.N0765.N1652.d005826 hh (_root_.GD.N0106.N0428.N0765.N1517.d029375 heta hh hd hsmall)
    (_root_.GD.N0106.N0428.N0765.N1517.d029376 heta hh hd hstrip) x y (_root_.GD.N0106.N0428.N0765.N1517.d029378 heta hh x y)
      (_root_.GD.N0106.N0428.N0765.N1517.d029379 heta hh hd hsmall x) (_root_.GD.N0106.N0428.N0765.N1517.d029380 heta hh hd hstrip)



theorem d029382 (location : ℝ) {eta h d0 d1 : ℝ}
    (heta : 0 < eta) (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ) / 2) * d0 < Real.pi)
    (hmixed : ((21 : ℝ) / 2) * (d1 + d1) < Real.pi) (x y : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1627.d021120 location eta -
      h ^ 2 * (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1516.d029220 eta (x + h * p.1, y + h * p.2))| ≤
      (2 * _root_.GD.N0106.N0428.N0765.N1516.d029223 eta d0 0 + 2 * _root_.GD.N0106.N0428.N0765.N1516.d029223 eta 0 d0) /
        (Real.exp (2 * Real.pi * d0 / h) - 1) +
      4 * _root_.GD.N0106.N0428.N0765.N1516.d029223 eta d1 d1 / (Real.exp (2 * Real.pi * d1 / h) - 1) ^ 2 := by
  have heq : (fun p : ℝ × ℝ => (_root_.GD.N0106.N0428.N0765.N1516.d029220 eta p : ℂ)) =
      _root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0 := by
    funext p
    exact (_root_.GD.N0106.N0428.N0765.N1516.d029238 heta p).symm
  have hi : Integrable (_root_.GD.N0106.N0428.N0765.N1516.d029220 eta) :=
    (_root_.GD.N0106.N0428.N0765.N1521.d020876 eta heta).const_mul _
  have hint : (∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1516.d029220 eta (a, b)) =
      _root_.GD.N0106.N0428.N0765.N1627.d021120 location eta := by
    rw [← integral_prod _ hi, ← Measure.volume_eq_prod,
      _root_.GD.N0106.N0428.N0765.N1516.d029239 location heta]
  rw [← hint]
  have hsmall : ((21 : ℝ) / 2) * d1 < Real.pi := by nlinarith
  refine _root_.GD.N0106.N0428.N0765.N1653.d005827 hh hd0 hd1 ?_ ?_ x y ?_ ?_ ?_ ?_ ?_ ?_
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1517.d029375 heta hh hd1 hsmall
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1517.d029376 heta hh hd1 hmixed
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1517.d029378 heta hh x y
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1517.d029379 heta hh hd1 hsmall x
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1517.d029380 heta hh hd1 hmixed
  · intro m _
    rw [heq]
    have hb := _root_.GD.N0106.N0428.N0765.N1517.d029374 heta hd0.le (le_refl (0 : ℝ))
      (by simpa only [add_zero] using haxis) (m / h) 0
    simpa only [mul_zero, zero_mul, Real.exp_zero, mul_one,
      _root_.GD.N0106.N0428.N0765.N1596.d029356 hh] using hb
  · intro n _
    rw [heq]
    have hb := _root_.GD.N0106.N0428.N0765.N1517.d029374 heta (le_refl (0 : ℝ)) hd0.le
      (by simpa only [zero_add] using haxis) 0 (n / h)
    simpa only [mul_zero, zero_mul, Real.exp_zero, mul_one,
      _root_.GD.N0106.N0428.N0765.N1596.d029356 hh] using hb
  · intro m n _ _
    rw [heq]
    simpa only [_root_.GD.N0106.N0428.N0765.N1596.d029356 hh] using
      _root_.GD.N0106.N0428.N0765.N1517.d029374 heta hd1.le hd1.le hmixed (m / h) (n / h)

end
end GD.N0106.N0428.N0765.N1517

#print axioms _root_.GD.N0106.N0428.N0765.N1517.d029364
#print axioms _root_.GD.N0106.N0428.N0765.N1517.d029374
#print axioms _root_.GD.N0106.N0428.N0765.N1517.d029375
#print axioms _root_.GD.N0106.N0428.N0765.N1517.d029376
#print axioms _root_.GD.N0106.N0428.N0765.N1517.d029378
#print axioms _root_.GD.N0106.N0428.N0765.N1517.d029379
#print axioms _root_.GD.N0106.N0428.N0765.N1517.d029380
#print axioms _root_.GD.N0106.N0428.N0765.N1517.d029381
#print axioms _root_.GD.N0106.N0428.N0765.N1517.d029382
