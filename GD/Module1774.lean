import GD.Module1765
import GD.Module1766
import GD.Module1773



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Set Filter Topology
open scoped FourierTransform
namespace GD.N0106.N0428.N0765.N1596
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1652 _root_.GD.N0106.N0428.N0765.N1587 _root_.GD.N0106.N0428.N0765.N1590 _root_.GD.N0106.N0428.N0765.N1597
open _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1601

theorem d029356 {h : ℝ} (hh : 0 < h) (d x : ℝ) :
    -2*Real.pi*d*|x/h| = -(2*Real.pi*d/h)*|x| := by
  rw [abs_div, abs_of_pos hh]
  ring

theorem d029357 {h : ℝ} (hh : 0 < h) (x n : ℝ) :
    h*(x/h+n) = x+h*n := by field_simp [hh.ne']

theorem d029358 {e h d : ℝ} (he : 0 ≤ e) (hh : 0 < h)
    (hd : 0 < d) (hstrip : ((21 : ℝ)/2)*d < Real.pi) (a : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) h (a,b)) :=
  _root_.GD.N0106.N0428.N0765.N1601.d029268 (_root_.GD.N0106.N0428.N0765.N1601.d029269 (_root_.GD.N0106.N0428.N0765.N1597.d029354 he hd hstrip (h*a)) hh)

theorem d029359 {e h d : ℝ} (he : 0 ≤ e) (hh : 0 < h)
    (hd : 0 < d) (hstrip : ((21 : ℝ)/2)*(d+d) < Real.pi) (n : ℤ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) h) n) := by
  have heq : _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) h) n =
      fun a : ℝ => h⁻¹ • _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) (n/h) (h*a) := by
    funext a
    exact _root_.GD.N0106.N0428.N0765.N1652.d005823 _ hh _ _
  rw [heq]
  exact _root_.GD.N0106.N0428.N0765.N1601.d029268 (_root_.GD.N0106.N0428.N0765.N1601.d029270 (_root_.GD.N0106.N0428.N0765.N1601.d029269 (_root_.GD.N0106.N0428.N0765.N1597.d029355 he hd hstrip (n/h)) hh) (h⁻¹))

theorem d029360 {e h : ℝ} (he : 0 ≤ e) (hh : 0 < h) (x y : ℝ) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 (x+h*p.1,y+h*p.2)) := by
  have hp : ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 0 0 < Real.pi := by simp [_root_.GD.N0106.N0428.N0765.N1538.d021192, Real.pi_pos]
  apply _root_.GD.N0106.N0428.N0765.N1652.d005819
    ((_root_.GD.N0106.N0428.N0765.N1590.d029266 (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (0 : ℝ) < 10) hh x).mul_left (_root_.GD.N0106.N0428.N0765.N1587.d029259 0 0))
    (_root_.GD.N0106.N0428.N0765.N1590.d029266 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 3) hh y)
  · intro n; exact mul_nonneg (_root_.GD.N0106.N0428.N0765.N1587.d029260 hp).le (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le
  · intro n; exact (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le
  · intro p; exact _root_.GD.N0106.N0428.N0765.N1587.d029262 he hp _ _

theorem d029361 {e h : ℝ} (he : 0 ≤ e) (hh : 0 < h) (x y : ℝ) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) h (x/h+p.1,y/h+p.2)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1652.d005822, _root_.GD.N0106.N0428.N0765.N1596.d029357 hh] using _root_.GD.N0106.N0428.N0765.N1596.d029360 he hh x y

theorem d029362 {e h d : ℝ} (he : 0 ≤ e) (hh : 0 < h)
    (hd : 0 < d) (hstrip : ((21 : ℝ)/2)*d < Real.pi) (x : ℝ) :
    Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) h) p.2 (x/h+p.1)) := by
  obtain ⟨C,hC,hbound⟩ := _root_.GD.N0106.N0428.N0765.N1597.d029353 hd.le hstrip
  have hk : 0 < 2*Real.pi*d/h := by positivity
  apply _root_.GD.N0106.N0428.N0765.N1652.d005819
    ((_root_.GD.N0106.N0428.N0765.N1590.d029266 (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (0 : ℝ) < 10) hh x).mul_left (h⁻¹*C))
    (_root_.GD.N0106.N0428.N0765.N1590.d029265 hk)
  · intro n; exact mul_nonneg (mul_nonneg (inv_pos.mpr hh).le hC) (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le
  · intro n; exact (Real.exp_pos _).le
  · intro p
    rw [_root_.GD.N0106.N0428.N0765.N1652.d005823 _ hh, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hh), _root_.GD.N0106.N0428.N0765.N1596.d029357 hh]
    have hb := mul_le_mul_of_nonneg_left (hbound e he (x+h*p.1) (p.2/h)) (inv_pos.mpr hh).le
    rw [_root_.GD.N0106.N0428.N0765.N1596.d029356 hh d (p.2 : ℝ)] at hb
    simpa only [mul_assoc] using hb

theorem d029363 {e h d : ℝ} (he : 0 ≤ e) (hh : 0 < h)
    (hd : 0 < d) (hstrip : ((21 : ℝ)/2)*(d+d) < Real.pi) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) h) p.1 p.2) := by
  have hk : 0 < 2*Real.pi*d/h := by positivity
  let C : ℝ := |h⁻¹*h⁻¹*_root_.GD.N0106.N0428.N0765.N1597.d029348 d d|
  apply _root_.GD.N0106.N0428.N0765.N1652.d005819 ((_root_.GD.N0106.N0428.N0765.N1590.d029265 hk).mul_left C)
    (_root_.GD.N0106.N0428.N0765.N1590.d029265 hk)
  · intro n; exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  · intro n; exact (Real.exp_pos _).le
  · intro p
    rw [_root_.GD.N0106.N0428.N0765.N1652.d005824 _ hh, norm_smul, Real.norm_eq_abs,
      abs_of_pos (mul_pos (inv_pos.mpr hh) (inv_pos.mpr hh))]
    have hb := mul_le_mul_of_nonneg_left
      (_root_.GD.N0106.N0428.N0765.N1597.d029350 he hd.le hd.le hstrip (p.1/h) (p.2/h))
      (mul_pos (inv_pos.mpr hh) (inv_pos.mpr hh)).le
    rw [_root_.GD.N0106.N0428.N0765.N1596.d029356 hh d (p.1 : ℝ), _root_.GD.N0106.N0428.N0765.N1596.d029356 hh d (p.2 : ℝ)] at hb
    have hc : h⁻¹*h⁻¹*_root_.GD.N0106.N0428.N0765.N1597.d029348 d d ≤ C := le_abs_self _
    calc _ ≤ (h⁻¹*h⁻¹*_root_.GD.N0106.N0428.N0765.N1597.d029348 d d) *
          Real.exp (-(2*Real.pi*d/h)*|(p.1 : ℝ)|) *
          Real.exp (-(2*Real.pi*d/h)*|(p.2 : ℝ)|) := by
            simpa only [mul_assoc] using hb
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)) (Real.exp_nonneg _)

end
end GD.N0106.N0428.N0765.N1596
#print axioms _root_.GD.N0106.N0428.N0765.N1596.d029363
#print axioms _root_.GD.N0106.N0428.N0765.N1596.d029362
