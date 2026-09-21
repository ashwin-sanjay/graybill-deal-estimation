import GD.Module0534

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0213.N0511
noncomputable section
open _root_.GD.N0213.N0519

variable {a b r s x : ℝ}

def d007996 (a b x : ℝ) : ℝ := (1 + b * x ^ a)⁻¹

def d007997 (a b x : ℝ) : ℝ :=
  -(a * b * x ^ (a - 1)) / (1 + b * x ^ a) ^ 2

theorem d007998 (a : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    0 < 1 + b * x ^ a := by
  have hp := mul_nonneg hb.le (Real.rpow_nonneg hx a)
  linarith

@[fun_prop] theorem d007999 (a b : ℝ) :
    Measurable (_root_.GD.N0213.N0511.d007996 a b) := by
  unfold _root_.GD.N0213.N0511.d007996
  fun_prop

@[fun_prop] theorem d008000 (a b : ℝ) :
    Measurable (_root_.GD.N0213.N0511.d007997 a b) := by
  unfold _root_.GD.N0213.N0511.d007997
  fun_prop

theorem d008001 (a : ℝ) (hb : 0 < b) (hx : 0 < x) :
    HasDerivAt (_root_.GD.N0213.N0511.d007996 a b) (_root_.GD.N0213.N0511.d007997 a b x) x := by
  have hd := _root_.GD.N0213.N0511.d007998 a hb hx.le
  have hp := (Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')).const_mul b
  have h := (hp.const_add 1).inv hd.ne'
  change HasDerivAt (fun y : ℝ => (1 + b * y ^ a)⁻¹)
    (-(a * b * x ^ (a - 1)) / (1 + b * x ^ a) ^ 2) x
  convert! h using 1
  ring

theorem d008002 (a : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    ‖_root_.GD.N0213.N0511.d007996 a b x‖ ≤ 1 := by
  have hd := _root_.GD.N0213.N0511.d007998 a hb hx
  have hp := mul_nonneg hb.le (Real.rpow_nonneg hx a)
  unfold _root_.GD.N0213.N0511.d007996
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  exact inv_le_one_of_one_le₀ (by linarith)

theorem d008003 (a : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    ‖_root_.GD.N0213.N0511.d007996 a b x ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (_root_.GD.N0213.N0511.d008002 a hb hx)



theorem d008004 (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    _root_.GD.N0213.N0511.d007996 a b x + (x / a) * _root_.GD.N0213.N0511.d007997 a b x =
      _root_.GD.N0213.N0511.d007996 a b x ^ 2 := by
  have hd := _root_.GD.N0213.N0511.d007998 a hb hx.le
  unfold _root_.GD.N0213.N0511.d007996 _root_.GD.N0213.N0511.d007997
  rw [Real.rpow_sub_one hx.ne' a]
  field_simp [ha.ne', hx.ne', hd.ne']
  ring

theorem d008005
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    ‖x * _root_.GD.N0213.N0511.d007997 a b x‖ ≤ a := by
  have hd := _root_.GD.N0213.N0511.d007998 a hb hx.le
  have hy : 0 ≤ b * x ^ a := mul_nonneg hb.le (Real.rpow_nonneg hx.le a)
  have hid : x * _root_.GD.N0213.N0511.d007997 a b x =
      -(a * (b * x ^ a) / (1 + b * x ^ a) ^ 2) := by
    unfold _root_.GD.N0213.N0511.d007997
    rw [Real.rpow_sub_one hx.ne' a]
    field_simp [hx.ne', hd.ne']
  rw [hid, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg ha.le hy) (sq_nonneg _))]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  apply mul_le_mul_of_nonneg_left _ ha.le
  nlinarith [sq_nonneg (b * x ^ a)]

theorem d008006 (a : ℝ)
    (hs : -1 < s) (hr : 0 < r) (hb : 0 < b) :
    IntegrableOn (fun x => _root_.GD.N0213.N0519.d007966 s r x * _root_.GD.N0213.N0511.d007996 a b x) (Ioi 0) := by
  exact _root_.GD.N0213.N0519.d007974 hs hr (_root_.GD.N0213.N0511.d007996 a b)
    (_root_.GD.N0213.N0511.d007999 a b).aestronglyMeasurable
    (fun x hx => _root_.GD.N0213.N0511.d008002 a hb hx.le)

theorem d008007 (a : ℝ)
    (hs : -1 < s) (hr : 0 < r) (hb : 0 < b) :
    IntegrableOn (fun x => _root_.GD.N0213.N0519.d007966 s r x * _root_.GD.N0213.N0511.d007996 a b x ^ 2) (Ioi 0) := by
  exact _root_.GD.N0213.N0519.d007974 hs hr (fun x => _root_.GD.N0213.N0511.d007996 a b x ^ 2)
    ((_root_.GD.N0213.N0511.d007999 a b).pow_const 2).aestronglyMeasurable
    (fun x hx => _root_.GD.N0213.N0511.d008003 a hb hx.le)

theorem d008008
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    IntegrableOn (fun x => _root_.GD.N0213.N0519.d007966 a r x * _root_.GD.N0213.N0511.d007997 a b x) (Ioi 0) := by
  exact _root_.GD.N0213.N0519.d007975 ha hr (_root_.GD.N0213.N0511.d007997 a b) a
    (_root_.GD.N0213.N0511.d008000 a b).aestronglyMeasurable
    (fun x hx => _root_.GD.N0213.N0511.d008005 ha hb hx)




theorem d008009 (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 (a - 1) r x * _root_.GD.N0213.N0511.d007996 a b x ^ 2) =
      (r / a) * (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 a r x * _root_.GD.N0213.N0511.d007996 a b x) := by
  have hscore := _root_.GD.N0213.N0519.d007979 ha hr
    (_root_.GD.N0213.N0511.d007996 a b) (_root_.GD.N0213.N0511.d007997 a b) a
    (fun x hx => _root_.GD.N0213.N0511.d008001 a hb hx)
    (fun x hx => _root_.GD.N0213.N0511.d008002 a hb hx)
    (_root_.GD.N0213.N0511.d008000 a b).aestronglyMeasurable
    (fun x hx => _root_.GD.N0213.N0511.d008005 ha hb hx)
  have hInv := _root_.GD.N0213.N0511.d008006 a (s := a - 1) (r := r)
    (by linarith) hr hb
  have hDiff := _root_.GD.N0213.N0511.d008008 ha hb hr
  have hpoint (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      _root_.GD.N0213.N0519.d007966 (a - 1) r x * _root_.GD.N0213.N0511.d007996 a b x ^ 2 =
        _root_.GD.N0213.N0519.d007966 (a - 1) r x * _root_.GD.N0213.N0511.d007996 a b x +
          a⁻¹ * (_root_.GD.N0213.N0519.d007966 a r x * _root_.GD.N0213.N0511.d007997 a b x) := by
    rw [← _root_.GD.N0213.N0511.d008004 ha hb hx, _root_.GD.N0213.N0519.d007970 a r hx]
    ring
  have hi :
      (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 (a - 1) r x * _root_.GD.N0213.N0511.d007996 a b x ^ 2) =
        (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 (a - 1) r x * _root_.GD.N0213.N0511.d007996 a b x) +
          a⁻¹ * (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 a r x * _root_.GD.N0213.N0511.d007997 a b x) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
          (_root_.GD.N0213.N0519.d007966 (a - 1) r x * _root_.GD.N0213.N0511.d007996 a b x +
            a⁻¹ * (_root_.GD.N0213.N0519.d007966 a r x * _root_.GD.N0213.N0511.d007997 a b x)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hpoint x hx
      _ = _ := by rw [integral_add hInv (hDiff.const_mul a⁻¹), integral_const_mul]
  rw [hi, hscore]
  ring

end
end GD.N0213.N0511

#print axioms _root_.GD.N0213.N0511.d008001
#print axioms _root_.GD.N0213.N0511.d008005
#print axioms _root_.GD.N0213.N0511.d008007
#print axioms _root_.GD.N0213.N0511.d008009
