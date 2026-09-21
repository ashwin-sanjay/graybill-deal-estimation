import GD.Module0463
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0213.N0519
noncomputable section

def d007966 (s r x : ℝ) : ℝ := x ^ s * Real.exp (-(r * x))

theorem d007967 (s r : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ _root_.GD.N0213.N0519.d007966 s r x := mul_nonneg (Real.rpow_nonneg hx _) (Real.exp_pos _).le

theorem d007968 {s r : ℝ} (hs : -1 < s) (hr : 0 < r) :
    IntegrableOn (_root_.GD.N0213.N0519.d007966 s r) (Ioi 0) := by
  change IntegrableOn (fun x => x ^ s * Real.exp (-(r * x))) (Ioi 0)
  simpa only [Real.rpow_one, neg_mul] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hs le_rfl hr

theorem d007969 (s r : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (_root_.GD.N0213.N0519.d007966 s r) (s * _root_.GD.N0213.N0519.d007966 (s - 1) r x - r * _root_.GD.N0213.N0519.d007966 s r x) x := by
  have he := (((hasDerivAt_id x).const_mul r).neg).exp
  convert! (Real.hasDerivAt_rpow_const (p := s) (Or.inl hx.ne')).mul he using 1
  simp only [_root_.GD.N0213.N0519.d007966, id_eq, mul_one, Pi.neg_apply]
  ring

theorem d007970 (s r : ℝ) {x : ℝ} (hx : 0 < x) :
    _root_.GD.N0213.N0519.d007966 s r x = _root_.GD.N0213.N0519.d007966 (s - 1) r x * x := by
  unfold _root_.GD.N0213.N0519.d007966
  rw [show s = (s - 1) + 1 by ring, Real.rpow_add hx, Real.rpow_one]
  ring

theorem d007971 (s r : ℝ) : Measurable (_root_.GD.N0213.N0519.d007966 s r) := by
  unfold _root_.GD.N0213.N0519.d007966
  fun_prop

theorem d007972 {s : ℝ} (hs : 0 ≤ s) (r : ℝ) :
    Continuous (_root_.GD.N0213.N0519.d007966 s r) := by
  exact (Real.continuous_rpow_const hs).mul (by fun_prop)

theorem d007973 (s r x : ℝ) (φ : ℝ → ℝ)
    (hx : 0 ≤ x) (hφ : ‖φ x‖ ≤ 1) :
    ‖_root_.GD.N0213.N0519.d007966 s r x * φ x‖ ≤ _root_.GD.N0213.N0519.d007966 s r x := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0213.N0519.d007967 s r hx)]
  exact mul_le_of_le_one_right (_root_.GD.N0213.N0519.d007967 s r hx) hφ

theorem d007974 {s r : ℝ} (hs : -1 < s) (hr : 0 < r)
    (φ : ℝ → ℝ) (hφm : AEStronglyMeasurable φ (volume.restrict (Ioi 0)))
    (hφ : ∀ x ∈ Ioi (0 : ℝ), ‖φ x‖ ≤ 1) :
    IntegrableOn (fun x => _root_.GD.N0213.N0519.d007966 s r x * φ x) (Ioi 0) := by
  apply (_root_.GD.N0213.N0519.d007968 hs hr).mono' ((_root_.GD.N0213.N0519.d007971 s r).aestronglyMeasurable.mul hφm)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact _root_.GD.N0213.N0519.d007973 s r x φ hx.le (hφ x hx)

theorem d007975 {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (φ' : ℝ → ℝ) (D : ℝ) (hφ'm : AEStronglyMeasurable φ' (volume.restrict (Ioi 0)))
    (hφ' : ∀ x ∈ Ioi (0 : ℝ), ‖x * φ' x‖ ≤ D) :
    IntegrableOn (fun x => _root_.GD.N0213.N0519.d007966 s r x * φ' x) (Ioi 0) := by
  apply ((_root_.GD.N0213.N0519.d007968 (s := s - 1) (by linarith) hr).mul_const D).mono'
    ((_root_.GD.N0213.N0519.d007971 s r).aestronglyMeasurable.mul hφ'm)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖_root_.GD.N0213.N0519.d007966 s r x * φ' x‖ ≤ _root_.GD.N0213.N0519.d007966 (s - 1) r x * D
  rw [_root_.GD.N0213.N0519.d007970 s r hx, mul_assoc, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (_root_.GD.N0213.N0519.d007967 (s - 1) r hx.le)]
  exact mul_le_mul_of_nonneg_left (hφ' x hx) (_root_.GD.N0213.N0519.d007967 (s - 1) r hx.le)

theorem d007976 {s r : ℝ} (hs : 0 < s)
    (φ : ℝ → ℝ) (hφ : ∀ x ∈ Ici (0 : ℝ), ‖φ x‖ ≤ 1) :
    ContinuousWithinAt (fun x => _root_.GD.N0213.N0519.d007966 s r x * φ x) (Ici 0) 0 := by
  have hz : _root_.GD.N0213.N0519.d007966 s r 0 = 0 := by simp [_root_.GD.N0213.N0519.d007966, Real.zero_rpow hs.ne']
  change Tendsto (fun x => _root_.GD.N0213.N0519.d007966 s r x * φ x) (𝓝[Ici (0 : ℝ)] 0)
    (𝓝 (_root_.GD.N0213.N0519.d007966 s r 0 * φ 0))
  rw [hz, zero_mul]
  apply squeeze_zero_norm' (a := _root_.GD.N0213.N0519.d007966 s r) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact _root_.GD.N0213.N0519.d007973 s r x φ hx (hφ x hx)
  · simpa only [hz] using ((_root_.GD.N0213.N0519.d007972 hs.le r).tendsto 0).mono_left
      (show 𝓝[Ici (0 : ℝ)] 0 ≤ 𝓝 0 from inf_le_left)

theorem d007977 (s : ℝ) {r : ℝ} (hr : 0 < r)
    (φ : ℝ → ℝ) (hφ : ∀ x ∈ Ioi (0 : ℝ), ‖φ x‖ ≤ 1) :
    Tendsto (fun x => _root_.GD.N0213.N0519.d007966 s r x * φ x) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := _root_.GD.N0213.N0519.d007966 s r) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact _root_.GD.N0213.N0519.d007973 s r x φ hx.le (hφ x hx)
  · change Tendsto (fun x => x ^ s * Real.exp (-(r * x))) atTop (𝓝 0)
    simpa only [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s r hr

theorem d007978 {s r : ℝ} (hs : 0 < s)
    (φ φ' : ℝ → ℝ)
    (hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt φ (φ' x) x)
    (hc : ContinuousWithinAt (fun x => _root_.GD.N0213.N0519.d007966 s r x * φ x) (Ici 0) 0)
    (hlim : Tendsto (fun x => _root_.GD.N0213.N0519.d007966 s r x * φ x) atTop (𝓝 0))
    (hInv : IntegrableOn (fun x => _root_.GD.N0213.N0519.d007966 (s - 1) r x * φ x) (Ioi 0))
    (hMass : IntegrableOn (fun x => _root_.GD.N0213.N0519.d007966 s r x * φ x) (Ioi 0))
    (hDiff : IntegrableOn (fun x => _root_.GD.N0213.N0519.d007966 s r x * φ' x) (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 (s - 1) r x * φ x) =
      (r * (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 s r x * φ x) -
        ∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 s r x * φ' x) / s := by
  have hderiv (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun y => _root_.GD.N0213.N0519.d007966 s r y * φ y)
        (s * (_root_.GD.N0213.N0519.d007966 (s - 1) r x * φ x) -
          r * (_root_.GD.N0213.N0519.d007966 s r x * φ x) + _root_.GD.N0213.N0519.d007966 s r x * φ' x) x := by
    convert! (_root_.GD.N0213.N0519.d007969 s r hx).mul (hd x hx) using 1
    ring
  have hi := ((hInv.const_mul s).sub (hMass.const_mul r)).add hDiff
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc hderiv hi hlim
  rw [integral_add (f := fun x => s * (_root_.GD.N0213.N0519.d007966 (s - 1) r x * φ x) -
      r * (_root_.GD.N0213.N0519.d007966 s r x * φ x)) (g := fun x => _root_.GD.N0213.N0519.d007966 s r x * φ' x)
      ((hInv.const_mul s).sub (hMass.const_mul r)) hDiff,
    integral_sub (f := fun x => s * (_root_.GD.N0213.N0519.d007966 (s - 1) r x * φ x))
      (g := fun x => r * (_root_.GD.N0213.N0519.d007966 s r x * φ x)) (hInv.const_mul s) (hMass.const_mul r)] at h
  simp only [integral_const_mul, _root_.GD.N0213.N0519.d007966, Real.zero_rpow hs.ne', zero_mul, sub_zero] at h
  apply (eq_div_iff hs.ne').mpr
  dsimp only [_root_.GD.N0213.N0519.d007966]
  linarith

theorem d007979 {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (φ φ' : ℝ → ℝ) (D : ℝ)
    (hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt φ (φ' x) x)
    (hφ : ∀ x ∈ Ici (0 : ℝ), ‖φ x‖ ≤ 1)
    (hφ'm : AEStronglyMeasurable φ' (volume.restrict (Ioi 0)))
    (hφ' : ∀ x ∈ Ioi (0 : ℝ), ‖x * φ' x‖ ≤ D) :
    (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 (s - 1) r x * φ x) =
      (r * (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 s r x * φ x) -
        ∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 s r x * φ' x) / s := by
  have hm : AEStronglyMeasurable φ (volume.restrict (Ioi 0)) :=
    (show ContinuousOn φ (Ioi 0) from fun x hx =>
      (hd x hx).continuousAt.continuousWithinAt).aestronglyMeasurable measurableSet_Ioi
  have hb (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : ‖φ x‖ ≤ 1 := hφ x (show 0 ≤ x from le_of_lt hx)
  exact _root_.GD.N0213.N0519.d007978 hs φ φ' hd (_root_.GD.N0213.N0519.d007976 hs φ hφ)
    (_root_.GD.N0213.N0519.d007977 s hr φ hb)
    (_root_.GD.N0213.N0519.d007974 (by linarith) hr φ hm hb)
    (_root_.GD.N0213.N0519.d007974 (by linarith) hr φ hm hb)
    (_root_.GD.N0213.N0519.d007975 hs hr φ' D hφ'm hφ')

open _root_.GD.N0213.N0495

theorem d007980 (x : ℝ) :
    |x| * Real.exp (-x ^ 2) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have he := Real.add_one_le_exp (x ^ 2)
  have hsq := sq_nonneg (|x| - 1)
  nlinarith [sq_abs x]

theorem d007981 {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    ‖r * _root_.GD.N0213.N0495.d007175 L r‖ ≤ 2 / L := by
  have heq : r * _root_.GD.N0213.N0495.d007175 L r =
      -(2 / L) * ((Real.log r / L) * _root_.GD.N0213.N0495.d007174 L r) := by
    unfold _root_.GD.N0213.N0495.d007175
    field_simp
  rw [heq, norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 / L),
    norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (_root_.GD.N0213.N0495.d007176 L r)]
  exact mul_le_of_le_one_right (by positivity) (_root_.GD.N0213.N0519.d007980 _)

theorem d007982 {L x b : ℝ}
    (hL : 0 < L) (hx : 0 < x) (hb : 0 ≤ b) :
    ‖x * _root_.GD.N0213.N0495.d007175 L (x + b)‖ ≤ 2 / L := by
  have hr : 0 < x + b := by linarith
  have heq : x * _root_.GD.N0213.N0495.d007175 L (x + b) =
      (x / (x + b)) * ((x + b) * _root_.GD.N0213.N0495.d007175 L (x + b)) := by field_simp
  rw [heq, norm_mul, Real.norm_eq_abs, abs_of_pos (div_pos hx hr)]
  calc
    _ ≤ 1 * (2 / L) := mul_le_mul ((div_le_one hr).mpr (by linarith))
      (_root_.GD.N0213.N0519.d007981 hL hr) (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem d007983 (L r : ℝ) : ‖_root_.GD.N0213.N0495.d007174 L r ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [_root_.GD.N0213.N0495.d007176 L r, _root_.GD.N0213.N0495.d007177 L r]

theorem d007984 {L x b : ℝ}
    (hL : 0 < L) (hx : 0 < x) (hb : 0 ≤ b) :
    HasDerivAt (fun y => _root_.GD.N0213.N0495.d007174 L (y + b) ^ 2)
      (2 * _root_.GD.N0213.N0495.d007174 L (x + b) * _root_.GD.N0213.N0495.d007175 L (x + b)) x := by
  convert! ((_root_.GD.N0213.N0495.d007178 hL (show 0 < x + b by linarith)).comp x
    ((hasDerivAt_id x).add_const b)).pow 2 using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Function.comp_def, id_eq]

theorem d007985 {L x b : ℝ}
    (hL : 0 < L) (hx : 0 < x) (hb : 0 ≤ b) :
    ‖x * (2 * _root_.GD.N0213.N0495.d007174 L (x + b) * _root_.GD.N0213.N0495.d007175 L (x + b))‖ ≤ 4 / L := by
  rw [show x * (2 * _root_.GD.N0213.N0495.d007174 L (x + b) * _root_.GD.N0213.N0495.d007175 L (x + b)) =
    (2 * _root_.GD.N0213.N0495.d007174 L (x + b)) * (x * _root_.GD.N0213.N0495.d007175 L (x + b)) by ring,
    norm_mul, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) (_root_.GD.N0213.N0495.d007176 L (x + b)))]
  calc
    _ ≤ 2 * (2 / L) := mul_le_mul (by linarith [_root_.GD.N0213.N0495.d007177 L (x + b)])
      (_root_.GD.N0213.N0519.d007982 hL hx hb) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem d007986 {s r L b : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hL : 0 < L) (hb : 0 ≤ b) :
    (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 (s - 1) r x * _root_.GD.N0213.N0495.d007174 L (x + b) ^ 2) =
      (r * (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 s r x * _root_.GD.N0213.N0495.d007174 L (x + b) ^ 2) -
        2 * ∫ x in Ioi (0 : ℝ),
          _root_.GD.N0213.N0519.d007966 s r x * (_root_.GD.N0213.N0495.d007174 L (x + b) * _root_.GD.N0213.N0495.d007175 L (x + b))) / s := by
  have hid := _root_.GD.N0213.N0519.d007979 hs hr
    (fun x => _root_.GD.N0213.N0495.d007174 L (x + b) ^ 2)
    (fun x => 2 * _root_.GD.N0213.N0495.d007174 L (x + b) * _root_.GD.N0213.N0495.d007175 L (x + b)) (4 / L)
    (fun x hx => _root_.GD.N0213.N0519.d007984 hL hx hb)
    (fun x _ => _root_.GD.N0213.N0519.d007983 L (x + b))
    (by apply Measurable.aestronglyMeasurable; dsimp only [_root_.GD.N0213.N0495.d007175, _root_.GD.N0213.N0495.d007174]; fun_prop)
    (fun x hx => _root_.GD.N0213.N0519.d007985 hL hx hb)
  rw [show (fun x => _root_.GD.N0213.N0519.d007966 s r x *
      (2 * _root_.GD.N0213.N0495.d007174 L (x + b) * _root_.GD.N0213.N0495.d007175 L (x + b))) =
      (fun x => 2 * (_root_.GD.N0213.N0519.d007966 s r x *
        (_root_.GD.N0213.N0495.d007174 L (x + b) * _root_.GD.N0213.N0495.d007175 L (x + b)))) by funext x; ring,
    integral_const_mul] at hid
  exact hid

end
end GD.N0213.N0519

#print axioms _root_.GD.N0213.N0519.d007968
#print axioms _root_.GD.N0213.N0519.d007969
#print axioms _root_.GD.N0213.N0519.d007978
#print axioms _root_.GD.N0213.N0519.d007979
#print axioms _root_.GD.N0213.N0519.d007981
#print axioms _root_.GD.N0213.N0519.d007986
