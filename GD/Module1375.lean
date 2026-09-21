import GD.Module1374
import GD.Module1358

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set

namespace GD.N0055
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441

def d022122 : ℝ := _root_.GD.N0232.N0720.N1436.d013271 2 4 * Real.Gamma (7 / 2 : ℝ)
def d022123 : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ (1 / 2 : ℝ)
def d022124 : ℝ := (8 : ℝ) ^ (-(7 / 2 : ℝ))
def d022125 : ℝ := _root_.GD.N0055.d022122 * _root_.GD.N0055.d022123 * _root_.GD.N0055.d022124

theorem d022126 : 0 < _root_.GD.N0055.d022122 :=
  mul_pos (_root_.GD.N0232.N0720.N1436.d013284 (by norm_num) (by norm_num))
    (Real.Gamma_pos_of_pos (by norm_num))

theorem d022127 : 0 < _root_.GD.N0055.d022123 :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)

theorem d022128 : 0 < _root_.GD.N0055.d022124 := Real.rpow_pos_of_pos (by norm_num) _

theorem d022129 : 0 < _root_.GD.N0055.d022125 :=
  mul_pos (mul_pos _root_.GD.N0055.d022126 _root_.GD.N0055.d022127) _root_.GD.N0055.d022128

theorem d022130 (t : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1436.d013273 2 4 t z = _root_.GD.N0055.d022122 *
      _root_.GD.N0232.N0720.N1436.d013270 2 4 t * _root_.GD.N0232.N0720.N1436.d013269 2 4 z *
        _root_.GD.N0232.N0720.N1436.d013268 2 4 t z ^ (-(7 / 2 : ℝ)) := by
  have ht : _root_.GD.N0232.N0720.N1436.d013210 2 4 = (7 / 2 : ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013210, _root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, _root_.GD.N0232.N0720.N1436.d013209]
  unfold _root_.GD.N0232.N0720.N1436.d013273 _root_.GD.N0055.d022122
  rw [ht, one_div, ← Real.rpow_neg_eq_inv_rpow]
  ring

theorem d022131 (q : ℝ) (hq : 2 ≤ q) (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hz : z ∈ _root_.GD.N0055.d022117 q) :
    _root_.GD.N0055.d022123 * q ^ 7 ≤ _root_.GD.N0232.N0720.N1436.d013269 2 4 z := by
  have hq0 : 0 < q := by linarith
  have hb := _root_.GD.N0055.d022118 q hq z hz
  have hu : (2 : ℝ) ^ (-(1 / 2 : ℝ)) * q ^ 3 ≤ (1 - z.1) ^ (-(1 / 2 : ℝ)) := by
    have hh := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hb.1.1.2) hb.2.2.2
      (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have heq : (2 / q ^ 6) ^ (-(1 / 2 : ℝ)) = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * q ^ 3 := by
      rw [show 2 / q ^ 6 = 2 * (1 / q ^ 6) by ring,
        Real.mul_rpow (by norm_num) (by positivity), _root_.GD.N0055.d022112 q hq0.le]
      norm_num
    rwa [heq] at hh
  have hx : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) ≤ z.1 ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hb.2.1 (by norm_num)
  have hw : q ^ 4 ≤ z.2 ^ (1 / 2 : ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hq0.le 8) hz.2.1
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
    rw [_root_.GD.N0055.d022111 q hq0.le] at hh
    norm_num at hh
    exact hh
  have heq : _root_.GD.N0232.N0720.N1436.d013269 2 4 z =
      (1 - z.1) ^ (-(1 / 2 : ℝ)) * z.1 ^ (1 / 2 : ℝ) * z.2 ^ (1 / 2 : ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013269, _root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, _root_.GD.N0232.N0720.N1436.d013209]
  rw [heq]
  calc
    _ = ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * q ^ 3) *
        (1 / 2 : ℝ) ^ (1 / 2 : ℝ) * q ^ 4 := by unfold _root_.GD.N0055.d022123; ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul hu hx (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (sub_pos.mpr hb.1.1.2).le _)) hw (pow_nonneg hq0.le 4)
      (mul_nonneg (Real.rpow_nonneg (sub_pos.mpr hb.1.1.2).le _)
        (Real.rpow_nonneg hb.1.1.1.le _))

theorem d022132 (q : ℝ) (hq : 2 ≤ q) :
    q ^ 12 ≤ _root_.GD.N0232.N0720.N1436.d013270 2 4 (_root_.GD.N0055.d022115 q hq) := by
  have hq0 : 0 < q := by linarith
  have ht := (_root_.GD.N0055.d022115 q hq).property
  have hfirst : 1 ≤ (1 - (_root_.GD.N0055.d022115 q hq : ℝ)) ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (sub_pos.mpr ht.2)
      (by linarith [ht.1]) (by norm_num)
  have hpow : (1 / q ^ 8) ^ (-(3 / 2 : ℝ)) = q ^ 12 := by
    rw [_root_.GD.N0055.d022112 q hq0.le]
    norm_num
  have hform : _root_.GD.N0232.N0720.N1436.d013270 2 4 (_root_.GD.N0055.d022115 q hq) =
      (1 - (_root_.GD.N0055.d022115 q hq : ℝ)) ^ (-(1 / 2 : ℝ)) * (1 / q ^ 8) ^ (-(3 / 2 : ℝ)) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013270, _root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, _root_.GD.N0055.d022115]
  rw [hform, hpow]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hfirst (pow_nonneg hq0.le 12)

theorem d022133 (q : ℝ) (hq : 2 ≤ q) :
    q ^ 7 ≤ _root_.GD.N0232.N0720.N1436.d013270 2 4 (_root_.GD.N0055.d022116 q hq) := by
  have hq0 : 0 < q := by linarith
  have hs := (_root_.GD.N0055.d022116 q hq).property
  have hsecond : 1 ≤ (_root_.GD.N0055.d022116 q hq : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs.1 hs.2.le (by norm_num)
  have hpow : (1 / q ^ 14) ^ (-(1 / 2 : ℝ)) = q ^ 7 := by
    rw [_root_.GD.N0055.d022112 q hq0.le]
    norm_num
  have hform : _root_.GD.N0232.N0720.N1436.d013270 2 4 (_root_.GD.N0055.d022116 q hq) =
      (1 / q ^ 14) ^ (-(1 / 2 : ℝ)) * (_root_.GD.N0055.d022116 q hq : ℝ) ^ (-(3 / 2 : ℝ)) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013270, _root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, _root_.GD.N0055.d022116]
  rw [hform, hpow]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsecond (pow_nonneg hq0.le 7)

theorem d022134 (q : ℝ) (hq : 2 ≤ q) (t : _root_.GD.N0232.N0720.N1441.d013676)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z ∈ _root_.GD.N0055.d022117 q)
    (hbound : _root_.GD.N0232.N0720.N1436.d013268 2 4 t z ≤ 8 * q ^ 8) :
    _root_.GD.N0055.d022124 / q ^ 28 ≤ _root_.GD.N0232.N0720.N1436.d013268 2 4 t z ^ (-(7 / 2 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  have hp := _root_.GD.N0232.N0720.N1436.d013281 (by norm_num : 2 ≤ 2) (by norm_num : 2 ≤ 4)
    t.property.1 t.property.2 (_root_.GD.N0055.d022118 q hq z hz).1
  have hh := Real.rpow_le_rpow_of_nonpos hp hbound (by norm_num : -(7 / 2 : ℝ) ≤ 0)
  have heq : (8 * q ^ 8) ^ (-(7 / 2 : ℝ)) = _root_.GD.N0055.d022124 / q ^ 28 := by
    rw [Real.mul_rpow (by norm_num) (pow_nonneg hq0.le 8), _root_.GD.N0055.d022111 q hq0.le,
      show ((8 : ℕ) : ℝ) * (-(7 / 2 : ℝ)) = -(28 : ℝ) by norm_num,
      Real.rpow_neg hq0.le,
      show q ^ (28 : ℝ) = q ^ (28 : ℕ) from by
        simpa only [Nat.cast_ofNat] using Real.rpow_natCast q 28]
    rfl
  rwa [heq] at hh

theorem d022135 (q : ℝ) (hq : 2 ≤ q) (t : _root_.GD.N0232.N0720.N1441.d013676)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z ∈ _root_.GD.N0055.d022117 q)
    (hbound : _root_.GD.N0232.N0720.N1436.d013268 2 4 t z ≤ 8 * q ^ 8)
    (P : ℝ) (hparam : P ≤ _root_.GD.N0232.N0720.N1436.d013270 2 4 t) :
    _root_.GD.N0055.d022122 * P * (_root_.GD.N0055.d022123 * q ^ 7) * (_root_.GD.N0055.d022124 / q ^ 28) ≤
      _root_.GD.N0232.N0720.N1436.d013273 2 4 t z := by
  have hq0 : 0 < q := by linarith
  have hp := _root_.GD.N0232.N0720.N1436.d013283 (m := 2) (n := 4) t.property.1 t.property.2
  have hs := _root_.GD.N0232.N0720.N1436.d013282 (m := 2) (n := 4) (_root_.GD.N0055.d022118 q hq z hz).1
  rw [_root_.GD.N0055.d022130]
  exact mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hparam _root_.GD.N0055.d022126.le)
      (_root_.GD.N0055.d022131 q hq z hz) (mul_nonneg _root_.GD.N0055.d022127.le (pow_nonneg hq0.le 7))
      (mul_nonneg _root_.GD.N0055.d022126.le hp.le))
    (_root_.GD.N0055.d022134 q hq t z hz hbound) (div_nonneg _root_.GD.N0055.d022128.le (pow_nonneg hq0.le 28))
    (mul_nonneg (mul_nonneg _root_.GD.N0055.d022126.le hp.le) hs.le)

theorem d022136 (q : ℝ) (hq : 2 ≤ q) (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hz : z ∈ _root_.GD.N0055.d022117 q) :
    _root_.GD.N0055.d022125 / q ^ 9 ≤ _root_.GD.N0232.N0720.N1436.d013273 2 4 (_root_.GD.N0055.d022115 q hq) z := by
  have hq0 : 0 < q := by linarith
  calc
    _ = _root_.GD.N0055.d022122 * q ^ 12 * (_root_.GD.N0055.d022123 * q ^ 7) *
        (_root_.GD.N0055.d022124 / q ^ 28) := by unfold _root_.GD.N0055.d022125; field_simp [hq0.ne']
    _ ≤ _ := _root_.GD.N0055.d022135 q hq _ z hz (_root_.GD.N0055.d022120 q hq z hz)
      (q ^ 12) (_root_.GD.N0055.d022132 q hq)

theorem d022137 (q : ℝ) (hq : 2 ≤ q) (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hz : z ∈ _root_.GD.N0055.d022117 q) :
    _root_.GD.N0055.d022125 / q ^ 14 ≤ _root_.GD.N0232.N0720.N1436.d013273 2 4 (_root_.GD.N0055.d022116 q hq) z := by
  have hq0 : 0 < q := by linarith
  calc
    _ = _root_.GD.N0055.d022122 * q ^ 7 * (_root_.GD.N0055.d022123 * q ^ 7) *
        (_root_.GD.N0055.d022124 / q ^ 28) := by unfold _root_.GD.N0055.d022125; field_simp [hq0.ne']
    _ ≤ _ := _root_.GD.N0055.d022135 q hq _ z hz (_root_.GD.N0055.d022121 q hq z hz)
      (q ^ 7) (_root_.GD.N0055.d022133 q hq)

end
end GD.N0055

#print axioms _root_.GD.N0055.d022136
#print axioms _root_.GD.N0055.d022137


set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0055
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0045



theorem d022138
    (q : ℝ) (hq : 2 ≤ q) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) :
    _root_.GD.N0055.d022125 / (8 * q ^ 7) ≤
      (∫ z, (g z - (_root_.GD.N0055.d022115 q hq : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 4 (_root_.GD.N0055.d022115 q hq)) +
        q ^ 5 * (∫ z, (g z - (_root_.GD.N0055.d022116 q hq : ℝ)) ^ 2
          ∂_root_.GD.N0232.N0720.N1441.d013678 2 4 (_root_.GD.N0055.d022116 q hq)) := by
  let t := _root_.GD.N0055.d022115 q hq
  let s := _root_.GD.N0055.d022116 q hq
  let F := fun z => _root_.GD.N0232.N0720.N1436.d013273 2 4 t z * (g z - (t : ℝ)) ^ 2 +
    q ^ 5 * (_root_.GD.N0232.N0720.N1436.d013273 2 4 s z * (g z - (s : ℝ)) ^ 2)
  have hIt := _root_.GD.N0045.d021928 2 4 (by norm_num) (by norm_num) t g hg hB (t : ℝ)
  have hIs := _root_.GD.N0045.d021928 2 4 (by norm_num) (by norm_num) s g hg hB (s : ℝ)
  have hI : Integrable F _root_.GD.N0232.N0720.N1436.d013288 := hIt.add (hIs.const_mul (q ^ 5))
  have hq0 : 0 < q := by linarith
  have htB := _root_.GD.N0055.d022114 q hq 8 (by norm_num)
  have hsB := _root_.GD.N0055.d022114 q hq 14 (by norm_num)
  have hgap : (1 / 2 : ℝ) ≤ (s : ℝ) - (t : ℝ) := by
    change (1 / 2 : ℝ) ≤ (1 - 1 / q ^ 14) - 1 / q ^ 8
    linarith [htB.2, hsB.2]
  have hpoint : ∀ z ∈ _root_.GD.N0055.d022117 q, _root_.GD.N0055.d022125 / (8 * q ^ 9) ≤ F z := by
    intro z hz
    have ht := _root_.GD.N0055.d022136 q hq z hz
    have hs : _root_.GD.N0055.d022125 / q ^ 9 ≤ q ^ 5 * _root_.GD.N0232.N0720.N1436.d013273 2 4 s z := by
      calc
        _ = q ^ 5 * (_root_.GD.N0055.d022125 / q ^ 14) := by field_simp [hq0.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (_root_.GD.N0055.d022137 q hq z hz) (pow_nonneg hq0.le 5)
    have hsq : (1 / 8 : ℝ) ≤ (g z - (t : ℝ)) ^ 2 + (g z - (s : ℝ)) ^ 2 := by
      nlinarith only [hgap, sq_nonneg (g z - ((s : ℝ) + (t : ℝ)) / 2),
        sq_nonneg ((s : ℝ) - (t : ℝ) - 1 / 2)]
    have hmul := mul_le_mul_of_nonneg_left hsq
      (div_nonneg _root_.GD.N0055.d022129.le (pow_nonneg hq0.le 9))
    have hfirst := mul_le_mul_of_nonneg_right ht (sq_nonneg (g z - (t : ℝ)))
    have hsecond := mul_le_mul_of_nonneg_right hs (sq_nonneg (g z - (s : ℝ)))
    calc
      _ = (_root_.GD.N0055.d022125 / q ^ 9) * (1 / 8) := by ring
      _ ≤ _ := hmul
      _ ≤ F z := by dsimp only [F]; nlinarith only [hfirst, hsecond]
  have hnonneg : 0 ≤ᵐ[_root_.GD.N0232.N0720.N1436.d013288] F := by
    filter_upwards [_root_.GD.N0045.d021922 2 4 (by norm_num) (by norm_num) t,
      _root_.GD.N0045.d021922 2 4 (by norm_num) (by norm_num) s] with z ht hs
    exact add_nonneg (mul_nonneg ht.le (sq_nonneg _))
      (mul_nonneg (pow_nonneg hq0.le 5) (mul_nonneg hs.le (sq_nonneg _)))
  have hS : MeasurableSet (_root_.GD.N0055.d022117 q) := measurableSet_Icc.prod measurableSet_Icc
  have hfinite : _root_.GD.N0232.N0720.N1436.d013288 (_root_.GD.N0055.d022117 q) ≠ ⊤ := by
    rw [_root_.GD.N0055.d022119 q hq]
    exact ENNReal.ofReal_ne_top
  have hbound := setIntegral_mono_on
    (integrableOn_const hfinite : IntegrableOn
      (fun _ : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0055.d022125 / (8 * q ^ 9))
        (_root_.GD.N0055.d022117 q) _root_.GD.N0232.N0720.N1436.d013288)
    hI.integrableOn hS hpoint
  have hconst : (∫ _ in _root_.GD.N0055.d022117 q, _root_.GD.N0055.d022125 / (8 * q ^ 9)
      ∂_root_.GD.N0232.N0720.N1436.d013288) = _root_.GD.N0055.d022125 / (8 * q ^ 7) := by
    rw [integral_const]
    simp only [measureReal_def, Measure.restrict_apply_univ, _root_.GD.N0055.d022119 q hq,
      ENNReal.toReal_ofReal (pow_nonneg hq0.le 2), smul_eq_mul]
    field_simp [hq0.ne']
  rw [hconst] at hbound
  have htotal := hbound.trans (setIntegral_le_integral hI hnonneg)
  rw [_root_.GD.N0045.d021923 2 4 (by norm_num) (by norm_num),
    _root_.GD.N0045.d021923 2 4 (by norm_num) (by norm_num)]
  simpa only [F, integral_add hIt (hIs.const_mul (q ^ 5)), integral_const_mul, t, s] using htotal

private theorem d022139 (C e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    C * e * (1 - e) ≤ |C| * e := by
  calc
    _ ≤ |C| * e * (1 - e) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) he0) (sub_nonneg.mpr he1)
    _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (abs_nonneg C) he0) (by linarith)



theorem d022140
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) (C : ℝ) :
    ¬ (∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      (∫ z, (g z - (t : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 4 t) ≤
        C * (t : ℝ) * (1 - (t : ℝ))) := by
  intro hcap
  let q := 16 * (|C| + 1) / _root_.GD.N0055.d022125 + 2
  have hq : 2 ≤ q := by
    have hh : 0 ≤ 16 * (|C| + 1) / _root_.GD.N0055.d022125 :=
      div_nonneg (by positivity) _root_.GD.N0055.d022129.le
    dsimp [q]
    linarith
  have hq0 : 0 < q := by linarith
  have hqbig : 16 * |C| < _root_.GD.N0055.d022125 * q := by
    have hh := div_mul_cancel₀ (16 * (|C| + 1)) _root_.GD.N0055.d022129.ne'
    dsimp [q]
    nlinarith [_root_.GD.N0055.d022129]
  have hlower := _root_.GD.N0055.d022138 q hq g hg hB
  have ht := hcap (_root_.GD.N0055.d022115 q hq)
  have hs := hcap (_root_.GD.N0055.d022116 q hq)
  have htB := _root_.GD.N0055.d022114 q hq 8 (by norm_num)
  have hsB := _root_.GD.N0055.d022114 q hq 14 (by norm_num)
  have htUpper : C * (1 / q ^ 8) * (1 - 1 / q ^ 8) ≤ |C| / q ^ 8 := by
    calc
      _ ≤ |C| * (1 / q ^ 8) := _root_.GD.N0055.d022139 C (1 / q ^ 8) htB.1.le
        (htB.2.trans (by norm_num : (1 / 4 : ℝ) ≤ 1))
      _ = _ := by ring
  have hsUpper : C * (1 - 1 / q ^ 14) * (1 - (1 - 1 / q ^ 14)) ≤ |C| / q ^ 14 := by
    have hh := _root_.GD.N0055.d022139 C (1 / q ^ 14) hsB.1.le
      (hsB.2.trans (by norm_num : (1 / 4 : ℝ) ≤ 1))
    convert hh using 1 <;> ring
  change _ ≤ C * (1 / q ^ 8) * (1 - 1 / q ^ 8) at ht
  change _ ≤ C * (1 - 1 / q ^ 14) * (1 - (1 - 1 / q ^ 14)) at hs
  have hsWeighted : q ^ 5 * (∫ z, (g z - (_root_.GD.N0055.d022116 q hq : ℝ)) ^ 2
      ∂_root_.GD.N0232.N0720.N1441.d013678 2 4 (_root_.GD.N0055.d022116 q hq)) ≤ |C| / q ^ 8 := by
    calc
      _ ≤ q ^ 5 * (|C| / q ^ 14) := mul_le_mul_of_nonneg_left (hs.trans hsUpper) (pow_nonneg hq0.le 5)
      _ = |C| / q ^ 9 := by field_simp [hq0.ne']
      _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg C) (pow_pos hq0 8)
        (pow_le_pow_right₀ (by linarith) (by norm_num : 8 ≤ 9))
  have hineq : _root_.GD.N0055.d022125 / (8 * q ^ 7) ≤ 2 * |C| / q ^ 8 := by
    calc
      _ ≤ _ := hlower
      _ ≤ |C| / q ^ 8 + |C| / q ^ 8 := add_le_add (ht.trans htUpper) hsWeighted
      _ = _ := by ring
  have hmul := (div_le_div_iff₀ (by positivity : 0 < 8 * q ^ 7) (pow_pos hq0 8)).mp hineq
  nlinarith [mul_pos (pow_pos hq0 7) (sub_pos.mpr hqbig)]

theorem d022141
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (C : ℝ) :
    ¬ (∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      (∫ z, (g z - (t : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 4 t) ≤
        C * (t : ℝ) * (1 - (t : ℝ))) := by
  apply _root_.GD.N0055.d022140 g hg (B := 1) _ C
  intro z
  rw [abs_of_nonneg (hb z).1]
  exact (hb z).2

end
end GD.N0055

#print axioms _root_.GD.N0055.d022138
#print axioms _root_.GD.N0055.d022140
#print axioms _root_.GD.N0055.d022141
