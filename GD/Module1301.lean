import GD.Module1300
import GD.Module0388
import GD.Module1286
import Mathlib.Tactic







































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set

namespace GD.N0106.N0428.N0765.N1538
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1534 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1539
open _root_.GD.N0106.N0428.N0765.N1536 (d021173)




def d021186 (c φ : ℝ) : ℂ := (c : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)

theorem d021187 (c : ℝ) : _root_.GD.N0106.N0428.N0765.N1538.d021186 c 0 = (c : ℂ) := by
  simp [_root_.GD.N0106.N0428.N0765.N1538.d021186]

theorem d021188 {c : ℝ} (hc : 0 ≤ c) (φ : ℝ) : ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 c φ‖ = c := by
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021186, norm_mul, Complex.norm_of_nonneg hc, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem d021189 (c φ θ : ℝ) :
    (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * _root_.GD.N0106.N0428.N0765.N1538.d021186 c φ).re = c * Real.cos (φ - θ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021186, mul_left_comm, ← Complex.exp_add]
  have h : ((-θ : ℝ) : ℂ) * Complex.I + (φ : ℂ) * Complex.I = ((φ - θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem d021190 {c φ θ w : ℝ} (hc : 0 ≤ c) (hφ : |φ - θ| ≤ w) (hw : w ≤ Real.pi) :
    c * Real.cos w ≤ (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * _root_.GD.N0106.N0428.N0765.N1538.d021186 c φ).re := by
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021189]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (φ - θ)) hw hφ
  rwa [Real.cos_abs] at h


def d021191 (α β : ℝ) : ℝ := (α + β) / 2
def d021192 (α β : ℝ) : ℝ := |α| + |β|

theorem d021193 (α β : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β := add_nonneg (abs_nonneg α) (abs_nonneg β)

theorem d021194 (α β : ℝ) : |_root_.GD.N0106.N0428.N0765.N1538.d021191 α β| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021191 _root_.GD.N0106.N0428.N0765.N1538.d021192
  rw [abs_div, abs_two]
  exact div_le_div_of_nonneg_right (abs_add_le α β) (by norm_num)

theorem d021195 (α β : ℝ) : |β - _root_.GD.N0106.N0428.N0765.N1538.d021191 α β| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021191 _root_.GD.N0106.N0428.N0765.N1538.d021192
  rcases abs_cases α with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases β with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [abs_le] <;> constructor <;> linarith

theorem d021196 (α β : ℝ) : |0 - _root_.GD.N0106.N0428.N0765.N1538.d021191 α β| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021191 _root_.GD.N0106.N0428.N0765.N1538.d021192
  rcases abs_cases α with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases β with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [abs_le] <;> constructor <;> linarith

theorem d021197 (α β : ℝ) : |α - _root_.GD.N0106.N0428.N0765.N1538.d021191 α β| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021191 _root_.GD.N0106.N0428.N0765.N1538.d021192
  rcases abs_cases α with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases β with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [abs_le] <;> constructor <;> linarith

theorem d021198 (α β : ℝ) : |α + β - _root_.GD.N0106.N0428.N0765.N1538.d021191 α β| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021191 _root_.GD.N0106.N0428.N0765.N1538.d021192
  rcases abs_cases α with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases β with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [abs_le] <;> constructor <;> linarith




def d021199 (e b ℓ : ℝ) : ℝ := e * Real.exp b * (1 - ℓ)
def d021200 (ℓ : ℝ) : ℝ := ℓ
def d021201 (e a ℓ : ℝ) : ℝ := (1 + e) * Real.exp a * (ℓ * (1 - ℓ))
def d021202 (e a b ℓ : ℝ) : ℝ := (1 + e) * Real.exp a * Real.exp b * (ℓ * (1 - ℓ))

theorem d021203 {e ℓ : ℝ} (he : 0 ≤ e) (b : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1538.d021199 e b ℓ :=
  mul_nonneg (mul_nonneg he (Real.exp_pos b).le) (sub_nonneg.mpr hℓ.2)

theorem d021204 {ℓ : ℝ} (hℓ : ℓ ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1538.d021200 ℓ := hℓ.1

theorem d021205 {e ℓ : ℝ} (he : 0 ≤ e) (a : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1538.d021201 e a ℓ :=
  mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos a).le)
    (mul_nonneg hℓ.1 (sub_nonneg.mpr hℓ.2))

theorem d021206 {e ℓ : ℝ} (he : 0 ≤ e) (a b : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1538.d021202 e a b ℓ :=
  mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos a).le) (Real.exp_pos b).le)
    (mul_nonneg hℓ.1 (sub_nonneg.mpr hℓ.2))


def d021207 (e a b ℓ : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1538.d021199 e b ℓ + _root_.GD.N0106.N0428.N0765.N1538.d021200 ℓ + _root_.GD.N0106.N0428.N0765.N1538.d021201 e a ℓ + _root_.GD.N0106.N0428.N0765.N1538.d021202 e a b ℓ

theorem d021208 {e ℓ : ℝ} (he : 0 < e) (a b : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021207
  have h3 := _root_.GD.N0106.N0428.N0765.N1538.d021205 he.le a hℓ
  have h4 := _root_.GD.N0106.N0428.N0765.N1538.d021206 he.le a b hℓ
  rcases lt_or_eq_of_le hℓ.1 with hpos | hzero
  · have h1 := _root_.GD.N0106.N0428.N0765.N1538.d021203 he.le b hℓ
    have h2 : 0 < _root_.GD.N0106.N0428.N0765.N1538.d021200 ℓ := hpos
    linarith
  · have h1 : 0 < _root_.GD.N0106.N0428.N0765.N1538.d021199 e b ℓ := by
      unfold _root_.GD.N0106.N0428.N0765.N1538.d021199
      rw [← hzero, sub_zero, mul_one]
      exact mul_pos he (Real.exp_pos b)
    have h2 := _root_.GD.N0106.N0428.N0765.N1538.d021204 hℓ
    linarith

theorem d021209 (e a b : ℝ) : Continuous (_root_.GD.N0106.N0428.N0765.N1538.d021207 e a b) := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021207 _root_.GD.N0106.N0428.N0765.N1538.d021199 _root_.GD.N0106.N0428.N0765.N1538.d021200 _root_.GD.N0106.N0428.N0765.N1538.d021201 _root_.GD.N0106.N0428.N0765.N1538.d021202
  fun_prop


def d021210 (e a b α β ℓ : ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021199 e b ℓ) β + _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021200 ℓ) 0 + _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021201 e a ℓ) α + _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021202 e a b ℓ) (α + β)


theorem d021211 (e a b α β ℓ : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ =
      (e : ℂ) * Complex.exp ((b : ℂ) + (β : ℂ) * Complex.I) * (1 - (ℓ : ℂ)) + (ℓ : ℂ) +
        (1 + (e : ℂ)) * Complex.exp ((a : ℂ) + (α : ℂ) * Complex.I) *
          (1 + Complex.exp ((b : ℂ) + (β : ℂ) * Complex.I)) * ((ℓ : ℂ) * (1 - (ℓ : ℂ))) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1538.d021210, _root_.GD.N0106.N0428.N0765.N1538.d021186, _root_.GD.N0106.N0428.N0765.N1538.d021199, _root_.GD.N0106.N0428.N0765.N1538.d021200, _root_.GD.N0106.N0428.N0765.N1538.d021201, _root_.GD.N0106.N0428.N0765.N1538.d021202, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one]
  push_cast
  simp only [add_mul, Complex.exp_add]
  ring

theorem d021212 (e a b ℓ : ℝ) : _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b 0 0 ℓ = (_root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ : ℂ) := by
  simp [_root_.GD.N0106.N0428.N0765.N1538.d021210, _root_.GD.N0106.N0428.N0765.N1538.d021207, _root_.GD.N0106.N0428.N0765.N1538.d021187]

theorem d021213 (e a b α β : ℝ) : Continuous fun ℓ => _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021210 _root_.GD.N0106.N0428.N0765.N1538.d021186 _root_.GD.N0106.N0428.N0765.N1538.d021199 _root_.GD.N0106.N0428.N0765.N1538.d021200 _root_.GD.N0106.N0428.N0765.N1538.d021201 _root_.GD.N0106.N0428.N0765.N1538.d021202
  fun_prop


theorem d021214 {e ℓ : ℝ} (he : 0 ≤ e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1) :
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ ≤ _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021210 _root_.GD.N0106.N0428.N0765.N1538.d021207
  calc ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021199 e b ℓ) β + _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021200 ℓ) 0 + _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021201 e a ℓ) α +
          _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021202 e a b ℓ) (α + β)‖
      ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021199 e b ℓ) β‖ + ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021200 ℓ) 0‖ + ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021201 e a ℓ) α‖ +
          ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1538.d021202 e a b ℓ) (α + β)‖ :=
        (norm_add_le _ _).trans (_root_.add_le_add ((norm_add_le _ _).trans
          (_root_.add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ = _root_.GD.N0106.N0428.N0765.N1538.d021199 e b ℓ + _root_.GD.N0106.N0428.N0765.N1538.d021200 ℓ + _root_.GD.N0106.N0428.N0765.N1538.d021201 e a ℓ + _root_.GD.N0106.N0428.N0765.N1538.d021202 e a b ℓ := by
        rw [_root_.GD.N0106.N0428.N0765.N1538.d021188 (_root_.GD.N0106.N0428.N0765.N1538.d021203 he b hℓ), _root_.GD.N0106.N0428.N0765.N1538.d021188 (_root_.GD.N0106.N0428.N0765.N1538.d021204 hℓ),
          _root_.GD.N0106.N0428.N0765.N1538.d021188 (_root_.GD.N0106.N0428.N0765.N1538.d021205 he a hℓ), _root_.GD.N0106.N0428.N0765.N1538.d021188 (_root_.GD.N0106.N0428.N0765.N1538.d021206 he a b hℓ)]


def d021215 (α β : ℝ) : ℂ := Complex.exp (((-(_root_.GD.N0106.N0428.N0765.N1538.d021191 α β) : ℝ) : ℂ) * Complex.I)

theorem d021216 (α β : ℝ) : ‖_root_.GD.N0106.N0428.N0765.N1538.d021215 α β‖ = 1 := Complex.norm_exp_ofReal_mul_I _


theorem d021217 {e ℓ : ℝ} (he : 0 ≤ e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β ≤ 2 * Real.pi) :
    Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).re := by
  have hwπ : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 ≤ Real.pi := by linarith
  have e1 := _root_.GD.N0106.N0428.N0765.N1538.d021190 (_root_.GD.N0106.N0428.N0765.N1538.d021203 he b hℓ) (_root_.GD.N0106.N0428.N0765.N1538.d021195 α β) hwπ
  have e2 := _root_.GD.N0106.N0428.N0765.N1538.d021190 (_root_.GD.N0106.N0428.N0765.N1538.d021204 hℓ) (_root_.GD.N0106.N0428.N0765.N1538.d021196 α β) hwπ
  have e3 := _root_.GD.N0106.N0428.N0765.N1538.d021190 (_root_.GD.N0106.N0428.N0765.N1538.d021205 he a hℓ) (_root_.GD.N0106.N0428.N0765.N1538.d021197 α β) hwπ
  have e4 := _root_.GD.N0106.N0428.N0765.N1538.d021190 (_root_.GD.N0106.N0428.N0765.N1538.d021206 he a b hℓ) (_root_.GD.N0106.N0428.N0765.N1538.d021198 α β) hwπ
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021215 _root_.GD.N0106.N0428.N0765.N1538.d021210 _root_.GD.N0106.N0428.N0765.N1538.d021207
  simp only [mul_add, Complex.add_re]
  linarith


theorem d021218 {e ℓ : ℝ} (he : 0 ≤ e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β ≤ 2 * Real.pi) :
    Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ :=
  calc Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ
      ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).re := _root_.GD.N0106.N0428.N0765.N1538.d021217 he a b α β hℓ hw
    _ ≤ |(_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).re| := le_abs_self _
    _ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ := Complex.abs_re_le_norm _
    _ = ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ := by rw [norm_mul, _root_.GD.N0106.N0428.N0765.N1538.d021216, one_mul]

theorem d021219 {α β : ℝ} (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    0 < Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have := _root_.GD.N0106.N0428.N0765.N1538.d021193 α β
    linarith [Real.pi_pos]
  · linarith

theorem d021220 {e ℓ : ℝ} (he : 0 < e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos (_root_.GD.N0106.N0428.N0765.N1538.d021219 hw) (_root_.GD.N0106.N0428.N0765.N1538.d021208 he a b hℓ))
    (_root_.GD.N0106.N0428.N0765.N1538.d021218 he.le a b α β hℓ (by linarith [Real.pi_pos]))




theorem d021221 {u : ℂ} {w : ℝ} (hu : u ≠ 0) (hw0 : 0 ≤ w) (hwπ : w ≤ Real.pi)
    (h : Real.cos w * ‖u‖ ≤ u.re) : |u.arg| ≤ w := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hcos : Real.cos w ≤ Real.cos u.arg := by
    rw [Complex.cos_arg hu, le_div_iff₀ hn]
    exact h
  calc |u.arg| = Real.arccos (Real.cos |u.arg|) :=
        (Real.arccos_cos (abs_nonneg _) (Complex.abs_arg_le_pi u)).symm
    _ = Real.arccos (Real.cos u.arg) := by rw [Real.cos_abs]
    _ ≤ Real.arccos (Real.cos w) := Real.arccos_le_arccos hcos
    _ = w := Real.arccos_cos hw0 hwπ


theorem d021222 {u : ℂ} {θ : ℝ} (hu : u ≠ 0)
    (hθ : θ + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u).arg ∈ Ioc (-Real.pi) Real.pi) :
    u.arg = θ + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u).arg := by
  have hu'ne : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) hu
  have h1 : u = Complex.exp ((θ : ℂ) * Complex.I) *
      (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u) := by
    rw [← mul_assoc, ← Complex.exp_add]
    have h0 : (θ : ℂ) * Complex.I + ((-θ : ℝ) : ℂ) * Complex.I = 0 := by
      push_cast
      ring
    rw [h0, Complex.exp_zero, one_mul]
  have h2 : Complex.exp ((θ : ℂ) * Complex.I) * (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u) =
      (‖Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u‖ : ℂ) *
        Complex.exp (((θ + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u).arg : ℝ) : ℂ) *
          Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u)]
    rw [mul_left_comm, ← Complex.exp_add]
    have h3 : (θ : ℂ) * Complex.I +
        ((Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u).arg : ℂ) * Complex.I =
        ((θ + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u).arg : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h3]
  have h4 : Complex.exp (((θ + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u).arg : ℝ) : ℂ) *
        Complex.I) =
      Complex.cos ((θ + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u).arg : ℝ) : ℂ) +
        Complex.sin ((θ + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u).arg : ℝ) : ℂ) *
          Complex.I :=
    Complex.exp_mul_I (x := ((θ + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * u).arg : ℝ) : ℂ))
  conv_lhs => rw [h1, h2, h4]
  exact Complex.arg_mul_cos_add_sin_mul_I (norm_pos_iff.mpr hu'ne) hθ


theorem d021223 {e ℓ : ℝ} (he : 0 < e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    |(_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg - _root_.GD.N0106.N0428.N0765.N1538.d021191 α β| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 := by
  have hu := _root_.GD.N0106.N0428.N0765.N1538.d021220 he a b α β hℓ hw
  have hw2 : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have hu'ne : _root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) hu
  have hcos : Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * ‖_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ ≤
      (_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).re := by
    rw [norm_mul, _root_.GD.N0106.N0428.N0765.N1538.d021216, one_mul]
    calc Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖
        ≤ Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ :=
          mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1538.d021214 he.le a b α β hℓ)
            (_root_.GD.N0106.N0428.N0765.N1538.d021219 hw).le
      _ ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).re := _root_.GD.N0106.N0428.N0765.N1538.d021217 he.le a b α β hℓ hw2
  have harg' : |(_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 :=
    _root_.GD.N0106.N0428.N0765.N1538.d021221 hu'ne (by linarith [_root_.GD.N0106.N0428.N0765.N1538.d021193 α β]) (by linarith [Real.pi_pos]) hcos
  have hmid := _root_.GD.N0106.N0428.N0765.N1538.d021194 α β
  have hθ : _root_.GD.N0106.N0428.N0765.N1538.d021191 α β + (_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg ∈ Ioc (-Real.pi) Real.pi := by
    obtain ⟨ha1, ha2⟩ := abs_le.mp harg'
    obtain ⟨hm1, hm2⟩ := abs_le.mp hmid
    constructor <;> linarith
  have heq : (_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg =
      _root_.GD.N0106.N0428.N0765.N1538.d021191 α β + (_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg :=
    _root_.GD.N0106.N0428.N0765.N1538.d021222 hu hθ
  rw [heq, add_sub_cancel_left]
  exact harg'

theorem d021224 {e ℓ : ℝ} (he : 0 < e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : |(_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β := by
  have h1 := _root_.GD.N0106.N0428.N0765.N1538.d021223 he a b α β hℓ hw
  have h2 := _root_.GD.N0106.N0428.N0765.N1538.d021194 α β
  calc |(_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg|
      = |((_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg - _root_.GD.N0106.N0428.N0765.N1538.d021191 α β) + _root_.GD.N0106.N0428.N0765.N1538.d021191 α β| := by ring_nf
    _ ≤ |(_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg - _root_.GD.N0106.N0428.N0765.N1538.d021191 α β| + |_root_.GD.N0106.N0428.N0765.N1538.d021191 α β| := abs_add_le _ _
    _ ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 + _root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2 := add_le_add h1 h2
    _ = _root_.GD.N0106.N0428.N0765.N1538.d021192 α β := by ring

theorem d021225 {e ℓ : ℝ} (he : 0 < e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ ∈ Complex.slitPlane := by
  have hne := _root_.GD.N0106.N0428.N0765.N1538.d021220 he a b α β hℓ hw
  have hlt : (_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg < Real.pi :=
    lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt (_root_.GD.N0106.N0428.N0765.N1538.d021224 he a b α β hℓ hw) hw)
  rcases Complex.arg_lt_pi_iff.mp hlt with hre | him
  · rw [Complex.mem_slitPlane_iff]
    by_cases him0 : (_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).im = 0
    · left
      rcases lt_or_eq_of_le hre with h | h
      · exact h
      · exact absurd (Complex.ext h.symm him0) hne
    · exact Or.inr him0
  · exact Complex.mem_slitPlane_iff.mpr (Or.inr him)




def d021226 (e a b α β ℓ : ℝ) : ℂ :=
  ((ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2) : ℝ) * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ ^ (-((21 : ℂ) / 2))

theorem d021227 {e : ℝ} (he : 0 < e) (a b α β : ℝ) (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β) (Icc (0 : ℝ) 1) := by
  have hr : Continuous (fun ℓ : ℝ => (ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2)) :=
    (Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021226
  exact (Complex.continuous_ofReal.comp hr).continuousOn.mul
    ((_root_.GD.N0106.N0428.N0765.N1538.d021213 e a b α β).continuousOn.cpow_const
      fun ℓ hℓ => _root_.GD.N0106.N0428.N0765.N1538.d021225 he a b α β hℓ hw)


def d021228 (α β : ℝ) : ℂ :=
  Complex.exp ((((21 : ℝ) / 2) * (α + β) / 2 : ℝ) * Complex.I)

theorem d021229 (α β : ℝ) : ‖_root_.GD.N0106.N0428.N0765.N1538.d021228 α β‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem d021230 {e ℓ : ℝ} (he : 0 < e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ).re =
      ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ‖ *
        Real.cos (((21 : ℝ) / 2) * ((α + β) / 2 - (_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg)) := by
  let w : ℝ := (ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2)
  have hw0 : 0 ≤ w := Real.rpow_nonneg (mul_nonneg hℓ.1 (sub_nonneg.mpr hℓ.2)) _
  have hrot : _root_.GD.N0106.N0428.N0765.N1538.d021228 α β =
      Complex.exp ((((21 : ℝ) / 2) * (α + β) / 2 : ℝ) * Complex.I) := rfl
  have hp := _root_.GD.N0106.N0428.N0765.N1536.d021173 (_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ) (_root_.GD.N0106.N0428.N0765.N1538.d021220 he a b α β hℓ hw)
    ((21 : ℝ) / 2) (α + β)
  push_cast at hp hrot
  rw [← hrot] at hp
  have hmul : _root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ =
      (w : ℂ) * (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ ^ (-((21 : ℂ) / 2))) := by
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021226 w
    ring
  have hn : ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ‖ = w * ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ ^ (-((21 : ℂ) / 2))‖ := by
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021226
    rw [norm_mul, Complex.norm_of_nonneg hw0]
  rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hp, hn]
  ring


def d021231 (α β : ℝ) : ℝ := Real.cos (((21 : ℝ) / 2) * (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2))

theorem d021232 {α β : ℝ} (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    0 < _root_.GD.N0106.N0428.N0765.N1538.d021231 α β := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021231
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have := _root_.GD.N0106.N0428.N0765.N1538.d021193 α β
    nlinarith [Real.pi_pos]
  · linarith

theorem d021233 {α β : ℝ} (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi := by
  linarith [_root_.GD.N0106.N0428.N0765.N1538.d021193 α β]


theorem d021234 {e ℓ : ℝ} (he : 0 < e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1538.d021231 α β * ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ‖ ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ).re := by
  have hwπ := _root_.GD.N0106.N0428.N0765.N1538.d021233 hw
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021230 he a b α β hℓ hwπ]
  have ha : |((21 : ℝ) / 2) * ((α + β) / 2 - (_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ).arg)| ≤
      ((21 : ℝ) / 2) * (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 21 / 2)]
    have h := _root_.GD.N0106.N0428.N0765.N1538.d021223 he a b α β hℓ hwπ
    rw [abs_sub_comm] at h
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021191 at h
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    (show ((21 : ℝ) / 2) * (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ≤ Real.pi by linarith) ha
  rw [Real.cos_abs] at hc
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021231
  nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg (_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ))]




def d021235 (e a b ℓ : ℝ) : ℝ :=
  (ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ ^ (-((21 : ℝ) / 2))

theorem d021236 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1538.d021235 e a b) (Icc (0 : ℝ) 1) := by
  have hr : Continuous (fun ℓ : ℝ => (ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2)) :=
    (Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021235
  exact hr.continuousOn.mul ((_root_.GD.N0106.N0428.N0765.N1538.d021209 e a b).continuousOn.rpow_const
    fun ℓ hℓ => Or.inl (_root_.GD.N0106.N0428.N0765.N1538.d021208 he a b hℓ).ne')

theorem d021237 {e ℓ : ℝ} (he : 0 < e) (a b : ℝ) (hℓ : ℓ ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021235
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos hℓ.1 (sub_pos.mpr hℓ.2)) _)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1538.d021208 he a b (Ioo_subset_Icc_self hℓ)) _)

theorem d021238 {e ℓ : ℝ} (he : 0 < e) (a b : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021235
  exact mul_nonneg (Real.rpow_nonneg (mul_nonneg hℓ.1 (sub_nonneg.mpr hℓ.2)) _)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1538.d021208 he a b hℓ) _).le

theorem d021239 {e ℓ : ℝ} (he : 0 < e) (a b : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b 0 0 ℓ = (_root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021226, _root_.GD.N0106.N0428.N0765.N1538.d021212]
  have hp := Complex.ofReal_cpow (_root_.GD.N0106.N0428.N0765.N1538.d021208 he a b hℓ).le (-((21 : ℝ) / 2))
  push_cast at hp
  rw [← hp]
  simp only [_root_.GD.N0106.N0428.N0765.N1538.d021235, Complex.ofReal_mul]


theorem d021240 {e ℓ : ℝ} (he : 0 < e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ‖ =
      (ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2) * ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ ^ (-((21 : ℝ) / 2)) := by
  have hu := _root_.GD.N0106.N0428.N0765.N1538.d021220 he a b α β hℓ hw
  have hexp : (-((21 : ℂ) / 2)) = ((-((21 : ℝ) / 2) : ℝ) : ℂ) := by norm_num
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021226
  rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg hℓ.1 (sub_nonneg.mpr hℓ.2)) _),
    hexp, Complex.norm_cpow_of_ne_zero hu, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    Real.exp_zero, div_one]

theorem d021241 {e ℓ : ℝ} (he : 0 < e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ‖ ≤
      Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ := by
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021240 he a b α β hℓ hw]
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021235
  have hc := _root_.GD.N0106.N0428.N0765.N1538.d021219 hw
  have hW := _root_.GD.N0106.N0428.N0765.N1538.d021208 he a b hℓ
  have hlow : Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ :=
    _root_.GD.N0106.N0428.N0765.N1538.d021218 he.le a b α β hℓ (by linarith [Real.pi_pos])
  have hpow : ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ ^ (-((21 : ℝ) / 2)) ≤
      (Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ) ^ (-((21 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hc hW) hlow (by norm_num)
  rw [Real.mul_rpow hc.le hW.le] at hpow
  have h9 : 0 ≤ (ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2) :=
    Real.rpow_nonneg (mul_nonneg hℓ.1 (sub_nonneg.mpr hℓ.2)) _
  calc (ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2) * ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ ^ (-((21 : ℝ) / 2))
      ≤ (ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2) * (Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) *
          _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ ^ (-((21 : ℝ) / 2))) := mul_le_mul_of_nonneg_left hpow h9
    _ = Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) *
          ((ℓ * (1 - ℓ)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ ^ (-((21 : ℝ) / 2))) := by ring

theorem d021242 {e ℓ : ℝ} (he : 0 < e) (a b α β : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ‖ := by
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021240 he a b α β hℓ hw]
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021235
  have hpos : 0 < ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ := norm_pos_iff.mpr (_root_.GD.N0106.N0428.N0765.N1538.d021220 he a b α β hℓ hw)
  have hle : ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ ≤ _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ := _root_.GD.N0106.N0428.N0765.N1538.d021214 he.le a b α β hℓ
  have hpow : _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ ^ (-((21 : ℝ) / 2)) ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β ℓ‖ ^ (-((21 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  exact mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg (mul_nonneg hℓ.1 (sub_nonneg.mpr hℓ.2)) _)

def d021243 (e a b α β : ℝ) : ℂ := ∫ ℓ in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ
def d021244 (e a b α β : ℝ) : ℂ := ∫ ℓ in (0 : ℝ)..1, (ℓ : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ
def d021245 (e a b : ℝ) : ℝ := ∫ ℓ in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ
def d021246 (e a b : ℝ) : ℝ := ∫ ℓ in (0 : ℝ)..1, ℓ * _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ


def d021247 (e a b α β : ℝ) : ℂ := ((e⁻¹ : ℝ) : ℂ) * (_root_.GD.N0106.N0428.N0765.N1538.d021244 e a b α β / _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β)

theorem d021248 {e : ℝ} (he : 0 < e) (a b : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021245
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((_root_.GD.N0106.N0428.N0765.N1538.d021236 he a b).intervalIntegrable_of_Icc zero_le_one)
    (fun ℓ hℓ => _root_.GD.N0106.N0428.N0765.N1538.d021237 he a b hℓ) zero_lt_one

theorem d021249 {e : ℝ} (he : 0 < e) (a b : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1538.d021246 e a b := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021246
  apply intervalIntegral.integral_nonneg zero_le_one
  intro ℓ hℓ
  exact mul_nonneg hℓ.1 (_root_.GD.N0106.N0428.N0765.N1538.d021238 he a b hℓ)


theorem d021250 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1538.d021231 α β * _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ := by
  have hwπ := _root_.GD.N0106.N0428.N0765.N1538.d021233 hw
  have hk := _root_.GD.N0106.N0428.N0765.N1538.d021227 he a b α β hwπ
  have hkr := _root_.GD.N0106.N0428.N0765.N1538.d021236 he a b
  have hr : ContinuousOn (fun ℓ => (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ).re) (Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn' (continuousOn_const.mul hk)
  have hre : (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β).re =
      ∫ ℓ in (0 : ℝ)..1, (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ).re := by
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021243
    rw [← intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact (integral_re ((hk.intervalIntegrable_of_Icc zero_le_one).1.const_mul
      (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β))).symm
  have hm : _root_.GD.N0106.N0428.N0765.N1538.d021231 α β * _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β).re := by
    rw [hre, _root_.GD.N0106.N0428.N0765.N1538.d021245, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on zero_le_one
      ((continuousOn_const.mul hkr).intervalIntegrable_of_Icc zero_le_one)
      (hr.intervalIntegrable_of_Icc zero_le_one)
      (fun ℓ hℓ => (mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1538.d021242 he a b α β hℓ hwπ)
        (_root_.GD.N0106.N0428.N0765.N1538.d021232 hw).le).trans (_root_.GD.N0106.N0428.N0765.N1538.d021234 he a b α β hℓ hw))
  calc _root_.GD.N0106.N0428.N0765.N1538.d021231 α β * _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β).re := hm
    _ ≤ |(_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β).re| := le_abs_self _
    _ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ := Complex.abs_re_le_norm _
    _ = ‖_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ := by rw [norm_mul, _root_.GD.N0106.N0428.N0765.N1538.d021229, one_mul]


theorem d021251 {e : ℝ} (he : 0 < e) (a b α β : ℝ) (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021244 e a b α β‖ ≤
      Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1538.d021246 e a b := by
  have hk := _root_.GD.N0106.N0428.N0765.N1538.d021227 he a b α β hw
  have hkr := _root_.GD.N0106.N0428.N0765.N1538.d021236 he a b
  have hn := Complex.continuous_ofReal.continuousOn.mul hk
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021244 _root_.GD.N0106.N0428.N0765.N1538.d021246
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one
    (hn.norm.intervalIntegrable_of_Icc zero_le_one)
    ((continuousOn_const.mul (continuousOn_id.mul hkr)).intervalIntegrable_of_Icc zero_le_one)
  intro ℓ hℓ
  change ‖(ℓ : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ‖ ≤
    Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * (ℓ * _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ)
  rw [norm_mul, Complex.norm_of_nonneg hℓ.1]
  have h := _root_.GD.N0106.N0428.N0765.N1538.d021241 he a b α β hℓ hw
  calc ℓ * ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β ℓ‖
      ≤ ℓ * (Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ) :=
        mul_le_mul_of_nonneg_left h hℓ.1
    _ = Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * (ℓ * _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ) := by ring



theorem d021252 (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 = Real.sigmoid a ∧
      _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 = (1 - Real.sigmoid a) * Real.sigmoid b ∧
      _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2 = (1 - Real.sigmoid a) * (1 - Real.sigmoid b) :=
  ⟨rfl, rfl, rfl⟩


theorem d021253 {e : ℝ} (he : 0 < e) (a b ℓ : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021207 e a b ℓ =
      (e * (1 + Real.exp a) * (1 + Real.exp b)) *
        _root_.GD.N0106.N0428.N0765.N1534.d005328 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2) ℓ := by
  obtain ⟨h0, h1, h2⟩ := _root_.GD.N0106.N0428.N0765.N1538.d021252 a b
  rw [h0, h1, h2]
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021207 _root_.GD.N0106.N0428.N0765.N1538.d021199 _root_.GD.N0106.N0428.N0765.N1538.d021200 _root_.GD.N0106.N0428.N0765.N1538.d021201 _root_.GD.N0106.N0428.N0765.N1538.d021202 _root_.GD.N0106.N0428.N0765.N1534.d005328
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369, _root_.GD.N0106.N0428.N0765.N1539.d005369]
  have ha : (1 + Real.exp a) ≠ 0 := by positivity
  have hb : (1 + Real.exp b) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem d021254 (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 / _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2 = Real.exp b := by
  obtain ⟨_, h1, h2⟩ := _root_.GD.N0106.N0428.N0765.N1538.d021252 a b
  rw [h1, h2, mul_div_mul_left _ _ (sub_pos.mpr (Real.sigmoid_lt_one a)).ne',
    _root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369]
  have hb : (1 + Real.exp b) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem d021255 {e ℓ : ℝ} (he : 0 < e) (a b : ℝ) (hℓ : ℓ ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1538.d021235 e a b ℓ =
      (e * (1 + Real.exp a) * (1 + Real.exp b)) ^ (-((21 : ℝ) / 2)) *
        _root_.GD.N0106.N0428.N0765.N1534.d005329 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2) ℓ := by
  have hK0 : 0 < e * (1 + Real.exp a) * (1 + Real.exp b) := by positivity
  have hC : 0 < _root_.GD.N0106.N0428.N0765.N1534.d005328 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1)
      (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2) ℓ := by
    have h := _root_.GD.N0106.N0428.N0765.N1538.d021208 he a b hℓ
    rw [_root_.GD.N0106.N0428.N0765.N1538.d021253 he a b ℓ] at h
    exact (mul_pos_iff_of_pos_left hK0).mp h
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021235 _root_.GD.N0106.N0428.N0765.N1534.d005329
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021253 he a b ℓ, Real.mul_rpow hK0.le hC.le]
  ring

theorem d021256 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b =
      (e * (1 + Real.exp a) * (1 + Real.exp b)) ^ (-((21 : ℝ) / 2)) *
        ∫ ℓ in (0 : ℝ)..1,
          _root_.GD.N0106.N0428.N0765.N1534.d005329 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2) ℓ := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021245
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro ℓ hℓ
  rw [uIcc_of_le zero_le_one] at hℓ
  exact _root_.GD.N0106.N0428.N0765.N1538.d021255 he a b hℓ

theorem d021257 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021246 e a b =
      (e * (1 + Real.exp a) * (1 + Real.exp b)) ^ (-((21 : ℝ) / 2)) *
        ∫ ℓ in (0 : ℝ)..1, ℓ *
          _root_.GD.N0106.N0428.N0765.N1534.d005329 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2) ℓ := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021246
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro ℓ hℓ
  rw [uIcc_of_le zero_le_one] at hℓ
  dsimp only
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021255 he a b hℓ]
  ring


theorem d021258 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    e⁻¹ * (_root_.GD.N0106.N0428.N0765.N1538.d021246 e a b / _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b) =
      e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) := by
  have hK0 : 0 < e * (1 + Real.exp a) * (1 + Real.exp b) := by positivity
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021257 he a b, _root_.GD.N0106.N0428.N0765.N1538.d021256 he a b,
    mul_div_mul_left _ _ (Real.rpow_pos_of_pos hK0 _).ne']
  rfl




theorem d021259 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021247 e a b α β‖ ≤
      Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹ *
        (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b))) := by
  have hwπ := _root_.GD.N0106.N0428.N0765.N1538.d021233 hw
  have hD := _root_.GD.N0106.N0428.N0765.N1538.d021250 he a b α β hw
  have hN := _root_.GD.N0106.N0428.N0765.N1538.d021251 he a b α β hwπ
  have hs := _root_.GD.N0106.N0428.N0765.N1538.d021232 hw
  have hDr := _root_.GD.N0106.N0428.N0765.N1538.d021248 he a b
  have hNr := _root_.GD.N0106.N0428.N0765.N1538.d021249 he a b
  have hDc : 0 < ‖_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ := lt_of_lt_of_le (mul_pos hs hDr) hD
  have hc : 0 ≤ Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) :=
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1538.d021219 hwπ) _).le
  rw [← _root_.GD.N0106.N0428.N0765.N1538.d021258 he a b]
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021247
  rw [norm_mul, Complex.norm_of_nonneg (inv_pos.mpr he).le, norm_div]
  have key : ‖_root_.GD.N0106.N0428.N0765.N1538.d021244 e a b α β‖ / ‖_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ ≤
      (Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1538.d021246 e a b) /
        (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β * _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b) := by
    rw [div_le_div_iff₀ hDc (mul_pos hs hDr)]
    exact mul_le_mul hN hD (mul_pos hs hDr).le (mul_nonneg hc hNr)
  calc e⁻¹ * (‖_root_.GD.N0106.N0428.N0765.N1538.d021244 e a b α β‖ / ‖_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖)
      ≤ e⁻¹ * ((Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1538.d021246 e a b) /
          (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β * _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b)) :=
        mul_le_mul_of_nonneg_left key (inv_pos.mpr he).le
    _ = Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹ *
          (e⁻¹ * (_root_.GD.N0106.N0428.N0765.N1538.d021246 e a b / _root_.GD.N0106.N0428.N0765.N1538.d021245 e a b)) := by ring


theorem d021260 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ≤ (3 / 2 : ℝ) * Real.exp b := by
  obtain ⟨h0, h1, h2⟩ := _root_.GD.N0106.N0428.N0765.N1538.d021252 a b
  have hu : 0 ≤ _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 := by
    rw [h0]
    exact (Real.sigmoid_pos a).le
  have hv : 0 < _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 := by
    rw [h1]
    exact mul_pos (sub_pos.mpr (Real.sigmoid_lt_one a)) (Real.sigmoid_pos b)
  have hw : 0 < _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2 := by
    rw [h2]
    exact mul_pos (sub_pos.mpr (Real.sigmoid_lt_one a)) (sub_pos.mpr (Real.sigmoid_lt_one b))
  have h := _root_.GD.N0106.N0428.N0765.N1681.d005962 (inv_pos.mpr he) hu hv hw
  rw [inv_inv] at h
  have hfrac : _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 / (e * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 + _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2) ≤
      _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 / _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2 := by
    rw [div_le_div_iff₀ (by positivity) hw]
    nlinarith [mul_nonneg he.le hv.le]
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020799
  calc e⁻¹ * _root_.GD.N0106.N0428.N0765.N1534.d005330 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2)
      ≤ (3 / 2 : ℝ) * (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 / (e * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 + _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2)) := h
    _ ≤ (3 / 2 : ℝ) * (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 / _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2) :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
    _ = (3 / 2 : ℝ) * Real.exp b := by rw [_root_.GD.N0106.N0428.N0765.N1538.d021254]


theorem d021261 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021247 e a b α β‖ ≤
      Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹ *
        ((3 / 2 : ℝ) * Real.exp b) := by
  refine (_root_.GD.N0106.N0428.N0765.N1538.d021259 he a b α β hw).trans ?_
  apply mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1538.d021260 he a b)
  exact mul_nonneg (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1538.d021219 (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)) _).le
    (inv_pos.mpr (_root_.GD.N0106.N0428.N0765.N1538.d021232 hw)).le

end
end GD.N0106.N0428.N0765.N1538
