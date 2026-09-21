import GD.Module0677










open MeasureTheory Set

namespace GD.N0232.N0719.N0922

noncomputable section

open _root_.GD.N0232.N0719.N0928



def d009948 : ℝ :=
  Real.sqrt (2 * Real.pi) * Real.Gamma 8

theorem d009949 : 0 < _root_.GD.N0232.N0719.N0922.d009948 := by
  exact mul_pos (Real.sqrt_pos.2 (by positivity))
    (Real.Gamma_pos_of_pos (by norm_num))



theorem d009950
    (p y t : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 p y t (5 / 2) =
      _root_.GD.N0232.N0719.N0922.d009948 * _root_.GD.N0232.N0719.N0928.d009409 _root_.GD.N0232.N0719.N0922.d009915 p *
        _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0922.d009915 p y t ^ (-(8 : ℝ)) := by
  unfold _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009948
  rw [_root_.GD.N0232.N0719.N0922.d009919]
  ring




theorem d009951
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t)
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009926) :
    _root_.GD.N0232.N0719.N0922.d009948 *
          ((1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3) *
          (7 * (ε + (xz.1 + xz.2))) ^ (-(8 : ℝ))
      ≤ _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) ∧
    _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2)
      ≤ _root_.GD.N0232.N0719.N0922.d009948 *
          ((1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3) *
          ((1 / 2 : ℝ) * (ε + (xz.1 + xz.2))) ^ (-(8 : ℝ)) := by
  have hbase : 0 < ε + (xz.1 + xz.2) := by
    rcases hE with ⟨hε, _⟩
    linarith [hxz.1, hxz.2.1]
  have hlowerPos : 0 < (1 / 2 : ℝ) * (ε + (xz.1 + xz.2)) :=
    mul_pos (by norm_num) hbase
  have henergyLower := _root_.GD.N0232.N0719.N0922.d009931 hE hxz
  have henergyPos :
      0 < _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t :=
    lt_of_lt_of_le hlowerPos henergyLower
  have henergyUpper := _root_.GD.N0232.N0719.N0922.d009933 hE hxz
  have hpowUpper :
      _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t ^ (-(8 : ℝ)) ≤
        ((1 / 2 : ℝ) * (ε + (xz.1 + xz.2))) ^ (-(8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hlowerPos henergyLower (by norm_num)
  have hpowLower :
      (7 * (ε + (xz.1 + xz.2))) ^ (-(8 : ℝ)) ≤
        _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t ^ (-(8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos henergyPos henergyUpper (by norm_num)
  have hmonoEq := _root_.GD.N0232.N0719.N0922.d009935 hxz
  have hmonoNonneg :
      0 ≤ (1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3 := by
    have hp0 : 0 ≤ 1 - xz.1 - xz.2 := by linarith [hxz.2.2]
    have hx : 0 ≤ xz.1 := hxz.1.le
    have hz : 0 ≤ xz.2 := hxz.2.1.le
    exact mul_nonneg
      (mul_nonneg hp0 (pow_nonneg hx 3))
      (pow_nonneg hz 3)
  have hfrontMono :
      0 ≤ _root_.GD.N0232.N0719.N0922.d009948 *
        ((1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3) :=
    mul_nonneg _root_.GD.N0232.N0719.N0922.d009949.le hmonoNonneg
  rw [_root_.GD.N0232.N0719.N0922.d009950, hmonoEq]
  exact ⟨
    mul_le_mul_of_nonneg_left hpowLower hfrontMono,
    mul_le_mul_of_nonneg_left hpowUpper hfrontMono⟩




def d009952 : Set (ℝ × ℝ) :=
  Set.Icc ((1 / 4 : ℝ), (1 / 4 : ℝ))
    ((1 / 3 : ℝ), (1 / 3 : ℝ))

theorem d009953 :
    _root_.GD.N0232.N0719.N0922.d009952 ⊆ _root_.GD.N0232.N0719.N0922.d009926 := by
  rintro xz ⟨hl, hu⟩
  exact ⟨by linarith [hl.1], by linarith [hl.2], by linarith [hu.1, hu.2]⟩




theorem d009954
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t)
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009952) :
    _root_.GD.N0232.N0719.N0922.d009948 *
        ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ 6) *
        (12 : ℝ) ^ (-(8 : ℝ)) ≤
      _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) := by
  have htri := _root_.GD.N0232.N0719.N0922.d009953 hxz
  have hsandwich := (_root_.GD.N0232.N0719.N0922.d009951 hE htri).1
  have hε : ε ≤ 1 := hE.2.1
  have hp0 : (1 / 3 : ℝ) ≤ 1 - xz.1 - xz.2 := by
    linarith [hxz.2.1, hxz.2.2]
  have hx : (1 / 4 : ℝ) ≤ xz.1 := hxz.1.1
  have hz : (1 / 4 : ℝ) ≤ xz.2 := hxz.1.2
  have hx0 : 0 ≤ xz.1 := by linarith
  have hz0 : 0 ≤ xz.2 := by linarith
  have hmono :
      (1 / 3 : ℝ) * (1 / 4 : ℝ) ^ 6 ≤
        (1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3 := by
    have hx3 : (1 / 4 : ℝ) ^ 3 ≤ xz.1 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hx 3
    have hz3 : (1 / 4 : ℝ) ^ 3 ≤ xz.2 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hz 3
    have hprod : (1 / 4 : ℝ) ^ 6 ≤ xz.1 ^ 3 * xz.2 ^ 3 := by
      rw [show (1 / 4 : ℝ) ^ 6 = (1 / 4 : ℝ) ^ 3 * (1 / 4 : ℝ) ^ 3 by ring]
      exact mul_le_mul hx3 hz3 (by positivity) (pow_nonneg hx0 3)
    calc
      (1 / 3 : ℝ) * (1 / 4 : ℝ) ^ 6 ≤
          (1 / 3 : ℝ) * (xz.1 ^ 3 * xz.2 ^ 3) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ ≤ (1 - xz.1 - xz.2) * (xz.1 ^ 3 * xz.2 ^ 3) :=
        mul_le_mul_of_nonneg_right hp0
          (mul_nonneg (pow_nonneg hx0 3) (pow_nonneg hz0 3))
      _ = (1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3 := by ring
  have hscale : 7 * (ε + (xz.1 + xz.2)) ≤ 12 := by
    linarith [hxz.2.1, hxz.2.2]
  have hscalePos : 0 < 7 * (ε + (xz.1 + xz.2)) := by
    have : 0 < ε := hE.1
    positivity
  have hpow :
      (12 : ℝ) ^ (-(8 : ℝ)) ≤
        (7 * (ε + (xz.1 + xz.2))) ^ (-(8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hscalePos hscale (by norm_num)
  have hf := _root_.GD.N0232.N0719.N0922.d009949.le
  have hm0 : 0 ≤ (1 / 3 : ℝ) * (1 / 4 : ℝ) ^ 6 := by positivity
  have hm : 0 ≤
      (1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3 := by
    have : 0 ≤ 1 - xz.1 - xz.2 := by linarith [hxz.2.1, hxz.2.2]
    positivity
  calc
    _root_.GD.N0232.N0719.N0922.d009948 * ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ 6) *
        (12 : ℝ) ^ (-(8 : ℝ)) ≤
      _root_.GD.N0232.N0719.N0922.d009948 *
          ((1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3) *
          (12 : ℝ) ^ (-(8 : ℝ)) := by
            gcongr
    _ ≤ _root_.GD.N0232.N0719.N0922.d009948 *
          ((1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3) *
          (7 * (ε + (xz.1 + xz.2))) ^ (-(8 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hf hm)
    _ ≤ _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) :=
      hsandwich



theorem d009955
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t)
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009952) :
    _root_.GD.N0232.N0719.N0922.d009948 *
        ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ 6) *
        (12 : ℝ) ^ (-(8 : ℝ)) * (1 / 2 : ℝ) ≤
      _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) *
        (_root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0922.d009922 xz) y - y 0) := by
  have hk := _root_.GD.N0232.N0719.N0922.d009954 hE hxz
  have hr := _root_.GD.N0232.N0719.N0922.d009934 hE
    (_root_.GD.N0232.N0719.N0922.d009953 hxz)
  have hhalf : (1 / 2 : ℝ) ≤ xz.1 + xz.2 := by
    linarith [hxz.1.1, hxz.1.2]
  have hresponse : (1 / 2 : ℝ) ≤
      _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0922.d009922 xz) y - y 0 := hhalf.trans hr
  have hfloorNonneg : 0 ≤ _root_.GD.N0232.N0719.N0922.d009948 *
      ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ 6) *
      (12 : ℝ) ^ (-(8 : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg _root_.GD.N0232.N0719.N0922.d009949.le (by positivity))
      (Real.rpow_nonneg (by norm_num) _)
  have hkernelNonneg : 0 ≤
      _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) :=
    le_trans hfloorNonneg hk
  exact mul_le_mul hk hresponse (by norm_num) hkernelNonneg

end

end GD.N0232.N0719.N0922
