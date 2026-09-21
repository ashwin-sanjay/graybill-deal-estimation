import GD.Module1376
import GD.Module0354

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set
open scoped BigOperators

namespace GD.N0057
noncomputable section

open _root_.GD.N0062 _root_.GD.N0025

def d022147 (t u z : ℝ) : ℝ := z ^ 2 + _root_.GD.N0062.d022142 t u

def d022148 (t p q R : ℝ) : ℝ := 10 * p / ((t * (1 - t)) ^ 2 * q ^ 3 * R)

def d022149 (t p u z : ℝ) : ℝ :=
  _root_.GD.N0057.d022148 t p (_root_.GD.N0057.d022147 t u z) (Real.sqrt (_root_.GD.N0057.d022147 t u z))

def d022150 (t p u z : ℝ) : ℝ := 3 * z ^ 2 * _root_.GD.N0057.d022149 t p u z

def d022151 (t u₀ z₀ u y : ℝ) : ℝ :=
  1 - 7 / (2 * _root_.GD.N0057.d022147 t u₀ z₀) *
    ((2 / t - 2 / (1 - t)) * (u - u₀) + 2 / (3 * z₀) * (y - z₀ ^ 3))


def d022152 (c : _root_.GD.N0025.d005225) : Fin 4 :=
  ⟨2 * (c.1 : ℕ) + (c.2 : ℕ), by omega⟩

theorem d022153 : Function.Bijective _root_.GD.N0057.d022152 := by decide

def d022154 : _root_.GD.N0025.d005225 ≃ Fin 4 := Equiv.ofBijective _root_.GD.N0057.d022152 _root_.GD.N0057.d022153

theorem d022155 (f : Fin 4 → ℝ) :
    (∑ k : _root_.GD.N0025.d005225, f (_root_.GD.N0057.d022152 k)) = ∑ j : Fin 4, f j :=
  Equiv.sum_comp _root_.GD.N0057.d022154 f

theorem d022156 {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) : 0 < _root_.GD.N0062.d022142 t u := by
  by_cases hzero : u = 0
  · subst u
    simpa [_root_.GD.N0062.d022142] using div_pos (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr ht.2)
  · have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hzero)
    exact add_pos_of_nonneg_of_pos
      (div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hu.2))
        (sub_pos.mpr ht.2).le)
      (div_pos (mul_pos (by norm_num) hupos) ht.1)

theorem d022157 {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (z : ℝ) : 0 < _root_.GD.N0057.d022147 t u z :=
  add_pos_of_nonneg_of_pos (sq_nonneg z) (_root_.GD.N0057.d022156 ht hu)

theorem d022158 {t p u z : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hp : 0 ≤ p) (hu : u ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0057.d022150 t p u z := by
  have hq := _root_.GD.N0057.d022157 ht hu z
  unfold _root_.GD.N0057.d022150 _root_.GD.N0057.d022149 _root_.GD.N0057.d022148
  positivity

theorem d022159 (t u u₀ : ℝ) :
    _root_.GD.N0062.d022142 t u - _root_.GD.N0062.d022142 t u₀ = (2 / t - 2 / (1 - t)) * (u - u₀) := by
  unfold _root_.GD.N0062.d022142
  ring


theorem d022160 {t p q R : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hp : 0 ≤ p) (hq : 0 < q) (hR : 0 < R) (hroot : q ≤ R ^ 2) :
    _root_.GD.N0057.d022148 t p q R ≤ _root_.GD.N0057.d022148 t p q (Real.sqrt q) := by
  have hsq : Real.sqrt q ≤ R := Real.sqrt_le_iff.mpr ⟨hR.le, hroot⟩
  have hden : 0 < (t * (1 - t)) ^ 2 * q ^ 3 := by
    exact mul_pos (sq_pos_of_pos (mul_pos ht.1 (sub_pos.mpr ht.2))) (pow_pos hq 3)
  unfold _root_.GD.N0057.d022148
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hp)
    (mul_pos hden (Real.sqrt_pos.mpr hq))
    (mul_le_mul_of_nonneg_left hsq hden.le)


theorem d022161 {t p u z u₀ z₀ : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hp : 0 ≤ p) (hu : u ∈ Icc (0 : ℝ) 1)
    (hz : 0 ≤ z) (hz₀ : 0 < z₀) (hq₀ : 0 < _root_.GD.N0057.d022147 t u₀ z₀) :
    _root_.GD.N0057.d022148 t p (_root_.GD.N0057.d022147 t u₀ z₀) (Real.sqrt (_root_.GD.N0057.d022147 t u₀ z₀)) *
      _root_.GD.N0057.d022151 t u₀ z₀ u (z ^ 3) ≤ _root_.GD.N0057.d022149 t p u z := by
  have hq := _root_.GD.N0057.d022157 ht hu z
  have h := _root_.GD.N0062.d008425 z z₀ (_root_.GD.N0062.d022142 t u) (_root_.GD.N0062.d022142 t u₀) hz hz₀ hq hq₀
  rw [_root_.GD.N0057.d022159] at h
  change (1 / ((_root_.GD.N0057.d022147 t u₀ z₀) ^ 3 * Real.sqrt (_root_.GD.N0057.d022147 t u₀ z₀))) *
      _root_.GD.N0057.d022151 t u₀ z₀ u (z ^ 3) ≤
        1 / ((_root_.GD.N0057.d022147 t u z) ^ 3 * Real.sqrt (_root_.GD.N0057.d022147 t u z)) at h
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ 10 * p / (t * (1 - t)) ^ 2 by positivity)
  calc
    _ = (10 * p / (t * (1 - t)) ^ 2) *
        ((1 / ((_root_.GD.N0057.d022147 t u₀ z₀) ^ 3 * Real.sqrt (_root_.GD.N0057.d022147 t u₀ z₀))) *
          _root_.GD.N0057.d022151 t u₀ z₀ u (z ^ 3)) := by
      unfold _root_.GD.N0057.d022148
      simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
      ring
    _ ≤ (10 * p / (t * (1 - t)) ^ 2) *
        (1 / ((_root_.GD.N0057.d022147 t u z) ^ 3 * Real.sqrt (_root_.GD.N0057.d022147 t u z))) := hm
    _ = _ := by
      unfold _root_.GD.N0057.d022149 _root_.GD.N0057.d022148
      simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
      ring



theorem d022162
    {t p u₀ z₀ R a b c d u z : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hp : 0 ≤ p)
    (hab : a < b) (hc : 0 ≤ c) (hcd : c < d)
    (hu : u ∈ Icc a b) (hz : z ∈ Icc c d)
    (hu01 : u ∈ Icc (0 : ℝ) 1)
    (hz₀ : 0 < z₀) (hq₀ : 0 < _root_.GD.N0057.d022147 t u₀ z₀)
    (hR : 0 < R) (hroot : _root_.GD.N0057.d022147 t u₀ z₀ ≤ R ^ 2)
    (v : _root_.GD.N0025.d005225 → ℝ)
    (hfactor : ∀ k : _root_.GD.N0025.d005225, 0 ≤ _root_.GD.N0057.d022151 t u₀ z₀
      (_root_.GD.N0025.d005226 a b k.1) (_root_.GD.N0025.d005226 (c ^ 3) (d ^ 3) k.2))
    (hround : ∀ k, v k ≤ _root_.GD.N0057.d022148 t p (_root_.GD.N0057.d022147 t u₀ z₀) R *
      _root_.GD.N0057.d022151 t u₀ z₀ (_root_.GD.N0025.d005226 a b k.1) (_root_.GD.N0025.d005226 (c ^ 3) (d ^ 3) k.2)) :
    (∑ k, _root_.GD.N0025.d005229 a b c d k u z * v k) ≤ _root_.GD.N0057.d022149 t p u z := by
  let B₀ := _root_.GD.N0057.d022148 t p (_root_.GD.N0057.d022147 t u₀ z₀) (Real.sqrt (_root_.GD.N0057.d022147 t u₀ z₀))
  let L := 7 / (2 * _root_.GD.N0057.d022147 t u₀ z₀)
  let S := 2 / t - 2 / (1 - t)
  let V := 2 / (3 * z₀)
  let A := B₀ * (1 + L * (S * u₀ + V * z₀ ^ 3))
  let B := -(B₀ * L * S)
  let C := -(B₀ * L * V)
  have haff (x y : ℝ) : B₀ * _root_.GD.N0057.d022151 t u₀ z₀ x y = A + B * x + C * y := by
    dsimp [A, B, C, L, S, V, _root_.GD.N0057.d022151]
    ring
  have hb := _root_.GD.N0057.d022160 ht hp hq₀ hR hroot
  have hv (k : _root_.GD.N0025.d005225) : v k ≤
      A + B * _root_.GD.N0025.d005226 a b k.1 + C * _root_.GD.N0025.d005226 (c ^ 3) (d ^ 3) k.2 := by
    rw [← haff]
    exact (hround k).trans (mul_le_mul_of_nonneg_right hb (hfactor k))
  have hcd3 : c ^ 3 < d ^ 3 := pow_lt_pow_left₀ hcd hc (by decide)
  have hcz : c ^ 3 ≤ z ^ 3 := pow_le_pow_left₀ hc hz.1 3
  have hzd : z ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ (hc.trans hz.1) hz.2 3
  have hi := _root_.GD.N0025.d005236 hab hcd3 hu ⟨hcz, hzd⟩ A B C v hv
  change (∑ k, _root_.GD.N0025.d005229 a b c d k u z * v k) ≤ A + B * u + C * z ^ 3 at hi
  rw [← haff] at hi
  exact hi.trans (_root_.GD.N0057.d022161 ht hp hu01 (hc.trans hz.1) hz₀ hq₀)


theorem d022163
    {t p u₀ z₀ R a b c d : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hp : 0 ≤ p)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hc : 0 ≤ c) (hcd : c < d)
    (hz₀ : 0 < z₀) (hq₀ : 0 < _root_.GD.N0057.d022147 t u₀ z₀)
    (hR : 0 < R) (hroot : _root_.GD.N0057.d022147 t u₀ z₀ ≤ R ^ 2)
    (v : _root_.GD.N0025.d005225 → ℝ)
    (hfactor : ∀ k : _root_.GD.N0025.d005225, 0 ≤ _root_.GD.N0057.d022151 t u₀ z₀
      (_root_.GD.N0025.d005226 a b k.1) (_root_.GD.N0025.d005226 (c ^ 3) (d ^ 3) k.2))
    (hround : ∀ k, v k ≤ _root_.GD.N0057.d022148 t p (_root_.GD.N0057.d022147 t u₀ z₀) R *
      _root_.GD.N0057.d022151 t u₀ z₀ (_root_.GD.N0025.d005226 a b k.1) (_root_.GD.N0025.d005226 (c ^ 3) (d ^ 3) k.2))
    (x : ℝ × ℝ) (hx : x ∈ _root_.GD.N0025.d005230 a b c d) :
    (∑ k, _root_.GD.N0025.d005231 a b c d k x * v k) ≤ _root_.GD.N0057.d022150 t p x.1 x.2 := by
  have hu : x.1 ∈ Icc a b := ⟨hx.1.1.le, hx.1.2⟩
  have hz : x.2 ∈ Icc c d := ⟨hx.2.1.le, hx.2.2⟩
  have hu01 : x.1 ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hu.1, hu.2.trans hb⟩
  have h := _root_.GD.N0057.d022162 ht hp hab hc hcd hu hz hu01 hz₀ hq₀
    hR hroot v hfactor hround
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 3 * x.2 ^ 2 by positivity)
  simpa only [Finset.mul_sum, mul_assoc, _root_.GD.N0025.d005231, _root_.GD.N0057.d022150] using hm

theorem d022164 {t p a b c d : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : b ≤ 1)
    (v : _root_.GD.N0025.d005225 → ℝ) (hv : ∀ k, v k = 0)
    (x : ℝ × ℝ) (hx : x ∈ _root_.GD.N0025.d005230 a b c d) :
    (∑ k, _root_.GD.N0025.d005231 a b c d k x * v k) ≤ _root_.GD.N0057.d022150 t p x.1 x.2 := by
  simp only [hv, mul_zero, Finset.sum_const_zero]
  exact _root_.GD.N0057.d022158 ht hp ⟨ha.trans hx.1.1.le, hx.1.2.trans hb⟩


theorem d022165 (t p u z : ℝ) :
    _root_.GD.N0057.d022150 t p u z = p *
      ((30 * z ^ 2 / (t * (1 - t) * (z ^ 2 + _root_.GD.N0062.d022142 t u) ^ 3 *
        Real.sqrt (z ^ 2 + _root_.GD.N0062.d022142 t u))) / (t * (1 - t))) := by
  unfold _root_.GD.N0057.d022150 _root_.GD.N0057.d022149 _root_.GD.N0057.d022148 _root_.GD.N0057.d022147
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring


theorem d022166 {t p u z : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) (hz : 0 < z) :
    _root_.GD.N0057.d022150 t p u z = p / (t * (1 - t)) *
      ((2 * z) * _root_.GD.N0232.N0720.N1436.d013273
        3 3 t (u, z ^ 2)) := by
  rw [_root_.GD.N0062.d022146 ht hu hz]
  unfold _root_.GD.N0057.d022150 _root_.GD.N0057.d022149 _root_.GD.N0057.d022148 _root_.GD.N0057.d022147
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring

end
end GD.N0057

#print axioms _root_.GD.N0057.d022160
#print axioms _root_.GD.N0057.d022153
#print axioms _root_.GD.N0057.d022155
#print axioms _root_.GD.N0057.d022161
#print axioms _root_.GD.N0057.d022162
#print axioms _root_.GD.N0057.d022163
#print axioms _root_.GD.N0057.d022164
#print axioms _root_.GD.N0057.d022165
#print axioms _root_.GD.N0057.d022166
