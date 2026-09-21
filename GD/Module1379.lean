import GD.Module0574
import GD.Module1378
import GD.Module0018
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0163
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0178
open _root_.GD.N0180
open _root_.GD.N0213.N0525
open _root_.GD.N0230.N0615

variable {I : Type*} [Fintype I]
variable (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676)

def d022177 (x : _root_.GD.N0232.N0720.N1436.d013217) (i : I) : ℝ :=
  p i * _root_.GD.N0178.d007131 (t i) x.1 x.2

def d022178 (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ := ∑ i, _root_.GD.N0163.d022177 p t x i

def d022179 (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  ∑ i, _root_.GD.N0163.d022177 p t x i * (t i : ℝ)

def d022180 (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  ∑ i, _root_.GD.N0163.d022177 p t x i * (t i : ℝ) ^ 2


def d022181 : _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  _root_.GD.N0232.N0720.N1436.d013218.indicator (fun x => _root_.GD.N0163.d022179 p t x / _root_.GD.N0163.d022178 p t x)

def d022182 (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0163.d022180 p t x - _root_.GD.N0163.d022179 p t x ^ 2 / _root_.GD.N0163.d022178 p t x

def d022183 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  ∑ i, _root_.GD.N0163.d022177 p t x i * (g x - (t i : ℝ)) ^ 2

def d022184 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0163.d022178 p t x * (g x - _root_.GD.N0163.d022181 p t x) ^ 2

def d022185 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) : ℝ :=
  ∑ i, p i * _root_.GD.N0180.d022173 (t i) g

def d022186 : ℝ :=
  ∫ x, _root_.GD.N0163.d022182 p t x ∂_root_.GD.N0232.N0720.N1436.d013288

theorem d022187 (r : _root_.GD.N0232.N0720.N1441.d013676) {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) : 0 < _root_.GD.N0178.d007131 r x.1 x.2 := by
  have hr0 := r.property.1
  have hr1 : 0 < 1 - (r : ℝ) := sub_pos.mpr r.property.2
  have hs := hx.2
  have hD := _root_.GD.N0178.d007138 hr0 r.property.2 hx.1.1.le hx.1.2.le hs
  have hseven := _root_.GD.N0178.d007134 hD
  unfold _root_.GD.N0178.d007131
  exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hs))
    (mul_pos (mul_pos (sq_pos_of_pos hr0) (sq_pos_of_pos hr1)) hseven)

theorem d022188 (r : _root_.GD.N0232.N0720.N1441.d013676) :
    Measurable (fun x : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0178.d007131 r x.1 x.2) := by
  unfold _root_.GD.N0178.d007131 _root_.GD.N0178.d007130 _root_.GD.N0178.d007129
  fun_prop

theorem d022189 (r : _root_.GD.N0232.N0720.N1441.d013676) :
    ContinuousOn (fun x : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0178.d007131 r x.1 x.2)
      _root_.GD.N0232.N0720.N1436.d013218 := by
  unfold _root_.GD.N0178.d007131
  apply ContinuousOn.div
  · fun_prop
  · unfold _root_.GD.N0178.d007130 _root_.GD.N0178.d007129
    fun_prop
  · intro x hx
    have hr0 := r.property.1
    have hr1 : 0 < 1 - (r : ℝ) := sub_pos.mpr r.property.2
    have hD := _root_.GD.N0178.d007138 hr0 r.property.2 hx.1.1.le hx.1.2.le hx.2
    have hseven := _root_.GD.N0178.d007134 hD
    exact (show 0 < (r : ℝ) ^ 2 * (1 - r) ^ 2 *
      _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 r x.1 x.2) by positivity).ne'

theorem d022190 : Measurable (_root_.GD.N0163.d022178 p t) := by
  unfold _root_.GD.N0163.d022178 _root_.GD.N0163.d022177
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (_root_.GD.N0163.d022188 (t i)))

theorem d022191 : Measurable (_root_.GD.N0163.d022179 p t) := by
  unfold _root_.GD.N0163.d022179 _root_.GD.N0163.d022177
  exact Finset.measurable_sum _ (fun i _ =>
    (measurable_const.mul (_root_.GD.N0163.d022188 (t i))).mul measurable_const)

theorem d022192 : Measurable (_root_.GD.N0163.d022181 p t) :=
  ((_root_.GD.N0163.d022191 p t).div (_root_.GD.N0163.d022190 p t)).indicator
    _root_.GD.N0232.N0720.N1436.d013219

theorem d022193 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) : _root_.GD.N0163.d022181 p t x = _root_.GD.N0163.d022179 p t x / _root_.GD.N0163.d022178 p t x := by
  exact Set.indicator_of_mem hx _

section Positive
variable [Nonempty I]
variable (hp : ∀ i, 0 < p i)
include hp

theorem d022194 {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218)
    (i : I) : 0 < _root_.GD.N0163.d022177 p t x i :=
  mul_pos (hp i) (_root_.GD.N0163.d022187 (t i) hx)

theorem d022195 {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0163.d022178 p t x :=
  Finset.sum_pos (fun i _ => _root_.GD.N0163.d022194 p t hp hx i) Finset.univ_nonempty

theorem d022196 (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0163.d022181 p t x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218
  · rw [_root_.GD.N0163.d022193 p t hx]
    change 0 ≤ _root_.GD.N0163.d022179 p t x / _root_.GD.N0163.d022178 p t x ∧ _root_.GD.N0163.d022179 p t x / _root_.GD.N0163.d022178 p t x ≤ 1
    simpa only [_root_.GD.N0230.N0615.d000152, _root_.GD.N0230.N0615.d000151, _root_.GD.N0163.d022178, _root_.GD.N0163.d022179] using
      _root_.GD.N0230.N0615.d000161 (_root_.GD.N0163.d022177 p t x) (fun i => (t i : ℝ)) 0 1
        (fun i => (_root_.GD.N0163.d022194 p t hp hx i).le) (_root_.GD.N0163.d022195 p t hp hx)
        (fun i => (t i).property.1.le) (fun i => (t i).property.2.le)
  · simp [_root_.GD.N0163.d022181, hx]

theorem d022197 (x : _root_.GD.N0232.N0720.N1436.d013217) :
    |_root_.GD.N0163.d022181 p t x| ≤ 1 := by
  rw [abs_of_nonneg (_root_.GD.N0163.d022196 p t hp x).1]
  exact (_root_.GD.N0163.d022196 p t hp x).2

theorem d022198 : ContinuousOn (_root_.GD.N0163.d022181 p t) _root_.GD.N0232.N0720.N1436.d013218 := by
  have h0 : ContinuousOn (_root_.GD.N0163.d022178 p t) _root_.GD.N0232.N0720.N1436.d013218 := by
    unfold _root_.GD.N0163.d022178 _root_.GD.N0163.d022177
    exact continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (_root_.GD.N0163.d022189 (t i)))
  have h1 : ContinuousOn (_root_.GD.N0163.d022179 p t) _root_.GD.N0232.N0720.N1436.d013218 := by
    unfold _root_.GD.N0163.d022179 _root_.GD.N0163.d022177
    exact continuousOn_finsetSum _ (fun i _ =>
      (continuousOn_const.mul (_root_.GD.N0163.d022189 (t i))).mul continuousOn_const)
  exact (h1.div h0 (fun _ hx => (_root_.GD.N0163.d022195 p t hp hx).ne')).congr
    (fun _ hx => _root_.GD.N0163.d022193 p t hx)


theorem d022199 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0163.d022183 p t g x = _root_.GD.N0163.d022182 p t x + _root_.GD.N0163.d022184 p t g x := by
  have hsum : ∑ i, _root_.GD.N0163.d022177 p t x i ≠ 0 := (_root_.GD.N0163.d022195 p t hp hx).ne'
  have h := _root_.GD.N0213.N0525.d008430 (_root_.GD.N0163.d022177 p t x) (fun i => (t i : ℝ))
    hsum (g x)
  rw [← _root_.GD.N0213.N0525.d008429 _ _ hsum] at h
  simpa only [_root_.GD.N0163.d022183, _root_.GD.N0163.d022182, _root_.GD.N0163.d022184, _root_.GD.N0163.d022193 p t hx,
    _root_.GD.N0163.d022178, _root_.GD.N0163.d022179, _root_.GD.N0163.d022180, sub_sq_comm] using h

theorem d022200 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0163.d022182 p t x =
      (∑ i, ∑ j, _root_.GD.N0163.d022177 p t x i * _root_.GD.N0163.d022177 p t x j *
        ((t i : ℝ) - (t j : ℝ)) ^ 2) / (2 * _root_.GD.N0163.d022178 p t x) := by
  exact _root_.GD.N0213.N0525.d008429 (_root_.GD.N0163.d022177 p t x) (fun i => (t i : ℝ))
    (_root_.GD.N0163.d022195 p t hp hx).ne'

theorem d022201 {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0163.d022183 p t (_root_.GD.N0163.d022181 p t) x = _root_.GD.N0163.d022182 p t x := by
  simpa [_root_.GD.N0163.d022184] using _root_.GD.N0163.d022199 p t hp (_root_.GD.N0163.d022181 p t) hx

theorem d022202 {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 ≤ _root_.GD.N0163.d022182 p t x := by
  rw [← _root_.GD.N0163.d022201 p t hp hx]
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (_root_.GD.N0163.d022194 p t hp hx i).le (sq_nonneg _))

end Positive

theorem d022203 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    Integrable (_root_.GD.N0163.d022183 p t g) _root_.GD.N0232.N0720.N1436.d013288 := by
  change Integrable (fun x => ∑ i, p i * _root_.GD.N0178.d007131 (t i) x.1 x.2 *
    (g x - (t i : ℝ)) ^ 2) _root_.GD.N0232.N0720.N1436.d013288
  simpa only [mul_assoc] using
    integrable_finsetSum (Finset.univ : Finset I) (fun i _ =>
      (_root_.GD.N0180.d022174 (t i) g hg hB).const_mul (p i))

theorem d022204 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    (∫ x, _root_.GD.N0163.d022183 p t g x ∂_root_.GD.N0232.N0720.N1436.d013288) = _root_.GD.N0163.d022185 p t g := by
  simpa only [_root_.GD.N0163.d022183, _root_.GD.N0163.d022177, _root_.GD.N0163.d022185, _root_.GD.N0180.d022173, mul_assoc, integral_const_mul] using
    integral_finsetSum (Finset.univ : Finset I) (fun i _ =>
      (_root_.GD.N0180.d022174 (t i) g hg hB).const_mul (p i))

section Positive
variable [Nonempty I]
variable (hp : ∀ i, 0 < p i)
include hp

theorem d022205 :
    Integrable (_root_.GD.N0163.d022182 p t) _root_.GD.N0232.N0720.N1436.d013288 := by
  apply (_root_.GD.N0163.d022203 p t (_root_.GD.N0163.d022181 p t) (_root_.GD.N0163.d022192 p t)
    (_root_.GD.N0163.d022197 p t hp)).congr
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
  exact _root_.GD.N0163.d022201 p t hp hx

theorem d022206 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    Integrable (_root_.GD.N0163.d022184 p t g) _root_.GD.N0232.N0720.N1436.d013288 := by
  apply ((_root_.GD.N0163.d022203 p t g hg hB).sub (_root_.GD.N0163.d022205 p t hp)).congr
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
  change _root_.GD.N0163.d022183 p t g x - _root_.GD.N0163.d022182 p t x = _root_.GD.N0163.d022184 p t g x
  linarith [_root_.GD.N0163.d022199 p t hp g hx]


theorem d022207 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    _root_.GD.N0163.d022185 p t g = _root_.GD.N0163.d022186 p t +
      ∫ x, _root_.GD.N0163.d022184 p t g x ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  rw [← _root_.GD.N0163.d022204 p t g hg hB]
  calc
    (∫ x, _root_.GD.N0163.d022183 p t g x ∂_root_.GD.N0232.N0720.N1436.d013288) =
        ∫ x, _root_.GD.N0163.d022182 p t x + _root_.GD.N0163.d022184 p t g x ∂_root_.GD.N0232.N0720.N1436.d013288 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
      exact _root_.GD.N0163.d022199 p t hp g hx
    _ = _root_.GD.N0163.d022186 p t + ∫ x, _root_.GD.N0163.d022184 p t g x ∂_root_.GD.N0232.N0720.N1436.d013288 := by
      exact integral_add (_root_.GD.N0163.d022205 p t hp)
        (_root_.GD.N0163.d022206 p t hp g hg hB)

theorem d022208 : 0 ≤ _root_.GD.N0163.d022186 p t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
  exact _root_.GD.N0163.d022202 p t hp hx

theorem d022209 :
    _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022181 p t) = _root_.GD.N0163.d022186 p t := by
  simpa [_root_.GD.N0163.d022184] using _root_.GD.N0163.d022207 p t hp (_root_.GD.N0163.d022181 p t)
    (_root_.GD.N0163.d022192 p t) (_root_.GD.N0163.d022197 p t hp)

theorem d022210 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) : _root_.GD.N0163.d022186 p t ≤ _root_.GD.N0163.d022185 p t g := by
  rw [_root_.GD.N0163.d022207 p t hp g hg hB]
  apply le_add_of_nonneg_right
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
  exact mul_nonneg (_root_.GD.N0163.d022195 p t hp hx).le (sq_nonneg _)

end Positive


def d022211 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) : _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  Function.extend ((↑) : _root_.GD.N0232.N0720.N1436.d013218 → _root_.GD.N0232.N0720.N1436.d013217) g (fun _ => 0)

theorem d022212 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (x : _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0163.d022211 g x = g x :=
  Subtype.coe_injective.extend_apply g (fun _ => 0) x

theorem d022213 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g) :
    Measurable (_root_.GD.N0163.d022211 g) :=
  (MeasurableEmbedding.subtype_coe _root_.GD.N0232.N0720.N1436.d013219).measurable_extend
    hg measurable_const

theorem d022214 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    (hg : ∀ x, g x ∈ Icc (0 : ℝ) 1) (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0163.d022211 g x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218
  · rw [show _root_.GD.N0163.d022211 g x = g ⟨x, hx⟩ from _root_.GD.N0163.d022212 g ⟨x, hx⟩]
    exact hg ⟨x, hx⟩
  · have hn : ¬ ∃ y : _root_.GD.N0232.N0720.N1436.d013218, (y : _root_.GD.N0232.N0720.N1436.d013217) = x := by
      rintro ⟨y, hy⟩
      apply hx
      rw [← hy]
      exact y.property
    rw [_root_.GD.N0163.d022211, Function.extend_apply' g (fun _ => 0) x hn]
    norm_num


theorem d022215 [Nonempty I] (hp : ∀ i, 0 < p i)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022181 p t) ≤ _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022211 g) := by
  rw [_root_.GD.N0163.d022209 p t hp]
  apply _root_.GD.N0163.d022210 p t hp (_root_.GD.N0163.d022211 g)
    (_root_.GD.N0163.d022213 g hg)
  intro x
  rw [abs_of_nonneg (_root_.GD.N0163.d022214 g h01 x).1]
  exact (_root_.GD.N0163.d022214 g h01 x).2

end
end GD.N0163

#print axioms _root_.GD.N0163.d022199
#print axioms _root_.GD.N0163.d022200
#print axioms _root_.GD.N0163.d022196
#print axioms _root_.GD.N0163.d022198
#print axioms _root_.GD.N0163.d022207
#print axioms _root_.GD.N0163.d022209
#print axioms _root_.GD.N0163.d022215
