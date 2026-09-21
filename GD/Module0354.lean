import GD.Module0345
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0025
noncomputable section

abbrev d005225 := Fin 2 × Fin 2

def d005226 (a b : ℝ) (i : Fin 2) : ℝ := if i = 0 then a else b

def d005227 (a b : ℝ) (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then (b - x) / (b - a) else (x - a) / (b - a)

def d005228 (a b c d : ℝ) (k : _root_.GD.N0025.d005225) (x y : ℝ) : ℝ :=
  _root_.GD.N0025.d005227 a b k.1 x * _root_.GD.N0025.d005227 c d k.2 y

def d005229 (a b c d : ℝ) (k : _root_.GD.N0025.d005225) (x z : ℝ) : ℝ :=
  _root_.GD.N0025.d005228 a b (c ^ 3) (d ^ 3) k x (z ^ 3)

def d005230 (a b c d : ℝ) : Set (ℝ × ℝ) := Ioc a b ×ˢ Ioc c d

def d005231 (a b c d : ℝ) (k : _root_.GD.N0025.d005225) (p : ℝ × ℝ) : ℝ :=
  3 * p.2 ^ 2 * _root_.GD.N0025.d005229 a b c d k p.1 p.2

theorem d005232 {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    (i : Fin 2) : 0 ≤ _root_.GD.N0025.d005227 a b i x := by
  unfold _root_.GD.N0025.d005227
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr hx.2) (sub_pos.mpr hab).le
  · exact div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le

theorem d005233 {a b c d x y : ℝ} (hab : a < b) (hcd : c < d)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) (k : _root_.GD.N0025.d005225) :
    0 ≤ _root_.GD.N0025.d005228 a b c d k x y :=
  mul_nonneg (_root_.GD.N0025.d005232 hab hx k.1) (_root_.GD.N0025.d005232 hcd hy k.2)

theorem d005234 {a b c d x z : ℝ} (hab : a < b)
    (hc : 0 ≤ c) (hcd : c < d) (hx : x ∈ Icc a b) (hz : z ∈ Icc c d)
    (k : _root_.GD.N0025.d005225) : 0 ≤ _root_.GD.N0025.d005229 a b c d k x z := by
  have hcd3 : c ^ 3 < d ^ 3 := pow_lt_pow_left₀ hcd hc (by decide)
  have hcz : c ^ 3 ≤ z ^ 3 := pow_le_pow_left₀ hc hz.1 3
  have hzd : z ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ (hc.trans hz.1) hz.2 3
  exact _root_.GD.N0025.d005233 hab hcd3 hx ⟨hcz, hzd⟩ k


theorem d005235 {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (A B C x y : ℝ) :
    (∑ k : _root_.GD.N0025.d005225, _root_.GD.N0025.d005228 a b c d k x y *
      (A + B * _root_.GD.N0025.d005226 a b k.1 + C * _root_.GD.N0025.d005226 c d k.2)) = A + B * x + C * y := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, _root_.GD.N0025.d005228, _root_.GD.N0025.d005227, _root_.GD.N0025.d005226]
  norm_num
  field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt (sub_pos.mpr hcd)]
  ring



theorem d005236 {a b c d x y : ℝ}
    (hab : a < b) (hcd : c < d) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (A B C : ℝ) (v : _root_.GD.N0025.d005225 → ℝ)
    (hv : ∀ k, v k ≤ A + B * _root_.GD.N0025.d005226 a b k.1 + C * _root_.GD.N0025.d005226 c d k.2) :
    (∑ k, _root_.GD.N0025.d005228 a b c d k x y * v k) ≤ A + B * x + C * y := by
  rw [← _root_.GD.N0025.d005235 hab hcd A B C x y]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (hv k) (_root_.GD.N0025.d005233 hab hcd hx hy k)

private theorem d005237 (i : Fin 2) : i=0 ∨ i=1 := by
  rcases i with ⟨v,hv⟩
  have h : v=0 ∨ v=1 := by omega
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem d005238 {a b : ℝ} (hab : a < b) (i : Fin 2) :
    (∫ x in a..b, _root_.GD.N0025.d005227 a b i x) = (b - a) / 2 := by
  have hi : IntervalIntegrable (fun x : ℝ => x) volume a b :=
    continuous_id.intervalIntegrable a b
  have hk (k : ℝ) : IntervalIntegrable (fun _ : ℝ => k) volume a b :=
    continuous_const.intervalIntegrable a b
  rcases _root_.GD.N0025.d005237 i with rfl | rfl
  · change (∫ x in a..b, (b-x)/(b-a)) = (b-a)/2
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hk b) hi,
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  · change (∫ x in a..b, (x-a)/(b-a)) = (b-a)/2
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hi (hk a),
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring


theorem d005239 {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (i : Fin 2) :
    (∫ z in c..d, 3 * z ^ 2 * _root_.GD.N0025.d005227 (c ^ 3) (d ^ 3) i (z ^ 3)) =
      (d ^ 3 - c ^ 3) / 2 := by
  have hcd3 : c ^ 3 < d ^ 3 := pow_lt_pow_left₀ hcd hc (by decide)
  have hp (n : ℕ) (k : ℝ) :
      IntervalIntegrable (fun z : ℝ => k * z ^ n) volume c d :=
    (continuous_const.mul (continuous_id.pow n)).intervalIntegrable c d
  rcases _root_.GD.N0025.d005237 i with rfl | rfl
  · have heq : (fun z : ℝ => 3 * z ^ 2 * _root_.GD.N0025.d005227 (c ^ 3) (d ^ 3) 0 (z ^ 3)) =
        fun z => ((3 * d ^ 3) * z ^ 2 - 3 * z ^ 5) / (d ^ 3 - c ^ 3) := by
      funext z
      change 3*z^2*((d^3-z^3)/(d^3-c^3)) = _
      ring
    rw [heq, intervalIntegral.integral_div,
      intervalIntegral.integral_sub (hp 2 (3 * d ^ 3)) (hp 5 3),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
    norm_num only
    field_simp [ne_of_gt (sub_pos.mpr hcd3)]
    ring
  · have heq : (fun z : ℝ => 3 * z ^ 2 * _root_.GD.N0025.d005227 (c ^ 3) (d ^ 3) 1 (z ^ 3)) =
        fun z => (3 * z ^ 5 - (3 * c ^ 3) * z ^ 2) / (d ^ 3 - c ^ 3) := by
      funext z
      change 3*z^2*((z^3-c^3)/(d^3-c^3)) = _
      ring
    rw [heq, intervalIntegral.integral_div,
      intervalIntegral.integral_sub (hp 5 3) (hp 2 (3 * c ^ 3)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
    norm_num only
    field_simp [ne_of_gt (sub_pos.mpr hcd3)]
    ring



theorem d005240 {a b c d : ℝ} (hab : a < b)
    (hc : 0 ≤ c) (hcd : c < d) (k : _root_.GD.N0025.d005225) :
    (∫ x in a..b, ∫ z in c..d, 3 * z ^ 2 * _root_.GD.N0025.d005229 a b c d k x z) =
      (b - a) * (d ^ 3 - c ^ 3) / 4 := by
  have hinner (x : ℝ) :
      (∫ z in c..d, 3 * z ^ 2 * _root_.GD.N0025.d005229 a b c d k x z) =
        _root_.GD.N0025.d005227 a b k.1 x * ((d ^ 3 - c ^ 3) / 2) := by
    have heq : (fun z : ℝ => 3 * z ^ 2 * _root_.GD.N0025.d005229 a b c d k x z) =
        fun z => _root_.GD.N0025.d005227 a b k.1 x *
          (3 * z ^ 2 * _root_.GD.N0025.d005227 (c ^ 3) (d ^ 3) k.2 (z ^ 3)) := by
      funext z
      unfold _root_.GD.N0025.d005229 _root_.GD.N0025.d005228
      ring
    rw [heq, intervalIntegral.integral_const_mul, _root_.GD.N0025.d005239 hc hcd]
  simp_rw [hinner]
  rw [intervalIntegral.integral_mul_const, _root_.GD.N0025.d005238 hab]
  ring

theorem d005241 {a b c d : ℝ} (hab : a < b)
    (hc : 0 ≤ c) (hcd : c < d) (k : _root_.GD.N0025.d005225) {p : ℝ × ℝ}
    (hp : p ∈ _root_.GD.N0025.d005230 a b c d) : 0 ≤ _root_.GD.N0025.d005231 a b c d k p := by
  apply mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
  exact _root_.GD.N0025.d005234 hab hc hcd ⟨hp.1.1.le, hp.1.2⟩
    ⟨hp.2.1.le, hp.2.2⟩ k

theorem d005242 (a b c d : ℝ) (k : _root_.GD.N0025.d005225) :
    IntegrableOn (_root_.GD.N0025.d005231 a b c d k) (_root_.GD.N0025.d005230 a b c d)
      (volume.prod volume) := by
  have hx : Continuous (_root_.GD.N0025.d005227 a b k.1) := by
    unfold _root_.GD.N0025.d005227
    split_ifs <;> fun_prop
  have hz : Continuous (fun z : ℝ => 3 * z ^ 2 *
      _root_.GD.N0025.d005227 (c ^ 3) (d ^ 3) k.2 (z ^ 3)) := by
    unfold _root_.GD.N0025.d005227
    split_ifs <;> fun_prop
  change Integrable _ ((volume.prod volume).restrict (Ioc a b ×ˢ Ioc c d))
  rw [← Measure.prod_restrict]
  have hprod := (hx.intervalIntegrable (μ := volume) a b).1.mul_prod (hz.intervalIntegrable (μ := volume) c d).1
  convert hprod using 1
  funext p
  unfold _root_.GD.N0025.d005231 _root_.GD.N0025.d005229 _root_.GD.N0025.d005228
  ring



theorem d005243 {a b c d : ℝ} (hab : a < b)
    (hc : 0 ≤ c) (hcd : c < d) (k : _root_.GD.N0025.d005225) :
    (∫ p in _root_.GD.N0025.d005230 a b c d, _root_.GD.N0025.d005231 a b c d k p ∂volume.prod volume) =
      (b - a) * (d ^ 3 - c ^ 3) / 4 := by
  have heq : _root_.GD.N0025.d005231 a b c d k = fun p : ℝ × ℝ =>
      _root_.GD.N0025.d005227 a b k.1 p.1 *
        (3 * p.2 ^ 2 * _root_.GD.N0025.d005227 (c ^ 3) (d ^ 3) k.2 (p.2 ^ 3)) := by
    funext p
    unfold _root_.GD.N0025.d005231 _root_.GD.N0025.d005229 _root_.GD.N0025.d005228
    ring
  rw [heq, _root_.GD.N0025.d005230]
  change (∫ p in Ioc a b ×ˢ Ioc c d, _root_.GD.N0025.d005227 a b k.1 p.1 *
    (3*p.2^2*_root_.GD.N0025.d005227 (c^3) (d^3) k.2 (p.2^3)) ∂volume.prod volume) = _
  rw [setIntegral_prod_mul (_root_.GD.N0025.d005227 a b k.1)
      (fun z : ℝ => 3*z^2*_root_.GD.N0025.d005227 (c^3) (d^3) k.2 (z^3)) (Ioc a b) (Ioc c d),
    ← intervalIntegral.integral_of_le hab.le,
    ← intervalIntegral.integral_of_le hcd.le,
    _root_.GD.N0025.d005238 hab, _root_.GD.N0025.d005239 hc hcd]
  ring



theorem d005244
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → ℝ) (density : ι → ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℝ)
    (uLo uHi zLo zHi : κ → ℝ)
    (hu : ∀ k, uLo k < uHi k) (hz0 : ∀ k, 0 ≤ zLo k)
    (hz : ∀ k, zLo k < zHi k)
    (hdis : Pairwise (fun k l => Disjoint
      (_root_.GD.N0025.d005230 (uLo k) (uHi k) (zLo k) (zHi k))
      (_root_.GD.N0025.d005230 (uLo l) (uHi l) (zLo l) (zHi l))))
    (lower : κ → _root_.GD.N0025.d005225 → ι → ℝ) (q : κ → _root_.GD.N0025.d005225 → ℝ)
    (hq : ∀ k c x, q k c ≤ ∑ i, lower k c i * (x - t i) ^ 2)
    (hd : ∀ k p, p ∈ _root_.GD.N0025.d005230 (uLo k) (uHi k) (zLo k) (zHi k) →
      ∀ i, (∑ c, _root_.GD.N0025.d005231 (uLo k) (uHi k) (zLo k) (zHi k) c p *
        lower k c i) ≤ density i p)
    (hF : Integrable (fun p => ∑ i, density i p * (g p - t i) ^ 2)
      (volume.prod volume))
    (hFn : ∀ᵐ p ∂volume.prod volume, 0 ≤ ∑ i, density i p * (g p - t i) ^ 2) :
    (∑ k, ((uHi k - uLo k) * ((zHi k) ^ 3 - (zLo k) ^ 3) / 4) *
      (∑ c, q k c)) ≤
      ∫ p, ∑ i, density i p * (g p - t i) ^ 2 ∂volume.prod volume := by
  apply _root_.GD.N0025.d005146 (volume.prod volume)
    (fun k => _root_.GD.N0025.d005230 (uLo k) (uHi k) (zLo k) (zHi k))
    (fun p => ∑ i, density i p * (g p - t i) ^ 2)
    (fun k => ((uHi k - uLo k) * ((zHi k) ^ 3 - (zLo k) ^ 3) / 4) *
      (∑ c, q k c))
    (fun _ => measurableSet_Ioc.prod measurableSet_Ioc) hdis hF hFn
  intro k
  have hE : MeasurableSet (_root_.GD.N0025.d005230 (uLo k) (uHi k) (zLo k) (zHi k)) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hb : ∀ᵐ p ∂(volume.prod volume).restrict
      (_root_.GD.N0025.d005230 (uLo k) (uHi k) (zLo k) (zHi k)),
      ∀ c, 0 ≤ _root_.GD.N0025.d005231 (uLo k) (uHi k) (zLo k) (zHi k) c p := by
    filter_upwards [ae_restrict_mem hE] with p hp
    intro c
    exact _root_.GD.N0025.d005241 (hu k) (hz0 k) (hz k) c hp
  have hdl : ∀ᵐ p ∂(volume.prod volume).restrict
      (_root_.GD.N0025.d005230 (uLo k) (uHi k) (zLo k) (zHi k)),
      ∀ i, (∑ c, _root_.GD.N0025.d005231 (uLo k) (uHi k) (zLo k) (zHi k) c p *
        lower k c i) ≤ density i p := by
    filter_upwards [ae_restrict_mem hE] with p hp
    exact hd k p hp
  have h := _root_.GD.N0025.d005145
    ((volume.prod volume).restrict (_root_.GD.N0025.d005230 (uLo k) (uHi k) (zLo k) (zHi k)))
    t density g (lower k) (q k)
    (_root_.GD.N0025.d005231 (uLo k) (uHi k) (zLo k) (zHi k))
    (fun _ => (uHi k - uLo k) * ((zHi k) ^ 3 - (zLo k) ^ 3) / 4)
    (fun c => _root_.GD.N0025.d005242 _ _ _ _ c)
    (fun c => _root_.GD.N0025.d005243 (hu k) (hz0 k) (hz k) c)
    hb hdl (hq k) hF.integrableOn
  simpa only [Finset.mul_sum] using h



theorem d005245
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ι → ℕ) (D N : ℕ) (hD : 0 < D) (hN : 0 < N)
    (density : ι → ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℝ)
    (uLo uHi zLo zHi : κ → ℝ)
    (hu : ∀ k, uLo k < uHi k) (hz0 : ∀ k, 0 ≤ zLo k)
    (hz : ∀ k, zLo k < zHi k)
    (hdis : Pairwise (fun k l => Disjoint
      (_root_.GD.N0025.d005230 (uLo k) (uHi k) (zLo k) (zHi k))
      (_root_.GD.N0025.d005230 (uLo l) (uHi l) (zLo l) (zHi l))))
    (a : κ → _root_.GD.N0025.d005225 → ι → ℕ) (q : κ → _root_.GD.N0025.d005225 → ℕ)
    (hA : ∀ k c, 0 < ∑ i, a k c i)
    (hdisc : ∀ k c, (∑ i, a k c i * n i) ^ 2 + (∑ i, a k c i) * q k c ≤
      (∑ i, a k c i) * (∑ i, a k c i * n i ^ 2))
    (hd : ∀ k p, p ∈ _root_.GD.N0025.d005230 (uLo k) (uHi k) (zLo k) (zHi k) →
      ∀ i, (∑ c, _root_.GD.N0025.d005231 (uLo k) (uHi k) (zLo k) (zHi k) c p *
        ((a k c i : ℝ) / D)) ≤ density i p)
    (hF : Integrable (fun p => ∑ i, density i p * (g p - (n i : ℝ) / N) ^ 2)
      (volume.prod volume))
    (hFn : ∀ᵐ p ∂volume.prod volume,
      0 ≤ ∑ i, density i p * (g p - (n i : ℝ) / N) ^ 2) :
    (∑ k, ((uHi k - uLo k) * ((zHi k) ^ 3 - (zLo k) ^ 3) / 4) *
      (∑ c, (q k c : ℝ) / ((D : ℝ) * (N : ℝ) ^ 2))) ≤
      ∫ p, ∑ i, density i p * (g p - (n i : ℝ) / N) ^ 2 ∂volume.prod volume :=
  _root_.GD.N0025.d005244 (fun i => (n i : ℝ) / N) density g
    uLo uHi zLo zHi hu hz0 hz hdis
    (fun k c i => (a k c i : ℝ) / D)
    (fun k c => (q k c : ℝ) / ((D : ℝ) * (N : ℝ) ^ 2))
    (fun k c x => _root_.GD.N0025.d005143 (a k c) n D N (q k c)
      hD hN (hA k c) (hdisc k c) x) hd hF hFn

theorem d005246 {m : ℕ} (U : Fin (m + 1) → ℝ)
    (hU : Monotone U) {i j : Fin m} (hij : i ≠ j) :
    Disjoint (Ioc (U i.castSucc) (U i.succ)) (Ioc (U j.castSucc) (U j.succ)) := by
  have hlt {i j : Fin m} (hij : i < j) :
      Disjoint (Ioc (U i.castSucc) (U i.succ)) (Ioc (U j.castSucc) (U j.succ)) := by
    have hstep : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      have hv : i.val < j.val := hij
      omega
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) (lt_of_le_of_lt (hU hstep) hy.1)
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt h
  · exact (hlt h).symm



theorem d005247
    {m n : ℕ} {κ : Type*}
    (U : Fin (m + 1) → ℝ) (Z : Fin (n + 1) → ℝ)
    (hU : Monotone U) (hZ : Monotone Z)
    (f : κ → Fin m × Fin n) (hf : Function.Injective f) :
    Pairwise (fun k l => Disjoint
      (_root_.GD.N0025.d005230 (U (f k).1.castSucc) (U (f k).1.succ)
        (Z (f k).2.castSucc) (Z (f k).2.succ))
      (_root_.GD.N0025.d005230 (U (f l).1.castSucc) (U (f l).1.succ)
        (Z (f l).2.castSucc) (Z (f l).2.succ))) := by
  intro k l hkl
  have hne : f k ≠ f l := fun h => hkl (hf h)
  by_cases hu : (f k).1 = (f l).1
  · have hz : (f k).2 ≠ (f l).2 := fun h => hne (Prod.ext hu h)
    have h := _root_.GD.N0025.d005246 Z hZ hz
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp h hp.2 hq.2
  · have h := _root_.GD.N0025.d005246 U hU hu
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp h hp.1 hq.1

end
end GD.N0025

#print axioms _root_.GD.N0025.d005234
#print axioms _root_.GD.N0025.d005235
#print axioms _root_.GD.N0025.d005236
#print axioms _root_.GD.N0025.d005238
#print axioms _root_.GD.N0025.d005239
#print axioms _root_.GD.N0025.d005240
#print axioms _root_.GD.N0025.d005241
#print axioms _root_.GD.N0025.d005242
#print axioms _root_.GD.N0025.d005243
#print axioms _root_.GD.N0025.d005244
#print axioms _root_.GD.N0025.d005245
#print axioms _root_.GD.N0025.d005246
#print axioms _root_.GD.N0025.d005247
