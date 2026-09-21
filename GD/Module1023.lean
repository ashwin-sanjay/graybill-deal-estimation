import GD.Module1017































open Filter Set
open scoped BigOperators Topology

namespace GD
namespace N0232
namespace N0720
namespace N1301

noncomputable section

open _root_.GD.N0232.N0720.N1492


def d016252 : ℝ := (5 : ℝ) / 2



def d016253 (q e F : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1492.d016123 e F q



def d016254 (q e F : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1301.d016253 q e F ^ (-_root_.GD.N0232.N0720.N1301.d016252)


def d016255 (q e F : ℝ) : ℝ :=
  (_root_.GD.N0232.N0720.N1301.d016253 q e F / F) ^ (-_root_.GD.N0232.N0720.N1301.d016252)

theorem d016256 (q e F : ℝ) :
    _root_.GD.N0232.N0720.N1301.d016253 q e F =
      e + (1 - 2 * e + F) * q - F * q ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1301.d016253 _root_.GD.N0232.N0720.N1492.d016123
  ring

@[simp] theorem d016257 (e F : ℝ) :
    _root_.GD.N0232.N0720.N1301.d016253 0 e F = e := by
  simp [_root_.GD.N0232.N0720.N1301.d016253, _root_.GD.N0232.N0720.N1492.d016123]

@[simp] theorem d016258 (e F : ℝ) :
    _root_.GD.N0232.N0720.N1301.d016253 1 e F = 1 - e := by
  simp [_root_.GD.N0232.N0720.N1301.d016253, _root_.GD.N0232.N0720.N1492.d016123]

@[simp] theorem d016259 (e F : ℝ) :
    _root_.GD.N0232.N0720.N1301.d016254 0 e F = e ^ (-_root_.GD.N0232.N0720.N1301.d016252) := by
  simp [_root_.GD.N0232.N0720.N1301.d016254]

@[simp] theorem d016260 (e F : ℝ) :
    _root_.GD.N0232.N0720.N1301.d016254 1 e F = (1 - e) ^ (-_root_.GD.N0232.N0720.N1301.d016252) := by
  simp [_root_.GD.N0232.N0720.N1301.d016254]



theorem d016261
    {q e F : ℝ} (hF : F ≠ 0) :
    _root_.GD.N0232.N0720.N1301.d016253 q e F / F =
      q * (1 - q) + (e + (1 - 2 * e) * q) / F := by
  rw [_root_.GD.N0232.N0720.N1301.d016256]
  field_simp [hF]
  ring



theorem d016262 (q e : ℝ) :
    Tendsto (fun F : ℝ => _root_.GD.N0232.N0720.N1301.d016253 q e F / F)
      atTop (nhds (q * (1 - q))) := by
  have hsmall :
      Tendsto (fun F : ℝ => (e + (1 - 2 * e) * q) / F)
        atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (e + (1 - 2 * e) * q)
  have hsum :
      Tendsto
        (fun F : ℝ => q * (1 - q) +
          (e + (1 - 2 * e) * q) / F)
        atTop (nhds (q * (1 - q))) := by
    simpa using tendsto_const_nhds.add hsmall
  apply hsum.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with F hF
  exact (_root_.GD.N0232.N0720.N1301.d016261 hF).symm



theorem d016263
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (e : ℝ) :
    Tendsto (fun F : ℝ => _root_.GD.N0232.N0720.N1301.d016255 q e F)
      atTop (nhds ((q * (1 - q)) ^ (-_root_.GD.N0232.N0720.N1301.d016252))) := by
  have hc : 0 < q * (1 - q) :=
    mul_pos hq.1 (sub_pos.mpr hq.2)
  exact
    (Real.continuousAt_rpow_const (q * (1 - q)) (-_root_.GD.N0232.N0720.N1301.d016252)
      (Or.inl hc.ne')).tendsto.comp
      (_root_.GD.N0232.N0720.N1301.d016262 q e)



theorem d016264
    {q e F : ℝ} (hF : 0 < F) (hQ : 0 < _root_.GD.N0232.N0720.N1301.d016253 q e F) :
    _root_.GD.N0232.N0720.N1301.d016255 q e F =
      F ^ _root_.GD.N0232.N0720.N1301.d016252 * _root_.GD.N0232.N0720.N1301.d016254 q e F := by
  unfold _root_.GD.N0232.N0720.N1301.d016255 _root_.GD.N0232.N0720.N1301.d016254
  rw [Real.div_rpow hQ.le hF.le, Real.rpow_neg hF.le]
  have hFp : F ^ _root_.GD.N0232.N0720.N1301.d016252 ≠ 0 :=
    (Real.rpow_pos_of_pos hF _root_.GD.N0232.N0720.N1301.d016252).ne'
  field_simp [hFp]






def d016265
    {ι : Type*} [Fintype ι]
    (mass atom kernel : ι → ℝ) : ℝ :=
  (∑ i, mass i * kernel i * atom i) /
    ∑ i, mass i * kernel i



theorem d016266
    {ι : Type*} [Fintype ι]
    (mass atom kernel : ι → ℝ) {c : ℝ} (hc : c ≠ 0) :
    _root_.GD.N0232.N0720.N1301.d016265 mass atom (fun i => c * kernel i) =
      _root_.GD.N0232.N0720.N1301.d016265 mass atom kernel := by
  unfold _root_.GD.N0232.N0720.N1301.d016265
  have hnum :
      (∑ i, mass i * (c * kernel i) * atom i) =
        c * ∑ i, mass i * kernel i * atom i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hden :
      (∑ i, mass i * (c * kernel i)) =
        c * ∑ i, mass i * kernel i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hc


def d016267
    {ι : Type*} [Fintype ι]
    (mass atom : ι → ℝ) (e F : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1301.d016265 mass atom (fun i => _root_.GD.N0232.N0720.N1301.d016254 (atom i) e F)


def d016268
    {ι : Type*} [Fintype ι]
    (mass atom : ι → ℝ) (e F : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1301.d016265 mass atom
    (fun i => _root_.GD.N0232.N0720.N1301.d016255 (atom i) e F)



theorem d016269
    {ι : Type*} [Fintype ι]
    {mass atom : ι → ℝ} {e F : ℝ}
    (hF : 0 < F)
    (hQ : ∀ i, 0 < _root_.GD.N0232.N0720.N1301.d016253 (atom i) e F) :
    _root_.GD.N0232.N0720.N1301.d016268 mass atom e F =
      _root_.GD.N0232.N0720.N1301.d016267 mass atom e F := by
  unfold _root_.GD.N0232.N0720.N1301.d016268 _root_.GD.N0232.N0720.N1301.d016267
  have hkernel :
      (fun i => _root_.GD.N0232.N0720.N1301.d016255 (atom i) e F) =
        (fun i => F ^ _root_.GD.N0232.N0720.N1301.d016252 * _root_.GD.N0232.N0720.N1301.d016254 (atom i) e F) := by
    funext i
    exact _root_.GD.N0232.N0720.N1301.d016264 hF (hQ i)
  rw [hkernel]
  apply _root_.GD.N0232.N0720.N1301.d016266
  exact (Real.rpow_pos_of_pos hF _root_.GD.N0232.N0720.N1301.d016252).ne'


def d016270 (q : ℝ) : ℝ :=
  (q * (1 - q)) ^ (-_root_.GD.N0232.N0720.N1301.d016252)



def d016271
    {ι : Type*} [Fintype ι]
    (mass atom : ι → ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1301.d016265 mass atom (fun i => _root_.GD.N0232.N0720.N1301.d016270 (atom i))

theorem d016272
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1301.d016270 q := by
  exact Real.rpow_pos_of_pos
    (mul_pos hq.1 (sub_pos.mpr hq.2)) (-_root_.GD.N0232.N0720.N1301.d016252)



theorem d016273
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {mass atom : ι → ℝ}
    (hmass : ∀ i, 0 < mass i)
    (hatom : ∀ i, atom i ∈ Ioo (0 : ℝ) 1)
    (e : ℝ) :
    Tendsto (fun F : ℝ =>
      _root_.GD.N0232.N0720.N1301.d016268 mass atom e F)
      atTop (nhds (_root_.GD.N0232.N0720.N1301.d016271 mass atom)) := by
  have hden : Tendsto
      (fun F : ℝ =>
        ∑ i, mass i * _root_.GD.N0232.N0720.N1301.d016255 (atom i) e F)
      atTop
      (nhds (∑ i, mass i * _root_.GD.N0232.N0720.N1301.d016270 (atom i))) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    exact tendsto_const_nhds.mul
      (_root_.GD.N0232.N0720.N1301.d016263 (hatom i) e)
  have hnum : Tendsto
      (fun F : ℝ =>
        ∑ i, mass i * _root_.GD.N0232.N0720.N1301.d016255 (atom i) e F * atom i)
      atTop
      (nhds (∑ i, mass i * _root_.GD.N0232.N0720.N1301.d016270 (atom i) * atom i)) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    exact (tendsto_const_nhds.mul
      (_root_.GD.N0232.N0720.N1301.d016263 (hatom i) e)).mul_const (atom i)
  have hdenPos :
      0 < ∑ i, mass i * _root_.GD.N0232.N0720.N1301.d016270 (atom i) := by
    exact Finset.sum_pos
      (fun i _ => mul_pos (hmass i) (_root_.GD.N0232.N0720.N1301.d016272 (hatom i)))
      Finset.univ_nonempty
  unfold _root_.GD.N0232.N0720.N1301.d016268 _root_.GD.N0232.N0720.N1301.d016271 _root_.GD.N0232.N0720.N1301.d016265
  exact hnum.div hden hdenPos.ne'




theorem d016274
    {ι : Type*} [Fintype ι]
    (mass atom : ι → ℝ) (e₁ e₂ : ℝ) :
    (fun _ : ℝ => _root_.GD.N0232.N0720.N1301.d016271 mass atom) e₁ =
      (fun _ : ℝ => _root_.GD.N0232.N0720.N1301.d016271 mass atom) e₂ := by
  rfl




def d016275 (massZero massOne e : ℝ) : ℝ :=
  (massOne * (1 - e) ^ (-_root_.GD.N0232.N0720.N1301.d016252)) /
    (massZero * e ^ (-_root_.GD.N0232.N0720.N1301.d016252) +
      massOne * (1 - e) ^ (-_root_.GD.N0232.N0720.N1301.d016252))


theorem d016276
    (massZero massOne e F : ℝ) :
    _root_.GD.N0232.N0720.N1301.d016275 massZero massOne e =
      (massZero * _root_.GD.N0232.N0720.N1301.d016254 0 e F * 0 +
        massOne * _root_.GD.N0232.N0720.N1301.d016254 1 e F * 1) /
      (massZero * _root_.GD.N0232.N0720.N1301.d016254 0 e F +
        massOne * _root_.GD.N0232.N0720.N1301.d016254 1 e F) := by
  simp [_root_.GD.N0232.N0720.N1301.d016275]



theorem d016277
    {mass e : ℝ} (hmass : 0 < mass)
    (he : 0 < e) (heOne : e < 1) :
    _root_.GD.N0232.N0720.N1301.d016275 mass mass e =
      e ^ _root_.GD.N0232.N0720.N1301.d016252 /
        (e ^ _root_.GD.N0232.N0720.N1301.d016252 + (1 - e) ^ _root_.GD.N0232.N0720.N1301.d016252) := by
  have htail : 0 < 1 - e := sub_pos.mpr heOne
  have hePow : e ^ _root_.GD.N0232.N0720.N1301.d016252 ≠ 0 :=
    (Real.rpow_pos_of_pos he _root_.GD.N0232.N0720.N1301.d016252).ne'
  have htailPow : (1 - e) ^ _root_.GD.N0232.N0720.N1301.d016252 ≠ 0 :=
    (Real.rpow_pos_of_pos htail _root_.GD.N0232.N0720.N1301.d016252).ne'
  unfold _root_.GD.N0232.N0720.N1301.d016275
  rw [Real.rpow_neg he.le, Real.rpow_neg htail.le]
  field_simp [hmass.ne', hePow, htailPow]
  ring


theorem d016278
    {massZero massOne : ℝ}
    (hmassZero : 0 < massZero) (hmassOne : 0 < massOne) :
    _root_.GD.N0232.N0720.N1301.d016275 massZero massOne (1 / 2 : ℝ) =
      massOne / (massZero + massOne) := by
  have hbase : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  have hk : (1 / 2 : ℝ) ^ (-_root_.GD.N0232.N0720.N1301.d016252) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) (-_root_.GD.N0232.N0720.N1301.d016252)).ne'
  have hsum : massZero + massOne ≠ 0 :=
    (add_pos hmassZero hmassOne).ne'
  unfold _root_.GD.N0232.N0720.N1301.d016275
  rw [hbase]
  field_simp [hk, hsum]



theorem d016279
    {mass : ℝ} (hmass : 0 < mass) :
    _root_.GD.N0232.N0720.N1301.d016275 mass mass (1 / 4 : ℝ) < 1 / 4 := by
  let a : ℝ := (1 / 4 : ℝ) ^ _root_.GD.N0232.N0720.N1301.d016252
  let b : ℝ := (3 / 4 : ℝ) ^ _root_.GD.N0232.N0720.N1301.d016252
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _root_.GD.N0232.N0720.N1301.d016252
  have hb : 0 < b := Real.rpow_pos_of_pos (by norm_num) _root_.GD.N0232.N0720.N1301.d016252
  have hform :
      _root_.GD.N0232.N0720.N1301.d016275 mass mass (1 / 4 : ℝ) = a / (a + b) := by
    rw [_root_.GD.N0232.N0720.N1301.d016277 hmass
      (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)]
    norm_num [a, b]
  have hthreePow : (3 : ℝ) < 3 ^ _root_.GD.N0232.N0720.N1301.d016252 := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt
        (by norm_num : (1 : ℝ) < 3)
        (by norm_num [_root_.GD.N0232.N0720.N1301.d016252] : (1 : ℝ) < _root_.GD.N0232.N0720.N1301.d016252)
  have hbFactor : b = 3 ^ _root_.GD.N0232.N0720.N1301.d016252 * a := by
    dsimp only [a, b]
    rw [show (3 / 4 : ℝ) = 3 * (1 / 4) by norm_num,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
        (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hthree : 3 * a < b := by
    rw [hbFactor]
    exact mul_lt_mul_of_pos_right hthreePow ha
  rw [hform, div_lt_iff₀ (add_pos ha hb)]
  nlinarith




theorem d016280
    {massZero massOne : ℝ}
    (hmassZero : 0 < massZero) (hmassOne : 0 < massOne) :
    ¬ ∀ e ∈ Ioo (0 : ℝ) 1,
      _root_.GD.N0232.N0720.N1301.d016275 massZero massOne e = e := by
  intro hidentity
  have hhalf := hidentity (1 / 2 : ℝ) (by norm_num)
  rw [_root_.GD.N0232.N0720.N1301.d016278 hmassZero hmassOne] at hhalf
  have hsum : massZero + massOne ≠ 0 :=
    (add_pos hmassZero hmassOne).ne'
  have hmassEq : massOne = massZero := by
    have hcross := (div_eq_iff hsum).mp hhalf
    linarith
  subst massOne
  have hquarter := hidentity (1 / 4 : ℝ) (by norm_num)
  have hstrict := _root_.GD.N0232.N0720.N1301.d016279 hmassZero
  linarith

end

end N1301
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1301.d016256
#print axioms _root_.GD.N0232.N0720.N1301.d016263
#print axioms _root_.GD.N0232.N0720.N1301.d016273
#print axioms _root_.GD.N0232.N0720.N1301.d016280
