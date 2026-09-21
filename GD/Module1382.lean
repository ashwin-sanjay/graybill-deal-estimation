import GD.Module0836
import GD.Module0658
import Mathlib.Probability.Distributions.Exponential

















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0183
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1207

abbrev d022241 := _root_.GD.N0137.d008894 3 × _root_.GD.N0137.d008894 3
abbrev d022242 := ℝ × (ℝ × ℝ)

def d022243 (sigma zeta : ℝ) : ℝ := _root_.GD.N0107.d009045 3 3 sigma zeta
def d022244 (sigma zeta : ℝ) : ℝ := _root_.GD.N0107.d009046 3 3 sigma zeta
def d022245 (sigma zeta : ℝ) : ℝ := _root_.GD.N0183.d022243 sigma zeta * _root_.GD.N0183.d022244 sigma zeta * (1 - _root_.GD.N0183.d022244 sigma zeta)
def d022246 : _root_.GD.N0183.d022241 → ℝ := _root_.GD.N0107.d009090 3 3
def d022247 (w : _root_.GD.N0183.d022241) : ℝ := _root_.GD.N0107.d009085 w.1 / 3
def d022248 (w : _root_.GD.N0183.d022241) : ℝ := _root_.GD.N0107.d009085 w.2 / 3
def d022249 (w : _root_.GD.N0183.d022241) : _root_.GD.N0183.d022242 := (_root_.GD.N0183.d022246 w, (_root_.GD.N0183.d022247 w, _root_.GD.N0183.d022248 w))
def d022250 (sigma zeta : ℝ) (w : _root_.GD.N0183.d022241) : _root_.GD.N0183.d022242 :=
  (_root_.GD.N0183.d022246 w ^ 2 / _root_.GD.N0183.d022243 sigma zeta, (_root_.GD.N0183.d022247 w / _root_.GD.N0183.d022243 sigma zeta, _root_.GD.N0183.d022248 w / _root_.GD.N0183.d022243 sigma zeta))
def d022251 : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioi 0
def d022252 : Set _root_.GD.N0183.d022242 := {b | 0 < b.2.1 ∧ 0 < b.2.2 ∧ 0 < b.1 ^ 2}
def d022253 : Set _root_.GD.N0183.d022241 := _root_.GD.N0183.d022249 ⁻¹' _root_.GD.N0183.d022252
def d022254 (b : _root_.GD.N0183.d022242) : ℝ × ℝ :=
  (b.2.2 / (b.2.1 + b.2.2), b.1 ^ 2 / (b.2.1 + b.2.2))

theorem d022255 (sigma zeta : ℝ) :
    _root_.GD.N0183.d022243 sigma zeta = (sigma ^ 2 + zeta ^ 2) / 3 ∧
      _root_.GD.N0183.d022244 sigma zeta = zeta ^ 2 / (sigma ^ 2 + zeta ^ 2) := by
  constructor
  · unfold _root_.GD.N0183.d022243 _root_.GD.N0107.d009045 _root_.GD.N0107.d009043 _root_.GD.N0107.d009044
    norm_num only [Nat.cast_ofNat]
    ring
  · unfold _root_.GD.N0183.d022244 _root_.GD.N0107.d009046 _root_.GD.N0107.d009045 _root_.GD.N0107.d009043 _root_.GD.N0107.d009044
    norm_num only [Nat.cast_ofNat]
    rw [← add_div]
    by_cases h : sigma ^ 2 + zeta ^ 2 = 0
    · simp [h]
    · field_simp [h]
      <;> ring

theorem d022256 (sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    0 < _root_.GD.N0183.d022243 sigma zeta ∧ 0 < _root_.GD.N0183.d022244 sigma zeta ∧ _root_.GD.N0183.d022244 sigma zeta < 1 :=
  ⟨_root_.GD.N0107.d009049 (by norm_num) (by norm_num) hsigma hzeta,
    _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta,
    _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta⟩

@[fun_prop] theorem d022257 : Measurable _root_.GD.N0183.d022249 := by
  unfold _root_.GD.N0183.d022249 _root_.GD.N0183.d022246 _root_.GD.N0183.d022247 _root_.GD.N0183.d022248 _root_.GD.N0107.d009090 _root_.GD.N0107.d009084 _root_.GD.N0107.d009085
    _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420
  fun_prop

@[fun_prop] theorem d022258 (sigma zeta : ℝ) :
    Measurable (_root_.GD.N0183.d022250 sigma zeta) :=
  ((_root_.GD.N0183.d022257.fst.pow_const 2).div_const _).prodMk
    ((_root_.GD.N0183.d022257.snd.fst.div_const _).prodMk
      (_root_.GD.N0183.d022257.snd.snd.div_const _))

theorem d022259 : MeasurableSet _root_.GD.N0183.d022252 :=
  (measurableSet_lt measurable_const measurable_snd.fst).inter
    ((measurableSet_lt measurable_const measurable_snd.snd).inter
      (measurableSet_lt measurable_const (measurable_fst.pow_const 2)))

theorem d022260 : MeasurableSet _root_.GD.N0183.d022253 :=
  _root_.GD.N0183.d022257 _root_.GD.N0183.d022259

@[fun_prop] theorem d022261 : Measurable _root_.GD.N0183.d022254 := by
  unfold _root_.GD.N0183.d022254
  fun_prop


theorem d022262 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) (w : _root_.GD.N0183.d022241) :
    _root_.GD.N0183.d022250 sigma zeta w =
      ((_root_.GD.N0107.d009032 3 3 mu sigma zeta (_root_.GD.N0183.d022244 sigma zeta) w) ^ 2,
        ((1 - _root_.GD.N0183.d022244 sigma zeta) * _root_.GD.N0107.d009033 3 3 mu sigma zeta w,
          _root_.GD.N0183.d022244 sigma zeta * _root_.GD.N0107.d009034 3 3 mu sigma zeta w)) := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have hD := _root_.GD.N0107.d012724 3 3 (by norm_num) (by norm_num)
    mu sigma zeta hsigma hzeta w
  change Real.sqrt (_root_.GD.N0183.d022243 sigma zeta) *
    _root_.GD.N0107.d009032 3 3 mu sigma zeta (_root_.GD.N0183.d022244 sigma zeta) w = _root_.GD.N0183.d022246 w at hD
  apply Prod.ext
  · change _root_.GD.N0183.d022246 w ^ 2 / _root_.GD.N0183.d022243 sigma zeta = _
    rw [← hD, mul_pow, Real.sq_sqrt hp.1.le]
    field_simp [hp.1.ne']
  · apply Prod.ext
    · change _root_.GD.N0183.d022247 w / _root_.GD.N0183.d022243 sigma zeta = _
      rw [_root_.GD.N0107.d012725 3 3 (by norm_num)]
      rw [show 1 - _root_.GD.N0183.d022244 sigma zeta = _root_.GD.N0107.d009043 3 sigma / _root_.GD.N0183.d022243 sigma zeta from
        _root_.GD.N0107.d012721 (by norm_num) (by norm_num) hsigma hzeta]
      unfold _root_.GD.N0183.d022247 _root_.GD.N0107.d009043
      norm_num only [Nat.cast_ofNat]
      field_simp [hsigma.ne', hp.1.ne']
    · change _root_.GD.N0183.d022248 w / _root_.GD.N0183.d022243 sigma zeta = _
      rw [_root_.GD.N0107.d012726 3 3 (by norm_num)]
      change (_root_.GD.N0107.d009085 w.2 / 3) / _root_.GD.N0183.d022243 sigma zeta =
        (zeta ^ 2 / 3 / _root_.GD.N0183.d022243 sigma zeta) * (_root_.GD.N0107.d009085 w.2 / zeta ^ 2)
      field_simp [hzeta.ne', hp.1.ne']


theorem d022263 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    (_root_.GD.N0107.d009030 3 3 mu sigma zeta).map (_root_.GD.N0183.d022250 sigma zeta) =
      (_root_.GD.N0121.d006346 1).prod
        ((expMeasure (1 / (1 - _root_.GD.N0183.d022244 sigma zeta))).prod
          (expMeasure (1 / _root_.GD.N0183.d022244 sigma zeta))) := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  letI : IsProbabilityMeasure (gammaMeasure (1 : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  let S := _root_.GD.N0107.d009035 3 3 mu sigma zeta (_root_.GD.N0183.d022244 sigma zeta)
  let F : _root_.GD.N0183.d022242 → _root_.GD.N0183.d022242 := Prod.map (fun z : ℝ => z ^ 2)
    (Prod.map (fun x : ℝ => (1 - _root_.GD.N0183.d022244 sigma zeta) * x)
      (fun y : ℝ => _root_.GD.N0183.d022244 sigma zeta * y))
  have hS : Measurable S := _root_.GD.N0107.d009036 3 3 mu sigma zeta _
  have hF : Measurable F := by dsimp [F]; fun_prop
  have heq : _root_.GD.N0183.d022250 sigma zeta = F ∘ S := by
    funext w
    exact _root_.GD.N0183.d022262 mu sigma zeta hsigma hzeta w
  have hraw := _root_.GD.N0107.d009037
    3 3 (by norm_num) (by norm_num) mu sigma zeta hsigma.ne' hzeta.ne'
    hp.2.1.le hp.2.2.le
  change (_root_.GD.N0107.d009030 3 3 mu sigma zeta).map S =
    _root_.GD.N0125.d008840 (((3 - 1 : ℕ) : ℝ) / 2)
      (((3 - 1 : ℕ) : ℝ) / 2) at hraw
  norm_num at hraw
  rw [heq, ← Measure.map_map hF hS, hraw]
  unfold _root_.GD.N0125.d008840 F
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    _root_.GD.N0121.d006355,
    _root_.GD.N0232.N0719.N0954.d009354
      (by norm_num) (by norm_num) (sub_pos.mpr hp.2.2),
    _root_.GD.N0232.N0719.N0954.d009354
      (by norm_num) (by norm_num) hp.2.1]
  rfl


theorem d022264 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    HasLaw (fun w => _root_.GD.N0183.d022246 w ^ 2 / _root_.GD.N0183.d022243 sigma zeta) (_root_.GD.N0121.d006346 1)
        (_root_.GD.N0107.d009030 3 3 mu sigma zeta) ∧
      HasLaw (fun w => _root_.GD.N0183.d022247 w / _root_.GD.N0183.d022243 sigma zeta) (expMeasure (1 / (1 - _root_.GD.N0183.d022244 sigma zeta)))
        (_root_.GD.N0107.d009030 3 3 mu sigma zeta) ∧
      HasLaw (fun w => _root_.GD.N0183.d022248 w / _root_.GD.N0183.d022243 sigma zeta) (expMeasure (1 / _root_.GD.N0183.d022244 sigma zeta))
        (_root_.GD.N0107.d009030 3 3 mu sigma zeta) := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have ht : 0 < _root_.GD.N0183.d022244 sigma zeta := hp.2.1
  have hnt : 0 < 1 - _root_.GD.N0183.d022244 sigma zeta := sub_pos.mpr hp.2.2
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 1) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (expMeasure (1 / (1 - _root_.GD.N0183.d022244 sigma zeta))) :=
    isProbabilityMeasure_expMeasure (by positivity)
  letI : IsProbabilityMeasure (expMeasure (1 / _root_.GD.N0183.d022244 sigma zeta)) :=
    isProbabilityMeasure_expMeasure (by positivity)
  have hj : HasLaw (_root_.GD.N0183.d022250 sigma zeta)
      ((_root_.GD.N0121.d006346 1).prod
        ((expMeasure (1 / (1 - _root_.GD.N0183.d022244 sigma zeta))).prod (expMeasure (1 / _root_.GD.N0183.d022244 sigma zeta))))
      (_root_.GD.N0107.d009030 3 3 mu sigma zeta) :=
    ⟨(_root_.GD.N0183.d022258 sigma zeta).aemeasurable,
      _root_.GD.N0183.d022263 mu sigma zeta hsigma hzeta⟩
  have hab := measurePreserving_snd.fun_comp_hasLaw hj
  exact ⟨measurePreserving_fst.fun_comp_hasLaw hj,
    measurePreserving_fst.fun_comp_hasLaw hab,
    measurePreserving_snd.fun_comp_hasLaw hab⟩


theorem d022265 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    IndepFun (fun w => _root_.GD.N0183.d022247 w / _root_.GD.N0183.d022243 sigma zeta) (fun w => _root_.GD.N0183.d022248 w / _root_.GD.N0183.d022243 sigma zeta)
        (_root_.GD.N0107.d009030 3 3 mu sigma zeta) ∧
      IndepFun (fun w => _root_.GD.N0183.d022246 w ^ 2 / _root_.GD.N0183.d022243 sigma zeta)
        (fun w => (_root_.GD.N0183.d022247 w / _root_.GD.N0183.d022243 sigma zeta, _root_.GD.N0183.d022248 w / _root_.GD.N0183.d022243 sigma zeta))
        (_root_.GD.N0107.d009030 3 3 mu sigma zeta) := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have ht : 0 < _root_.GD.N0183.d022244 sigma zeta := hp.2.1
  have hnt : 0 < 1 - _root_.GD.N0183.d022244 sigma zeta := sub_pos.mpr hp.2.2
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 1) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (expMeasure (1 / (1 - _root_.GD.N0183.d022244 sigma zeta))) :=
    isProbabilityMeasure_expMeasure (by positivity)
  letI : IsProbabilityMeasure (expMeasure (1 / _root_.GD.N0183.d022244 sigma zeta)) :=
    isProbabilityMeasure_expMeasure (by positivity)
  have hj : HasLaw (_root_.GD.N0183.d022250 sigma zeta)
      ((_root_.GD.N0121.d006346 1).prod
        ((expMeasure (1 / (1 - _root_.GD.N0183.d022244 sigma zeta))).prod (expMeasure (1 / _root_.GD.N0183.d022244 sigma zeta))))
      (_root_.GD.N0107.d009030 3 3 mu sigma zeta) :=
    ⟨(_root_.GD.N0183.d022258 sigma zeta).aemeasurable,
      _root_.GD.N0183.d022263 mu sigma zeta hsigma hzeta⟩
  have hab := measurePreserving_snd.fun_comp_hasLaw hj
  constructor
  · exact _root_.GD.N0107.d012741 (_root_.GD.N0183.d022258 sigma zeta).snd
      measurable_fst measurable_snd hab.map_eq
      (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)
  · exact _root_.GD.N0107.d012741 (_root_.GD.N0183.d022258 sigma zeta)
      measurable_fst measurable_snd hj.map_eq
      (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)


theorem d022266 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    Integrable (fun w => _root_.GD.N0183.d022247 w / _root_.GD.N0183.d022243 sigma zeta) (_root_.GD.N0107.d009030 3 3 mu sigma zeta) ∧
      Integrable (fun w => _root_.GD.N0183.d022248 w / _root_.GD.N0183.d022243 sigma zeta) (_root_.GD.N0107.d009030 3 3 mu sigma zeta) ∧
      (∫ w, _root_.GD.N0183.d022247 w / _root_.GD.N0183.d022243 sigma zeta ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta) = 1 - _root_.GD.N0183.d022244 sigma zeta ∧
      (∫ w, _root_.GD.N0183.d022248 w / _root_.GD.N0183.d022243 sigma zeta ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta) = _root_.GD.N0183.d022244 sigma zeta := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have ht : 0 < _root_.GD.N0183.d022244 sigma zeta := hp.2.1
  have hnt : 0 < 1 - _root_.GD.N0183.d022244 sigma zeta := sub_pos.mpr hp.2.2
  have hl := _root_.GD.N0183.d022264 mu sigma zeta hsigma hzeta
  have hx : (∫ w, _root_.GD.N0183.d022247 w / _root_.GD.N0183.d022243 sigma zeta ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta) =
      1 - _root_.GD.N0183.d022244 sigma zeta := by
    rw [hl.2.1.integral_eq]
    unfold expMeasure
    rw [_root_.GD.N0232.N0719.N0960.d009682
      (by norm_num) (by positivity)]
    field_simp [(sub_pos.mpr hp.2.2).ne']
  have hy : (∫ w, _root_.GD.N0183.d022248 w / _root_.GD.N0183.d022243 sigma zeta ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta) =
      _root_.GD.N0183.d022244 sigma zeta := by
    rw [hl.2.2.integral_eq]
    unfold expMeasure
    rw [_root_.GD.N0232.N0719.N0960.d009682
      (by norm_num) (by positivity)]
    field_simp [hp.2.1.ne']
  exact ⟨Integrable.of_integral_ne_zero (hx.trans_ne (sub_pos.mpr hp.2.2).ne'),
    Integrable.of_integral_ne_zero (hy.trans_ne hp.2.1.ne'), hx, hy⟩


theorem d022267 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    ∀ᵐ w ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta, w ∈ _root_.GD.N0183.d022253 := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have ht : 0 < _root_.GD.N0183.d022244 sigma zeta := hp.2.1
  have hnt : 0 < 1 - _root_.GD.N0183.d022244 sigma zeta := sub_pos.mpr hp.2.2
  have hl := _root_.GD.N0183.d022264 mu sigma zeta hsigma hzeta
  have hz := (hl.1.ae_iff (show Measurable (fun x : ℝ => 0 < x) by fun_prop)).2
    (_root_.GD.N0119.d009072 (by norm_num) (by norm_num))
  have hx := (hl.2.1.ae_iff (show Measurable (fun x : ℝ => 0 < x) by fun_prop)).2
    (_root_.GD.N0119.d009072 (by norm_num) (by positivity))
  have hy := (hl.2.2.ae_iff (show Measurable (fun x : ℝ => 0 < x) by fun_prop)).2
    (_root_.GD.N0119.d009072 (by norm_num) (by positivity))
  filter_upwards [hz, hx, hy] with w hz hx hy
  exact ⟨(div_pos_iff_of_pos_right hp.1).mp hx,
    (div_pos_iff_of_pos_right hp.1).mp hy,
    (div_pos_iff_of_pos_right hp.1).mp hz⟩

theorem d022268 {b : _root_.GD.N0183.d022242} (hb : b ∈ _root_.GD.N0183.d022252) :
    _root_.GD.N0183.d022254 b ∈ _root_.GD.N0183.d022251 := by
  have hd := add_pos hb.1 hb.2.1
  exact ⟨⟨div_pos hb.2.1 hd, (div_lt_one hd).mpr (by linarith [hb.1])⟩,
    div_pos hb.2.2 hd⟩

theorem d022269 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    ∀ᵐ w ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta, _root_.GD.N0183.d022254 (_root_.GD.N0183.d022249 w) ∈ _root_.GD.N0183.d022251 := by
  filter_upwards [_root_.GD.N0183.d022267 mu sigma zeta hsigma hzeta] with w hw
  exact _root_.GD.N0183.d022268 hw

def d022270 (b : _root_.GD.N0183.d022242) : ℝ × ℝ := by
  classical
  exact if b ∈ _root_.GD.N0183.d022252 then _root_.GD.N0183.d022254 b else (1 / 2, 1)

theorem d022271 (b : _root_.GD.N0183.d022242) : _root_.GD.N0183.d022270 b ∈ _root_.GD.N0183.d022251 := by
  unfold _root_.GD.N0183.d022270
  split_ifs with hb
  · exact _root_.GD.N0183.d022268 hb
  · norm_num [_root_.GD.N0183.d022251]

def d022272 (b : _root_.GD.N0183.d022242) : _root_.GD.N0183.d022251 := ⟨_root_.GD.N0183.d022270 b, _root_.GD.N0183.d022271 b⟩

@[fun_prop] theorem d022273 : Measurable _root_.GD.N0183.d022270 :=
  Measurable.ite _root_.GD.N0183.d022259 _root_.GD.N0183.d022261 measurable_const

@[fun_prop] theorem d022274 : Measurable _root_.GD.N0183.d022272 :=
  _root_.GD.N0183.d022273.subtype_mk

def d022275 (g : _root_.GD.N0183.d022251 → ℝ) (b : _root_.GD.N0183.d022242) : ℝ := by
  classical
  exact if b ∈ _root_.GD.N0183.d022252 then g (_root_.GD.N0183.d022272 b) else 1 / 2

def d022276 (g : _root_.GD.N0183.d022251 → ℝ) (w : _root_.GD.N0183.d022241) : ℝ :=
  _root_.GD.N0107.d009084 w.2 + _root_.GD.N0183.d022246 w * _root_.GD.N0183.d022275 g (_root_.GD.N0183.d022249 w)

@[fun_prop] theorem d022277 (g : _root_.GD.N0183.d022251 → ℝ) (hg : Measurable g) :
    Measurable (_root_.GD.N0183.d022275 g) :=
  Measurable.ite _root_.GD.N0183.d022259
    (hg.comp _root_.GD.N0183.d022274) measurable_const

theorem d022278 (g : _root_.GD.N0183.d022251 → ℝ) (hgb : ∀ p, g p ∈ Icc (0 : ℝ) 1)
    (b : _root_.GD.N0183.d022242) : _root_.GD.N0183.d022275 g b ∈ Icc (0 : ℝ) 1 := by
  unfold _root_.GD.N0183.d022275
  split_ifs
  · exact hgb _
  · norm_num

@[fun_prop] theorem d022279 (g : _root_.GD.N0183.d022251 → ℝ) (hg : Measurable g) :
    Measurable (_root_.GD.N0183.d022276 g) := by
  have hm : Measurable (fun w : _root_.GD.N0183.d022241 => _root_.GD.N0107.d009084 w.2) := by
    unfold _root_.GD.N0107.d009084 _root_.GD.N0126.d006420
    fun_prop
  exact hm.add (_root_.GD.N0183.d022257.fst.mul ((_root_.GD.N0183.d022277 g hg).comp _root_.GD.N0183.d022257))

theorem d022280 (g : _root_.GD.N0183.d022251 → ℝ) (w : _root_.GD.N0183.d022241) (hw : w ∈ _root_.GD.N0183.d022253) :
    _root_.GD.N0183.d022276 g w = _root_.GD.N0107.d009084 w.2 + _root_.GD.N0183.d022246 w *
      g ⟨_root_.GD.N0183.d022254 (_root_.GD.N0183.d022249 w), _root_.GD.N0183.d022268 hw⟩ := by
  have hb : _root_.GD.N0183.d022249 w ∈ _root_.GD.N0183.d022252 := hw
  simp [_root_.GD.N0183.d022276, _root_.GD.N0183.d022275, hb, _root_.GD.N0183.d022272, _root_.GD.N0183.d022270]

theorem d022281 (g : _root_.GD.N0183.d022251 → ℝ) (w : _root_.GD.N0183.d022241) (hw : w ∉ _root_.GD.N0183.d022253) :
    _root_.GD.N0183.d022276 g w = (_root_.GD.N0107.d009084 w.1 + _root_.GD.N0107.d009084 w.2) / 2 := by
  have hb : _root_.GD.N0183.d022249 w ∉ _root_.GD.N0183.d022252 := hw
  simp only [_root_.GD.N0183.d022276, _root_.GD.N0183.d022275, if_neg hb]
  unfold _root_.GD.N0183.d022246 _root_.GD.N0107.d009090
  ring

def d022282 (mu sigma zeta : ℝ) : _root_.GD.N0183.d022241 → ℝ :=
  _root_.GD.N0107.d012732 3 3 mu (_root_.GD.N0183.d022244 sigma zeta)


theorem d022283 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    IndepFun (_root_.GD.N0183.d022282 mu sigma zeta) _root_.GD.N0183.d022249 (_root_.GD.N0107.d009030 3 3 mu sigma zeta) := by
  let e := _root_.GD.N0183.d022244 sigma zeta
  let W := _root_.GD.N0183.d022243 sigma zeta
  let S := _root_.GD.N0107.d009025 3 3 mu sigma zeta
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have hi := _root_.GD.N0107.d012741
    (P := _root_.GD.N0107.d009030 3 3 mu sigma zeta) (Q := _root_.GD.N0137.d008914 3 3)
    (S := S) (f := _root_.GD.N0137.d008931 3 3 e) (g := _root_.GD.N0137.d008935 3 3 e)
    (_root_.GD.N0107.d009027 3 3 mu sigma zeta)
    (_root_.GD.N0137.d008936 3 3 e) (_root_.GD.N0137.d008937 3 3 e)
    (_root_.GD.N0107.d009031 3 3 mu sigma zeta hsigma.ne' hzeta.ne')
    (_root_.GD.N0137.d008940 3 3 (by norm_num) (by norm_num) hp.2.1.le hp.2.2.le)
  have hi' := hi.comp
    (show Measurable (fun u : ℝ => Real.sqrt (W * e * (1 - e)) * u) by fun_prop)
    (show Measurable (fun b : _root_.GD.N0183.d022242 =>
      (Real.sqrt W * b.1, (sigma ^ 2 / 3 * b.2.1, zeta ^ 2 / 3 * b.2.2))) by fun_prop)
  change IndepFun
    (fun w => Real.sqrt (W * e * (1 - e)) * _root_.GD.N0137.d008931 3 3 e (S w))
    (fun w => (Real.sqrt W * _root_.GD.N0137.d008932 3 3 e (S w),
      (sigma ^ 2 / 3 * _root_.GD.N0137.d008933 3 3 (S w), zeta ^ 2 / 3 * _root_.GD.N0137.d008934 3 3 (S w))))
    (_root_.GD.N0107.d009030 3 3 mu sigma zeta) at hi'
  have hu : (fun w => Real.sqrt (W * e * (1 - e)) * _root_.GD.N0137.d008931 3 3 e (S w)) =
      _root_.GD.N0183.d022282 mu sigma zeta := by
    funext w
    exact _root_.GD.N0107.d012740 3 3 (by norm_num) (by norm_num)
      mu sigma zeta hsigma hzeta w
  have hb : (fun w => (Real.sqrt W * _root_.GD.N0137.d008932 3 3 e (S w),
      (sigma ^ 2 / 3 * _root_.GD.N0137.d008933 3 3 (S w), zeta ^ 2 / 3 * _root_.GD.N0137.d008934 3 3 (S w)))) = _root_.GD.N0183.d022249 := by
    funext w
    apply Prod.ext
    · exact _root_.GD.N0107.d012724 3 3 (by norm_num) (by norm_num)
        mu sigma zeta hsigma hzeta w
    · apply Prod.ext
      · change sigma ^ 2 / 3 * _root_.GD.N0107.d009033 3 3 mu sigma zeta w = _root_.GD.N0183.d022247 w
        rw [_root_.GD.N0107.d012725 3 3 (by norm_num)]
        unfold _root_.GD.N0183.d022247
        field_simp [hsigma.ne']
      · change zeta ^ 2 / 3 * _root_.GD.N0107.d009034 3 3 mu sigma zeta w = _root_.GD.N0183.d022248 w
        rw [_root_.GD.N0107.d012726 3 3 (by norm_num)]
        unfold _root_.GD.N0183.d022248
        field_simp [hzeta.ne']
  rw [hu, hb] at hi'
  exact hi'

theorem d022284 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    MemLp (_root_.GD.N0183.d022282 mu sigma zeta) 2 (_root_.GD.N0107.d009030 3 3 mu sigma zeta) :=
  _root_.GD.N0107.d012747 3 3 (by norm_num) (by norm_num) mu sigma zeta hsigma hzeta

theorem d022285 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    ∫ w, _root_.GD.N0183.d022282 mu sigma zeta w ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta = 0 :=
  _root_.GD.N0107.d012746 3 3 (by norm_num) (by norm_num)
    mu sigma zeta hsigma hzeta

theorem d022286 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 3 3 mu sigma zeta) (_root_.GD.N0183.d022282 mu sigma zeta) =
      _root_.GD.N0183.d022245 sigma zeta := by
  let e := _root_.GD.N0183.d022244 sigma zeta
  let W := _root_.GD.N0183.d022243 sigma zeta
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have hLaw : HasLaw (_root_.GD.N0137.d008931 3 3 e) (gaussianReal 0 1) (_root_.GD.N0137.d008914 3 3) :=
    ⟨(_root_.GD.N0137.d008936 3 3 e).aemeasurable,
      _root_.GD.N0137.d008939 3 3 (by norm_num) (by norm_num) hp.2.1.le hp.2.2.le⟩
  have hstandard : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
    simpa only [sub_zero, NNReal.coe_one] using h
  have hsq : (∫ w, _root_.GD.N0137.d008931 3 3 e w ^ 2 ∂_root_.GD.N0137.d008914 3 3) = 1 := by
    calc
      _ = ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1 := by
        simpa only [Function.comp_def] using
          hLaw.integral_comp (show AEStronglyMeasurable (fun z : ℝ => z ^ 2)
            (gaussianReal 0 1) by fun_prop)
      _ = 1 := hstandard
  have heq (w : _root_.GD.N0183.d022241) : _root_.GD.N0183.d022282 mu sigma zeta w =
      _root_.GD.N0137.d008945 3 3 e W (_root_.GD.N0107.d009025 3 3 mu sigma zeta w) :=
    (_root_.GD.N0107.d012740 3 3 (by norm_num) (by norm_num)
      mu sigma zeta hsigma hzeta w).symm
  unfold _root_.GD.N0141.d006684
  simp_rw [heq]
  rw [_root_.GD.N0107.d012742
    (_root_.GD.N0107.d009027 3 3 mu sigma zeta)
    (show Measurable (fun w => _root_.GD.N0137.d008945 3 3 e W w ^ 2) by
      unfold _root_.GD.N0137.d008945
      exact (measurable_const.mul (_root_.GD.N0137.d008936 3 3 e)).pow_const 2)
    (_root_.GD.N0107.d009031 3 3 mu sigma zeta hsigma.ne' hzeta.ne')]
  simp_rw [_root_.GD.N0137.d008945, mul_pow]
  rw [integral_const_mul, hsq, mul_one,
    Real.sq_sqrt (mul_nonneg (mul_nonneg hp.1.le hp.2.1.le) (sub_nonneg.mpr hp.2.2.le))]
  rfl

theorem d022287 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    Var[_root_.GD.N0183.d022282 mu sigma zeta; _root_.GD.N0107.d009030 3 3 mu sigma zeta] =
      _root_.GD.N0183.d022245 sigma zeta := by
  have hm : Measurable (_root_.GD.N0183.d022282 mu sigma zeta) := by
    unfold _root_.GD.N0183.d022282 _root_.GD.N0107.d012732 _root_.GD.N0107.d009090 _root_.GD.N0107.d009084
      _root_.GD.N0126.d006420
    fun_prop
  rw [variance_eq_integral hm.aemeasurable,
    _root_.GD.N0183.d022285 mu sigma zeta hsigma hzeta]
  simpa only [sub_zero, _root_.GD.N0141.d006684] using _root_.GD.N0183.d022286 mu sigma zeta hsigma hzeta

theorem d022288 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    MemLp _root_.GD.N0183.d022246 2 (_root_.GD.N0107.d009030 3 3 mu sigma zeta) := by
  simpa only [_root_.GD.N0183.d022246, mul_one] using
    (_root_.GD.N0107.d012749 3 3 (by norm_num) (by norm_num)
      mu sigma zeta hsigma hzeta (fun _ => 1) measurable_const
      (B := 1) (by norm_num) (by intro p; norm_num)).2

theorem d022289 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (g : _root_.GD.N0183.d022251 → ℝ) (hg : Measurable g) (hgb : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    MemLp (fun w => _root_.GD.N0183.d022246 w * (_root_.GD.N0183.d022275 g (_root_.GD.N0183.d022249 w) - _root_.GD.N0183.d022244 sigma zeta)) 2
      (_root_.GD.N0107.d009030 3 3 mu sigma zeta) := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  apply _root_.GD.N0119.d009071
    (_root_.GD.N0183.d022288 mu sigma zeta hsigma hzeta)
    (((_root_.GD.N0183.d022277 g hg).comp _root_.GD.N0183.d022257).sub measurable_const).aestronglyMeasurable
    (C := 1) (by norm_num)
  exact ae_of_all _ fun w => abs_le.mpr (by
    have hb := _root_.GD.N0183.d022278 g hgb (_root_.GD.N0183.d022249 w)
    dsimp only [Function.comp_def]
    constructor <;> linarith [hb.1, hb.2, hp.2.1, hp.2.2])


theorem d022290 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (g : _root_.GD.N0183.d022251 → ℝ) (hg : Measurable g) (hgb : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Measurable (_root_.GD.N0183.d022276 g) ∧
      MemLp (fun w => _root_.GD.N0183.d022276 g w - mu) 2 (_root_.GD.N0107.d009030 3 3 mu sigma zeta) ∧
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 3 3 mu sigma zeta) (fun w => _root_.GD.N0183.d022276 g w - mu) =
        _root_.GD.N0183.d022245 sigma zeta + ∫ w, _root_.GD.N0183.d022246 w ^ 2 * (_root_.GD.N0183.d022275 g (_root_.GD.N0183.d022249 w) - _root_.GD.N0183.d022244 sigma zeta) ^ 2
          ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta := by
  let U := _root_.GD.N0183.d022282 mu sigma zeta
  let L := fun w => _root_.GD.N0183.d022275 g (_root_.GD.N0183.d022249 w)
  let e := _root_.GD.N0183.d022244 sigma zeta
  have hU := _root_.GD.N0183.d022284 mu sigma zeta hsigma hzeta
  have hc := _root_.GD.N0183.d022289 mu sigma zeta hsigma hzeta g hg hgb
  have hi := (_root_.GD.N0183.d022283 mu sigma zeta hsigma hzeta).comp
    measurable_id (show Measurable (fun b : _root_.GD.N0183.d022242 => b.1 * (_root_.GD.N0183.d022275 g b - e)) from
      measurable_fst.mul ((_root_.GD.N0183.d022277 g hg).sub measurable_const))
  have ho : (∫ w, U w * (_root_.GD.N0183.d022246 w * (L w - e)) ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta) = 0 :=
    _root_.GD.N0141.d006692 hi hU.aestronglyMeasurable
      hc.aestronglyMeasurable (_root_.GD.N0183.d022285 mu sigma zeta hsigma hzeta)
  have heq : (fun w => _root_.GD.N0183.d022276 g w - mu) = _root_.GD.N0141.d006685 U _root_.GD.N0183.d022246 L e := by
    funext w
    unfold _root_.GD.N0183.d022276 _root_.GD.N0141.d006685 U L e _root_.GD.N0183.d022282 _root_.GD.N0107.d012732 _root_.GD.N0183.d022246
    ring
  refine ⟨_root_.GD.N0183.d022279 g hg, ?_, ?_⟩
  · rw [heq]
    exact hU.add hc
  · have hr := _root_.GD.N0232.N0720.N1207.d012751 hU hc ho
    rw [← heq] at hr
    have hv := _root_.GD.N0183.d022286 mu sigma zeta hsigma hzeta
    change _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 3 3 mu sigma zeta) U = _root_.GD.N0183.d022245 sigma zeta at hv
    linarith


theorem d022291 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (g : _root_.GD.N0183.d022251 → ℝ) (hg : Measurable g) (hgb : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫⁻ w, ENNReal.ofReal ((_root_.GD.N0183.d022276 g w - mu) ^ 2)
      ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta) < ⊤ := by
  have h := (_root_.GD.N0183.d022290 mu sigma zeta hsigma hzeta g hg hgb).2.1
  rw [← ofReal_integral_eq_lintegral_ofReal h.integrable_sq
    (ae_of_all _ fun w => sq_nonneg (_root_.GD.N0183.d022276 g w - mu))]
  exact ENNReal.ofReal_lt_top

end
end GD.N0183

#print axioms _root_.GD.N0183.d022255
#print axioms _root_.GD.N0183.d022256
#print axioms _root_.GD.N0183.d022257
#print axioms _root_.GD.N0183.d022258
#print axioms _root_.GD.N0183.d022259
#print axioms _root_.GD.N0183.d022260
#print axioms _root_.GD.N0183.d022261
#print axioms _root_.GD.N0183.d022262
#print axioms _root_.GD.N0183.d022263
#print axioms _root_.GD.N0183.d022264
#print axioms _root_.GD.N0183.d022265
#print axioms _root_.GD.N0183.d022266
#print axioms _root_.GD.N0183.d022267
#print axioms _root_.GD.N0183.d022268
#print axioms _root_.GD.N0183.d022269
#print axioms _root_.GD.N0183.d022271
#print axioms _root_.GD.N0183.d022273
#print axioms _root_.GD.N0183.d022274
#print axioms _root_.GD.N0183.d022277
#print axioms _root_.GD.N0183.d022278
#print axioms _root_.GD.N0183.d022279
#print axioms _root_.GD.N0183.d022280
#print axioms _root_.GD.N0183.d022281
#print axioms _root_.GD.N0183.d022283
#print axioms _root_.GD.N0183.d022284
#print axioms _root_.GD.N0183.d022285
#print axioms _root_.GD.N0183.d022286
#print axioms _root_.GD.N0183.d022287
#print axioms _root_.GD.N0183.d022288
#print axioms _root_.GD.N0183.d022289
#print axioms _root_.GD.N0183.d022290
#print axioms _root_.GD.N0183.d022291
