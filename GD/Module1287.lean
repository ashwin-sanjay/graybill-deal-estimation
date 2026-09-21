import GD.Module0373
import GD.Module1285
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.Polynomial.Coeff














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set Polynomial
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1615
noncomputable section

open _root_.GD.N0235 _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1556


def d020882 : Measure (ℝ × ℝ) :=
  (betaMeasure ((3 : ℝ) / 2) 10).prod (betaMeasure 5 5)

def d020883 : Set (ℝ × ℝ) := (Ioo (0 : ℝ) 1) ×ˢ Ioo 0 1

def d020884 (p : ℝ × ℝ) : ℝ≥0∞ :=
  betaPDF ((3 : ℝ) / 2) 10 p.1 * betaPDF 5 5 p.2

@[fun_prop] theorem d020885 : Measurable _root_.GD.N0106.N0428.N0765.N1615.d020884 := by
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020884 betaPDF
  exact ((measurable_betaPDFReal _ _).comp measurable_fst).ennreal_ofReal.mul
    (((measurable_betaPDFReal _ _).comp measurable_snd).ennreal_ofReal)

theorem d020886 :
    _root_.GD.N0106.N0428.N0765.N1615.d020882 = (volume : Measure (ℝ × ℝ)).withDensity _root_.GD.N0106.N0428.N0765.N1615.d020884 := by
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020882 betaMeasure _root_.GD.N0106.N0428.N0765.N1615.d020884
  exact prod_withDensity (measurable_betaPDFReal _ _).ennreal_ofReal
    (measurable_betaPDFReal _ _).ennreal_ofReal

theorem d020887 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1615.d020883) :
    0 < _root_.GD.N0106.N0428.N0765.N1615.d020884 p := by
  obtain ⟨hu, ht⟩ := hp
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020884 betaPDF
  exact ENNReal.mul_pos_iff.mpr
    ⟨ENNReal.ofReal_pos.mpr (betaPDFReal_pos hu.1 hu.2 (by norm_num) (by norm_num)),
      ENNReal.ofReal_pos.mpr (betaPDFReal_pos ht.1 ht.2 (by norm_num) (by norm_num))⟩

theorem d020888 (a b : ℝ) :
    ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff (measurable_betaPDFReal a b).ennreal_ofReal]
  filter_upwards with x hx
  by_contra hnot
  have houtside : ¬ (0 < x ∧ x < 1) := hnot
  simp [betaPDFReal, houtside] at hx

theorem d020889 : ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1615.d020882, p ∈ _root_.GD.N0106.N0428.N0765.N1615.d020883 := by
  letI : IsProbabilityMeasure (betaMeasure (5 : ℝ) 5) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod measurableSet_Ioo)).2
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1615.d020888 ((3 : ℝ) / 2) 10] with u hu
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1615.d020888 5 5] with t ht
  exact ⟨hu, ht⟩



theorem d020890 {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) (hsub : U ⊆ _root_.GD.N0106.N0428.N0765.N1615.d020883) : 0 < _root_.GD.N0106.N0428.N0765.N1615.d020882 U := by
  apply bot_lt_iff_ne_bot.mpr
  intro hz
  change _root_.GD.N0106.N0428.N0765.N1615.d020882 U = (0 : ℝ≥0∞) at hz
  rw [_root_.GD.N0106.N0428.N0765.N1615.d020886,
    withDensity_apply_eq_zero _root_.GD.N0106.N0428.N0765.N1615.d020885] at hz
  have he : {p | _root_.GD.N0106.N0428.N0765.N1615.d020884 p ≠ 0} ∩ U = U := by
    ext p
    exact ⟨fun hp => hp.2, fun hp => ⟨(_root_.GD.N0106.N0428.N0765.N1615.d020887 (hsub hp)).ne', hp⟩⟩
  rw [he] at hz
  exact hU.measure_ne_zero volume hne hz


def d020891 (eta : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, eta * (1 - p.2) / p.2)

def d020892 (eta : ℝ) (p : Fin 3 → ℝ) : ℝ × ℝ :=
  (p 0, eta * p 2 / p 1)

def d020893 (eta : ℝ) : Measure (ℝ × ℝ) := _root_.GD.N0106.N0428.N0765.N1615.d020882.map (_root_.GD.N0106.N0428.N0765.N1615.d020891 eta)

@[fun_prop] theorem d020894 (eta : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1615.d020891 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020891
  fun_prop

@[fun_prop] theorem d020895 (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1615.d020892 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020892
  fun_prop

theorem d020896 (eta : ℝ) : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1615.d020891 eta) _root_.GD.N0106.N0428.N0765.N1615.d020883 := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hp2 : p.2 ≠ 0 := hp.2.1.ne'
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020891
  fun_prop (disch := assumption)

theorem d020897 (eta : ℝ) (heta : 0 < eta)
    {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1615.d020883) : _root_.GD.N0106.N0428.N0765.N1615.d020891 eta p ∈ _root_.GD.N0106.N0428.N0765.N1556.d005646 := by
  exact ⟨hp.1.1, hp.1.2, div_pos (mul_pos heta (sub_pos.mpr hp.2.2)) hp.2.1⟩

theorem d020898 (eta : ℝ) (heta : 0 < eta)
    {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1556.d005646) :
    (p.1, eta / (eta + p.2)) ∈ _root_.GD.N0106.N0428.N0765.N1615.d020883 ∧
      _root_.GD.N0106.N0428.N0765.N1615.d020891 eta (p.1, eta / (eta + p.2)) = p := by
  have hd : 0 < eta + p.2 := add_pos heta hp.2.2
  refine ⟨⟨⟨hp.1, hp.2.1⟩, div_pos heta hd, (div_lt_one hd).2 (by linarith [hp.2.2])⟩, ?_⟩
  apply Prod.ext
  · rfl
  · unfold _root_.GD.N0106.N0428.N0765.N1615.d020891
    dsimp only
    field_simp [heta.ne', hd.ne']
    ring



theorem d020899 (eta : ℝ) (heta : 0 < eta)
    (V : Set (ℝ × ℝ)) (hV : IsOpen V) (hne : (V ∩ _root_.GD.N0106.N0428.N0765.N1556.d005646).Nonempty) :
    0 < _root_.GD.N0106.N0428.N0765.N1615.d020893 eta V := by
  obtain ⟨p, hpV, hpI⟩ := hne
  obtain ⟨hq, heq⟩ := _root_.GD.N0106.N0428.N0765.N1615.d020898 eta heta hpI
  let U := _root_.GD.N0106.N0428.N0765.N1615.d020883 ∩ _root_.GD.N0106.N0428.N0765.N1615.d020891 eta ⁻¹' V
  have hU : IsOpen U :=
    (_root_.GD.N0106.N0428.N0765.N1615.d020896 eta).isOpen_inter_preimage (isOpen_Ioo.prod isOpen_Ioo) hV
  have hneU : U.Nonempty := ⟨(p.1, eta / (eta + p.2)), hq, by simpa [heq] using hpV⟩
  have hpos := _root_.GD.N0106.N0428.N0765.N1615.d020890 hU hneU (fun _ hp => hp.1)
  rw [_root_.GD.N0106.N0428.N0765.N1615.d020893, Measure.map_apply (_root_.GD.N0106.N0428.N0765.N1615.d020894 eta) hV.measurableSet]
  exact hpos.trans_le (measure_mono (fun _ hp => hp.2))

theorem d020900 : _root_.GD.N0106.N0428.N0765.N1615.d020882.map _root_.GD.N0235.d004247 = _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1615.d020882, _root_.GD.N0106.N0428.N0765.N1529.d020798, _root_.GD.N0235.d004250]

theorem d020901 (eta : ℝ) {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1615.d020883) :
    _root_.GD.N0106.N0428.N0765.N1615.d020892 eta (_root_.GD.N0235.d004247 p) = _root_.GD.N0106.N0428.N0765.N1615.d020891 eta p := by
  apply Prod.ext
  · rfl
  · have hu : 1 - p.1 ≠ 0 := (sub_pos.mpr hp.1.2).ne'
    have ht : p.2 ≠ 0 := hp.2.1.ne'
    change eta * ((1 - p.1) * (1 - p.2)) / ((1 - p.1) * p.2) =
      eta * (1 - p.2) / p.2
    field_simp [hu, ht] <;> ring

theorem d020902 (eta : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020798.map (_root_.GD.N0106.N0428.N0765.N1615.d020892 eta) = _root_.GD.N0106.N0428.N0765.N1615.d020893 eta := by
  rw [← _root_.GD.N0106.N0428.N0765.N1615.d020900,
    Measure.map_map (_root_.GD.N0106.N0428.N0765.N1615.d020895 eta) _root_.GD.N0235.d004248]
  apply Measure.map_congr
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1615.d020889] with p hp
  exact _root_.GD.N0106.N0428.N0765.N1615.d020901 eta hp


theorem d020903 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map
      (_root_.GD.N0106.N0428.N0765.N1615.d020892 eta ∘ _root_.GD.N0106.N0428.N0765.N1633.d014080 eta) = _root_.GD.N0106.N0428.N0765.N1615.d020893 eta := by
  rw [← Measure.map_map (_root_.GD.N0106.N0428.N0765.N1615.d020895 eta)
    (_root_.GD.N0106.N0428.N0765.N1633.d014085 eta),
    _root_.GD.N0106.N0428.N0765.N1633.d014101 location eta heta]
  exact _root_.GD.N0106.N0428.N0765.N1615.d020902 eta

def d020904 (eta : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![p.1, _root_.GD.N0106.N0428.N0765.N1556.d005641 eta p.1 p.2, _root_.GD.N0106.N0428.N0765.N1556.d005642 eta p.1 p.2]

@[fun_prop] theorem d020905 (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1615.d020904 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020904 _root_.GD.N0106.N0428.N0765.N1556.d005641 _root_.GD.N0106.N0428.N0765.N1556.d005642
  fun_prop

theorem d020906 (eta : ℝ) (heta : 0 < eta)
    {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1615.d020883) :
    _root_.GD.N0106.N0428.N0765.N1615.d020904 eta (_root_.GD.N0106.N0428.N0765.N1615.d020891 eta p) = _root_.GD.N0235.d004247 p := by
  have ht : p.2 ≠ 0 := hp.2.1.ne'
  have hs : eta + eta * (1 - p.2) / p.2 = eta / p.2 := by
    field_simp [ht]
    ring
  funext i
  fin_cases i
  · rfl
  · change (1 - p.1) * eta / (eta + eta * (1 - p.2) / p.2) =
      (1 - p.1) * p.2
    rw [hs]
    field_simp [heta.ne', ht] <;> ring
  · change (1 - p.1) * (eta * (1 - p.2) / p.2) /
      (eta + eta * (1 - p.2) / p.2) = (1 - p.1) * (1 - p.2)
    rw [hs]
    field_simp [heta.ne', ht] <;> ring

theorem d020907 (eta : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1615.d020904 eta p) = _root_.GD.N0106.N0428.N0765.N1556.d005643 eta p.1 p.2 := rfl

theorem d020908 (eta : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1615.d020904 eta p) = _root_.GD.N0106.N0428.N0765.N1556.d005644 eta p.1 p.2 := rfl



def d020909 (eta s : ℝ) : ℝ := 10 * (1 + eta) * (eta + s) / (eta * (1 + s))

theorem d020910 (eta s : ℝ) (heta : 0 < eta) (hs : 0 < s) (u : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1556.d005644 eta u s = _root_.GD.N0106.N0428.N0765.N1615.d020909 eta s * u / (1 - u) := by
  by_cases hu : u = 1
  · simp [_root_.GD.N0106.N0428.N0765.N1556.d005644, _root_.GD.N0106.N0428.N0765.N1556.d005641, _root_.GD.N0106.N0428.N0765.N1556.d005642, hu]
  · have hes : eta + s ≠ 0 := (add_pos heta hs).ne'
    have hs1 : 1 + s ≠ 0 := (by positivity : 0 < 1 + s).ne'
    have hu' : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    unfold _root_.GD.N0106.N0428.N0765.N1556.d005644 _root_.GD.N0106.N0428.N0765.N1556.d005641 _root_.GD.N0106.N0428.N0765.N1556.d005642 _root_.GD.N0106.N0428.N0765.N1615.d020909
    have hd : (1 - u) * eta / (eta + s) + eta * ((1 - u) * s / (eta + s)) =
        (1 - u) * eta * (1 + s) / (eta + s) := by ring
    rw [hd]
    field_simp [heta.ne', hes, hs1, hu'] <;> ring

theorem d020911 (eta s : ℝ) (heta : 0 < eta) (hs : 0 < s) :
    HasDerivAt (fun u => _root_.GD.N0106.N0428.N0765.N1556.d005644 eta u s) (_root_.GD.N0106.N0428.N0765.N1615.d020909 eta s) 0 := by
  have he : (fun u => _root_.GD.N0106.N0428.N0765.N1556.d005644 eta u s) = (fun u => _root_.GD.N0106.N0428.N0765.N1615.d020909 eta s * u / (1 - u)) := by
    funext u
    exact _root_.GD.N0106.N0428.N0765.N1615.d020910 eta s heta hs u
  rw [he]
  have hn : HasDerivAt (fun u : ℝ => _root_.GD.N0106.N0428.N0765.N1615.d020909 eta s * u) (_root_.GD.N0106.N0428.N0765.N1615.d020909 eta s) 0 :=
    hasDerivAt_const_mul (_root_.GD.N0106.N0428.N0765.N1615.d020909 eta s)
  have hd : HasDerivAt (fun u : ℝ => 1 - u) (-1) 0 :=
    (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hq := hn.fun_div hd (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simpa only [sub_zero, mul_one, mul_zero, zero_mul, one_pow, div_one] using hq

theorem d020912 (eta s : ℝ) (heta : 0 < eta) (hs : 0 < s) :
    0 < deriv (fun u => _root_.GD.N0106.N0428.N0765.N1556.d005644 eta u s) 0 := by
  rw [(_root_.GD.N0106.N0428.N0765.N1615.d020911 eta s heta hs).deriv]
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020909
  positivity


theorem d020913 (eta : ℝ) (heta : 0 < eta)
    (A B : ℝ[X])
    (h : ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798,
      A.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) * _root_.GD.N0106.N0428.N0765.N1529.d020801 eta p - B.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) = 0) :
    A = 0 ∧ B = 0 := by
  have hr : ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1615.d020882,
      A.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0235.d004247 p)) * _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0235.d004247 p) -
        B.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0235.d004247 p)) = 0 := by
    exact ae_of_ae_map _root_.GD.N0235.d004248.aemeasurable
      (_root_.GD.N0106.N0428.N0765.N1615.d020900.symm ▸ h)
  have hm : Measurable fun p : ℝ × ℝ =>
      A.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 eta p.1 p.2) * _root_.GD.N0106.N0428.N0765.N1556.d005644 eta p.1 p.2 - B.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 eta p.1 p.2) := by
    change Measurable (fun p => A.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1615.d020904 eta p)) *
      _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1615.d020904 eta p) - B.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1615.d020904 eta p)))
    fun_prop
  have hc : ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1615.d020893 eta,
      A.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 eta p.1 p.2) * _root_.GD.N0106.N0428.N0765.N1556.d005644 eta p.1 p.2 - B.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 eta p.1 p.2) = 0 := by
    apply (ae_map_iff (_root_.GD.N0106.N0428.N0765.N1615.d020894 eta).aemeasurable (hm (measurableSet_singleton 0))).2
    filter_upwards [hr, _root_.GD.N0106.N0428.N0765.N1615.d020889] with p hp hpI
    change A.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1615.d020904 eta (_root_.GD.N0106.N0428.N0765.N1615.d020891 eta p))) *
      _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1615.d020904 eta (_root_.GD.N0106.N0428.N0765.N1615.d020891 eta p)) -
      B.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1615.d020904 eta (_root_.GD.N0106.N0428.N0765.N1615.d020891 eta p))) = 0
    rw [_root_.GD.N0106.N0428.N0765.N1615.d020906 eta heta hpI]
    exact hp
  exact _root_.GD.N0106.N0428.N0765.N1556.d005681 heta
    (_root_.GD.N0106.N0428.N0765.N1615.d020899 eta heta) (hc.mono fun _ hp _ => hp)

def d020914 (c : Fin 5 → ℝ) : ℝ[X] :=
  ∑ i : Fin 5, C (c i) * X ^ i.val

def d020915 (c : Fin 5 → ℝ) : ℝ[X] := X * (1 - X) * _root_.GD.N0106.N0428.N0765.N1615.d020914 c

theorem d020916 (c : Fin 5 → ℝ) (i : Fin 5) :
    (_root_.GD.N0106.N0428.N0765.N1615.d020914 c).coeff i.val = c i := by
  fin_cases i <;> simp [_root_.GD.N0106.N0428.N0765.N1615.d020914, Fin.sum_univ_succ,
    coeff_C_mul_X_pow, finsetSum_coeff]

theorem d020917 (c : Fin 5 → ℝ)
    (h : _root_.GD.N0106.N0428.N0765.N1615.d020915 c = 0) : c = 0 := by
  have hfactor : (X * (1 - X) : ℝ[X]) ≠ 0 := by
    apply mul_ne_zero X_ne_zero
    intro hz
    have hc := congrArg (fun p : ℝ[X] => p.coeff 1) hz
    norm_num [coeff_one] at hc
  have hz : _root_.GD.N0106.N0428.N0765.N1615.d020914 c = 0 :=
    (mul_eq_zero.mp h).resolve_left hfactor
  funext i
  have hc := congrArg (fun p : ℝ[X] => p.coeff i.val) hz
  simpa only [_root_.GD.N0106.N0428.N0765.N1615.d020916, coeff_zero, Pi.zero_apply] using hc

def d020918 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (eta : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  ∑ j, b j * _root_.GD.N0106.N0428.N0765.N1529.d020803 j eta p

@[fun_prop] theorem d020919 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1615.d020918 b eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020918
  fun_prop

theorem d020920 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (eta : ℝ) (p : Fin 3 → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1615.d020918 b eta p =
      (_root_.GD.N0106.N0428.N0765.N1615.d020915 (fun i => b (i, 1))).eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) * _root_.GD.N0106.N0428.N0765.N1529.d020801 eta p -
        (_root_.GD.N0106.N0428.N0765.N1615.d020915 (fun i => b (i, 0))).eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) := by
  simp [_root_.GD.N0106.N0428.N0765.N1615.d020918, _root_.GD.N0106.N0428.N0765.N1529.d020803, _root_.GD.N0106.N0428.N0765.N1607.d012644, _root_.GD.N0106.N0428.N0765.N1615.d020915, _root_.GD.N0106.N0428.N0765.N1615.d020914,
    Fintype.sum_prod_type, Fin.sum_univ_succ, pow_succ]
  ring


theorem d020921 (eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (h : ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798, _root_.GD.N0106.N0428.N0765.N1615.d020918 b eta p = 0) : b = 0 := by
  have hp := _root_.GD.N0106.N0428.N0765.N1615.d020913 eta heta
    (_root_.GD.N0106.N0428.N0765.N1615.d020915 (fun i => b (i, 1))) (_root_.GD.N0106.N0428.N0765.N1615.d020915 (fun i => b (i, 0)))
    (h.mono fun p hp => by rw [← _root_.GD.N0106.N0428.N0765.N1615.d020920]; exact hp)
  have h1 := _root_.GD.N0106.N0428.N0765.N1615.d020917 _ hp.1
  have h0 := _root_.GD.N0106.N0428.N0765.N1615.d020917 _ hp.2
  funext j
  rcases j with ⟨i, k⟩
  fin_cases k
  · exact congrFun h0 i
  · exact congrFun h1 i

theorem d020922 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (eta : ℝ) (p : Fin 3 → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1615.d020918 b eta p ^ 2 = ∑ i, ∑ j, (b i * b j) * _root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta p := by
  unfold _root_.GD.N0106.N0428.N0765.N1615.d020918
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020805
  ring

theorem d020923 (eta : ℝ) (heta : 0 < eta) (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1615.d020918 b eta p ^ 2) _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1615.d020922]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (_root_.GD.N0106.N0428.N0765.N1529.d020831 i j eta heta).const_mul (b i * b j)

theorem d020924 (eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (hb : b ≠ 0) :
    0 < ∫ p, _root_.GD.N0106.N0428.N0765.N1615.d020918 b eta p ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  have hnon : 0 ≤ ∫ p, _root_.GD.N0106.N0428.N0765.N1615.d020918 b eta p ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    integral_nonneg (fun p => sq_nonneg _)
  apply lt_of_le_of_ne hnon
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg (_root_.GD.N0106.N0428.N0765.N1615.d020918 b eta p))
    (_root_.GD.N0106.N0428.N0765.N1615.d020923 eta heta b)).1 he.symm
  apply hb
  apply _root_.GD.N0106.N0428.N0765.N1615.d020921 eta heta b
  filter_upwards [hz] with p hp
  exact sq_eq_zero_iff.mp hp

theorem d020925 (eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    (∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1529.d020808 eta i j) =
      ((1 + eta) / 11) * ∫ p, _root_.GD.N0106.N0428.N0765.N1615.d020918 b eta p ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  have hint (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
      Integrable (fun p => (b i * b j) * _root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta p) _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    (_root_.GD.N0106.N0428.N0765.N1529.d020831 i j eta heta).const_mul (b i * b j)
  simp_rw [_root_.GD.N0106.N0428.N0765.N1615.d020922]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020808
  ring



theorem d020926 (eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (hb : b ≠ 0) :
    0 < ∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1529.d020808 eta i j := by
  rw [_root_.GD.N0106.N0428.N0765.N1615.d020925 eta heta b]
  exact mul_pos (by positivity) (_root_.GD.N0106.N0428.N0765.N1615.d020924 eta heta b hb)

theorem d020927 (location eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (hb : b ≠ 0) :
    0 < ∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1607.d012677 location eta i j := by
  have he (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : _root_.GD.N0106.N0428.N0765.N1607.d012677 location eta i j = _root_.GD.N0106.N0428.N0765.N1529.d020808 eta i j :=
    _root_.GD.N0106.N0428.N0765.N1529.d020834 location eta heta i j
  simp_rw [he]
  exact _root_.GD.N0106.N0428.N0765.N1615.d020926 eta heta b hb

theorem d020928 (location eta : ℝ) (heta : 0 < eta) :
    (∀ s, 0 < s → 0 < deriv (fun u => _root_.GD.N0106.N0428.N0765.N1556.d005644 eta u s) 0) ∧
    (∃ U : Set (ℝ × ℝ), IsOpen U ∧ U.Nonempty ∧ U ⊆ _root_.GD.N0106.N0428.N0765.N1556.d005645 eta '' _root_.GD.N0106.N0428.N0765.N1556.d005646) ∧
    (∀ A B : ℝ[X],
      (∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798,
        A.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) * _root_.GD.N0106.N0428.N0765.N1529.d020801 eta p - B.eval (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) = 0) →
      A = 0 ∧ B = 0) ∧
    (∀ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ, b ≠ 0 →
      0 < ∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1607.d012677 location eta i j) := by
  exact ⟨fun s hs => _root_.GD.N0106.N0428.N0765.N1615.d020912 eta s heta hs,
    _root_.GD.N0106.N0428.N0765.N1556.d005676 heta,
    fun A B h => _root_.GD.N0106.N0428.N0765.N1615.d020913 eta heta A B h,
    fun b hb => _root_.GD.N0106.N0428.N0765.N1615.d020927 location eta heta b hb⟩

end
end GD.N0106.N0428.N0765.N1615

#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020886
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020890
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020899
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020903
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020911
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020912
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020913
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020917
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020921
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020923
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020926
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020927
#print axioms _root_.GD.N0106.N0428.N0765.N1615.d020928
