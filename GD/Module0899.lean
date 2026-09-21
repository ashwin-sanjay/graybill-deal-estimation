import GD.Module0877
import GD.Module0898
import GD.Module0237

set_option warningAsError true



































open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0232.N0720.N1046

noncomputable section

open _root_.GD.N0228.N0546
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1435
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1504



def d013980 (rho : ℝ) : ℝ :=
  rho / (1 + rho)



def d013981 (rho : ℝ) : ℝ × ℝ → ℝ :=
  _root_.GD.N0232.N0720.N1091.d012759 (_root_.GD.N0232.N0720.N1046.d013980 rho)

@[fun_prop]
theorem d013982 (rho : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1046.d013981 rho) := by
  exact _root_.GD.N0232.N0720.N1091.d012767 _


def d013983 (rho : ℝ) : Measure ℝ :=
  (_root_.GD.N0232.N0720.N1091.d012754 (1 / 2) (1 / 2)).map
    (_root_.GD.N0232.N0720.N1046.d013981 rho)

theorem d013984 {rho : ℝ} (hrho : 0 < rho) :
    0 < _root_.GD.N0232.N0720.N1046.d013980 rho := by
  unfold _root_.GD.N0232.N0720.N1046.d013980
  positivity

theorem d013985 {rho : ℝ} (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1046.d013980 rho < 1 := by
  unfold _root_.GD.N0232.N0720.N1046.d013980
  rw [div_lt_one (by positivity : 0 < 1 + rho)]
  linarith



theorem d013986
    {rho : ℝ} (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1091.d012762 (1 / 2) (1 / 2) (_root_.GD.N0232.N0720.N1046.d013980 rho) = rho := by
  unfold _root_.GD.N0232.N0720.N1091.d012762 _root_.GD.N0232.N0720.N1046.d013980
  field_simp [ne_of_gt hrho, ne_of_gt (show 0 < 1 + rho by positivity)]
  ring



theorem d013987
    {rho : ℝ} (hrho : 0 < rho) {q : ℝ × ℝ}
    (hq₁ : 0 < q.1) (hq₂ : 0 < q.2) :
    _root_.GD.N0232.N0720.N1046.d013981 rho q =
      rho * q.2 / (q.1 + rho * q.2) := by
  have hsum : 1 + rho ≠ 0 :=
    ne_of_gt (show 0 < 1 + rho by positivity)
  have hden : q.1 + rho * q.2 ≠ 0 := by positivity
  unfold _root_.GD.N0232.N0720.N1046.d013981 _root_.GD.N0232.N0720.N1091.d012759 _root_.GD.N0232.N0720.N1046.d013980
  field_simp [hsum, hden]
  ring


theorem d013988
    {rho : ℝ} (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1046.d013983 rho =
      (betaMeasure (1 / 2) (1 / 2)).map (_root_.GD.N0232.N0720.N1091.d012763 rho) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hp0 : 0 < _root_.GD.N0232.N0720.N1046.d013980 rho := _root_.GD.N0232.N0720.N1046.d013984 hrho
  have hp1 : _root_.GD.N0232.N0720.N1046.d013980 rho < 1 := _root_.GD.N0232.N0720.N1046.d013985 hrho
  unfold _root_.GD.N0232.N0720.N1046.d013983
  calc
    (_root_.GD.N0232.N0720.N1091.d012754 (1 / 2) (1 / 2)).map
          (_root_.GD.N0232.N0720.N1046.d013981 rho) =
        (_root_.GD.N0232.N0720.N1091.d012754 (1 / 2) (1 / 2)).map
          (_root_.GD.N0232.N0720.N1091.d012763
            (_root_.GD.N0232.N0720.N1091.d012762 (1 / 2) (1 / 2) (_root_.GD.N0232.N0720.N1046.d013980 rho)) ∘
              _root_.GD.N0232.N0720.N1091.d012760 (1 / 2) (1 / 2)) := by
      apply Measure.map_congr
      filter_upwards [_root_.GD.N0232.N0720.N1091.d012774 hhalf hhalf]
        with q hq
      exact _root_.GD.N0232.N0720.N1091.d012781
        hhalf hhalf hp0 hp1 hq.1 hq.2
    _ = ((_root_.GD.N0232.N0720.N1091.d012754 (1 / 2) (1 / 2)).map
          (_root_.GD.N0232.N0720.N1091.d012760 (1 / 2) (1 / 2))).map
            (_root_.GD.N0232.N0720.N1091.d012763
              (_root_.GD.N0232.N0720.N1091.d012762 (1 / 2) (1 / 2) (_root_.GD.N0232.N0720.N1046.d013980 rho))) := by
      exact (Measure.map_map
        (_root_.GD.N0232.N0720.N1091.d012771 _)
        (_root_.GD.N0232.N0720.N1091.d012770 (1 / 2) (1 / 2))).symm
    _ = (betaMeasure (1 / 2) (1 / 2)).map
          (_root_.GD.N0232.N0720.N1091.d012763
            (_root_.GD.N0232.N0720.N1091.d012762 (1 / 2) (1 / 2) (_root_.GD.N0232.N0720.N1046.d013980 rho))) := by
      rw [_root_.GD.N0232.N0720.N1504.d013979 hhalf hhalf]
    _ = (betaMeasure (1 / 2) (1 / 2)).map (_root_.GD.N0232.N0720.N1091.d012763 rho) := by
      rw [_root_.GD.N0232.N0720.N1046.d013986 hrho]




theorem d013989
    {rho₁ rho₂ u : ℝ} (hrho₁ : 0 < rho₁) (hrho : rho₁ < rho₂)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 rho₁ u < _root_.GD.N0232.N0720.N1091.d012763 rho₂ u := by
  have hrho₂ : 0 < rho₂ := lt_trans hrho₁ hrho
  have hden₁ := _root_.GD.N0232.N0720.N1091.d012779 hrho₁ hu.1 hu.2
  have hden₂ := _root_.GD.N0232.N0720.N1091.d012779 hrho₂ hu.1 hu.2
  unfold _root_.GD.N0232.N0720.N1091.d012763
  rw [div_lt_div_iff₀ hden₁ hden₂]
  have hgap : 0 < (rho₂ - rho₁) * u * (1 - u) :=
    mul_pos (mul_pos (sub_pos.mpr hrho) hu.1) (sub_pos.mpr hu.2)
  nlinarith




theorem d013990
    (rho : ℝ) (z : _root_.GD.N0124.d006387) :
    (_root_.GD.N0232.N0720.N1435.d013470 (_root_.GD.N0232.N0720.N1046.d013980 rho) z).1 =
      _root_.GD.N0232.N0720.N1046.d013981 rho (_root_.GD.N0232.N0720.N1091.d012794 z) := by
  unfold _root_.GD.N0232.N0720.N1435.d013470 _root_.GD.N0232.N0720.N1435.d013468
    _root_.GD.N0232.N0720.N1435.d013462 _root_.GD.N0232.N0720.N1435.d013457 _root_.GD.N0232.N0720.N1435.d013460
    _root_.GD.N0232.N0720.N1046.d013981 _root_.GD.N0232.N0720.N1091.d012759 _root_.GD.N0232.N0720.N1046.d013980 _root_.GD.N0232.N0720.N1091.d012794
  dsimp




theorem d013991
    {rho : ℝ} (hrho : 0 < rho) :
    (_root_.GD.N0232.N0720.N1436.d013289 2 2 (_root_.GD.N0232.N0720.N1046.d013980 rho)).map Prod.fst =
      _root_.GD.N0232.N0720.N1046.d013983 rho := by
  have hp0 : 0 < _root_.GD.N0232.N0720.N1046.d013980 rho := _root_.GD.N0232.N0720.N1046.d013984 hrho
  have hp1 : _root_.GD.N0232.N0720.N1046.d013980 rho < 1 := _root_.GD.N0232.N0720.N1046.d013985 hrho
  have hhalf : _root_.GD.N0232.N0720.N1436.d013207 2 = (1 / 2 : ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013207]
  have hhalf' : _root_.GD.N0232.N0720.N1436.d013208 2 = (1 / 2 : ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013208]
  rw [← _root_.GD.N0232.N0720.N1434.d013563
    (m := 2) (n := 2) (by norm_num) (by norm_num) hp0 hp1]
  rw [Measure.map_map measurable_fst
    (_root_.GD.N0232.N0720.N1435.d013471 (_root_.GD.N0232.N0720.N1046.d013980 rho))]
  calc
    (_root_.GD.N0125.d008852
          (_root_.GD.N0232.N0720.N1436.d013207 2) (_root_.GD.N0232.N0720.N1436.d013208 2)).map
        (Prod.fst ∘ _root_.GD.N0232.N0720.N1435.d013470 (_root_.GD.N0232.N0720.N1046.d013980 rho)) =
      (_root_.GD.N0125.d008852
          (_root_.GD.N0232.N0720.N1436.d013207 2) (_root_.GD.N0232.N0720.N1436.d013208 2)).map
        (_root_.GD.N0232.N0720.N1046.d013981 rho ∘ _root_.GD.N0232.N0720.N1091.d012794) := by
          apply Measure.map_congr
          filter_upwards with z
          exact _root_.GD.N0232.N0720.N1046.d013990
            rho z
    _ = ((_root_.GD.N0125.d008852
          (_root_.GD.N0232.N0720.N1436.d013207 2) (_root_.GD.N0232.N0720.N1436.d013208 2)).map
            _root_.GD.N0232.N0720.N1091.d012794).map (_root_.GD.N0232.N0720.N1046.d013981 rho) := by
          rw [Measure.map_map
            (_root_.GD.N0232.N0720.N1046.d013982 rho)
            _root_.GD.N0232.N0720.N1091.d012795]
    _ = _root_.GD.N0232.N0720.N1046.d013983 rho := by
          rw [hhalf, hhalf',
            _root_.GD.N0232.N0720.N1091.d012796 (by norm_num) (by norm_num)]
          rfl


def d013992 (rho w : ℝ) : ℝ :=
  rho * (1 - w) + w


def d013993 (rho w : ℝ) : ℝ :=
  1 / _root_.GD.N0232.N0720.N1046.d013992 rho w



def d013994 (rho w : ℝ) : ℝ :=
  if 0 < rho ∧ 0 < w ∧ w < 1 then
    Real.sqrt rho /
      (Real.pi * Real.sqrt (w * (1 - w))) * _root_.GD.N0232.N0720.N1046.d013993 rho w
  else 0

theorem d013995
    {rho w : ℝ} (hrho : 0 < rho) (hw0 : 0 < w) (hw1 : w < 1) :
    0 < _root_.GD.N0232.N0720.N1046.d013992 rho w := by
  unfold _root_.GD.N0232.N0720.N1046.d013992
  positivity

theorem d013996
    {rho w : ℝ} (hrho : 0 < rho) (hw0 : 0 < w) (hw1 : w < 1) :
    0 < _root_.GD.N0232.N0720.N1046.d013993 rho w := by
  unfold _root_.GD.N0232.N0720.N1046.d013993
  exact one_div_pos.mpr (_root_.GD.N0232.N0720.N1046.d013995 hrho hw0 hw1)

theorem d013997
    {rho w : ℝ} (hrho : 0 < rho) (hw0 : 0 < w) (hw1 : w < 1) :
    0 < _root_.GD.N0232.N0720.N1046.d013994 rho w := by
  rw [_root_.GD.N0232.N0720.N1046.d013994, if_pos ⟨hrho, hw0, hw1⟩]
  have hprod : 0 < w * (1 - w) := mul_pos hw0 (sub_pos.mpr hw1)
  exact mul_pos
    (div_pos (Real.sqrt_pos.2 hrho)
      (mul_pos Real.pi_pos (Real.sqrt_pos.2 hprod)))
    (_root_.GD.N0232.N0720.N1046.d013996 hrho hw0 hw1)









theorem d013998 :
    ProbabilityTheory.beta (1 / 2 : ℝ) (1 / 2) = Real.pi := by
  unfold ProbabilityTheory.beta
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsqrt : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    Real.Gamma_one_half_eq, Real.Gamma_one]
  field_simp [hpi, hsqrt]
  exact Real.sq_sqrt Real.pi_pos.le


theorem d013999
    {rho u : ℝ} (hrho : 0 < rho) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (_root_.GD.N0232.N0720.N1091.d012763 rho)
      (-rho / _root_.GD.N0232.N0720.N1046.d013992 rho u ^ 2) (Ioo (0 : ℝ) 1) u := by
  have hden : 0 < u + rho * (1 - u) :=
    add_pos hu.1 (mul_pos hrho (sub_pos.mpr hu.2))
  have hnum : HasDerivAt (fun x : ℝ => rho * (1 - x)) (-rho) u := by
    simpa using
      ((hasDerivAt_const u 1).sub (hasDerivAt_id u)).const_mul rho
  have hden' : HasDerivAt (fun x : ℝ => x + rho * (1 - x)) (1 - rho) u := by
    have hbase := (hasDerivAt_id u).add hnum
    have hev : (id + fun x : ℝ => rho * (1 - x)) =ᶠ[nhds u]
        (fun x : ℝ => x + rho * (1 - x)) := by
      filter_upwards with x
      rfl
    have h := hbase.congr_of_eventuallyEq hev.symm
    simpa only [sub_eq_add_neg] using h
  have hquot := hnum.div hden' hden.ne'
  have hsimp :
      ((-rho) * (u + rho * (1 - u)) -
          (rho * (1 - u)) * (1 - rho)) /
          (u + rho * (1 - u)) ^ 2 =
        -rho / _root_.GD.N0232.N0720.N1046.d013992 rho u ^ 2 := by
    unfold _root_.GD.N0232.N0720.N1046.d013992
    congr 1 <;> ring
  rw [hsimp] at hquot
  exact hquot.hasDerivWithinAt


theorem d014000
    {rho u : ℝ} (hrho : 0 < rho) (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 rho (_root_.GD.N0232.N0720.N1091.d012763 rho u) = u := by
  have hden : 0 < u + rho * (1 - u) :=
    add_pos hu.1 (mul_pos hrho (sub_pos.mpr hu.2))
  have hw := _root_.GD.N0232.N0720.N1091.d012780 hrho hu.1 hu.2
  have hdenw : 0 < _root_.GD.N0232.N0720.N1091.d012763 rho u + rho * (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) :=
    add_pos hw.1 (mul_pos hrho (sub_pos.mpr hw.2))
  unfold _root_.GD.N0232.N0720.N1091.d012763 at *
  field_simp [hden.ne', hdenw.ne']
  ring

theorem d014001 {rho : ℝ} (hrho : 0 < rho) :
    InjOn (_root_.GD.N0232.N0720.N1091.d012763 rho) (Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  calc
    u = _root_.GD.N0232.N0720.N1091.d012763 rho (_root_.GD.N0232.N0720.N1091.d012763 rho u) :=
      (_root_.GD.N0232.N0720.N1046.d014000 hrho hu).symm
    _ = _root_.GD.N0232.N0720.N1091.d012763 rho (_root_.GD.N0232.N0720.N1091.d012763 rho v) := by rw [huv]
    _ = v := _root_.GD.N0232.N0720.N1046.d014000 hrho hv

theorem d014002 {rho : ℝ} (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1091.d012763 rho '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro w ⟨u, hu, rfl⟩
    exact _root_.GD.N0232.N0720.N1091.d012780 hrho hu.1 hu.2
  · intro w hw
    refine ⟨_root_.GD.N0232.N0720.N1091.d012763 rho w, _root_.GD.N0232.N0720.N1091.d012780 hrho hw.1 hw.2, ?_⟩
    exact _root_.GD.N0232.N0720.N1046.d014000 hrho hw


theorem d014003
    {rho u : ℝ} (hrho : 0 < rho) (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1046.d013992 rho (_root_.GD.N0232.N0720.N1091.d012763 rho u) =
      rho / _root_.GD.N0232.N0720.N1046.d013992 rho u := by
  let D := _root_.GD.N0232.N0720.N1046.d013992 rho u
  have hD : 0 < D := _root_.GD.N0232.N0720.N1046.d013995 hrho hu.1 hu.2
  have hbeta : _root_.GD.N0232.N0720.N1091.d012763 rho u = rho * (1 - u) / D := by
    unfold _root_.GD.N0232.N0720.N1091.d012763 D _root_.GD.N0232.N0720.N1046.d013992
    congr 1
    ring
  have hbetaMul : _root_.GD.N0232.N0720.N1091.d012763 rho u * D = rho * (1 - u) := by
    rw [hbeta, div_mul_cancel₀ _ hD.ne']
  have honeMul : (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) * D = u := by
    calc
      (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) * D = D - _root_.GD.N0232.N0720.N1091.d012763 rho u * D := by ring
      _ = D - rho * (1 - u) := by rw [hbetaMul]
      _ = u := by unfold D _root_.GD.N0232.N0720.N1046.d013992; ring
  rw [eq_div_iff hD.ne']
  unfold _root_.GD.N0232.N0720.N1046.d013992
  calc
    (rho * (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) + _root_.GD.N0232.N0720.N1091.d012763 rho u) * D =
        rho * ((1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) * D) + _root_.GD.N0232.N0720.N1091.d012763 rho u * D := by ring
    _ = rho * u + rho * (1 - u) := by rw [honeMul, hbetaMul]
    _ = rho := by ring


theorem d014004
    {rho u : ℝ} (hrho : 0 < rho) (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 rho u * (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) =
      rho * (u * (1 - u)) / _root_.GD.N0232.N0720.N1046.d013992 rho u ^ 2 := by
  let D := _root_.GD.N0232.N0720.N1046.d013992 rho u
  have hD : 0 < D := _root_.GD.N0232.N0720.N1046.d013995 hrho hu.1 hu.2
  have hbeta : _root_.GD.N0232.N0720.N1091.d012763 rho u = rho * (1 - u) / D := by
    unfold _root_.GD.N0232.N0720.N1091.d012763 D _root_.GD.N0232.N0720.N1046.d013992
    congr 1
    ring
  have hbetaMul : _root_.GD.N0232.N0720.N1091.d012763 rho u * D = rho * (1 - u) := by
    rw [hbeta, div_mul_cancel₀ _ hD.ne']
  have honeMul : (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) * D = u := by
    calc
      (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) * D = D - _root_.GD.N0232.N0720.N1091.d012763 rho u * D := by ring
      _ = D - rho * (1 - u) := by rw [hbetaMul]
      _ = u := by unfold D _root_.GD.N0232.N0720.N1046.d013992; ring
  change _root_.GD.N0232.N0720.N1091.d012763 rho u * (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) =
    rho * (u * (1 - u)) / D ^ 2
  rw [eq_div_iff (pow_ne_zero 2 hD.ne')]
  calc
    _root_.GD.N0232.N0720.N1091.d012763 rho u * (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) * D ^ 2 =
        (_root_.GD.N0232.N0720.N1091.d012763 rho u * D) * ((1 - _root_.GD.N0232.N0720.N1091.d012763 rho u) * D) := by ring
    _ = (rho * (1 - u)) * u := by rw [hbetaMul, honeMul]
    _ = rho * (u * (1 - u)) := by ring

theorem d014005
    {rho u : ℝ} (hrho : 0 < rho) (hu : u ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt (_root_.GD.N0232.N0720.N1091.d012763 rho u * (1 - _root_.GD.N0232.N0720.N1091.d012763 rho u)) =
      Real.sqrt rho * Real.sqrt (u * (1 - u)) /
        _root_.GD.N0232.N0720.N1046.d013992 rho u := by
  have hden := _root_.GD.N0232.N0720.N1046.d013995 hrho hu.1 hu.2
  have hnum : 0 ≤ rho * (u * (1 - u)) :=
    mul_nonneg hrho.le (mul_nonneg hu.1.le (sub_pos.mpr hu.2).le)
  rw [_root_.GD.N0232.N0720.N1046.d014004 hrho hu,
    Real.sqrt_div hnum, Real.sqrt_mul hrho.le,
    Real.sqrt_sq hden.le]

theorem d014006
    {rho u : ℝ} (hrho : 0 < rho) (hu : u ∈ Ioo (0 : ℝ) 1) :
    |-rho / _root_.GD.N0232.N0720.N1046.d013992 rho u ^ 2| =
      rho / _root_.GD.N0232.N0720.N1046.d013992 rho u ^ 2 := by
  have hden := _root_.GD.N0232.N0720.N1046.d013995 hrho hu.1 hu.2
  rw [abs_div, abs_neg, abs_of_pos hrho, abs_pow, abs_of_pos hden]


theorem d014007
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal (1 / 2 : ℝ) (1 / 2) u =
      1 / (Real.pi * Real.sqrt (u * (1 - u))) := by
  have hu0 : 0 < u := hu.1
  have h1u : 0 < 1 - u := sub_pos.mpr hu.2
  rw [betaPDFReal, if_pos (by simpa only [mem_Ioo] using hu),
    _root_.GD.N0232.N0720.N1046.d013998]
  norm_num
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hu0.le h1u.le]
  rw [Real.rpow_neg hu0.le, Real.rpow_neg h1u.le]
  have hur : u ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  have h1ur : (1 - u) ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  field_simp [hur, h1ur, Real.pi_ne_zero]



theorem d014008
    {rho u : ℝ} (hrho : 0 < rho) (hu : u ∈ Ioo (0 : ℝ) 1) :
    |-rho / _root_.GD.N0232.N0720.N1046.d013992 rho u ^ 2| *
        _root_.GD.N0232.N0720.N1046.d013994 rho (_root_.GD.N0232.N0720.N1091.d012763 rho u) =
      betaPDFReal (1 / 2 : ℝ) (1 / 2) u := by
  have hw := _root_.GD.N0232.N0720.N1091.d012780 hrho hu.1 hu.2
  have hD := _root_.GD.N0232.N0720.N1046.d013995 hrho hu.1 hu.2
  have hprod : 0 < u * (1 - u) := mul_pos hu.1 (sub_pos.mpr hu.2)
  have hsqrtrho : Real.sqrt rho ≠ 0 := Real.sqrt_ne_zero'.mpr hrho
  have hsqrtprod : Real.sqrt (u * (1 - u)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hprod
  rw [_root_.GD.N0232.N0720.N1046.d014006 hrho hu,
    _root_.GD.N0232.N0720.N1046.d013994, if_pos ⟨hrho, hw.1, hw.2⟩,
    _root_.GD.N0232.N0720.N1046.d014005 hrho hu,
    _root_.GD.N0232.N0720.N1046.d013993, _root_.GD.N0232.N0720.N1046.d014003 hrho hu,
    _root_.GD.N0232.N0720.N1046.d014007 hu]
  field_simp [hrho.ne', hD.ne', hsqrtrho, hsqrtprod, Real.pi_ne_zero]

theorem d014009 (rho : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1046.d013994 rho) := by
  by_cases hrho : 0 < rho
  · unfold _root_.GD.N0232.N0720.N1046.d013994
    simp only [hrho, true_and]
    apply Measurable.ite
    · exact measurableSet_Ioo
    · unfold _root_.GD.N0232.N0720.N1046.d013993 _root_.GD.N0232.N0720.N1046.d013992
      fun_prop
    · fun_prop
  · unfold _root_.GD.N0232.N0720.N1046.d013994
    simp only [hrho, false_and, if_false]
    exact measurable_const


theorem d014010
    {rho u : ℝ} (hrho : 0 < rho) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal |-rho / _root_.GD.N0232.N0720.N1046.d013992 rho u ^ 2| *
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1046.d013994 rho (_root_.GD.N0232.N0720.N1091.d012763 rho u)) =
      betaPDF (1 / 2 : ℝ) (1 / 2) u := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _),
    _root_.GD.N0232.N0720.N1046.d014008 hrho hu]
  rfl


theorem d014011
    {rho : ℝ} (hrho : 0 < rho)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ w, f w ∂((betaMeasure (1 / 2) (1 / 2)).map (_root_.GD.N0232.N0720.N1091.d012763 rho)) =
      ∫⁻ w, ENNReal.ofReal (_root_.GD.N0232.N0720.N1046.d013994 rho w) * f w := by
  rw [MeasureTheory.lintegral_map hf (_root_.GD.N0232.N0720.N1091.d012771 rho)]
  rw [betaMeasure]
  change (∫⁻ u, f (_root_.GD.N0232.N0720.N1091.d012763 rho u) ∂volume.withDensity
      (fun u => ENNReal.ofReal (betaPDFReal (1 / 2 : ℝ) (1 / 2) u))) = _
  have hcomp : Measurable (fun u => f (_root_.GD.N0232.N0720.N1091.d012763 rho u)) :=
    hf.comp (_root_.GD.N0232.N0720.N1091.d012771 rho)
  rw [lintegral_withDensity_eq_lintegral_mul
    (g := fun u => f (_root_.GD.N0232.N0720.N1091.d012763 rho u)) volume
    ((measurable_betaPDFReal (1 / 2 : ℝ) (1 / 2)).ennreal_ofReal) hcomp]
  simp only [Pi.mul_apply]
  change (∫⁻ u, betaPDF (1 / 2 : ℝ) (1 / 2) u *
    f (_root_.GD.N0232.N0720.N1091.d012763 rho u)) = _
  have hsource :
      (∫⁻ u, betaPDF (1 / 2 : ℝ) (1 / 2) u * f (_root_.GD.N0232.N0720.N1091.d012763 rho u)) =
        ∫⁻ u in Ioo (0 : ℝ) 1,
          betaPDF (1 / 2 : ℝ) (1 / 2) u * f (_root_.GD.N0232.N0720.N1091.d012763 rho u) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · simp only [Set.indicator, hu, if_true]
    · have hout : ¬(0 < u ∧ u < 1) := by
        simpa only [Set.mem_Ioo] using hu
      simp [Set.indicator, hu, betaPDF, betaPDFReal, hout]
  rw [hsource]
  let g : ℝ → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1046.d013994 rho w) * f w
  have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Ioo (0 : ℝ) 1) (f := _root_.GD.N0232.N0720.N1091.d012763 rho)
    (f' := fun u => -rho / _root_.GD.N0232.N0720.N1046.d013992 rho u ^ 2)
    measurableSet_Ioo
    (fun u hu => _root_.GD.N0232.N0720.N1046.d013999 hrho hu)
    (_root_.GD.N0232.N0720.N1046.d014001 hrho) g
  rw [_root_.GD.N0232.N0720.N1046.d014002 hrho] at hcov
  have hsourceJac :
      (∫⁻ u in Ioo (0 : ℝ) 1,
          betaPDF (1 / 2 : ℝ) (1 / 2) u * f (_root_.GD.N0232.N0720.N1091.d012763 rho u)) =
        ∫⁻ u in Ioo (0 : ℝ) 1,
          ENNReal.ofReal |-rho / _root_.GD.N0232.N0720.N1046.d013992 rho u ^ 2| *
            g (_root_.GD.N0232.N0720.N1091.d012763 rho u) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro u hu
    dsimp only [g]
    rw [← mul_assoc,
      _root_.GD.N0232.N0720.N1046.d014010 hrho hu]
  rw [hsourceJac, ← hcov]
  have htarget :
      (∫⁻ w, ENNReal.ofReal (_root_.GD.N0232.N0720.N1046.d013994 rho w) * f w) =
        ∫⁻ w in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1046.d013994 rho w) * f w := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro w
    by_cases hw : w ∈ Ioo (0 : ℝ) 1
    · simp only [Set.indicator, hw, if_true]
    · have hout : ¬(0 < rho ∧ 0 < w ∧ w < 1) := by
        intro h
        exact hw ⟨h.2.1, h.2.2⟩
      simp [Set.indicator, hw, _root_.GD.N0232.N0720.N1046.d013994, hout]
  exact htarget.symm


theorem d014012
    {rho : ℝ} (hrho : 0 < rho) :
    (betaMeasure (1 / 2) (1 / 2)).map (_root_.GD.N0232.N0720.N1091.d012763 rho) =
      volume.withDensity
        (fun w => ENNReal.ofReal (_root_.GD.N0232.N0720.N1046.d013994 rho w)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [_root_.GD.N0232.N0720.N1046.d014011 hrho f hf,
    lintegral_withDensity_eq_lintegral_mul volume
      ((_root_.GD.N0232.N0720.N1046.d014009 rho).ennreal_ofReal) hf]
  simp only [Pi.mul_apply]




theorem d014013
    {rho : ℝ} (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1046.d013983 rho =
      volume.withDensity
        (fun w => ENNReal.ofReal (_root_.GD.N0232.N0720.N1046.d013994 rho w)) := by
  rw [_root_.GD.N0232.N0720.N1046.d013988 hrho,
    _root_.GD.N0232.N0720.N1046.d014012 hrho]



theorem d014014
    (rho₁ rho₂ w₁ w₂ : ℝ) :
    _root_.GD.N0232.N0720.N1046.d013992 rho₁ w₂ * _root_.GD.N0232.N0720.N1046.d013992 rho₂ w₁ -
        _root_.GD.N0232.N0720.N1046.d013992 rho₁ w₁ * _root_.GD.N0232.N0720.N1046.d013992 rho₂ w₂ =
      (rho₂ - rho₁) * (w₂ - w₁) := by
  unfold _root_.GD.N0232.N0720.N1046.d013992
  ring



theorem d014015
    {rho₁ rho₂ w₁ w₂ : ℝ}
    (hrho₁ : 0 < rho₁) (hrho : rho₁ < rho₂)
    (hw₁ : 0 < w₁) (hw : w₁ < w₂) (hw₂ : w₂ < 1) :
    _root_.GD.N0232.N0720.N1046.d013993 rho₁ w₂ * _root_.GD.N0232.N0720.N1046.d013993 rho₂ w₁ <
      _root_.GD.N0232.N0720.N1046.d013993 rho₁ w₁ * _root_.GD.N0232.N0720.N1046.d013993 rho₂ w₂ := by
  have hrho₂ : 0 < rho₂ := lt_trans hrho₁ hrho
  have hw₁one : w₁ < 1 := lt_trans hw hw₂
  have hw₂zero : 0 < w₂ := lt_trans hw₁ hw
  have h₁₁ := _root_.GD.N0232.N0720.N1046.d013995 hrho₁ hw₁ hw₁one
  have h₁₂ := _root_.GD.N0232.N0720.N1046.d013995 hrho₁ hw₂zero hw₂
  have h₂₁ := _root_.GD.N0232.N0720.N1046.d013995 hrho₂ hw₁ hw₁one
  have h₂₂ := _root_.GD.N0232.N0720.N1046.d013995 hrho₂ hw₂zero hw₂
  have hnum : 0 < (rho₂ - rho₁) * (w₂ - w₁) := by positivity
  have hdenOrder :
      _root_.GD.N0232.N0720.N1046.d013992 rho₁ w₁ * _root_.GD.N0232.N0720.N1046.d013992 rho₂ w₂ <
        _root_.GD.N0232.N0720.N1046.d013992 rho₁ w₂ * _root_.GD.N0232.N0720.N1046.d013992 rho₂ w₁ := by
    have hcross := _root_.GD.N0232.N0720.N1046.d014014 rho₁ rho₂ w₁ w₂
    nlinarith
  unfold _root_.GD.N0232.N0720.N1046.d013993
  simp only [div_eq_mul_inv, one_mul, ← mul_inv]
  simpa only [one_div] using
    (one_div_lt_one_div_of_lt (mul_pos h₁₁ h₂₂) hdenOrder)



theorem d014016
    {rho₁ rho₂ w₁ w₂ : ℝ}
    (hrho₁ : 0 < rho₁) (hrho : rho₁ < rho₂)
    (hw₁ : 0 < w₁) (hw : w₁ < w₂) (hw₂ : w₂ < 1) :
    _root_.GD.N0232.N0720.N1046.d013994 rho₁ w₂ *
        _root_.GD.N0232.N0720.N1046.d013994 rho₂ w₁ <
      _root_.GD.N0232.N0720.N1046.d013994 rho₁ w₁ *
        _root_.GD.N0232.N0720.N1046.d013994 rho₂ w₂ := by
  have hrho₂ : 0 < rho₂ := lt_trans hrho₁ hrho
  have hw₁one : w₁ < 1 := lt_trans hw hw₂
  have hw₂zero : 0 < w₂ := lt_trans hw₁ hw
  rw [_root_.GD.N0232.N0720.N1046.d013994, if_pos ⟨hrho₁, hw₂zero, hw₂⟩,
    _root_.GD.N0232.N0720.N1046.d013994, if_pos ⟨hrho₂, hw₁, hw₁one⟩,
    _root_.GD.N0232.N0720.N1046.d013994, if_pos ⟨hrho₁, hw₁, hw₁one⟩,
    _root_.GD.N0232.N0720.N1046.d013994, if_pos ⟨hrho₂, hw₂zero, hw₂⟩]
  let A₁ := Real.sqrt rho₁
  let A₂ := Real.sqrt rho₂
  let B₁ := Real.pi * Real.sqrt (w₁ * (1 - w₁))
  let B₂ := Real.pi * Real.sqrt (w₂ * (1 - w₂))
  have hA₁ : 0 < A₁ := Real.sqrt_pos.2 hrho₁
  have hA₂ : 0 < A₂ := Real.sqrt_pos.2 hrho₂
  have hB₁ : 0 < B₁ := by
    dsimp [B₁]
    positivity
  have hB₂ : 0 < B₂ := by
    dsimp [B₂]
    positivity
  have hcore := _root_.GD.N0232.N0720.N1046.d014015 hrho₁ hrho hw₁ hw hw₂
  dsimp [A₁, A₂, B₁, B₂] at *
  calc
    (Real.sqrt rho₁ /
          (Real.pi * Real.sqrt (w₂ * (1 - w₂))) *
          _root_.GD.N0232.N0720.N1046.d013993 rho₁ w₂) *
        (Real.sqrt rho₂ /
          (Real.pi * Real.sqrt (w₁ * (1 - w₁))) *
          _root_.GD.N0232.N0720.N1046.d013993 rho₂ w₁) =
      ((Real.sqrt rho₁ * Real.sqrt rho₂) /
        ((Real.pi * Real.sqrt (w₁ * (1 - w₁))) *
          (Real.pi * Real.sqrt (w₂ * (1 - w₂))))) *
        (_root_.GD.N0232.N0720.N1046.d013993 rho₁ w₂ * _root_.GD.N0232.N0720.N1046.d013993 rho₂ w₁) := by ring
    _ < ((Real.sqrt rho₁ * Real.sqrt rho₂) /
        ((Real.pi * Real.sqrt (w₁ * (1 - w₁))) *
          (Real.pi * Real.sqrt (w₂ * (1 - w₂))))) *
        (_root_.GD.N0232.N0720.N1046.d013993 rho₁ w₁ * _root_.GD.N0232.N0720.N1046.d013993 rho₂ w₂) := by
      exact mul_lt_mul_of_pos_left hcore (div_pos (mul_pos hA₁ hA₂)
        (mul_pos hB₁ hB₂))
    _ =
      (Real.sqrt rho₁ /
          (Real.pi * Real.sqrt (w₁ * (1 - w₁))) *
          _root_.GD.N0232.N0720.N1046.d013993 rho₁ w₁) *
        (Real.sqrt rho₂ /
          (Real.pi * Real.sqrt (w₂ * (1 - w₂))) *
          _root_.GD.N0232.N0720.N1046.d013993 rho₂ w₂) := by ring



theorem d014017
    {rho₁ rho₂ w₁ w₂ : ℝ}
    (hrho₁ : 0 < rho₁) (hrho : rho₁ < rho₂)
    (hw₁ : 0 < w₁) (hw : w₁ < w₂) (hw₂ : w₂ < 1) :
    _root_.GD.N0232.N0720.N1046.d013994 rho₂ w₁ /
        _root_.GD.N0232.N0720.N1046.d013994 rho₁ w₁ <
      _root_.GD.N0232.N0720.N1046.d013994 rho₂ w₂ /
        _root_.GD.N0232.N0720.N1046.d013994 rho₁ w₂ := by
  have hleft := _root_.GD.N0232.N0720.N1046.d013997
    (lt_trans hrho₁ hrho) hw₁ (lt_trans hw hw₂)
  have hright := _root_.GD.N0232.N0720.N1046.d013997 hrho₁
    (lt_trans hw₁ hw) hw₂
  rw [div_lt_div_iff₀
    (_root_.GD.N0232.N0720.N1046.d013997 hrho₁ hw₁ (lt_trans hw hw₂))
    hright]
  simpa [mul_comm] using
    _root_.GD.N0232.N0720.N1046.d014016 hrho₁ hrho hw₁ hw hw₂

















#print axioms _root_.GD.N0232.N0720.N1046.d013988
#print axioms _root_.GD.N0232.N0720.N1046.d013999
#print axioms _root_.GD.N0232.N0720.N1046.d014008
#print axioms _root_.GD.N0232.N0720.N1046.d014011
#print axioms _root_.GD.N0232.N0720.N1046.d014012
#print axioms _root_.GD.N0232.N0720.N1046.d014013
#print axioms _root_.GD.N0232.N0720.N1046.d013989
#print axioms _root_.GD.N0232.N0720.N1046.d013991
#print axioms _root_.GD.N0232.N0720.N1046.d014015
#print axioms _root_.GD.N0232.N0720.N1046.d014016
#print axioms _root_.GD.N0232.N0720.N1046.d014017

end

end GD.N0232.N0720.N1046
