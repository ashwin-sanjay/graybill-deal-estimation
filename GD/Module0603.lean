import Mathlib
import GD.Module0601
















open MeasureTheory Set

namespace GD.N0113
namespace d008651

noncomputable section

open _root_.GD.N0118
open _root_.GD.N0115
open _root_.GD.N0115.d006632
open _root_.GD.N0134
open _root_.GD.N0135
open _root_.GD.N0146
open _root_.GD.N0113
open _root_.GD.N0113.d008651
open _root_.GD.N0147

variable {rhoQ : (ℚ × ℚ) → ℝ}
variable {D : _root_.GD.N0134.d006518} {k : ℕ}

abbrev d008696
    (T : _root_.GD.N0113.d008651 rhoQ D k) :=
  Fin (_root_.GD.N0146.d008622 D k).length

def d008697
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ) : ℝ :=
  _root_.GD.N0118.d008583 ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
    (T.width : ℝ) x

def d008698
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) : ℝ × ℝ :=
  (((T.d008652 i).ell : ℝ), ((T.d008652 i).f : ℝ))

def d008699
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) : ℝ :=
  ((T.d008652 i).weight : ℝ)

def d008700
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) : ℝ :=
  (T.d008653 i : ℝ)

@[simp] theorem d008701
    (T : _root_.GD.N0113.d008651 rhoQ D k) (x : ℝ × ℝ) :
    T.d008659 x =
      ∑ i : _root_.GD.N0113.d008651.d008696 T,
        T.d008699 i * T.d008700 i * T.d008697 i x := by
  simp [_root_.GD.N0113.d008651.d008659, _root_.GD.N0113.d008651.d008699, _root_.GD.N0113.d008651.d008700,
    _root_.GD.N0113.d008651.d008697]



theorem d008702
    (T : _root_.GD.N0113.d008651 rhoQ D k) (i : _root_.GD.N0113.d008651.d008696 T) :
    (T.boxes i).lower ≤ (T.boxes i).upper := by
  have hc :
      _root_.GD.N0115.d006631 (T.boxes i).center (T.boxes i).width
        (T.boxes i).center := by
    simp [_root_.GD.N0115.d006631, (T.boxes i).width_pos]
  have hb := (T.boxes i).bounds (T.boxes i).center hc
  exact_mod_cast hb.1.trans hb.2

theorem d008703
    (T : _root_.GD.N0113.d008651 rhoQ D k) (i : _root_.GD.N0113.d008651.d008696 T) :
    0 < (T.boxes i).upper :=
  (T.boxes i).lower_pos.trans_le (T.d008702 i)

theorem d008704
    (T : _root_.GD.N0113.d008651 rhoQ D k) (i : _root_.GD.N0113.d008651.d008696 T) :
    0 ≤ T.d008654 i := by
  unfold _root_.GD.N0113.d008651.d008654 _root_.GD.N0115.d006629
  exact div_nonneg
    (sub_nonneg.mpr (T.d008702 i))
    (add_nonneg (T.d008703 i).le
      (T.boxes i).lower_pos.le)

theorem d008705
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho : ℝ × ℝ → ℝ)
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hLower : ((T.boxes i).lower : ℝ) ≤ rho x)
    (hUpper : rho x ≤ ((T.boxes i).upper : ℝ)) :
    |T.d008700 i * rho x - 1|
      ≤ (T.d008654 i : ℝ) := by
  exact _root_.GD.N0115.d006630
    (T.boxes i).lower_pos hLower hUpper









structure d008706
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho carrier power : ℝ × ℝ → ℝ)
    (gradientBound carrierBound inversePower : ℚ) where
  measurable_rho : Measurable rho
  measurable_carrier : Measurable carrier
  measurable_power : Measurable power
  tents_pairwise_disjoint :
    ∀ i j : _root_.GD.N0113.d008651.d008696 T, i ≠ j → ∀ x,
      T.d008697 i x * T.d008697 j x = 0
  density_bounds :
    ∀ i : _root_.GD.N0113.d008651.d008696 T, ∀ x,
      T.d008697 i x ≠ 0 →
        ((T.boxes i).lower : ℝ) ≤ rho x
          ∧ rho x ≤ ((T.boxes i).upper : ℝ)
  carrier_lipschitz :
    ∀ i : _root_.GD.N0113.d008651.d008696 T, ∀ x,
      T.d008697 i x ≠ 0 →
        |carrier x - carrier (T.d008698 i)|
          ≤ (gradientBound : ℝ) * (T.width : ℝ)
  carrier_abs :
    ∀ i : _root_.GD.N0113.d008651.d008696 T, ∀ x,
      T.d008697 i x ≠ 0 →
        |carrier x| ≤ (carrierBound : ℝ)
  power_bounds :
    ∀ i : _root_.GD.N0113.d008651.d008696 T, ∀ x,
      T.d008697 i x ≠ 0 →
        0 ≤ power x ∧ power x ≤ (inversePower : ℝ)

namespace d008706

theorem d008707
    {T : _root_.GD.N0113.d008651 rhoQ D k}
    {rho carrier power : ℝ × ℝ → ℝ}
    {gradientBound carrierBound inversePower : ℚ}
    (E : _root_.GD.N0113.d008651.d008706 T rho carrier power
      gradientBound carrierBound inversePower)
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hx : T.d008697 i x ≠ 0) :
    0 ≤ rho x := by
  have hlower : (0 : ℝ) ≤ ((T.boxes i).lower : ℝ) := by
    exact_mod_cast (T.boxes i).lower_pos.le
  exact hlower.trans (E.density_bounds i x hx).1

theorem d008708
    {T : _root_.GD.N0113.d008651 rhoQ D k}
    {rho carrier power : ℝ × ℝ → ℝ}
    {gradientBound carrierBound inversePower : ℚ}
    (E : _root_.GD.N0113.d008651.d008706 T rho carrier power
      gradientBound carrierBound inversePower)
    (hinverse : 0 ≤ inversePower)
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hx : T.d008697 i x ≠ 0) :
    0 ≤ rho x * power x
      ∧ rho x * power x
          ≤ ((T.boxes i).upper * inversePower : ℚ) := by
  have hρ := E.density_bounds i x hx
  have hρ0 := E.d008707 i x hx
  have hp := E.power_bounds i x hx
  constructor
  · exact mul_nonneg hρ0 hp.1
  · norm_num only [Rat.cast_mul]
    exact mul_le_mul hρ.2 hp.2 hp.1
      (by exact_mod_cast (T.d008703 i).le)

end d008706



theorem d008709
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) (f : ℝ × ℝ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hf : Measurable f)
    (hBound :
      ∀ x, T.d008697 i x ≠ 0 → |f x| ≤ B) :
    Integrable (fun x => T.d008697 i x * f x)
      (volume.prod volume) := by
  have htInt :
      Integrable (T.d008697 i) (volume.prod volume) := by
    exact _root_.GD.N0118.d008591 _ _ _
  have hmajor :
      Integrable (fun x => B * T.d008697 i x)
        (volume.prod volume) :=
    htInt.const_mul B
  refine hmajor.mono'
    (((_root_.GD.N0118.d008590 _ _ _).mul hf).aestronglyMeasurable) ?_
  filter_upwards [] with x
  by_cases ht : T.d008697 i x = 0
  · simp [ht]
  · have ht0 : 0 ≤ T.d008697 i x :=
      _root_.GD.N0147.d008605 _ _ _ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left (hBound x ht) ht0)

theorem d008710
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho power : ℝ × ℝ → ℝ)
    (i : _root_.GD.N0113.d008651.d008696 T) (upper : ℝ)
    (hupper : 0 ≤ upper)
    (hρ : Measurable rho) (hp : Measurable power)
    (hBound :
      ∀ x, T.d008697 i x ≠ 0 →
        0 ≤ rho x * power x ∧ rho x * power x ≤ upper) :
    Integrable
      (fun x =>
        (rho x * power x) *
          (T.d008699 i * T.d008700 i *
            T.d008697 i x) ^ 2)
      (volume.prod volume) := by
  have hsquare :
      Integrable (fun x => T.d008697 i x ^ 2)
        (volume.prod volume) := by
    exact _root_.GD.N0118.d008600 _ _ _
  let coeff := T.d008699 i * T.d008700 i
  have hmajor :
      Integrable
        (fun x => (upper * coeff ^ 2) * T.d008697 i x ^ 2)
        (volume.prod volume) :=
    hsquare.const_mul (upper * coeff ^ 2)
  have htentMeas :
      Measurable
        (fun x => (coeff * T.d008697 i x) ^ 2) := by
    exact
      ((_root_.GD.N0118.d008590
        ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
        (T.width : ℝ)).const_mul coeff).pow_const 2
  refine hmajor.mono'
    (((hρ.mul hp).mul htentMeas).aestronglyMeasurable) ?_
  filter_upwards [] with x
  by_cases ht : T.d008697 i x = 0
  · simp [ht, coeff]
  · have hd := hBound x ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hd.1 (sq_nonneg _))]
    change
      rho x * power x *
          (T.d008699 i * T.d008700 i *
            T.d008697 i x) ^ 2
        ≤ (upper * coeff ^ 2) * T.d008697 i x ^ 2
    have hsq :
        (T.d008699 i * T.d008700 i *
            T.d008697 i x) ^ 2 =
          coeff ^ 2 * T.d008697 i x ^ 2 := by
      dsimp [coeff]
      ring
    rw [hsq]
    nlinarith [sq_nonneg coeff, sq_nonneg (T.d008697 i x)]



def d008711
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (carrier : ℝ × ℝ → ℝ) : ℝ :=
  ∑ i : _root_.GD.N0113.d008651.d008696 T,
    T.d008699 i * carrier (T.d008698 i)

def d008712
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (carrier : ℝ × ℝ → ℝ) : ℝ :=
  ∑ i : _root_.GD.N0113.d008651.d008696 T,
    T.d008699 i *
      ∫ x, T.d008697 i x *
        (carrier x - carrier (T.d008698 i))
        ∂(volume.prod volume)

def d008713
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho carrier : ℝ × ℝ → ℝ) : ℝ :=
  ∑ i : _root_.GD.N0113.d008651.d008696 T,
    T.d008699 i *
      ∫ x, T.d008697 i x *
        ((T.d008700 i * rho x - 1) * carrier x)
        ∂(volume.prod volume)

def d008714
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho carrier : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x, rho x * T.d008659 x * carrier x
    ∂(volume.prod volume)

def d008715
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho power : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x, (rho x * power x) * T.d008659 x ^ 2
    ∂(volume.prod volume)

theorem d008716
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho carrier power : ℝ × ℝ → ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (hgradient : 0 ≤ gradientBound)
    (E : _root_.GD.N0113.d008651.d008706 T rho carrier power
      gradientBound carrierBound inversePower) :
    |T.d008712 carrier|
      ≤ (_root_.GD.N0113.d008668 T gradientBound : ℝ) := by
  have hw : (0 : ℝ) < (T.width : ℝ) := by
    exact_mod_cast T.width_pos
  have hB : (0 : ℝ) ≤ (gradientBound : ℝ) := by
    exact_mod_cast hgradient
  have hlocal :
      ∀ i : _root_.GD.N0113.d008651.d008696 T,
        |∫ x, T.d008697 i x *
            (carrier x - carrier (T.d008698 i))
            ∂(volume.prod volume)|
          ≤ (gradientBound : ℝ) * (T.width : ℝ) := by
    intro i
    exact _root_.GD.N0147.d008606
      ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
      (T.width : ℝ) (gradientBound : ℝ) carrier
      hw hB
      (T.d008709 i
        (fun x => carrier x - carrier (T.d008698 i))
        ((gradientBound : ℝ) * (T.width : ℝ))
        (mul_nonneg hB hw.le)
        (E.measurable_carrier.sub measurable_const)
        (E.carrier_lipschitz i))
      (E.carrier_lipschitz i)
  calc
    |T.d008712 carrier|
        ≤ ∑ i : _root_.GD.N0113.d008651.d008696 T,
            |T.d008699 i| *
              ((gradientBound : ℝ) * (T.width : ℝ)) := by
          apply _root_.GD.N0147.d008608 Finset.univ
            T.d008699
            (fun i =>
              ∫ x, T.d008697 i x *
                (carrier x - carrier (T.d008698 i))
                ∂(volume.prod volume))
            (fun _ => (gradientBound : ℝ) * (T.width : ℝ))
          intro i hi
          exact hlocal i
    _ = (_root_.GD.N0113.d008668 T gradientBound : ℝ) := by
      simp only [_root_.GD.N0113.d008668, _root_.GD.N0113.d008667, Rat.cast_mul,
        Rat.cast_sum, Rat.cast_abs]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [_root_.GD.N0113.d008651.d008699]
      ring

theorem d008717
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho carrier power : ℝ × ℝ → ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (hcarrier : 0 ≤ carrierBound)
    (E : _root_.GD.N0113.d008651.d008706 T rho carrier power
      gradientBound carrierBound inversePower) :
    |T.d008713 rho carrier|
      ≤ (_root_.GD.N0113.d008669 T carrierBound : ℝ) := by
  have hw : (0 : ℝ) < (T.width : ℝ) := by
    exact_mod_cast T.width_pos
  have hB : (0 : ℝ) ≤ (carrierBound : ℝ) := by
    exact_mod_cast hcarrier
  have hlocal :
      ∀ i : _root_.GD.N0113.d008651.d008696 T,
        |∫ x, T.d008697 i x *
            ((T.d008700 i * rho x - 1) * carrier x)
            ∂(volume.prod volume)|
          ≤ (T.d008654 i : ℝ) * (carrierBound : ℝ) := by
    intro i
    have hκ : (0 : ℝ) ≤ (T.d008654 i : ℝ) := by
      exact_mod_cast T.d008704 i
    exact _root_.GD.N0147.d008607
      ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
      (T.width : ℝ) (T.d008700 i)
      (T.d008654 i : ℝ) (carrierBound : ℝ)
      rho carrier hw hκ hB
      (T.d008709 i
        (fun x =>
          (T.d008700 i * rho x - 1) * carrier x)
        ((T.d008654 i : ℝ) * (carrierBound : ℝ))
        (mul_nonneg hκ hB)
        (((measurable_const.mul E.measurable_rho).sub
          measurable_const).mul E.measurable_carrier)
        (by
          intro x hx
          rw [abs_mul]
          exact mul_le_mul
            (T.d008705 rho i x
              (E.density_bounds i x hx).1
              (E.density_bounds i x hx).2)
            (E.carrier_abs i x hx) (abs_nonneg _)
            (by exact_mod_cast T.d008704 i)))
      (by
        intro x hx
        exact T.d008705 rho i x
          (E.density_bounds i x hx).1
          (E.density_bounds i x hx).2)
      (E.carrier_abs i)
  calc
    |T.d008713 rho carrier|
        ≤ ∑ i : _root_.GD.N0113.d008651.d008696 T,
            |T.d008699 i| *
              ((T.d008654 i : ℝ) * (carrierBound : ℝ)) := by
          apply _root_.GD.N0147.d008608 Finset.univ
            T.d008699
            (fun i =>
              ∫ x, T.d008697 i x *
                ((T.d008700 i * rho x - 1) * carrier x)
                ∂(volume.prod volume))
            (fun i =>
              (T.d008654 i : ℝ) * (carrierBound : ℝ))
          intro i hi
          exact hlocal i
    _ = (_root_.GD.N0113.d008669 T carrierBound : ℝ) := by
      simp only [_root_.GD.N0113.d008669, Rat.cast_sum, Rat.cast_mul,
        Rat.cast_abs]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [_root_.GD.N0113.d008651.d008699]
      ring

theorem d008718
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho carrier power : ℝ × ℝ → ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (hgradient : 0 ≤ gradientBound)
    (hcarrier : 0 ≤ carrierBound)
    (E : _root_.GD.N0113.d008651.d008706 T rho carrier power
      gradientBound carrierBound inversePower)
    (i : _root_.GD.N0113.d008651.d008696 T) :
    (∫ x,
        rho x *
          (T.d008699 i * T.d008700 i *
            T.d008697 i x) * carrier x
        ∂(volume.prod volume))
      =
      T.d008699 i * carrier (T.d008698 i)
        + T.d008699 i *
            (∫ x, T.d008697 i x *
              (carrier x - carrier (T.d008698 i))
              ∂(volume.prod volume))
        + T.d008699 i *
            (∫ x, T.d008697 i x *
              ((T.d008700 i * rho x - 1) * carrier x)
              ∂(volume.prod volume)) := by
  have hw : (0 : ℝ) < (T.width : ℝ) := by
    exact_mod_cast T.width_pos
  have hgradientR : (0 : ℝ) ≤ (gradientBound : ℝ) := by
    exact_mod_cast hgradient
  have hcarrierR : (0 : ℝ) ≤ (carrierBound : ℝ) := by
    exact_mod_cast hcarrier
  let base : ℝ × ℝ → ℝ :=
    fun x => T.d008697 i x * carrier (T.d008698 i)
  let smear : ℝ × ℝ → ℝ :=
    fun x => T.d008697 i x *
      (carrier x - carrier (T.d008698 i))
  let density : ℝ × ℝ → ℝ :=
    fun x => T.d008697 i x *
      ((T.d008700 i * rho x - 1) * carrier x)
  have hbase : Integrable base (volume.prod volume) := by
    exact (_root_.GD.N0118.d008591 _ _ _).mul_const _
  have hsmear : Integrable smear (volume.prod volume) := by
    exact T.d008709 i _ _
      (mul_nonneg hgradientR hw.le)
      (E.measurable_carrier.sub measurable_const)
      (E.carrier_lipschitz i)
  have hκ : (0 : ℝ) ≤ (T.d008654 i : ℝ) := by
    exact_mod_cast T.d008704 i
  have hdensity : Integrable density (volume.prod volume) := by
    exact T.d008709 i _ _
      (mul_nonneg hκ hcarrierR)
      (((measurable_const.mul E.measurable_rho).sub
        measurable_const).mul E.measurable_carrier)
      (by
        intro x hx
        rw [abs_mul]
        exact mul_le_mul
          (T.d008705 rho i x
            (E.density_bounds i x hx).1
            (E.density_bounds i x hx).2)
          (E.carrier_abs i x hx) (abs_nonneg _) hκ)
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => by
    change
      rho x *
          (T.d008699 i * T.d008700 i *
            T.d008697 i x) * carrier x
        =
      T.d008699 i * (base x + smear x + density x)
    dsimp [base, smear, density]
    ring))]
  rw [integral_const_mul]
  have hIntegral :
      (∫ x, base x + smear x + density x
          ∂(volume.prod volume)) =
        (∫ x, base x ∂(volume.prod volume))
          + (∫ x, smear x ∂(volume.prod volume))
          + (∫ x, density x ∂(volume.prod volume)) := by
    calc
      (∫ x, base x + smear x + density x
          ∂(volume.prod volume))
          =
        (∫ x, base x + smear x ∂(volume.prod volume))
          + ∫ x, density x ∂(volume.prod volume) :=
        integral_add (hbase.add hsmear) hdensity
      _ =
        (∫ x, base x ∂(volume.prod volume))
          + (∫ x, smear x ∂(volume.prod volume))
          + (∫ x, density x ∂(volume.prod volume)) := by
        rw [integral_add hbase hsmear]
  rw [hIntegral]
  have hbaseEval :
      (∫ x, base x ∂(volume.prod volume)) =
        carrier (T.d008698 i) := by
    dsimp [base]
    rw [integral_mul_const, show
      (∫ x, T.d008697 i x ∂(volume.prod volume)) = 1 by
        exact _root_.GD.N0118.d008601 _ _ _ hw, one_mul]
  rw [hbaseEval]
  change
    T.d008699 i *
        (carrier (T.d008698 i)
          + (∫ x, smear x ∂(volume.prod volume))
          + (∫ x, density x ∂(volume.prod volume)))
      =
    T.d008699 i * carrier (T.d008698 i)
      + T.d008699 i *
          (∫ x, smear x ∂(volume.prod volume))
      + T.d008699 i *
          (∫ x, density x ∂(volume.prod volume))
  ring

theorem d008719
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho carrier power : ℝ × ℝ → ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (hgradient : 0 ≤ gradientBound)
    (hcarrier : 0 ≤ carrierBound)
    (E : _root_.GD.N0113.d008651.d008706 T rho carrier power
      gradientBound carrierBound inversePower) :
    T.d008714 rho carrier =
      T.d008711 carrier + T.d008712 carrier
        + T.d008713 rho carrier := by
  have hatomInt :
      ∀ i : _root_.GD.N0113.d008651.d008696 T,
        Integrable
          (fun x =>
            rho x *
              (T.d008699 i * T.d008700 i *
                T.d008697 i x) * carrier x)
          (volume.prod volume) := by
    intro i
    let base : ℝ × ℝ → ℝ :=
      fun x => (T.d008699 i * carrier (T.d008698 i)) *
        T.d008697 i x
    let smear : ℝ × ℝ → ℝ :=
      fun x => T.d008699 i * (T.d008697 i x *
        (carrier x - carrier (T.d008698 i)))
    let density : ℝ × ℝ → ℝ :=
      fun x => T.d008699 i * (T.d008697 i x *
        ((T.d008700 i * rho x - 1) * carrier x))
    have hb : Integrable base (volume.prod volume) := by
      simpa [base, _root_.GD.N0113.d008651.d008697] using
        (_root_.GD.N0118.d008591
          ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
          (T.width : ℝ)).const_mul
            (T.d008699 i * carrier (T.d008698 i))
    have hgR : (0 : ℝ) ≤ (gradientBound : ℝ) := by
      exact_mod_cast hgradient
    have hwR : (0 : ℝ) ≤ (T.width : ℝ) := by
      exact_mod_cast T.width_pos.le
    have hs0 :
        Integrable
          (fun x => T.d008697 i x *
            (carrier x - carrier (T.d008698 i)))
          (volume.prod volume) :=
      T.d008709 i _ _
        (mul_nonneg hgR hwR)
        (E.measurable_carrier.sub measurable_const)
        (E.carrier_lipschitz i)
    have hs : Integrable smear (volume.prod volume) := by
      simpa [smear] using
        hs0.const_mul (T.d008699 i)
    have hκ : (0 : ℝ) ≤ (T.d008654 i : ℝ) := by
      exact_mod_cast T.d008704 i
    have hd0 :
        Integrable
          (fun x => T.d008697 i x *
            ((T.d008700 i * rho x - 1) * carrier x))
          (volume.prod volume) :=
      T.d008709 i _ _
        (mul_nonneg hκ
          (show (0 : ℝ) ≤ (carrierBound : ℝ) by
            exact_mod_cast hcarrier))
        (((measurable_const.mul E.measurable_rho).sub
          measurable_const).mul E.measurable_carrier)
        (by
          intro x hx
          rw [abs_mul]
          exact mul_le_mul
            (T.d008705 rho i x
              (E.density_bounds i x hx).1
              (E.density_bounds i x hx).2)
            (E.carrier_abs i x hx) (abs_nonneg _) hκ)
    have hd : Integrable density (volume.prod volume) := by
      simpa [density] using
        hd0.const_mul (T.d008699 i)
    have hsum : Integrable (fun x => base x + smear x + density x)
        (volume.prod volume) :=
      (hb.add hs).add hd
    apply hsum.congr
    filter_upwards [] with x
    dsimp [base, smear, density]
    ring
  have hrewrite :
      (fun x => rho x * T.d008659 x * carrier x) =
        fun x => ∑ i : _root_.GD.N0113.d008651.d008696 T,
          rho x *
            (T.d008699 i * T.d008700 i *
              T.d008697 i x) * carrier x := by
    funext x
    rw [T.d008701, Finset.mul_sum,
      Finset.sum_mul]
  rw [_root_.GD.N0113.d008651.d008714, hrewrite,
    integral_finset_sum Finset.univ (fun i _ => hatomInt i)]
  simp_rw [T.d008718 rho carrier power
    gradientBound carrierBound inversePower hgradient hcarrier E]
  simp only [_root_.GD.N0113.d008651.d008711, _root_.GD.N0113.d008651.d008712, _root_.GD.N0113.d008651.d008713,
    Finset.sum_add_distrib]

theorem d008720
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho carrier power : ℝ × ℝ → ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (hinverse : 0 ≤ inversePower)
    (E : _root_.GD.N0113.d008651.d008706 T rho carrier power
      gradientBound carrierBound inversePower) :
    T.d008715 rho power
      ≤ (_root_.GD.N0113.d008670 T inversePower : ℝ) := by
  have hw : (0 : ℝ) < (T.width : ℝ) := by
    exact_mod_cast T.width_pos
  have h :=
    _root_.GD.N0147.d008612
      (s := (Finset.univ : Finset (_root_.GD.N0113.d008651.d008696 T)))
      (center₁ := fun i => ((T.d008652 i).ell : ℝ))
      (center₂ := fun i => ((T.d008652 i).f : ℝ))
      (coeff := fun i => T.d008699 i * T.d008700 i)
      (upper := fun i =>
        (((T.boxes i).upper * inversePower : ℚ) : ℝ))
      (w := (T.width : ℝ))
      (density := fun x => rho x * power x)
      hw
      (by
        intro i hi
        exact_mod_cast
          (mul_nonneg (T.d008703 i).le hinverse))
      (by
        intro i hi j hj hij x
        have ht := E.tents_pairwise_disjoint i j hij x
        calc
          ((T.d008699 i * T.d008700 i) *
              T.d008697 i x) *
              ((T.d008699 j * T.d008700 j) *
                T.d008697 j x)
              =
            ((T.d008699 i * T.d008700 i) *
              (T.d008699 j * T.d008700 j)) *
              (T.d008697 i x * T.d008697 j x) := by ring
          _ = 0 := by rw [ht, mul_zero])
      (by
        intro i hi
        exact T.d008710 rho power i
          (((T.boxes i).upper * inversePower : ℚ) : ℝ)
          (by exact_mod_cast
            (mul_nonneg (T.d008703 i).le hinverse))
          E.measurable_rho E.measurable_power
          (E.d008708 hinverse i))
      (by
        intro i hi x hx
        exact E.d008708 hinverse i x hx)
  rw [_root_.GD.N0113.d008651.d008715]
  have hleft :
      (fun x =>
        rho x * power x * T.d008659 x ^ 2) =
      (fun x =>
        rho x * power x *
          (∑ i : _root_.GD.N0113.d008651.d008696 T,
            (T.d008699 i * T.d008700 i) *
              T.d008697 i x) ^ 2) := by
    funext x
    rw [T.d008701]
  rw [hleft]
  calc
    _ ≤ ∑ i : _root_.GD.N0113.d008651.d008696 T,
        4 / (9 * (T.width : ℝ) ^ 2) *
          (T.d008699 i * T.d008700 i) ^ 2 *
          (((T.boxes i).upper * inversePower : ℚ) : ℝ) := h
    _ = (_root_.GD.N0113.d008670 T inversePower : ℝ) := by
      simp only [_root_.GD.N0113.d008670, Rat.cast_mul, Rat.cast_sum,
        Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [_root_.GD.N0113.d008651.d008699, _root_.GD.N0113.d008651.d008700]
      ring

theorem d008721
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (x : ℝ × ℝ) (hx : T.d008659 x ≠ 0) :
    ∃ i : _root_.GD.N0113.d008651.d008696 T, T.d008697 i x ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hx
  rw [T.d008701]
  apply Finset.sum_eq_zero
  intro i hi
  simp [h i]

theorem d008722
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (rho carrier power : ℝ × ℝ → ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (E : _root_.GD.N0113.d008651.d008706 T rho carrier power
      gradientBound carrierBound inversePower) :
    0 ≤ T.d008715 rho power := by
  rw [_root_.GD.N0113.d008651.d008715]
  apply integral_nonneg
  intro x
  change 0 ≤ rho x * power x * T.d008659 x ^ 2
  by_cases hx : T.d008659 x = 0
  · rw [show T.d008659 x = 0 from hx]
    simp
  · obtain ⟨i, hi⟩ := T.d008721 x hx
    exact mul_nonneg
      (mul_nonneg (E.d008707 i x hi)
        (E.power_bounds i x hi).1)
      (sq_nonneg _)










structure d008723
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) where
  emitted : _root_.GD.N0113.d008682 m n hm hn
  rho : ℝ × ℝ → ℝ
  carrier : ℝ × ℝ → ℝ
  power : ℝ × ℝ → ℝ
  envelope :
    _root_.GD.N0113.d008651.d008706 emitted.table rho carrier power
      emitted.ledger.gradientBound
      emitted.ledger.carrierBound
      emitted.ledger.inversePower
  atomic_margin :
    emitted.table.d008711 carrier
      ≤ -(3 * (emitted.ledger.C : ℝ) / 4)

namespace d008723

def d008724
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (A : _root_.GD.N0113.d008651.d008723 m n hm hn) :
    _root_.GD.N0146.d008638 m n hm hn := by
  let M : ℚ :=
    _root_.GD.N0113.d008670 A.emitted.table A.emitted.ledger.inversePower
  refine
    { seed := A.emitted.header.d008647
      geometry := A.emitted.table.d008657
      centers_match := rfl
      C := A.emitted.ledger.C
      M := M
      C_pos := A.emitted.ledger.C_pos
      M_pos := A.emitted.ledger.energy_ceiling_pos
      atomic := A.emitted.table.d008711 A.carrier
      smear := A.emitted.table.d008712 A.carrier
      densityError :=
        A.emitted.table.d008713 A.rho A.carrier
      energy := A.emitted.table.d008715 A.rho A.power
      trace := A.emitted.table.d008714 A.rho A.carrier
      trace_eq := ?_
      atomic_margin := ?_
      smearing_bound := ?_
      density_bound := ?_
      energy_nonneg := ?_
      energy_ceiling := ?_ }
  · exact A.emitted.table.d008719
      A.rho A.carrier A.power
      A.emitted.ledger.gradientBound
      A.emitted.ledger.carrierBound
      A.emitted.ledger.inversePower
      A.emitted.ledger.gradientBound_nonneg
      A.emitted.ledger.carrierBound_nonneg A.envelope
  · exact A.atomic_margin
  · exact
      (A.emitted.table.d008716
        A.rho A.carrier A.power
        A.emitted.ledger.gradientBound
        A.emitted.ledger.carrierBound
        A.emitted.ledger.inversePower
        A.emitted.ledger.gradientBound_nonneg A.envelope).trans
        (by exact_mod_cast A.emitted.ledger.smear_budget)
  · exact
      (A.emitted.table.d008717
        A.rho A.carrier A.power
        A.emitted.ledger.gradientBound
        A.emitted.ledger.carrierBound
        A.emitted.ledger.inversePower
        A.emitted.ledger.carrierBound_nonneg A.envelope).trans
        (by exact_mod_cast A.emitted.ledger.density_budget)
  · exact A.emitted.table.d008722
      A.rho A.carrier A.power
      A.emitted.ledger.gradientBound
      A.emitted.ledger.carrierBound
      A.emitted.ledger.inversePower A.envelope
  · exact A.emitted.table.d008720
      A.rho A.carrier A.power
      A.emitted.ledger.gradientBound
      A.emitted.ledger.carrierBound
      A.emitted.ledger.inversePower
      A.emitted.ledger.inversePower_pos.le A.envelope

@[simp] theorem d008725
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (A : _root_.GD.N0113.d008651.d008723 m n hm hn) :
    A.d008724.trace =
      A.emitted.table.d008714 A.rho A.carrier := rfl

@[simp] theorem d008726
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (A : _root_.GD.N0113.d008651.d008723 m n hm hn) :
    A.d008724.energy =
      A.emitted.table.d008715 A.rho A.power := rfl






theorem d008727
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (A : _root_.GD.N0113.d008651.d008723 m n hm hn) :
    let C := A.d008724
    C.trace = A.emitted.table.d008714 A.rho A.carrier
      ∧ C.energy = A.emitted.table.d008715 A.rho A.power
      ∧ C.trace ≤ -((A.emitted.ledger.C : ℝ) / 2)
      ∧ 0 < C.d008640
      ∧ C.d008640 =
          (A.emitted.ledger.C / 2) /
            _root_.GD.N0113.d008670 A.emitted.table
              A.emitted.ledger.inversePower
      ∧ 2 * (C.d008640 : ℝ) * C.trace
          + (C.d008640 : ℝ) ^ 2 * C.energy
            ≤ -((((A.emitted.ledger.C / 2 : ℚ) : ℝ) ^ 2) /
              (_root_.GD.N0113.d008670 A.emitted.table
                A.emitted.ledger.inversePower : ℝ))
      ∧ 2 * (C.d008640 : ℝ) * C.trace
          + (C.d008640 : ℝ) ^ 2 * C.energy < 0 := by
  dsimp
  let C := A.d008724
  have hclose :=
    _root_.GD.N0146.d008645
      m n hm hn C
  exact ⟨rfl, rfl, hclose.2.2.2.1, hclose.2.2.2.2.1,
    rfl, hclose.2.2.2.2.2.1, hclose.2.2.2.2.2.2⟩

end d008723

end

end d008651
end GD.N0113
