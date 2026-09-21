import Mathlib
import GD.Module0428




























open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0144

noncomputable section


def d006699 (v₁ v₂ : ℝ) : ℝ := v₂ / (v₁ + v₂)


def d006700 (xbar ybar : ℝ) : ℝ := xbar - ybar


def d006701 (l xbar ybar : ℝ) : ℝ :=
  ybar + l * _root_.GD.N0144.d006700 xbar ybar



def d006702 (m n sx2 sy2 : ℝ) : ℝ :=
  (m / sx2) / (m / sx2 + n / sy2)


def d006703 (m n sx2 sy2 xbar ybar : ℝ) : ℝ :=
  ((m / sx2) * xbar + (n / sy2) * ybar)
    / (m / sx2 + n / sy2)


def d006704 (v₁ v₂ xbar ybar : ℝ) : ℝ :=
  _root_.GD.N0144.d006701 (_root_.GD.N0144.d006699 v₁ v₂) xbar ybar


def d006705 (v₁ v₂ μ xbar ybar : ℝ) : ℝ :=
  _root_.GD.N0144.d006704 v₁ v₂ xbar ybar - μ

theorem d006706
    {v₁ v₂ : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    0 < _root_.GD.N0144.d006699 v₁ v₂ := by
  exact div_pos hv₂ (add_pos hv₁ hv₂)

theorem d006707
    {v₁ v₂ : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    _root_.GD.N0144.d006699 v₁ v₂ < 1 := by
  unfold _root_.GD.N0144.d006699
  exact (div_lt_one (add_pos hv₁ hv₂)).2 (by linarith)

theorem d006708
    {v₁ v₂ : ℝ} (hs : v₁ + v₂ ≠ 0) :
    1 - _root_.GD.N0144.d006699 v₁ v₂ = v₁ / (v₁ + v₂) := by
  unfold _root_.GD.N0144.d006699
  field_simp [hs] <;> ring



theorem d006709
    {m n sx2 sy2 xbar ybar : ℝ}
    (hden : m / sx2 + n / sy2 ≠ 0) :
    _root_.GD.N0144.d006703 m n sx2 sy2 xbar ybar =
      _root_.GD.N0144.d006701 (_root_.GD.N0144.d006702 m n sx2 sy2) xbar ybar := by
  unfold _root_.GD.N0144.d006703 _root_.GD.N0144.d006701 _root_.GD.N0144.d006702 _root_.GD.N0144.d006700
  field_simp [hden]
  ring


theorem d006710
    {v₁ v₂ xbar ybar : ℝ} (hs : v₁ + v₂ ≠ 0) :
    _root_.GD.N0144.d006704 v₁ v₂ xbar ybar =
      (v₂ * xbar + v₁ * ybar) / (v₁ + v₂) := by
  unfold _root_.GD.N0144.d006704 _root_.GD.N0144.d006701 _root_.GD.N0144.d006700 _root_.GD.N0144.d006699
  field_simp [hs]
  ring



theorem d006711
    {v₁ v₂ : ℝ} (hs : v₁ + v₂ ≠ 0) :
    _root_.GD.N0144.d006699 v₁ v₂ * v₁
        - (1 - _root_.GD.N0144.d006699 v₁ v₂) * v₂ = 0 := by
  rw [_root_.GD.N0144.d006708 hs]
  unfold _root_.GD.N0144.d006699
  field_simp [hs]
  ring



theorem d006712
    {v₁ v₂ : ℝ} (hs : v₁ + v₂ ≠ 0) :
    _root_.GD.N0144.d006699 v₁ v₂ ^ 2 * v₁
        + (1 - _root_.GD.N0144.d006699 v₁ v₂) ^ 2 * v₂ =
      v₁ * v₂ / (v₁ + v₂) := by
  rw [_root_.GD.N0144.d006708 hs]
  unfold _root_.GD.N0144.d006699
  field_simp [hs]
  ring




theorem d006713
    (v₁ v₂ μ xbar ybar l : ℝ) :
    _root_.GD.N0144.d006701 l xbar ybar - μ =
      _root_.GD.N0144.d006705 v₁ v₂ μ xbar ybar
        + _root_.GD.N0144.d006700 xbar ybar * (l - _root_.GD.N0144.d006699 v₁ v₂) := by
  simp only [_root_.GD.N0144.d006701, _root_.GD.N0144.d006705, _root_.GD.N0144.d006704]
  ring



theorem d006714
    {m n sx2 sy2 v₁ v₂ μ xbar ybar : ℝ}
    (hden : m / sx2 + n / sy2 ≠ 0) :
    _root_.GD.N0144.d006703 m n sx2 sy2 xbar ybar - μ =
      _root_.GD.N0144.d006705 v₁ v₂ μ xbar ybar
        + _root_.GD.N0144.d006700 xbar ybar
            * (_root_.GD.N0144.d006702 m n sx2 sy2 - _root_.GD.N0144.d006699 v₁ v₂) := by
  rw [_root_.GD.N0144.d006709 hden]
  exact _root_.GD.N0144.d006713
    v₁ v₂ μ xbar ybar (_root_.GD.N0144.d006702 m n sx2 sy2)



theorem d006715
    (v₁ v₂ μ xbar ybar l ε q : ℝ) :
    _root_.GD.N0144.d006701 l xbar ybar + ε * _root_.GD.N0144.d006700 xbar ybar * q - μ =
      _root_.GD.N0144.d006705 v₁ v₂ μ xbar ybar
        + _root_.GD.N0144.d006700 xbar ybar * (l - _root_.GD.N0144.d006699 v₁ v₂)
        + ε * _root_.GD.N0144.d006700 xbar ybar * q := by
  calc
    _root_.GD.N0144.d006701 l xbar ybar + ε * _root_.GD.N0144.d006700 xbar ybar * q - μ =
        (_root_.GD.N0144.d006701 l xbar ybar - μ)
          + ε * _root_.GD.N0144.d006700 xbar ybar * q := by ring
    _ = _root_.GD.N0144.d006705 v₁ v₂ μ xbar ybar
          + _root_.GD.N0144.d006700 xbar ybar * (l - _root_.GD.N0144.d006699 v₁ v₂)
          + ε * _root_.GD.N0144.d006700 xbar ybar * q := by
      rw [_root_.GD.N0144.d006713]


theorem d006716
    {v₁ v₂ μ xbar ybar : ℝ} (hs : v₁ + v₂ ≠ 0) :
    xbar - μ =
      _root_.GD.N0144.d006705 v₁ v₂ μ xbar ybar
        + (v₁ / (v₁ + v₂)) * _root_.GD.N0144.d006700 xbar ybar := by
  unfold _root_.GD.N0144.d006705 _root_.GD.N0144.d006704 _root_.GD.N0144.d006701 _root_.GD.N0144.d006700 _root_.GD.N0144.d006699
  field_simp [hs]
  ring


theorem d006717
    {v₁ v₂ μ xbar ybar : ℝ} (hs : v₁ + v₂ ≠ 0) :
    ybar - μ =
      _root_.GD.N0144.d006705 v₁ v₂ μ xbar ybar
        - (v₂ / (v₁ + v₂)) * _root_.GD.N0144.d006700 xbar ybar := by
  unfold _root_.GD.N0144.d006705 _root_.GD.N0144.d006704 _root_.GD.N0144.d006701 _root_.GD.N0144.d006700 _root_.GD.N0144.d006699
  field_simp [hs]
  ring



theorem d006718
    {v₁ v₂ : ℝ} (hs : v₁ + v₂ ≠ 0) :
    _root_.GD.N0144.d006699 v₁ v₂ * (-1)
        - (1 - _root_.GD.N0144.d006699 v₁ v₂) * 1 = -1 := by
  rw [_root_.GD.N0144.d006708 hs]
  unfold _root_.GD.N0144.d006699
  field_simp [hs] <;> ring



theorem d006719
    {v₁ v₂ μ xbar ybar : ℝ} (hs : v₁ + v₂ ≠ 0) :
    _root_.GD.N0144.d006705 v₁ v₂ μ xbar ybar * _root_.GD.N0144.d006700 xbar ybar =
      (v₂ / (v₁ + v₂)) * (xbar - μ) ^ 2
        - (v₁ / (v₁ + v₂)) * (ybar - μ) ^ 2
        + ((v₁ - v₂) / (v₁ + v₂))
            * ((xbar - μ) * (ybar - μ)) := by
  unfold _root_.GD.N0144.d006705 _root_.GD.N0144.d006704 _root_.GD.N0144.d006701 _root_.GD.N0144.d006700 _root_.GD.N0144.d006699
  field_simp [hs]
  ring

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]




theorem d006720
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {v₁ v₂ : ℝ}
    (hs : v₁ + v₂ ≠ 0)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P)
    (hXY : Integrable (fun ω => X ω * Y ω) P)
    (hEX2 : ∫ ω, X ω ^ 2 ∂P = v₁)
    (hEY2 : ∫ ω, Y ω ^ 2 ∂P = v₂)
    (hEXY : ∫ ω, X ω * Y ω ∂P = 0) :
    ∫ ω,
        ((v₂ * X ω + v₁ * Y ω) / (v₁ + v₂))
          * (X ω - Y ω) ∂P = 0 := by
  have hpw :
      (fun ω =>
          ((v₂ * X ω + v₁ * Y ω) / (v₁ + v₂))
            * (X ω - Y ω)) =
        (fun ω => (v₂ / (v₁ + v₂)) * X ω ^ 2)
          + (fun ω => -(v₁ / (v₁ + v₂)) * Y ω ^ 2)
          + (fun ω =>
              ((v₁ - v₂) / (v₁ + v₂)) * (X ω * Y ω)) := by
    funext ω
    simp only [Pi.add_apply]
    field_simp [hs]
    ring
  rw [hpw]
  rw [integral_add'
      ((hX2.const_mul (v₂ / (v₁ + v₂))).add
        (hY2.const_mul (-(v₁ / (v₁ + v₂)))))
      (hXY.const_mul ((v₁ - v₂) / (v₁ + v₂)))]
  rw [integral_add'
      (hX2.const_mul (v₂ / (v₁ + v₂)))
      (hY2.const_mul (-(v₁ / (v₁ + v₂))))]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    hEX2, hEY2, hEXY]
  field_simp [hs]
  ring


def d006721
    (D : Ω → ℝ) (Sobs : Ω → S) (q : ℝ × S → ℝ) : Ω → ℝ :=
  fun ω => D ω * q (D ω, Sobs ω)



theorem d006722
    {P : Measure Ω}
    {U D : Ω → ℝ} {Sobs : Ω → S} {q : ℝ × S → ℝ}
    (hIndep : IndepFun U (fun ω => (D ω, Sobs ω)) P)
    (hq : Measurable q) :
    IndepFun U (_root_.GD.N0144.d006721 D Sobs q) P := by
  have hmap : Measurable (fun p : ℝ × S => p.1 * q p) :=
    measurable_fst.mul hq
  have h := hIndep.comp measurable_id hmap
  change
    IndepFun U (fun ω => D ω * q (D ω, Sobs ω)) P
  convert h using 1 <;> rfl








theorem d006723
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D L : Ω → ℝ} {Sobs : Ω → S} {q : ℝ × S → ℝ}
    {e ε : ℝ}
    (hq : Measurable q)
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun ω => D ω * (L ω - e)) 2 P)
    (hCarrier : MemLp (_root_.GD.N0144.d006721 D Sobs q) 2 P)
    (hIndep : IndepFun U (fun ω => (D ω, Sobs ω)) P)
    (hCentered : ∫ ω, U ω ∂P = 0) :
    _root_.GD.N0141.d006684 P
          (fun ω =>
            _root_.GD.N0141.d006685 U D L e ω
              + ε * _root_.GD.N0144.d006721 D Sobs q ω)
        - _root_.GD.N0141.d006684 P
          (_root_.GD.N0141.d006685 U D L e) =
      2 * ε * _root_.GD.N0141.d006687 P D L
          (fun ω => q (D ω, Sobs ω)) e
        + ε ^ 2 * _root_.GD.N0141.d006688 P D
          (fun ω => q (D ω, Sobs ω)) := by
  have hIndepCarrier :
      IndepFun U (_root_.GD.N0144.d006721 D Sobs q) P :=
    _root_.GD.N0144.d006722 hIndep hq
  have hOrth :
      ∫ ω, U ω * _root_.GD.N0144.d006721 D Sobs q ω ∂P = 0 :=
    _root_.GD.N0141.d006692
      hIndepCarrier hU.aestronglyMeasurable
        hCarrier.aestronglyMeasurable hCentered
  have hIdentity :=
    _root_.GD.N0141.d006691
      (U := U) (D := D) (L := L)
      (q := fun ω => q (D ω, Sobs ω))
      (e := e) (ε := ε)
      hU hWeight hCarrier hOrth
  have hCorrected :
      (fun ω =>
          _root_.GD.N0141.d006685 U D L e ω
            + ε * _root_.GD.N0144.d006721 D Sobs q ω) =
        _root_.GD.N0141.d006686 U D L
          (fun ω => q (D ω, Sobs ω)) e ε := by
    funext ω
    unfold _root_.GD.N0141.d006686 _root_.GD.N0144.d006721
    ring
  rw [hCorrected]
  exact hIdentity

end

end GD.N0144
