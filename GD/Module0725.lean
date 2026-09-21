import GD.Module0056
import GD.Module0724
import GD.Module0723
























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0858

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1024
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0571

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)


noncomputable def d010851
    (_hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
      (fun omega ↦
        _root_.GD.N0232.N0719.N0859.d010815 k sizes omega -
          theta.location) +
    _root_.GD.N0232.N0719.N1024.d010727 k sizes hk * _root_.GD.N0232.N0719.N1024.d010712 k sizes hk theta.scale


noncomputable def d010852
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ENNReal :=
  ENNReal.ofReal (_root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta)


theorem d010853 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta := by
  have hdiff :=
    _root_.GD.N0232.N0719.N1024.d010807
      k sizes hk hsizes theta.location theta.scale theta.scale_pos
  have hseedNonneg : 0 ≤
      ∫ omega,
        (_root_.GD.N0232.N0719.N0859.d010816
          k sizes hk hsizes omega - theta.location) ^ 2
        ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hdiff' :
      (∫ omega,
          (_root_.GD.N0232.N0719.N0859.d010816
            k sizes hk hsizes omega - theta.location) ^ 2
          ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) -
        ∫ omega,
          (_root_.GD.N0232.N0719.N0859.d010815 k sizes omega -
            theta.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta <
        _root_.GD.N0232.N0719.N1024.d010727 k sizes hk * _root_.GD.N0232.N0719.N1024.d010712 k sizes hk theta.scale := by
    simpa [_root_.GD.N0232.N0719.N0859.d010816,
      _root_.GD.N0232.N0719.N0859.d010815, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N1024.d010711] using hdiff
  unfold _root_.GD.N0232.N0719.N0858.d010851 _root_.GD.N0141.d006684
  nlinarith

theorem d010854 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta := by
  rw [_root_.GD.N0232.N0719.N0858.d010852]
  exact ENNReal.ofReal_pos.mpr
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta)


theorem d010855 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) <
      _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta := by
  have hdiff :=
    _root_.GD.N0232.N0719.N1024.d010807
      k sizes hk hsizes theta.location theta.scale theta.scale_pos
  rw [_root_.GD.N0232.N0719.N0859.d010824 k sizes hk hsizes theta, _root_.GD.N0232.N0719.N0858.d010852]
  apply (ENNReal.ofReal_lt_ofReal_iff
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta)).2
  unfold _root_.GD.N0232.N0719.N0858.d010851 _root_.GD.N0141.d006684
  have hdiff' := sub_lt_iff_lt_add.mp hdiff
  simpa [_root_.GD.N0232.N0719.N0859.d010816,
    _root_.GD.N0232.N0719.N0859.d010815, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N1024.d010711, add_comm] using hdiff'


theorem d010856 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta <
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
  have hstep : 0 < _root_.GD.N0232.N0719.N1024.d010727 k sizes hk :=
    _root_.GD.N0232.N0719.N1024.d010728 k sizes hk
  have hcross : _root_.GD.N0232.N0719.N1024.d010712 k sizes hk theta.scale < 0 :=
    _root_.GD.N0232.N0719.N1024.d010804 hk sizes hsizes theta.scale theta.scale_pos
  have hcapBelow :
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta <
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega ↦
            _root_.GD.N0232.N0719.N0859.d010815 k sizes omega -
              theta.location) := by
    unfold _root_.GD.N0232.N0719.N0858.d010851
    nlinarith [mul_neg_of_pos_of_neg hstep hcross]
  have hbasePos :
      0 <
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega ↦
            _root_.GD.N0232.N0719.N0859.d010815 k sizes omega -
              theta.location) := by
    exact (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta).trans hcapBelow
  rw [_root_.GD.N0232.N0719.N0858.d010852, _root_.GD.N0232.N0719.N0859.d010823 k sizes hk hsizes theta]
  apply (ENNReal.ofReal_lt_ofReal_iff hbasePos).2
  exact hcapBelow



theorem d010857 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta ∧
      _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta <
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) :=
  ⟨_root_.GD.N0232.N0719.N0858.d010855 k sizes hk hsizes theta,
    _root_.GD.N0232.N0719.N0858.d010856 k sizes hk hsizes theta⟩


def d010858 : Set
    (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :=
  {d | _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes) d}

theorem d010859 :
    _root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
  intro theta
  exact (_root_.GD.N0232.N0719.N0858.d010855 k sizes hk hsizes theta).le

theorem d010860 :
    (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes).Nonempty :=
  ⟨_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes,
    _root_.GD.N0232.N0719.N0858.d010859 k sizes hk hsizes⟩

theorem d010861 :
    IsClosed (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) := by
  change IsClosed
    (_root_.GD.N0230.N0602.d000118
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes))
  exact _root_.GD.N0230.N0602.d000122
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
    (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes)

theorem d010862 :
    Convex ℝ (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) := by
  change Convex ℝ
    (_root_.GD.N0230.N0602.d000118
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes))
  exact _root_.GD.N0230.N0602.d000123
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
    (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes)


noncomputable def d010863 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  _root_.GD.N0230.N0571.d000688
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010861 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)


theorem d010864 :
    _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes) := by
  simpa [_root_.GD.N0232.N0719.N0858.d010863] using
    (_root_.GD.N0230.N0571.d000690
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010861 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes))


theorem d010865 :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes) := by
  simpa [_root_.GD.N0232.N0719.N0858.d010863] using
    (_root_.GD.N0230.N0571.d000691
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010861 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes))


theorem d010866 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
  simpa [_root_.GD.N0232.N0719.N0858.d010863] using
    (_root_.GD.N0230.N0571.d000697
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010861 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes)
      (_root_.GD.N0232.N0719.N0858.d010856 k sizes hk hsizes))


theorem d010867
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes) d) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)
        (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes) ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d := by
  simpa [_root_.GD.N0232.N0719.N0858.d010863] using
    (_root_.GD.N0230.N0571.d000692
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010861 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)


theorem d010868
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes) d) :
    ‖_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes‖ ≤ ‖d‖ := by
  simpa [_root_.GD.N0232.N0719.N0858.d010863] using
    (_root_.GD.N0230.N0571.d000693
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010861 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)


theorem d010869
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes) d) :
    ‖d - _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes‖ ^ 2 ≤
      ‖d‖ ^ 2 - ‖_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes‖ ^ 2 := by
  simpa [_root_.GD.N0232.N0719.N0858.d010863] using
    (_root_.GD.N0230.N0571.d000695
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010861 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)


noncomputable def d010870 :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  AEStronglyMeasurable.mk
    (fun omega ↦ _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes omega)
    (Lp.aestronglyMeasurable
      (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes))

theorem d010871 :
    Measurable (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) :=
  AEStronglyMeasurable.measurable_mk
    (Lp.aestronglyMeasurable
      (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes))



theorem d010872 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
      (fun omega ↦ _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes omega) := by
  have href :=
    (Lp.aestronglyMeasurable
      (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes)).ae_eq_mk.symm
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le href


theorem d010873
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010840 _root_.GD.N0232.N0719.N0859.d010821 _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [
    _root_.GD.N0232.N0719.N0858.d010872
      k sizes hk hsizes theta] with omega homega
  rw [homega]



theorem d010874
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp
      (fun omega ↦
        _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes omega -
          theta.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  have hmeas : Measurable
      (fun omega ↦
        _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes omega -
          theta.location) :=
    (_root_.GD.N0232.N0719.N0858.d010871
      k sizes hk hsizes).sub measurable_const
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
  have hlin :
      (∫⁻ omega,
        ENNReal.ofReal
          ((_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes omega -
            theta.location) ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) ≠ ⊤ := by
    change _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
      (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) ≠ ⊤
    rw [_root_.GD.N0232.N0719.N0858.d010873]
    apply ne_top_of_le_ne_top _
      (_root_.GD.N0232.N0719.N0858.d010864 k sizes hk hsizes theta)
    unfold _root_.GD.N0232.N0719.N0858.d010852
    exact ENNReal.ofReal_ne_top
  exact
    (lintegral_ofReal_ne_top_iff_integrable
      (hmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)).1 hlin


theorem d010875
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega ↦
            _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes omega -
              theta.location)) := by
  unfold _root_.GD.N0232.N0719.N0859.d010840 _root_.GD.N0141.d006684
  exact
    (ofReal_integral_eq_lintegral_ofReal
      (_root_.GD.N0232.N0719.N0858.d010874
        k sizes hk hsizes theta).integrable_sq
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)).symm



theorem d010876 :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
  intro theta
  rw [_root_.GD.N0232.N0719.N0858.d010873,
    _root_.GD.N0232.N0719.N0859.d010842 k sizes hk hsizes theta]
  exact _root_.GD.N0232.N0719.N0858.d010866
    k sizes hk hsizes theta



theorem d010877
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : Measurable d)
    (hdom : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes)) :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
        _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes := by
  have hdRisk_ne_top :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (hdom (_root_.GD.N0232.N0719.N0859.d010810 k))
    rw [_root_.GD.N0232.N0719.N0858.d010873,
      _root_.GD.N0232.N0719.N0859.d010829]
    exact ENNReal.ofReal_ne_top
  have hdMemLp : MemLp d 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).2
    have hlin :
        (∫⁻ omega, ENNReal.ofReal (d omega ^ 2)
          ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) ≠ ⊤ := by
      simpa [_root_.GD.N0232.N0719.N0859.d010840, _root_.GD.N0232.N0719.N0859.d010813,
        _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0859.d010810, _root_.GD.N0232.N0719.d009182] using
        hdRisk_ne_top
    have hint :=
      integrable_toReal_of_lintegral_ne_top
        ((hd.pow_const 2).ennreal_ofReal.aemeasurable) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  let dL2 : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    MemLp.toLp d hdMemLp
  have hdomL2 :
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) dL2
        (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes) := by
    intro theta
    have hdRisk : _root_.GD.N0232.N0719.N0859.d010821 k sizes theta dL2 =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
      simpa only [dL2] using
        (_root_.GD.N0232.N0719.N0859.d010841 k sizes theta d hdMemLp).symm
    have hcanonicalRisk :
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
            (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes) =
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) :=
      (_root_.GD.N0232.N0719.N0858.d010873
        k sizes hk hsizes theta).symm
    rw [hdRisk, hcanonicalRisk]
    exact hdom theta
  have hdL2eq :
      dL2 = _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes :=
    _root_.GD.N0232.N0719.N0858.d010865
      k sizes hk hsizes dL2 hdomL2
  have hraw_ref :
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes := by
    have hcoe :
        (fun omega ↦ dL2 omega) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes] d := by
      simpa [dL2] using hdMemLp.coeFn_toLp
    have hcanon :
        _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
          (fun omega ↦
            _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes omega) :=
      _root_.GD.N0232.N0719.N0858.d010872
        k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
    have hcoe' :
        (fun omega ↦ dL2 omega) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
          (fun omega ↦
            _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes omega) := by
      rw [hdL2eq]
    exact hcoe.symm.trans (hcoe'.trans hcanon.symm)
  intro theta
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le hraw_ref


theorem d010878
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : Measurable d)
    (hne :
      ¬ d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) :
    ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
  by_contra hno
  push Not at hno
  have hdom : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) := by
    intro theta
    exact hno theta
  exact hne
    (_root_.GD.N0232.N0719.N0858.d010877
      k sizes hk hsizes d hd hdom (_root_.GD.N0232.N0719.N0859.d010810 k))



theorem d010879 :
    Measurable (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) ∧
      (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) <
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) ∧
      (∀ d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
        Measurable d →
        (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
            _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
              (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes)) →
        ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
            _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) ∧
      (∀ d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
        Measurable d →
        (¬ d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          _root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) →
        ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
              (_root_.GD.N0232.N0719.N0858.d010870 k sizes hk hsizes) <
            _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) := by
  refine ⟨_root_.GD.N0232.N0719.N0858.d010871 k sizes hk hsizes,
    _root_.GD.N0232.N0719.N0858.d010876
      k sizes hk hsizes, ?_, ?_⟩
  · intro d hd hdom
    exact _root_.GD.N0232.N0719.N0858.d010877
      k sizes hk hsizes d hd hdom
  · intro d hd hne
    exact _root_.GD.N0232.N0719.N0858.d010878
      k sizes hk hsizes d hd hne

end

end N0858
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0858.d010857
#print axioms _root_.GD.N0232.N0719.N0858.d010865
#print axioms _root_.GD.N0232.N0719.N0858.d010866
#print axioms _root_.GD.N0232.N0719.N0858.d010869
#print axioms _root_.GD.N0232.N0719.N0858.d010877
#print axioms _root_.GD.N0232.N0719.N0858.d010879
