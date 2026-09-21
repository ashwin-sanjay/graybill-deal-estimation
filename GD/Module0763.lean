import GD.Module0724
import GD.Module0750
import GD.Module0058































open Filter MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0719.N1013

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0609
open _root_.GD.N0230.N0610
open _root_.GD.N0232.N0719.N0852
open _root_.GD.N0232.N0719.N0851
open _root_.GD.N0232.N0719.N0943
open _root_.GD.N0232.N0719.N0874
open _root_.GD.N0232.N0719.N0900

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)



def d011520 : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0943.d011243 hk sizes

theorem d011521 :
    Measurable (_root_.GD.N0232.N0719.N1013.d011520 k sizes hk) := by
  exact _root_.GD.N0232.N0719.N0943.d011246 hk sizes



theorem d011522
    (sigma : Equiv.Perm (Fin k))
    (omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0232.N0719.N1013.d011520 k (sizes ∘ sigma) hk
        (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega) =
      _root_.GD.N0232.N0719.N1013.d011520 k sizes hk omega := by
  exact _root_.GD.N0232.N0719.N0943.d011252
    hk sizes sigma omega


theorem d011523
    (hsizes0 : ∀ i, 0 < sizes i)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0232.N0719.N1013.d011520 k sizes hk
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale omega) =
      location + scale * _root_.GD.N0232.N0719.N1013.d011520 k sizes hk omega := by
  exact _root_.GD.N0232.N0719.N0943.d011255
    hk hsizes0 location hscale omega

include hsizes in


theorem d011524
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp
      (fun omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes =>
        _root_.GD.N0232.N0719.N0943.d011242 hk sizes omega)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  apply (memLp_two_iff_integrable_sq
    (_root_.GD.N0232.N0719.N0943.d011245
      hk sizes).aestronglyMeasurable).2
  exact _root_.GD.N0232.N0719.N0943.d011264
    hk sizes hsizes theta.location theta.scale theta.scale_pos

include hsizes in


theorem d011525
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp
      (fun omega => _root_.GD.N0232.N0719.N1013.d011520 k sizes hk omega - theta.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  have hbase :=
    _root_.GD.N0232.N0719.N0859.d010817
      k sizes hk hsizes theta
  have hcorrection :=
    _root_.GD.N0232.N0719.N1013.d011524
      k sizes hk hsizes theta
  apply (memLp_congr_ae ?_).2 (hbase.add hcorrection)
  filter_upwards with omega
  unfold _root_.GD.N0232.N0719.N1013.d011520 _root_.GD.N0232.N0719.N0943.d011243
    _root_.GD.N0232.N0719.N0859.d010815 _root_.GD.N0232.N0719.N0900.d009111
  simp only [Pi.add_apply]
  ring

include hk hsizes in

noncomputable def d011526 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  MemLp.toLp (_root_.GD.N0232.N0719.N1013.d011520 k sizes hk)
    (by
      have h := _root_.GD.N0232.N0719.N1013.d011525 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0859.d010810 k)
      simpa [_root_.GD.N0232.N0719.N0859.d010813,
        _root_.GD.N0232.N0719.N0859.d010812,
        _root_.GD.N0232.N0719.N0859.d010810,
        _root_.GD.N0232.N0719.d009182] using h)



theorem d011527
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega => _root_.GD.N0232.N0719.N1013.d011520 k sizes hk omega - theta.location)) := by
  apply _root_.GD.N0232.N0719.N0859.d010822
    k sizes
    (_root_.GD.N0232.N0719.N0859.d010814
      k sizes theta)
  exact _root_.GD.N0232.N0719.N1013.d011525 k sizes hk hsizes theta



theorem d011528 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
  intro theta
  have hstrict :=
    _root_.GD.N0232.N0719.N0943.d011269 hk sizes hsizes
      theta.location theta.scale theta.scale_pos
  have hbasePos :
      0 < _root_.GD.N0141.d006684
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
        (fun omega =>
          _root_.GD.N0232.N0719.N0859.d010815 k sizes omega -
            theta.location) := by
    exact lt_of_le_of_lt
      (integral_nonneg fun _ => sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0719.N1013.d011527 k sizes hk hsizes theta,
    _root_.GD.N0232.N0719.N0859.d010823
      k sizes hk hsizes theta]
  exact (ENNReal.ofReal_lt_ofReal_iff hbasePos).2 hstrict


def d011529 :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :=
  {d | _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
    (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) d}

theorem d011530 :
    IsClosed (_root_.GD.N0232.N0719.N1013.d011529 k sizes hk hsizes) := by
  simpa [_root_.GD.N0232.N0719.N1013.d011529, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672,
    _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta => _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes))
      (_root_.GD.N0232.N0719.N0859.d010814
        k sizes))

theorem d011531 :
    Convex ℝ (_root_.GD.N0232.N0719.N1013.d011529 k sizes hk hsizes) := by
  simpa [_root_.GD.N0232.N0719.N1013.d011529, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672,
    _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta => _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes))
      (_root_.GD.N0232.N0719.N0859.d010814
        k sizes))


noncomputable def d011532 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  _root_.GD.N0230.N0608.d000681
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011530 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011531 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)



theorem d011533 :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
        (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes) ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
        (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes) ∧
      (∀ d,
        _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
          (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) d →
        _root_.GD.N0232.N0719.N0859.d010821 k sizes
            (_root_.GD.N0232.N0719.N0859.d010810 k)
            (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes) ≤
          _root_.GD.N0232.N0719.N0859.d010821 k sizes
            (_root_.GD.N0232.N0719.N0859.d010810 k) d) := by
  exact _root_.GD.N0230.N0608.d000682
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011530 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011531 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)


theorem d011534
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) d) :
    ‖d - _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes‖ ^ 2 ≤
      ‖d‖ ^ 2 - ‖_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes‖ ^ 2 := by
  simpa [_root_.GD.N0232.N0719.N1013.d011532] using
    (_root_.GD.N0230.N0609.d000701
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) d
      (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011530 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011531 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)


theorem d011535
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) d) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes
          (_root_.GD.N0232.N0719.N0859.d010810 k)
          (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes) +
        ENNReal.ofReal
          (‖d - _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes‖ ^ 2) ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes
        (_root_.GD.N0232.N0719.N0859.d010810 k) d := by
  simpa [_root_.GD.N0232.N0719.N1013.d011532] using
    (_root_.GD.N0230.N0609.d000702
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) d
      (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011530 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011531 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)


theorem d011536 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
  exact _root_.GD.N0230.N0608.d000683
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011530 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011531 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)
    (_root_.GD.N0232.N0719.N1013.d011528 k sizes hk hsizes)



noncomputable def d011537 :
    _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  AEStronglyMeasurable.mk
    (fun omega => _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes omega)
    (Lp.aestronglyMeasurable (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes))

theorem d011538 :
    Measurable (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) :=
  AEStronglyMeasurable.measurable_mk
    (Lp.aestronglyMeasurable (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes))

theorem d011539
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
      (fun omega => _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes omega) := by
  have href :=
    (Lp.aestronglyMeasurable
      (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes)).ae_eq_mk.symm
  exact
    (_root_.GD.N0232.N0719.N0859.d010814
      k sizes theta).ae_le href

theorem d011540
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010840
    _root_.GD.N0232.N0719.N0859.d010821 _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0232.N0719.N1013.d011539
    k sizes hk hsizes theta] with omega homega
  rw [homega]



theorem d011541
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp
      (fun omega =>
        _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes omega - theta.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  have hmeas : Measurable
      (fun omega =>
        _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes omega - theta.location) :=
    (_root_.GD.N0232.N0719.N1013.d011538 k sizes hk hsizes).sub
      measurable_const
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
  have hlin :
      (∫⁻ omega,
          ENNReal.ofReal
            ((_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes omega -
              theta.location) ^ 2)
        ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) ≠ ⊤ := by
    change _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
      (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) ≠ ⊤
    rw [_root_.GD.N0232.N0719.N1013.d011540]
    apply ne_top_of_le_ne_top _
      ((_root_.GD.N0232.N0719.N1013.d011533 k sizes hk hsizes).1 theta)
    rw [_root_.GD.N0232.N0719.N1013.d011527]
    exact ENNReal.ofReal_ne_top
  exact
    (lintegral_ofReal_ne_top_iff_integrable
      (hmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).1 hlin



theorem d011542
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega =>
            _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes omega -
              theta.location)) := by
  unfold _root_.GD.N0232.N0719.N0859.d010840
    _root_.GD.N0141.d006684
  exact
    (ofReal_integral_eq_lintegral_ofReal
      (_root_.GD.N0232.N0719.N1013.d011541
        k sizes hk hsizes theta).integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm



theorem d011543
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Measurable d)
    (hdom : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes)) :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
        _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes := by
  have hdRisk_ne_top :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes
          (_root_.GD.N0232.N0719.N0859.d010810 k) d ≠ ⊤ := by
    apply ne_top_of_le_ne_top _
      (hdom (_root_.GD.N0232.N0719.N0859.d010810 k))
    rw [_root_.GD.N0232.N0719.N1013.d011540,
      _root_.GD.N0232.N0719.N0859.d010829]
    exact ENNReal.ofReal_ne_top
  have hdMemLp :
      MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).2
    have hlin :
        (∫⁻ omega, ENNReal.ofReal (d omega ^ 2)
          ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) ≠ ⊤ := by
      simpa [_root_.GD.N0232.N0719.N0859.d010840,
        _root_.GD.N0232.N0719.N0859.d010813,
        _root_.GD.N0232.N0719.N0859.d010812,
        _root_.GD.N0232.N0719.N0859.d010810,
        _root_.GD.N0232.N0719.d009182] using hdRisk_ne_top
    have hint :=
      integrable_toReal_of_lintegral_ne_top
        ((hd.pow_const 2).ennreal_ofReal.aemeasurable) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  let dL2 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    MemLp.toLp d hdMemLp
  have hdomL2 :
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) dL2
        (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes) := by
    intro theta
    have hdRisk :
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta dL2 =
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
      simpa only [dL2] using
        (_root_.GD.N0232.N0719.N0859.d010841
          k sizes theta d hdMemLp).symm
    have hcanonicalRisk :
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
            (_root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes) =
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) :=
      (_root_.GD.N0232.N0719.N1013.d011540
        k sizes hk hsizes theta).symm
    rw [hdRisk, hcanonicalRisk]
    exact hdom theta
  have hdL2eq : dL2 = _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes :=
    (_root_.GD.N0232.N0719.N1013.d011533 k sizes hk hsizes).2.1 dL2 hdomL2
  have hraw_ref :
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes := by
    have hcoe :
        (fun omega => dL2 omega) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes] d := by
      simpa [dL2] using hdMemLp.coeFn_toLp
    have hcanon :
        _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
          (fun omega => _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes omega) :=
      _root_.GD.N0232.N0719.N1013.d011539
        k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
    have hcoe' :
        (fun omega => dL2 omega) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
          (fun omega => _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes omega) := by
      rw [hdL2eq]
    exact hcoe.symm.trans (hcoe'.trans hcanon.symm)
  intro theta
  exact
    (_root_.GD.N0232.N0719.N0859.d010814
      k sizes theta).ae_le hraw_ref



theorem d011544
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Measurable d)
    (hne : ¬ d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) :
    ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
  by_contra hno
  push Not at hno
  exact hne
    (_root_.GD.N0232.N0719.N1013.d011543 k sizes hk hsizes d hd
      (fun theta => hno theta)
      (_root_.GD.N0232.N0719.N0859.d010810 k))


theorem d011545 :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
  intro theta
  rw [_root_.GD.N0232.N0719.N1013.d011540,
    _root_.GD.N0232.N0719.N0859.d010842]
  exact _root_.GD.N0232.N0719.N1013.d011536
    k sizes hk hsizes theta



theorem d011546 :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega =>
            _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes omega -
              theta.location) <
        _root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega =>
            _root_.GD.N0232.N0719.N0859.d010815 k sizes omega -
              theta.location) := by
  intro theta
  have h := _root_.GD.N0232.N0719.N1013.d011545
    k sizes hk hsizes theta
  rw [_root_.GD.N0232.N0719.N1013.d011542,
    _root_.GD.N0232.N0719.N0859.d010842
      k sizes hk hsizes theta,
    _root_.GD.N0232.N0719.N0859.d010823
      k sizes hk hsizes theta] at h
  have hbasePos :
      0 < _root_.GD.N0141.d006684
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
        (fun omega =>
          _root_.GD.N0232.N0719.N0859.d010815 k sizes omega -
            theta.location) := by
    exact lt_of_le_of_lt
      (integral_nonneg fun _ => sq_nonneg _)
      (_root_.GD.N0232.N0719.N0943.d011269 hk sizes hsizes
        theta.location theta.scale theta.scale_pos)
  exact (ENNReal.ofReal_lt_ofReal_iff hbasePos).1 h


theorem d011547 :
    Measurable (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) ∧
      (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) <
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) ∧
      (∀ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable d →
        (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
            _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
              (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes)) →
        ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
            _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) ∧
      (∀ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable d →
        (¬ d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) →
        ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
              (_root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes) <
            _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) := by
  refine ⟨_root_.GD.N0232.N0719.N1013.d011538 k sizes hk hsizes,
    _root_.GD.N0232.N0719.N1013.d011545
      k sizes hk hsizes, ?_, ?_⟩
  · intro d hd hdom
    exact _root_.GD.N0232.N0719.N1013.d011543
      k sizes hk hsizes d hd hdom
  · intro d hd hne
    exact _root_.GD.N0232.N0719.N1013.d011544
      k sizes hk hsizes d hd hne








theorem d011548
    {G : Type*} [Group G]
    [MulAction G (_root_.GD.N0232.N0719.N0859.d010809 k)]
    [MulAction G
      (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))]
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G)
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes))
    (hseed : ∀ g : G,
      g • _root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes = _root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes)
    (hnorm : ∀ (g : G)
      (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)),
      ‖g • d‖ = ‖d‖) :
    ∀ g : G,
      g • _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes =
        _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes := by
  apply _root_.GD.N0230.N0610.d000717
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011530 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N1013.d011529] using _root_.GD.N0232.N0719.N1013.d011531 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)
    hRisk hseed
  intro g d
  simpa using hnorm g d

end

end GD.N0232.N0719.N1013
