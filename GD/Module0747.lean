import GD.Module0724
import GD.Module0745
























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0719.N0935

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0609

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)


noncomputable def d011165 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  MemLp.toLp (_root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes)
    (by
      have h :=
        _root_.GD.N0232.N0719.N0911.d011150
          k sizes hk hsizes 0 (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
      simpa [_root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N1024.d010711,
        _root_.GD.N0232.N0719.d009182] using h)



theorem d011166 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega ↦
            _root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes omega -
              theta.location)) := by
  apply _root_.GD.N0232.N0719.N0859.d010822
    k sizes (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta)
  exact _root_.GD.N0232.N0719.N0911.d011150
    k sizes hk hsizes theta.location theta.scale theta.scale_pos



theorem d011167 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
  intro theta
  have hstrict :=
    _root_.GD.N0232.N0719.N0911.d011152
      k sizes hk hsizes theta.location theta.scale theta.scale_pos
  have hbasePos :
      0 <
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega ↦
            _root_.GD.N0232.N0719.N0859.d010815 k sizes omega - theta.location) := by
    exact lt_of_le_of_lt
      (integral_nonneg fun _ ↦ sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0719.N0935.d011166 k sizes hk hsizes theta,
    _root_.GD.N0232.N0719.N0859.d010823 k sizes hk hsizes theta]
  exact (ENNReal.ofReal_lt_ofReal_iff hbasePos).2 hstrict



theorem d011168 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) := by
  intro theta
  have hstrict :=
    _root_.GD.N0232.N0719.N0911.d011153
      k sizes hk hsizes theta.location theta.scale theta.scale_pos
  have hreleasedPos :
      0 <
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
          (fun omega ↦
            _root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes omega - theta.location) := by
    exact lt_of_le_of_lt
      (integral_nonneg fun _ ↦ sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0719.N0935.d011166 k sizes hk hsizes theta,
    _root_.GD.N0232.N0719.N0859.d010824 k sizes hk hsizes theta]
  exact (ENNReal.ofReal_lt_ofReal_iff hreleasedPos).2 hstrict


def d011169 : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :=
  {d | _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes) d}

theorem d011170 :
    IsClosed (_root_.GD.N0232.N0719.N0935.d011169 k sizes hk hsizes) := by
  simpa [_root_.GD.N0232.N0719.N0935.d011169, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta ↦ _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes))
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))

theorem d011171 :
    Convex ℝ (_root_.GD.N0232.N0719.N0935.d011169 k sizes hk hsizes) := by
  simpa [_root_.GD.N0232.N0719.N0935.d011169, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta ↦ _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes))
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))



noncomputable def d011172 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  _root_.GD.N0230.N0608.d000681
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011170 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011171 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)

theorem d011173 :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes)
      ∧ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
        (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes)
      ∧ (∀ d,
        _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes) d →
        _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)
            (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes) ≤
          _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d) := by
  exact _root_.GD.N0230.N0608.d000682
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011170 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011171 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)



theorem d011174
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes) d) :
    ‖d - _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ ^ 2 ≤
      ‖d‖ ^ 2 - ‖_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ ^ 2 := by
  simpa [_root_.GD.N0232.N0719.N0935.d011172] using
    (_root_.GD.N0230.N0609.d000701
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes) d
      (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011170 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011171 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)


theorem d011175
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes) d) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)
          (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes) +
        ENNReal.ofReal
          (‖d - _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ ^ 2) ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d := by
  simpa [_root_.GD.N0232.N0719.N0935.d011172] using
    (_root_.GD.N0230.N0609.d000702
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes) d
      (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011170 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011171 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)



theorem d011176 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
  exact _root_.GD.N0230.N0608.d000683
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011170 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011171 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)
    (_root_.GD.N0232.N0719.N0935.d011167 k sizes hk hsizes)



theorem d011177 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) := by
  exact _root_.GD.N0230.N0608.d000683
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011170 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0935.d011169] using _root_.GD.N0232.N0719.N0935.d011171 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)
    (_root_.GD.N0232.N0719.N0935.d011168
      k sizes hk hsizes)


noncomputable def d011178 : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  AEStronglyMeasurable.mk
    (fun omega ↦ _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes omega)
    (Lp.aestronglyMeasurable (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes))

theorem d011179 :
    Measurable (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) :=
  AEStronglyMeasurable.measurable_mk
    (Lp.aestronglyMeasurable (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes))

theorem d011180 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
      (fun omega ↦ _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes omega) := by
  have href :=
    (Lp.aestronglyMeasurable
      (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes)).ae_eq_mk.symm
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le href



theorem d011181
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010840 _root_.GD.N0232.N0719.N0859.d010821 _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0232.N0719.N0935.d011180
    k sizes hk hsizes theta] with omega homega
  rw [homega]



theorem d011182
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes) =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N0935.d011165 k sizes hk hsizes) := by
  exact _root_.GD.N0232.N0719.N0859.d010841 k sizes theta
    (_root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes)
    (by
      have h := _root_.GD.N0232.N0719.N0911.d011150
        k sizes hk hsizes 0 (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
      simpa [_root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N1024.d010711,
        _root_.GD.N0232.N0719.d009182] using h)



theorem d011183
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp
      (fun omega ↦
        _root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes omega - theta.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  have hmeas : Measurable
      (fun omega ↦
        _root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes omega - theta.location) :=
    (_root_.GD.N0232.N0719.N0935.d011179 k sizes hk hsizes).sub measurable_const
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
  have hlin :
      (∫⁻ omega,
          ENNReal.ofReal
            ((_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes omega -
              theta.location) ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) ≠ ⊤ := by
    change _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
      (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) ≠ ⊤
    rw [_root_.GD.N0232.N0719.N0935.d011181
      k sizes hk hsizes theta]
    apply ne_top_of_le_ne_top _ ((_root_.GD.N0232.N0719.N0935.d011173
      k sizes hk hsizes).1 theta)
    rw [_root_.GD.N0232.N0719.N0935.d011166 k sizes hk hsizes theta]
    exact ENNReal.ofReal_ne_top
  exact
    (lintegral_ofReal_ne_top_iff_integrable
      (hmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)).1 hlin



theorem d011184 :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
  intro theta
  rw [_root_.GD.N0232.N0719.N0935.d011181 k sizes hk hsizes theta,
    _root_.GD.N0232.N0719.N0859.d010842 k sizes hk hsizes theta]
  exact _root_.GD.N0232.N0719.N0935.d011176
    k sizes hk hsizes theta



theorem d011185 :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes) := by
  intro theta
  rw [_root_.GD.N0232.N0719.N0935.d011181 k sizes hk hsizes theta]
  have hrawSeed :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes) =
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) := by
    exact _root_.GD.N0232.N0719.N0859.d010841 k sizes theta
      (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes)
      (by
        have h := _root_.GD.N0232.N0719.N0859.d010818 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0859.d010810 k)
        simpa [_root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0859.d010810, _root_.GD.N0232.N0719.N0859.d010816,
          _root_.GD.N0232.N0719.d009182] using h)
  rw [hrawSeed]
  exact _root_.GD.N0232.N0719.N0935.d011177
    k sizes hk hsizes theta



theorem d011186
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Measurable d)
    (hdom : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes)) :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
        _root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes := by
  have hdRisk_ne_top :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (hdom (_root_.GD.N0232.N0719.N0859.d010810 k))
    rw [_root_.GD.N0232.N0719.N0935.d011181,
      _root_.GD.N0232.N0719.N0859.d010829]
    exact ENNReal.ofReal_ne_top
  have hdMemLp : MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).2
    have hlin :
        (∫⁻ omega, ENNReal.ofReal (d omega ^ 2)
          ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) ≠ ⊤ := by
      simpa [_root_.GD.N0232.N0719.N0859.d010840, _root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812,
        _root_.GD.N0232.N0719.N0859.d010810, _root_.GD.N0232.N0719.d009182] using
        hdRisk_ne_top
    have hint := integrable_toReal_of_lintegral_ne_top
      ((hd.pow_const 2).ennreal_ofReal.aemeasurable) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  let dL2 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := MemLp.toLp d hdMemLp
  have hdomL2 : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) dL2
      (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes) := by
    intro theta
    have hdRisk : _root_.GD.N0232.N0719.N0859.d010821 k sizes theta dL2 =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
      simpa only [dL2] using
        (_root_.GD.N0232.N0719.N0859.d010841 k sizes theta d hdMemLp).symm
    have hcanonicalRisk :
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes) =
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) :=
      (_root_.GD.N0232.N0719.N0935.d011181
        k sizes hk hsizes theta).symm
    rw [hdRisk, hcanonicalRisk]
    exact hdom theta
  have hdL2eq : dL2 = _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes :=
    (_root_.GD.N0232.N0719.N0935.d011173 k sizes hk hsizes).2.1 dL2 hdomL2
  have hraw_ref : d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes := by
    have hcoe : (fun omega ↦ dL2 omega) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] d := by
      simpa [dL2] using hdMemLp.coeFn_toLp
    have hcanon : _root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010813 k sizes]
        (fun omega ↦ _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes omega) :=
      _root_.GD.N0232.N0719.N0935.d011180
        k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
    have hcoe' : (fun omega ↦ dL2 omega) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
        (fun omega ↦ _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes omega) := by
      rw [hdL2eq]
    exact hcoe.symm.trans (hcoe'.trans hcanon.symm)
  intro theta
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le hraw_ref


theorem d011187
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Measurable d)
    (hne : ¬ d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) :
    ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
  by_contra hno
  push Not at hno
  have hdom : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) := by
    intro theta
    exact hno theta
  exact hne (_root_.GD.N0232.N0719.N0935.d011186
    k sizes hk hsizes d hd hdom (_root_.GD.N0232.N0719.N0859.d010810 k))



theorem d011188 :
    Measurable (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) ∧
      (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) <
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) ∧
      (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) <
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes)) ∧
      (∀ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable d →
        (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
            _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
              (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes)) →
        ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
            _root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) ∧
      (∀ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable d →
        (¬ d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          _root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) →
        ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
              (_root_.GD.N0232.N0719.N0935.d011178 k sizes hk hsizes) <
            _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) := by
  refine ⟨_root_.GD.N0232.N0719.N0935.d011179 k sizes hk hsizes,
    _root_.GD.N0232.N0719.N0935.d011184
      k sizes hk hsizes,
    _root_.GD.N0232.N0719.N0935.d011185
      k sizes hk hsizes, ?_, ?_⟩
  · intro d hd hdom
    exact _root_.GD.N0232.N0719.N0935.d011186 k sizes hk hsizes d hd hdom
  · intro d hd hne
    exact _root_.GD.N0232.N0719.N0935.d011187 k sizes hk hsizes d hd hne






theorem d011189 :
    _root_.GD.N0232.N0719.N0935.d011169 k sizes hk hsizes ⊆
      _root_.GD.N0232.N0719.N0859.d010826 k sizes hk hsizes := by
  intro d hd theta
  exact le_trans (hd theta)
    (le_of_lt
      (_root_.GD.N0232.N0719.N0935.d011168
        k sizes hk hsizes theta))





theorem d011190 :
    _root_.GD.N0232.N0719.N0935.d011169 k sizes hk hsizes ⊂
      _root_.GD.N0232.N0719.N0859.d010826 k sizes hk hsizes := by
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨_root_.GD.N0232.N0719.N0935.d011189 k sizes hk hsizes, ?_⟩
  intro heq
  have hreleasedMem :
      _root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes ∈
        _root_.GD.N0232.N0719.N0859.d010826 k sizes hk hsizes :=
    _root_.GD.N0230.N0608.d000676
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes)
  have hreleasedSharp :
      _root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes ∈
        _root_.GD.N0232.N0719.N0935.d011169 k sizes hk hsizes := by
    rw [heq]
    exact hreleasedMem
  have hle := hreleasedSharp (_root_.GD.N0232.N0719.N0859.d010810 k)
  have hlt :=
    _root_.GD.N0232.N0719.N0935.d011168
      k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
  exact (not_lt_of_ge hle) hlt




theorem d011191 :
    ‖_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes -
        _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ ^ 2 -
        ‖_root_.GD.N0232.N0719.N0859.d010830
          k sizes hk hsizes‖ ^ 2 := by
  apply _root_.GD.N0232.N0719.N0859.d010832
  exact _root_.GD.N0232.N0719.N0935.d011189 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0935.d011173 k sizes hk hsizes).1



theorem d011192 :
    _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes =
        _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes ↔
      _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes ∈
        _root_.GD.N0232.N0719.N0935.d011169 k sizes hk hsizes := by
  constructor
  · intro heq
    rw [← heq]
    exact (_root_.GD.N0232.N0719.N0935.d011173 k sizes hk hsizes).1
  · intro hold
    have hnewOld := _root_.GD.N0232.N0719.N0935.d011191 k sizes hk hsizes
    have holdNew :=
      _root_.GD.N0232.N0719.N0935.d011174
        k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes)
        hold
    have hnonneg :
        0 ≤ ‖_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes -
          _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ ^ 2 := sq_nonneg _
    have hnormsymm :
        ‖_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes -
            _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes‖ =
          ‖_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes -
            _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ := by
      rw [← norm_neg]
      congr 1
      abel
    rw [hnormsymm] at hnewOld
    have hzero :
        ‖_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes -
          _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ = 0 := by
      nlinarith
    have hsub :
        _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes -
          _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes = 0 := norm_eq_zero.mp hzero
    exact (sub_eq_zero.mp hsub).symm




theorem d011193 :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes
          (_root_.GD.N0232.N0719.N0859.d010810 k)
          (_root_.GD.N0232.N0719.N0859.d010830
            k sizes hk hsizes) +
        ENNReal.ofReal
          (‖_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes -
            _root_.GD.N0232.N0719.N0859.d010830
              k sizes hk hsizes‖ ^ 2) ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes
        (_root_.GD.N0232.N0719.N0859.d010810 k)
        (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes) := by
  apply _root_.GD.N0232.N0719.N0859.d010833
  exact _root_.GD.N0232.N0719.N0935.d011189 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0935.d011173 k sizes hk hsizes).1



theorem d011194
    (hne : _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes ≠
      _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes) :
    ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
          (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
          (_root_.GD.N0232.N0719.N0859.d010830
            k sizes hk hsizes) := by
  have hnot :
      ¬ _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes ∈
        _root_.GD.N0232.N0719.N0935.d011169 k sizes hk hsizes := by
    intro hold
    exact hne
      ((_root_.GD.N0232.N0719.N0935.d011192
        k sizes hk hsizes).2 hold)
  simp only [_root_.GD.N0232.N0719.N0935.d011169, Set.mem_setOf_eq, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672] at hnot
  push Not at hnot
  obtain ⟨theta, hseedlt⟩ := hnot
  exact ⟨theta, lt_of_le_of_lt
    ((_root_.GD.N0232.N0719.N0935.d011173 k sizes hk hsizes).1 theta) hseedlt⟩





theorem d011195 :
    _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes =
        _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes ∨
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes
            (_root_.GD.N0232.N0719.N0859.d010810 k)
            (_root_.GD.N0232.N0719.N0859.d010830
              k sizes hk hsizes) <
          _root_.GD.N0232.N0719.N0859.d010821 k sizes
            (_root_.GD.N0232.N0719.N0859.d010810 k)
            (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes) ∧
        ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
              (_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes) <
            _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
              (_root_.GD.N0232.N0719.N0859.d010830
                k sizes hk hsizes)) := by
  by_cases heq : _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes =
      _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes
  · exact Or.inl heq
  · right
    constructor
    · rw [_root_.GD.N0232.N0719.N0859.d010829,
        _root_.GD.N0232.N0719.N0859.d010829]
      have htax := _root_.GD.N0232.N0719.N0935.d011191 k sizes hk hsizes
      have hdistpos :
          0 < ‖_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes -
            _root_.GD.N0232.N0719.N0859.d010830
              k sizes hk hsizes‖ ^ 2 := by
        have hsubne :
            _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes -
              _root_.GD.N0232.N0719.N0859.d010830
                k sizes hk hsizes ≠ 0 := sub_ne_zero.mpr heq
        exact sq_pos_of_pos (norm_pos_iff.mpr hsubne)
      have hsq :
          ‖_root_.GD.N0232.N0719.N0859.d010830
              k sizes hk hsizes‖ ^ 2 <
            ‖_root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ ^ 2 := by
        linarith
      have hsq0 :
          ‖(0 : _root_.GD.N0230.N0602.d000116
              (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) -
              _root_.GD.N0232.N0719.N0859.d010830
                k sizes hk hsizes‖ ^ 2 <
            ‖(0 : _root_.GD.N0230.N0602.d000116
              (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) -
              _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ ^ 2 := by
        simpa only [zero_sub, norm_neg] using hsq
      have hrightPos :
          0 <
            ‖(0 : _root_.GD.N0230.N0602.d000116
              (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) -
              _root_.GD.N0232.N0719.N0935.d011172 k sizes hk hsizes‖ ^ 2 :=
        lt_of_le_of_lt (sq_nonneg _) hsq0
      exact (ENNReal.ofReal_lt_ofReal_iff hrightPos).2 hsq0
    · exact _root_.GD.N0232.N0719.N0935.d011194
        k sizes hk hsizes heq

end

end GD.N0232.N0719.N0935
