import GD.Module0014
import GD.Module0055
import GD.Module0057
import GD.Module0633
import GD.Module0723




































open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0859

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0609


structure d010809 (k : ℕ) where
  location : ℝ
  scale : Fin k → ℝ
  scale_pos : ∀ i, 0 < scale i


def d010810 (k : ℕ) : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := 0
  scale := fun _ => 1
  scale_pos := fun _ => zero_lt_one

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)


abbrev d010811 := _root_.GD.N0232.N0719.d009173 k sizes


noncomputable def d010812 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Measure (_root_.GD.N0232.N0719.N0859.d010811 k sizes) :=
  _root_.GD.N0232.N0719.d009176 k sizes θ.location θ.scale


noncomputable def d010813 :
    Measure (_root_.GD.N0232.N0719.N0859.d010811 k sizes) :=
  _root_.GD.N0232.N0719.d009182 k sizes



theorem d010814 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ ≪ _root_.GD.N0232.N0719.N0859.d010813 k sizes := by
  exact
    (_root_.GD.N0232.N0719.d009183
      k sizes θ.location θ.scale θ.scale_pos).1


noncomputable def d010815 : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0900.d009111 k sizes


noncomputable def d010816 : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes

include hk hsizes in



theorem d010817 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp
      (fun ω => _root_.GD.N0232.N0719.N0859.d010815 k sizes ω - θ.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  exact
    _root_.GD.N0232.N0719.N1024.d010733
      k sizes hk hsizes θ.location θ.scale θ.scale_pos



theorem d010818 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp
      (fun ω => _root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes ω - θ.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  exact
    _root_.GD.N0232.N0719.N1024.d010734
      k sizes hk hsizes θ.location θ.scale θ.scale_pos

include hk hsizes in

noncomputable def d010819 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  MemLp.toLp (_root_.GD.N0232.N0719.N0859.d010815 k sizes)
    (by
      have h :=
        _root_.GD.N0232.N0719.N0859.d010817 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0859.d010810 k)
      simpa [_root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0859.d010810, _root_.GD.N0232.N0719.N0859.d010815,
        _root_.GD.N0232.N0719.d009182] using h)


noncomputable def d010820 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  MemLp.toLp (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes)
    (by
      have h :=
        _root_.GD.N0232.N0719.N0859.d010818 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0859.d010810 k)
      simpa [_root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0859.d010810, _root_.GD.N0232.N0719.N0859.d010816,
        _root_.GD.N0232.N0719.d009182] using h)


noncomputable def d010821
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) : ℝ≥0∞ :=
  _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location d



theorem d010822
    {μ₀ μ : Measure (_root_.GD.N0232.N0719.N0859.d010811 k sizes)}
    (hμ : μ ≪ μ₀) (target : ℝ)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf₀ : MemLp f 2 μ₀)
    (hfμ : MemLp (fun ω => f ω - target) 2 μ) :
    _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target (MemLp.toLp f hf₀) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 μ (fun ω => f ω - target)) := by
  have hae₀ :
      (fun ω =>
        (MemLp.toLp f hf₀ : _root_.GD.N0230.N0602.d000116 μ₀) ω) =ᵐ[μ₀] f :=
    hf₀.coeFn_toLp
  have hae :
      (fun ω =>
        (MemLp.toLp f hf₀ : _root_.GD.N0230.N0602.d000116 μ₀) ω) =ᵐ[μ] f :=
    hμ.ae_le hae₀
  rw [_root_.GD.N0230.N0602.d000117]
  calc
    (∫⁻ ω,
        ENNReal.ofReal
          (((MemLp.toLp f hf₀ : _root_.GD.N0230.N0602.d000116 μ₀) ω - target) ^ 2) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal ((f ω - target) ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ω hω
      rw [hω]
    _ =
        ENNReal.ofReal
          (∫ ω, (f ω - target) ^ 2 ∂μ) := by
      exact
        (ofReal_integral_eq_lintegral_ofReal
          hfμ.integrable_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ = _ := rfl


theorem d010823 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)
          (fun ω => _root_.GD.N0232.N0719.N0859.d010815 k sizes ω - θ.location)) := by
  apply _root_.GD.N0232.N0719.N0859.d010822
    k sizes (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ)
  exact _root_.GD.N0232.N0719.N0859.d010817 k sizes hk hsizes θ


theorem d010824 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)
          (fun ω =>
            _root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes ω - θ.location)) := by
  apply _root_.GD.N0232.N0719.N0859.d010822
    k sizes (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ)
  exact _root_.GD.N0232.N0719.N0859.d010818 k sizes hk hsizes θ



theorem d010825 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
  intro θ
  have hstrict :=
    _root_.GD.N0232.N0719.N1024.d010808
      k sizes hk hsizes
      θ.location θ.scale θ.scale_pos
  have hbasePos :
      0 <
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)
          (fun ω => _root_.GD.N0232.N0719.N0859.d010815 k sizes ω - θ.location) := by
    exact lt_of_le_of_lt
      (integral_nonneg fun _ => sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0719.N0859.d010824 k sizes hk hsizes θ,
    _root_.GD.N0232.N0719.N0859.d010823 k sizes hk hsizes θ]
  exact (ENNReal.ofReal_lt_ofReal_iff hbasePos).2 hstrict


def d010826 : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :=
  {d | _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) d}

theorem d010827 :
    IsClosed (_root_.GD.N0232.N0719.N0859.d010826 k sizes hk hsizes) := by
  simpa [_root_.GD.N0232.N0719.N0859.d010826, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun θ => _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes))
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))

theorem d010828 :
    Convex ℝ (_root_.GD.N0232.N0719.N0859.d010826 k sizes hk hsizes) := by
  simpa [_root_.GD.N0232.N0719.N0859.d010826, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun θ => _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes))
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))



theorem d010829
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d =
      ENNReal.ofReal
        (‖(0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) - d‖ ^ 2) := by
  simpa [_root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010810,
    _root_.GD.N0232.N0719.d009182] using
    _root_.GD.N0230.N0602.d000124 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) d








noncomputable def d010830 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  _root_.GD.N0230.N0608.d000681
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
      _root_.GD.N0232.N0719.N0859.d010827 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
      _root_.GD.N0232.N0719.N0859.d010828 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)

theorem d010831 :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes)
      ∧ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
        (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes)
      ∧ (∀ d,
        _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) d →
        _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)
            (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes) ≤
          _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d) := by
  exact _root_.GD.N0230.N0608.d000682
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
      _root_.GD.N0232.N0719.N0859.d010827 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
      _root_.GD.N0232.N0719.N0859.d010828 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)









theorem d010832
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) d) :
    ‖d - _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes‖ ^ 2 ≤
      ‖d‖ ^ 2 - ‖_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes‖ ^ 2 := by
  simpa [_root_.GD.N0232.N0719.N0859.d010830] using
    (_root_.GD.N0230.N0609.d000701
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) d
      (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
        _root_.GD.N0232.N0719.N0859.d010827 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
        _root_.GD.N0232.N0719.N0859.d010828 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)





theorem d010833
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) d) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)
          (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes) +
        ENNReal.ofReal
          (‖d - _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes‖ ^ 2) ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d := by
  simpa [_root_.GD.N0232.N0719.N0859.d010830] using
    (_root_.GD.N0230.N0609.d000702
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) d
      (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
        _root_.GD.N0232.N0719.N0859.d010827 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
        _root_.GD.N0232.N0719.N0859.d010828 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)





theorem d010834
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) d)
    {η : ℝ} (hη : 0 ≤ η)
    (hgap :
      ‖d‖ ^ 2 - ‖_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes‖ ^ 2 ≤ η) :
    ‖d - _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes‖ ≤ Real.sqrt η := by
  have hsq :=
    _root_.GD.N0232.N0719.N0859.d010832
      k sizes hk hsizes d hd
  have hsqrtSq : (Real.sqrt η) ^ 2 = η := Real.sq_sqrt hη
  nlinarith [norm_nonneg
      (d - _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes),
    Real.sqrt_nonneg η]











theorem d010835
    (d q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) d)
    (relaxed : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)))
    (hcontains : _root_.GD.N0232.N0719.N0859.d010826 k sizes hk hsizes ⊆ relaxed)
    (hqmin : ∀ e, e ∈ relaxed → ‖q‖ ≤ ‖e‖)
    {η : ℝ} (hη : 0 ≤ η)
    (hgap : ‖d‖ ^ 2 - ‖q‖ ^ 2 ≤ η) :
    ‖d - _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes‖ ≤ Real.sqrt η := by
  simpa [_root_.GD.N0232.N0719.N0859.d010830] using
    (_root_.GD.N0230.N0609.d000706
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
      (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) d q
      (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
        _root_.GD.N0232.N0719.N0859.d010827 k sizes hk hsizes)
      (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
        _root_.GD.N0232.N0719.N0859.d010828 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd relaxed
      (by
        intro e he
        exact hcontains he)
      (by
        intro e he
        simpa using hqmin e he)
      hη (by simpa using hgap))



theorem d010836 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
  exact _root_.GD.N0230.N0608.d000683
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
      _root_.GD.N0232.N0719.N0859.d010827 k sizes hk hsizes)
    (by simpa [_root_.GD.N0232.N0719.N0859.d010826] using
      _root_.GD.N0232.N0719.N0859.d010828 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010825 k sizes hk hsizes)


noncomputable def d010837 :
    _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  AEStronglyMeasurable.mk
    (fun ω => _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes ω)
    (Lp.aestronglyMeasurable
      (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes))

theorem d010838 :
    Measurable (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) :=
  AEStronglyMeasurable.measurable_mk
    (Lp.aestronglyMeasurable
      (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes))



theorem d010839 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
      (fun ω => _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes ω) := by
  have href :=
    (Lp.aestronglyMeasurable
      (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes)).ae_eq_mk.symm
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le href


noncomputable def d010840
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((d ω - θ.location) ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ



theorem d010841
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (MemLp.toLp d hd) := by
  have href :
      (fun ω =>
        (MemLp.toLp d hd : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) ω) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes] d :=
    hd.coeFn_toLp
  have hθ :
      (fun ω =>
        (MemLp.toLp d hd : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) ω) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010812 k sizes θ] d :=
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le href
  unfold _root_.GD.N0232.N0719.N0859.d010840 _root_.GD.N0232.N0719.N0859.d010821 _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [hθ] with ω hω
  rw [hω]

theorem d010842
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes) =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
  exact _root_.GD.N0232.N0719.N0859.d010841 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes)
    (by
      have h :=
        _root_.GD.N0232.N0719.N0859.d010817 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0859.d010810 k)
      simpa [_root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0859.d010810, _root_.GD.N0232.N0719.N0859.d010815,
        _root_.GD.N0232.N0719.d009182] using h)

theorem d010843
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
        (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes θ
        (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010840 _root_.GD.N0232.N0719.N0859.d010821 _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [
    _root_.GD.N0232.N0719.N0859.d010839 k sizes hk hsizes θ] with ω hω
  rw [hω]



theorem d010844
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp
      (fun ω =>
        _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes ω - θ.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  have hmeas :
      Measurable
        (fun ω =>
          _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes ω - θ.location) :=
    (_root_.GD.N0232.N0719.N0859.d010838 k sizes hk hsizes).sub
      measurable_const
  apply
    (memLp_two_iff_integrable_sq
      hmeas.aestronglyMeasurable).2
  have hlin :
      (∫⁻ ω,
          ENNReal.ofReal
            ((_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes ω -
                θ.location) ^ 2)
          ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) ≠ ⊤ := by
    change
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
        (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) ≠ ⊤
    rw [_root_.GD.N0232.N0719.N0859.d010843
      k sizes hk hsizes θ]
    apply ne_top_of_le_ne_top _
      ((_root_.GD.N0232.N0719.N0859.d010831 k sizes hk hsizes).1 θ)
    rw [_root_.GD.N0232.N0719.N0859.d010824 k sizes hk hsizes θ]
    exact ENNReal.ofReal_ne_top
  exact
    (lintegral_ofReal_ne_top_iff_integrable
      (hmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).1 hlin



theorem d010845
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
        (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)
          (fun ω =>
            _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes ω -
              θ.location)) := by
  unfold _root_.GD.N0232.N0719.N0859.d010840 _root_.GD.N0141.d006684
  exact
    (ofReal_integral_eq_lintegral_ofReal
      (_root_.GD.N0232.N0719.N0859.d010844
        k sizes hk hsizes θ).integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm



theorem d010846 :
    ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
          (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
  intro θ
  rw [_root_.GD.N0232.N0719.N0859.d010843
      k sizes hk hsizes θ,
    _root_.GD.N0232.N0719.N0859.d010842 k sizes hk hsizes θ]
  exact
    _root_.GD.N0232.N0719.N0859.d010836
      k sizes hk hsizes θ




theorem d010847 :
    ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)
          (fun ω =>
            _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes ω -
              θ.location) <
        _root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)
          (fun ω =>
            _root_.GD.N0232.N0719.N0859.d010815 k sizes ω - θ.location) := by
  intro θ
  have h :=
    _root_.GD.N0232.N0719.N0859.d010846
      k sizes hk hsizes θ
  rw [
    _root_.GD.N0232.N0719.N0859.d010845
      k sizes hk hsizes θ,
    _root_.GD.N0232.N0719.N0859.d010842 k sizes hk hsizes θ,
    _root_.GD.N0232.N0719.N0859.d010823 k sizes hk hsizes θ
  ] at h
  have hbasePos :
      0 <
        _root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)
          (fun ω => _root_.GD.N0232.N0719.N0859.d010815 k sizes ω - θ.location) := by
    exact lt_of_le_of_lt
      (integral_nonneg fun _ => sq_nonneg _)
      (_root_.GD.N0232.N0719.N1024.d010808
        k sizes hk hsizes
        θ.location θ.scale θ.scale_pos)
  exact ((ENNReal.ofReal_lt_ofReal_iff hbasePos).1 h)









theorem d010848
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Measurable d)
    (hdom :
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d ≤
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
            (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes)) :
    ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
        _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes := by
  have hdRisk_ne_top :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d ≠ ⊤ := by
    apply ne_top_of_le_ne_top _
      (hdom (_root_.GD.N0232.N0719.N0859.d010810 k))
    rw [_root_.GD.N0232.N0719.N0859.d010843,
      _root_.GD.N0232.N0719.N0859.d010829]
    exact ENNReal.ofReal_ne_top
  have hdMemLp : MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    apply
      (memLp_two_iff_integrable_sq
        hd.aestronglyMeasurable).2
    have hlin :
        (∫⁻ ω, ENNReal.ofReal (d ω ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) ≠ ⊤ := by
      simpa [_root_.GD.N0232.N0719.N0859.d010840, _root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812,
        _root_.GD.N0232.N0719.N0859.d010810, _root_.GD.N0232.N0719.d009182] using
        hdRisk_ne_top
    have hint :=
      integrable_toReal_of_lintegral_ne_top
        ((hd.pow_const 2).ennreal_ofReal.aemeasurable) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  let dL2 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    MemLp.toLp d hdMemLp
  have hdomL2 :
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) dL2
        (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes) := by
    intro θ
    have hdRisk :
        _root_.GD.N0232.N0719.N0859.d010821 k sizes θ dL2 =
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d := by
      simpa only [dL2] using
        (_root_.GD.N0232.N0719.N0859.d010841 k sizes θ d hdMemLp).symm
    have hcanonicalRisk :
        _root_.GD.N0232.N0719.N0859.d010821 k sizes θ
            (_root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes) =
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
            (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) :=
      (_root_.GD.N0232.N0719.N0859.d010843
        k sizes hk hsizes θ).symm
    rw [hdRisk, hcanonicalRisk]
    exact hdom θ
  have hdL2eq :
      dL2 = _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes :=
    (_root_.GD.N0232.N0719.N0859.d010831 k sizes hk hsizes).2.1
      dL2 hdomL2
  have hraw_ref :
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes := by
    have hcoe :
        (fun ω => dL2 ω) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] d := by
      simpa [dL2] using hdMemLp.coeFn_toLp
    have hcanon :
        _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
          (fun ω => _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes ω) :=
      _root_.GD.N0232.N0719.N0859.d010839
        k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
    have hcoe' :
        (fun ω => dL2 ω) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          (fun ω => _root_.GD.N0232.N0719.N0859.d010830 k sizes hk hsizes ω) := by
      rw [hdL2eq]
    exact hcoe.symm.trans (hcoe'.trans hcanon.symm)
  intro θ
  exact
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hraw_ref












theorem d010849
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Measurable d)
    (hne :
      ¬ d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) :
    ∃ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
          (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d := by
  by_contra hno
  push Not at hno
  have hdom :
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d ≤
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
            (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) := by
    intro θ
    exact hno θ
  exact hne
    (_root_.GD.N0232.N0719.N0859.d010848
      k sizes hk hsizes d hd hdom (_root_.GD.N0232.N0719.N0859.d010810 k))














theorem d010850 :
    Measurable (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) ∧
      (∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
            (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) <
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) ∧
      (∀ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable d →
        (∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d ≤
            _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
              (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes)) →
        ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
          d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
            _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) ∧
      (∀ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable d →
        (¬ d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          _root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) →
        ∃ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
              (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hsizes) <
            _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) := by
  refine ⟨_root_.GD.N0232.N0719.N0859.d010838 k sizes hk hsizes,
    _root_.GD.N0232.N0719.N0859.d010846
      k sizes hk hsizes, ?_, ?_⟩
  · intro d hd hdom
    exact _root_.GD.N0232.N0719.N0859.d010848
      k sizes hk hsizes d hd hdom
  · intro d hd hne
    exact _root_.GD.N0232.N0719.N0859.d010849
      k sizes hk hsizes d hd hne

end

end N0859
end N0719
end N0232
end GD
