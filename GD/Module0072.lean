import GD.Module0014
import GD.Module0057
import GD.Module0023


















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD.N0230.N0660

noncomputable section

variable {Ω Θ : Type*} [MeasurableSpace Ω]

abbrev d000880 (μ₀ : Measure Ω) :=
  _root_.GD.N0230.N0602.d000116 μ₀

abbrev d000881
    (μ₀ : Measure Ω) (μ : Measure Ω) (target : ℝ)
    (d : _root_.GD.N0230.N0660.d000880 μ₀) : ENNReal :=
  _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target d


def d000882
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ : Θ) (d : _root_.GD.N0230.N0660.d000880 μ₀) : ENNReal :=
  _root_.GD.N0230.N0660.d000881 μ₀ (μ θ) (target θ) d


def d000883
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (benchmark : _root_.GD.N0230.N0660.d000880 μ₀) : Set (_root_.GD.N0230.N0660.d000880 μ₀) :=
  {d | _root_.GD.N0230.N0608.d000673
    (_root_.GD.N0230.N0660.d000882 μ₀ μ target) benchmark d}

theorem d000884
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀) :
    IsClosed (_root_.GD.N0230.N0660.d000883 μ₀ μ target benchmark) := by
  simpa only [_root_.GD.N0230.N0660.d000883, _root_.GD.N0230.N0660.d000882,
    _root_.GD.N0230.N0608.d000673,
    _root_.GD.N0230.N0608.d000672,
    _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (μ₀ := μ₀) (μ := μ) (target := target)
      (cap := fun θ => _root_.GD.N0230.N0660.d000882 μ₀ μ target θ benchmark) hμ)

theorem d000885
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀) :
    Convex ℝ (_root_.GD.N0230.N0660.d000883 μ₀ μ target benchmark) := by
  simpa only [_root_.GD.N0230.N0660.d000883, _root_.GD.N0230.N0660.d000882,
    _root_.GD.N0230.N0608.d000673,
    _root_.GD.N0230.N0608.d000672,
    _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (μ₀ := μ₀) (μ := μ) (target := target)
      (cap := fun θ => _root_.GD.N0230.N0660.d000882 μ₀ μ target θ benchmark) hμ)

theorem d000886
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0)
    (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    _root_.GD.N0230.N0660.d000882 μ₀ μ target θ₀ d =
      ENNReal.ofReal (‖(0 : _root_.GD.N0230.N0660.d000880 μ₀) - d‖ ^ 2) := by
  rw [_root_.GD.N0230.N0660.d000882, hμ₀, htarget₀]
  exact _root_.GD.N0230.N0602.d000124 μ₀ d





noncomputable def d000887
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0) :
    _root_.GD.N0230.N0660.d000880 μ₀ :=
  _root_.GD.N0230.N0608.d000681
    (_root_.GD.N0230.N0660.d000882 μ₀ μ target) θ₀ 0 benchmark
    (_root_.GD.N0230.N0660.d000884 μ₀ μ target benchmark hμ)
    (_root_.GD.N0230.N0660.d000885 μ₀ μ target benchmark hμ)
    (_root_.GD.N0230.N0660.d000886 μ₀ μ target θ₀ hμ₀ htarget₀)






theorem d000888
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0) :
    let selected := _root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀
    _root_.GD.N0230.N0608.d000673
        (_root_.GD.N0230.N0660.d000882 μ₀ μ target) benchmark selected ∧
      _root_.GD.N0230.N0608.d000674
        (_root_.GD.N0230.N0660.d000882 μ₀ μ target) selected ∧
      (∀ d,
        _root_.GD.N0230.N0608.d000673
            (_root_.GD.N0230.N0660.d000882 μ₀ μ target) benchmark d →
          _root_.GD.N0230.N0660.d000882 μ₀ μ target θ₀ selected ≤
            _root_.GD.N0230.N0660.d000882 μ₀ μ target θ₀ d) ∧
      (∀ d,
        _root_.GD.N0230.N0608.d000673
            (_root_.GD.N0230.N0660.d000882 μ₀ μ target) benchmark d →
          ‖d - selected‖ ^ 2 ≤ ‖d‖ ^ 2 - ‖selected‖ ^ 2) := by
  dsimp only
  have hbase :=
    _root_.GD.N0230.N0608.d000682
      (risk := _root_.GD.N0230.N0660.d000882 μ₀ μ target)
      (θ₀ := θ₀) (target := (0 : _root_.GD.N0230.N0660.d000880 μ₀)) (bar := benchmark)
      (_root_.GD.N0230.N0660.d000884 μ₀ μ target benchmark hμ)
      (_root_.GD.N0230.N0660.d000885 μ₀ μ target benchmark hμ)
      (_root_.GD.N0230.N0660.d000886
        μ₀ μ target θ₀ hμ₀ htarget₀)
  refine ⟨hbase.1, hbase.2.1, hbase.2.2, ?_⟩
  intro d hd
  simpa only [_root_.GD.N0230.N0660.d000887, sub_zero, norm_zero, zero_sub, norm_neg] using
    (_root_.GD.N0230.N0609.d000701
      (risk := _root_.GD.N0230.N0660.d000882 μ₀ μ target)
      (θ₀ := θ₀) (target := (0 : _root_.GD.N0230.N0660.d000880 μ₀)) (bar := benchmark)
      (hclosed := _root_.GD.N0230.N0660.d000884 μ₀ μ target benchmark hμ)
      (hconvex := _root_.GD.N0230.N0660.d000885 μ₀ μ target benchmark hμ)
      (href := _root_.GD.N0230.N0660.d000886
        μ₀ μ target θ₀ hμ₀ htarget₀)
      (e := d) hd)



abbrev d000889 (x : ℝ) : ℝ :=
  _root_.GD.N0230.N0637.d000240 x

theorem d000890 : Continuous (_root_.GD.N0230.N0660.d000889 : ℝ → ℝ) := by
  change Continuous (fun x : ℝ => min 1 (max 0 x))
  fun_prop

theorem d000891 (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    MemLp (fun ω => _root_.GD.N0230.N0660.d000889 (d ω)) 2 μ₀ := by
  apply (Lp.memLp d).mono
  · exact _root_.GD.N0230.N0660.d000890.comp_aestronglyMeasurable (Lp.aestronglyMeasurable d)
  · filter_upwards with ω
    simpa only [Real.norm_eq_abs, sub_zero] using
      (_root_.GD.N0230.N0637.d000245
        (t := (0 : ℝ)) (x := d ω)
        (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num))


noncomputable def d000892 (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    _root_.GD.N0230.N0660.d000880 μ₀ :=
  (_root_.GD.N0230.N0660.d000891 μ₀ d).toLp (fun ω => _root_.GD.N0230.N0660.d000889 (d ω))

theorem d000893 (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    (fun ω => _root_.GD.N0230.N0660.d000892 μ₀ d ω) =ᵐ[μ₀] fun ω => _root_.GD.N0230.N0660.d000889 (d ω) := by
  simpa only [_root_.GD.N0230.N0660.d000892] using (_root_.GD.N0230.N0660.d000891 μ₀ d).coeFn_toLp

theorem d000894
    (μ₀ μ : Measure Ω) (hμ : μ ≪ μ₀) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    _root_.GD.N0230.N0660.d000881 μ₀ μ t (_root_.GD.N0230.N0660.d000892 μ₀ d) ≤ _root_.GD.N0230.N0660.d000881 μ₀ μ t d := by
  unfold _root_.GD.N0230.N0660.d000881 _root_.GD.N0230.N0602.d000117
  apply lintegral_mono_ae
  filter_upwards [hμ.ae_le (_root_.GD.N0230.N0660.d000893 μ₀ d)] with ω hω
  rw [hω]
  exact ENNReal.ofReal_le_ofReal
    (_root_.GD.N0230.N0637.d000246
      (t := t) (x := d ω) ht)

theorem d000895
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (hμ : ∀ θ, μ θ ≪ μ₀) (htarget : ∀ θ, target θ ∈ Set.Icc 0 1)
    (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    _root_.GD.N0230.N0608.d000672
      (_root_.GD.N0230.N0660.d000882 μ₀ μ target) (_root_.GD.N0230.N0660.d000892 μ₀ d) d := by
  intro θ
  exact _root_.GD.N0230.N0660.d000894 μ₀ (μ θ) (hμ θ)
    (target θ) (htarget θ) d


theorem d000896
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0)
    (htarget : ∀ θ, target θ ∈ Set.Icc 0 1) :
    _root_.GD.N0230.N0660.d000892 μ₀
        (_root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀) =
      _root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ := by
  exact (_root_.GD.N0230.N0660.d000888 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀).2.1
    (_root_.GD.N0230.N0660.d000892 μ₀
      (_root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀))
    (_root_.GD.N0230.N0660.d000895 μ₀ μ target hμ htarget
      (_root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀))




noncomputable def d000897
    (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) : Ω → ℝ :=
  (Lp.aestronglyMeasurable d).mk (fun ω => d ω)

theorem d000898
    (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    Measurable (_root_.GD.N0230.N0660.d000897 μ₀ d) :=
  (Lp.aestronglyMeasurable d).measurable_mk

theorem d000899
    (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    _root_.GD.N0230.N0660.d000897 μ₀ d =ᵐ[μ₀] fun ω => d ω :=
  (Lp.aestronglyMeasurable d).ae_eq_mk.symm


noncomputable def d000900
    (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) : Ω → ℝ :=
  fun ω => _root_.GD.N0230.N0660.d000889 (_root_.GD.N0230.N0660.d000897 μ₀ d ω)

theorem d000901
    (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    Measurable (_root_.GD.N0230.N0660.d000900 μ₀ d) :=
  _root_.GD.N0230.N0660.d000890.measurable.comp (_root_.GD.N0230.N0660.d000898 μ₀ d)

theorem d000902
    (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) (ω : Ω) :
    _root_.GD.N0230.N0660.d000900 μ₀ d ω ∈ Set.Icc (0 : ℝ) 1 :=
  _root_.GD.N0230.N0637.d000243 _

theorem d000903
    (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0660.d000880 μ₀) :
    _root_.GD.N0230.N0660.d000900 μ₀ d =ᵐ[μ₀] fun ω => _root_.GD.N0230.N0660.d000892 μ₀ d ω := by
  filter_upwards [_root_.GD.N0230.N0660.d000899 μ₀ d,
    _root_.GD.N0230.N0660.d000893 μ₀ d] with ω hrep hclip
  change _root_.GD.N0230.N0660.d000889 (_root_.GD.N0230.N0660.d000897 μ₀ d ω) = _root_.GD.N0230.N0660.d000892 μ₀ d ω
  rw [hrep, hclip]


def d000904 (μ : Measure Ω) (target : ℝ) (d : Ω → ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal ((d ω - target) ^ 2) ∂μ

theorem d000905
    (μ₀ μ : Measure Ω) (hμ : μ ≪ μ₀) (target : ℝ)
    (d : Ω → ℝ) (hd : MemLp d 2 μ₀) :
    _root_.GD.N0230.N0660.d000904 μ target d =
      _root_.GD.N0230.N0660.d000881 μ₀ μ target (hd.toLp d) := by
  unfold _root_.GD.N0230.N0660.d000904 _root_.GD.N0230.N0660.d000881 _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [hμ.ae_le hd.coeFn_toLp] with ω hω
  rw [hω]






noncomputable def d000906
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0) : Ω → ℝ :=
  _root_.GD.N0230.N0660.d000900 μ₀
    (_root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀)

theorem d000907
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0) :
    Measurable
      (_root_.GD.N0230.N0660.d000906 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀) :=
  _root_.GD.N0230.N0660.d000901 μ₀ _

theorem d000908
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0)
    (ω : Ω) :
    _root_.GD.N0230.N0660.d000906 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ ω ∈
      Set.Icc (0 : ℝ) 1 :=
  _root_.GD.N0230.N0660.d000902 μ₀ _ ω

theorem d000909
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0)
    (htarget : ∀ θ, target θ ∈ Set.Icc 0 1) :
    _root_.GD.N0230.N0660.d000906 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ =ᵐ[μ₀]
      fun ω => _root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ ω := by
  let selected := _root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀
  have hclip : _root_.GD.N0230.N0660.d000900 μ₀ selected =ᵐ[μ₀]
      fun ω => _root_.GD.N0230.N0660.d000892 μ₀ selected ω :=
    _root_.GD.N0230.N0660.d000903 μ₀ selected
  have hfixed : _root_.GD.N0230.N0660.d000892 μ₀ selected = selected := by
    exact _root_.GD.N0230.N0660.d000896
      μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ htarget
  simpa only [_root_.GD.N0230.N0660.d000906, selected, hfixed] using hclip

theorem d000910
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0)
    (htarget : ∀ θ, target θ ∈ Set.Icc 0 1)
    (θ : Θ) :
    _root_.GD.N0230.N0660.d000906 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ =ᵐ[μ θ]
      fun ω => _root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ ω :=
  (hμ θ).ae_le
    (_root_.GD.N0230.N0660.d000909
      μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ htarget)

theorem d000911
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0)
    (htarget : ∀ θ, target θ ∈ Set.Icc 0 1)
    (θ : Θ) :
    _root_.GD.N0230.N0660.d000904 (μ θ) (target θ)
        (_root_.GD.N0230.N0660.d000906 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀) =
      _root_.GD.N0230.N0660.d000882 μ₀ μ target θ
        (_root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀) := by
  unfold _root_.GD.N0230.N0660.d000904 _root_.GD.N0230.N0660.d000882 _root_.GD.N0230.N0660.d000881
    _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0230.N0660.d000910
    μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ htarget θ] with ω hω
  rw [hω]






theorem d000912
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0)
    (htarget : ∀ θ, target θ ∈ Set.Icc 0 1)
    (e : Ω → ℝ) (he : Measurable e)
    (hdom : ∀ θ,
      _root_.GD.N0230.N0660.d000904 (μ θ) (target θ) e ≤
        _root_.GD.N0230.N0660.d000904 (μ θ) (target θ)
          (_root_.GD.N0230.N0660.d000906
            μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀)) :
    ∀ θ,
      e =ᵐ[μ θ]
        _root_.GD.N0230.N0660.d000906
          μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ := by
  let selected := _root_.GD.N0230.N0660.d000887 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀
  let selectedBorel :=
    _root_.GD.N0230.N0660.d000906 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀
  have hselectedRisk (θ : Θ) :
      _root_.GD.N0230.N0660.d000904 (μ θ) (target θ) selectedBorel =
        _root_.GD.N0230.N0660.d000882 μ₀ μ target θ selected := by
    exact _root_.GD.N0230.N0660.d000911
      μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ htarget θ
  have heRisk_ne_top : _root_.GD.N0230.N0660.d000904 μ₀ 0 e ≠ ⊤ := by
    have href := hdom θ₀
    rw [hselectedRisk θ₀,
      _root_.GD.N0230.N0660.d000886
        μ₀ μ target θ₀ hμ₀ htarget₀,
      hμ₀, htarget₀] at href
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top href
  have heMemLp : MemLp e 2 μ₀ := by
    apply (memLp_two_iff_integrable_sq he.aestronglyMeasurable).2
    have hlin : (∫⁻ ω, ENNReal.ofReal ((e ω) ^ 2) ∂μ₀) ≠ ⊤ := by
      simpa only [_root_.GD.N0230.N0660.d000904, sub_zero] using heRisk_ne_top
    have hint := integrable_toReal_of_lintegral_ne_top
      ((he.pow_const 2).ennreal_ofReal.aemeasurable) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  let eL2 : _root_.GD.N0230.N0660.d000880 μ₀ := heMemLp.toLp e
  have heL2Risk (θ : Θ) :
      _root_.GD.N0230.N0660.d000904 (μ θ) (target θ) e =
        _root_.GD.N0230.N0660.d000882 μ₀ μ target θ eL2 := by
    exact _root_.GD.N0230.N0660.d000905 μ₀ (μ θ) (hμ θ) (target θ) e heMemLp
  have heDominates :
      _root_.GD.N0230.N0608.d000672
        (_root_.GD.N0230.N0660.d000882 μ₀ μ target) eL2 selected := by
    intro θ
    rw [← heL2Risk θ, ← hselectedRisk θ]
    exact hdom θ
  have heClass : eL2 = selected :=
    (_root_.GD.N0230.N0660.d000888 μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀).2.1
      eL2 heDominates
  have href : e =ᵐ[μ₀] selectedBorel := by
    have he_toLp : (fun ω => eL2 ω) =ᵐ[μ₀] e := by
      simpa only [eL2] using heMemLp.coeFn_toLp
    have he_selected : (fun ω => eL2 ω) =ᵐ[μ₀] fun ω => selected ω := by
      rw [heClass]
    have hselected_toBorel : (fun ω => selected ω) =ᵐ[μ₀] selectedBorel :=
      (_root_.GD.N0230.N0660.d000909
        μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ htarget).symm
    exact he_toLp.symm.trans (he_selected.trans hselected_toBorel)
  intro θ
  exact (hμ θ).ae_le href


theorem d000913
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (θ₀ : Θ) (benchmark : _root_.GD.N0230.N0660.d000880 μ₀)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0)
    (htarget : ∀ θ, target θ ∈ Set.Icc 0 1)
    (e : Ω → ℝ) (he : Measurable e)
    (_heRange : ∀ ω, e ω ∈ Set.Icc (0 : ℝ) 1)
    (hdom : ∀ θ,
      _root_.GD.N0230.N0660.d000904 (μ θ) (target θ) e ≤
        _root_.GD.N0230.N0660.d000904 (μ θ) (target θ)
          (_root_.GD.N0230.N0660.d000906
            μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀)) :
    ∀ θ,
      e =ᵐ[μ θ]
        _root_.GD.N0230.N0660.d000906
          μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ :=
  _root_.GD.N0230.N0660.d000912
    μ₀ μ target θ₀ benchmark hμ hμ₀ htarget₀ htarget e he hdom

#print axioms _root_.GD.N0230.N0660.d000888
#print axioms _root_.GD.N0230.N0660.d000896
#print axioms _root_.GD.N0230.N0660.d000913

end

end GD.N0230.N0660
