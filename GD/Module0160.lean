import GD.Module0052
import GD.Module0159
import Mathlib.Probability.Kernel.MeasurableIntegral






















open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace GD
namespace N0230
namespace N0642

noncomputable section

universe u v

variable {Omega : Type u} [MeasurableSpace Omega]
variable {Theta : Type v}

open _root_.GD.N0230.N0688 _root_.GD.N0230.N0636



structure d001800 (Omega : Type u) [MeasurableSpace Omega] where
  kernel : Kernel Omega ℝ
  isMarkov : IsMarkovKernel kernel
  memLp_id : ∀ omega, MemLp id 2 (kernel omega)

namespace d001800


def d001801 (rule : _root_.GD.N0230.N0642.d001800 Omega) (omega : Omega) :
    _root_.GD.N0230.N0688.d000642 where
  measure := rule.kernel omega
  isProbability := rule.isMarkov.isProbabilityMeasure omega
  memLp_id := rule.memLp_id omega


def d001802 (rule : _root_.GD.N0230.N0642.d001800 Omega) (omega : Omega) : ℝ :=
  (rule.d001801 omega).d000643


def d001803 (rule : _root_.GD.N0230.N0642.d001800 Omega) (omega : Omega) : ℝ :=
  (rule.d001801 omega).d000644


def d001804
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (target : ℝ) (omega : Omega) : ℝ :=
  (rule.d001801 omega).d000645 target

theorem d001805
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (omega : Omega) :
    rule.d001802 omega = ∫ a, a ∂rule.kernel omega := by
  rfl

theorem d001806
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (omega : Omega) :
    rule.d001803 omega = variance id (rule.kernel omega) := by
  rfl



theorem d001807
    (rule : _root_.GD.N0230.N0642.d001800 Omega) :
    StronglyMeasurable rule.d001802 := by
  letI : IsMarkovKernel rule.kernel := rule.isMarkov
  change StronglyMeasurable
    (fun omega : Omega => ∫ a : ℝ, a ∂rule.kernel omega)
  exact continuous_id.stronglyMeasurable.integral_kernel
    (κ := rule.kernel)

theorem d001808
    (rule : _root_.GD.N0230.N0642.d001800 Omega) :
    Measurable rule.d001802 :=
  rule.d001807.measurable



theorem d001809
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (omega : Omega) :
    rule.d001803 omega =
      (∫ a, a ^ 2 ∂rule.kernel omega) - (rule.d001802 omega) ^ 2 := by
  letI : IsProbabilityMeasure (rule.kernel omega) :=
    rule.isMarkov.isProbabilityMeasure omega
  simpa [_root_.GD.N0230.N0642.d001800.d001806, _root_.GD.N0230.N0642.d001800.d001805] using
    (variance_eq_sub (rule.memLp_id omega))


theorem d001810
    (rule : _root_.GD.N0230.N0642.d001800 Omega) :
    StronglyMeasurable rule.d001803 := by
  letI : IsMarkovKernel rule.kernel := rule.isMarkov
  have hsecond : StronglyMeasurable
      (fun omega : Omega => ∫ a, a ^ 2 ∂rule.kernel omega) :=
    (continuous_pow 2).stronglyMeasurable.integral_kernel
      (κ := rule.kernel)
  have hmean : StronglyMeasurable rule.d001802 :=
    rule.d001807
  have hsquare : StronglyMeasurable (fun omega => (rule.d001802 omega) ^ 2) := by
    exact (hmean.measurable.pow_const 2).stronglyMeasurable
  have heq : rule.d001803 =
      (fun omega : Omega =>
        (∫ a, a ^ 2 ∂rule.kernel omega) - (rule.d001802 omega) ^ 2) := by
    funext omega
    exact rule.d001809 omega
  rw [heq]
  exact hsecond.sub hsquare

theorem d001811
    (rule : _root_.GD.N0230.N0642.d001800 Omega) :
    Measurable rule.d001803 :=
  rule.d001810.measurable



def d001812
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (mu : Measure Omega) :
    _root_.GD.N0230.N0636.d000655 mu where
  actionLaw := rule.d001801
  dispersion_aemeasurable := rule.d001811.aemeasurable


def d001813
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (mu : Measure Omega) : ℝ≥0∞ :=
  (rule.d001812 mu).d000656



theorem d001814
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (mu : Measure Omega)
    (hzero : rule.d001813 mu = 0) :
    ∀ᵐ omega ∂mu,
      rule.kernel omega = Measure.dirac (rule.d001802 omega) := by
  exact
    (rule.d001812 mu).d000661
      hzero


theorem d001815
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (target : ℝ) (omega : Omega) :
    rule.d001804 target omega =
      (rule.d001802 omega - target) ^ 2 + rule.d001803 omega := by
  exact (rule.d001801 omega).d000650 target


theorem d001816
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (target : ℝ) :
    Measurable (rule.d001804 target) := by
  have hb : Measurable (fun omega : Omega =>
      (rule.d001802 omega - target) ^ 2) := by
    exact (rule.d001808.sub measurable_const).pow_const 2
  have hv : Measurable rule.d001803 := rule.d001811
  convert hb.add hv using 1
  funext omega
  exact rule.d001815 target omega


def d001817
    (mu : Measure Omega) (target : ℝ) (decision : Omega -> ℝ) : ℝ≥0∞ :=
  ∫⁻ omega, ENNReal.ofReal ((decision omega - target) ^ 2) ∂mu


def d001818
    (rule : _root_.GD.N0230.N0642.d001800 Omega)
    (mu : Measure Omega) (target : ℝ) : ℝ≥0∞ :=
  ∫⁻ omega,
    ENNReal.ofReal (rule.d001804 target omega) ∂mu

theorem d001819
    (rule : _root_.GD.N0230.N0642.d001800 Omega) (target : ℝ) :
    Measurable (fun omega : Omega =>
      ENNReal.ofReal ((rule.d001802 omega - target) ^ 2)) := by
  exact
    ((rule.d001808.sub measurable_const).pow_const 2).ennreal_ofReal

theorem d001820
    (rule : _root_.GD.N0230.N0642.d001800 Omega) :
    Measurable (fun omega : Omega =>
      ENNReal.ofReal (rule.d001803 omega)) :=
  rule.d001811.ennreal_ofReal





theorem d001821
    (rule : _root_.GD.N0230.N0642.d001800 Omega)
    (mu : Measure Omega) (target : ℝ) :
    rule.d001818 mu target =
      _root_.GD.N0230.N0642.d001800.d001817 mu target rule.d001802 +
        rule.d001813 mu := by
  rw [_root_.GD.N0230.N0642.d001800.d001818, _root_.GD.N0230.N0642.d001800.d001817, _root_.GD.N0230.N0642.d001800.d001813,
    _root_.GD.N0230.N0636.d000655.d000656]
  have hpoint : ∀ omega,
      ENNReal.ofReal (rule.d001804 target omega) =
        ENNReal.ofReal ((rule.d001802 omega - target) ^ 2) +
          ENNReal.ofReal (rule.d001803 omega) := by
    intro omega
    rw [rule.d001815 target omega]
    exact ENNReal.ofReal_add (sq_nonneg _) (variance_nonneg _ _)
  simp_rw [hpoint]
  exact lintegral_add_left
    (rule.d001819 target) _





def d001822
    (kappa : Kernel Omega ℝ) (target : ℝ) (omega : Omega) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal ((a - target) ^ 2) ∂kappa omega



def d001823
    (kappa : Kernel Omega ℝ) (mu : Measure Omega) (target : ℝ) : ℝ≥0∞ :=
  ∫⁻ omega, _root_.GD.N0230.N0642.d001800.d001822 kappa target omega ∂mu

theorem d001824
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa] (target : ℝ) :
    Measurable (_root_.GD.N0230.N0642.d001800.d001822 kappa target) := by
  have h : Measurable (fun p : Omega × ℝ =>
      ENNReal.ofReal ((p.2 - target) ^ 2)) := by
    fun_prop
  exact h.lintegral_kernel_prod_right' (κ := kappa)


def d001825
    (kappa : Kernel Omega ℝ) (target : ℝ) : Set Omega :=
  {omega | _root_.GD.N0230.N0642.d001800.d001822 kappa target omega < ∞}

theorem d001826
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa] (target : ℝ) :
    MeasurableSet (_root_.GD.N0230.N0642.d001800.d001825 kappa target) :=
  measurableSet_lt (_root_.GD.N0230.N0642.d001800.d001824 kappa target)
    measurable_const



theorem d001827
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa]
    (target : ℝ) {omega : Omega}
    (homega : omega ∈ _root_.GD.N0230.N0642.d001800.d001825 kappa target) :
    MemLp id 2 (kappa omega) := by
  have hne :
      (∫⁻ a, ENNReal.ofReal ((a - target) ^ 2) ∂kappa omega) ≠ ∞ :=
    (show _root_.GD.N0230.N0642.d001800.d001822 kappa target omega < ∞ from homega).ne
  have hint : Integrable (fun a : ℝ => (a - target) ^ 2) (kappa omega) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (by fun_prop)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).1 hne
  have hcenter : MemLp (fun a : ℝ => a - target) 2 (kappa omega) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hint
  have hsum : MemLp
      ((fun a : ℝ => a - target) + fun _ => target) 2 (kappa omega) :=
    hcenter.add (memLp_const target)
  have hfun : ((fun a : ℝ => a - target) + fun _ => target) = id := by
    funext a
    simp
  rw [hfun] at hsum
  exact hsum



theorem d001828
    (rule : _root_.GD.N0230.N0642.d001800 Omega)
    (target : ℝ) (omega : Omega) :
    ENNReal.ofReal (rule.d001804 target omega) =
      _root_.GD.N0230.N0642.d001800.d001822 rule.kernel target omega := by
  letI : IsProbabilityMeasure (rule.kernel omega) :=
    rule.isMarkov.isProbabilityMeasure omega
  have hmem : MemLp (fun a : ℝ => a - target) 2 (rule.kernel omega) :=
    (rule.memLp_id omega).sub (memLp_const target)
  have hint : Integrable (fun a : ℝ => (a - target) ^ 2)
      (rule.kernel omega) := hmem.integrable_sq
  exact ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)



theorem d001829
    (rule : _root_.GD.N0230.N0642.d001800 Omega)
    (mu : Measure Omega) (target : ℝ) :
    rule.d001818 mu target =
      _root_.GD.N0230.N0642.d001800.d001823 rule.kernel mu target := by
  unfold _root_.GD.N0230.N0642.d001800.d001818 _root_.GD.N0230.N0642.d001800.d001823
  apply lintegral_congr
  intro omega
  exact rule.d001828 target omega



theorem d001830
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa]
    (mu : Measure Omega) (target : ℝ)
    (hfinite : _root_.GD.N0230.N0642.d001800.d001823 kappa mu target ≠ ∞) :
    ∀ᵐ omega ∂mu, omega ∈ _root_.GD.N0230.N0642.d001800.d001825 kappa target := by
  have hlt : ∀ᵐ omega ∂mu,
      _root_.GD.N0230.N0642.d001800.d001822 kappa target omega < ∞ :=
    ae_lt_top (_root_.GD.N0230.N0642.d001800.d001824 kappa target) hfinite
  exact hlt



noncomputable def d001831
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa] (target : ℝ) :
    Kernel Omega ℝ := by
  classical
  exact Kernel.piecewise
    (_root_.GD.N0230.N0642.d001800.d001826 kappa target)
    kappa (Kernel.const Omega (Measure.dirac 0))

theorem d001832
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa] (target : ℝ)
    {omega : Omega} (homega : omega ∈ _root_.GD.N0230.N0642.d001800.d001825 kappa target) :
    _root_.GD.N0230.N0642.d001800.d001831 kappa target omega = kappa omega := by
  classical
  rw [_root_.GD.N0230.N0642.d001800.d001831, Kernel.piecewise_apply, if_pos homega]

theorem d001833
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa] (target : ℝ)
    {omega : Omega} (homega : omega ∉ _root_.GD.N0230.N0642.d001800.d001825 kappa target) :
    _root_.GD.N0230.N0642.d001800.d001831 kappa target omega = Measure.dirac 0 := by
  classical
  rw [_root_.GD.N0230.N0642.d001800.d001831, Kernel.piecewise_apply, if_neg homega]
  rfl



noncomputable def d001834
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa] (target : ℝ) :
    _root_.GD.N0230.N0642.d001800 Omega where
  kernel := _root_.GD.N0230.N0642.d001800.d001831 kappa target
  isMarkov := by
    classical
    unfold _root_.GD.N0230.N0642.d001800.d001831
    infer_instance
  memLp_id := by
    intro omega
    classical
    by_cases homega : omega ∈ _root_.GD.N0230.N0642.d001800.d001825 kappa target
    · rw [_root_.GD.N0230.N0642.d001800.d001832 kappa target homega]
      exact _root_.GD.N0230.N0642.d001800.d001827 kappa target homega
    · rw [_root_.GD.N0230.N0642.d001800.d001833 kappa target homega]
      apply (memLp_const 0).ae_eq
      exact (MeasureTheory.ae_eq_dirac id).symm



theorem d001835
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa]
    (mu : Measure Omega) (target : ℝ)
    (hgood : ∀ᵐ omega ∂mu, omega ∈ _root_.GD.N0230.N0642.d001800.d001825 kappa target) :
    _root_.GD.N0230.N0642.d001800.d001831 kappa target =ᵐ[mu] kappa := by
  filter_upwards [hgood] with omega homega
  exact _root_.GD.N0230.N0642.d001800.d001832 kappa target homega



theorem d001836
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa]
    (mu : Measure Omega) (target repairTarget : ℝ)
    (hgood : ∀ᵐ omega ∂mu, omega ∈ _root_.GD.N0230.N0642.d001800.d001825 kappa repairTarget) :
    _root_.GD.N0230.N0642.d001800.d001823 (_root_.GD.N0230.N0642.d001800.d001831 kappa repairTarget) mu target =
      _root_.GD.N0230.N0642.d001800.d001823 kappa mu target := by
  unfold _root_.GD.N0230.N0642.d001800.d001823
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0230.N0642.d001800.d001835 kappa mu repairTarget hgood]
    with omega homega
  unfold _root_.GD.N0230.N0642.d001800.d001822
  rw [homega]


def d001837
    (experiment : Theta -> Measure Omega)
    (target : Theta -> ℝ)
    (terminal : Omega -> ℝ) : Prop :=
  ∀ decision : Omega -> ℝ,
    Measurable decision ->
    (∀ theta,
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) decision <=
        _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal) ->
    ∀ theta, decision =ᵐ[experiment theta] terminal








theorem d001838
    (experiment : Theta -> Measure Omega)
    (target : Theta -> ℝ)
    (terminal : Omega -> ℝ)
    (rule : _root_.GD.N0230.N0642.d001800 Omega)
    (theta0 : Theta)
    (hterminal : _root_.GD.N0230.N0642.d001800.d001837 experiment target terminal)
    (hfinite :
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta0) (target theta0) terminal ≠ ∞)
    (hdom : ∀ theta,
      rule.d001818 (experiment theta) (target theta) <=
        _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal)
    (hAC : ∀ theta, experiment theta ≪ experiment theta0) :
    ∀ theta, ∀ᵐ omega ∂experiment theta,
      rule.kernel omega = Measure.dirac (terminal omega) := by
  have hbary_dom : ∀ theta,
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) rule.d001802 <=
        _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal := by
    intro theta
    calc
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) rule.d001802 <=
          _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) rule.d001802 +
            rule.d001813 (experiment theta) := le_self_add
      _ = rule.d001818 (experiment theta) (target theta) :=
        (rule.d001821
          (experiment theta) (target theta)).symm
      _ <= _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal :=
        hdom theta
  have hbary_eq : ∀ theta,
      rule.d001802 =ᵐ[experiment theta] terminal :=
    hterminal rule.d001802 rule.d001808 hbary_dom
  have hrisk_eq : ∀ theta,
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) rule.d001802 =
        _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal := by
    intro theta
    apply lintegral_congr_ae
    filter_upwards [hbary_eq theta] with omega homega
    simp [homega]
  have hsum :
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta0) (target theta0) terminal +
          rule.d001813 (experiment theta0) <=
        _root_.GD.N0230.N0642.d001800.d001817 (experiment theta0) (target theta0) terminal := by
    calc
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta0) (target theta0) terminal +
          rule.d001813 (experiment theta0) =
          _root_.GD.N0230.N0642.d001800.d001817 (experiment theta0) (target theta0) rule.d001802 +
            rule.d001813 (experiment theta0) := by
              rw [hrisk_eq theta0]
      _ = rule.d001818 (experiment theta0) (target theta0) :=
        (rule.d001821
          (experiment theta0) (target theta0)).symm
      _ <= _root_.GD.N0230.N0642.d001800.d001817 (experiment theta0) (target theta0) terminal :=
        hdom theta0
  have hdisp : rule.d001813 (experiment theta0) = 0 :=
    _root_.GD.N0232.N0719.N1001.d001795.d001797
      hfinite hsum
  have hdirac0 : ∀ᵐ omega ∂experiment theta0,
      rule.kernel omega = Measure.dirac (rule.d001802 omega) :=
    rule.d001814
      (experiment theta0) hdisp
  have hpure0 : ∀ᵐ omega ∂experiment theta0,
      rule.kernel omega = Measure.dirac (terminal omega) := by
    filter_upwards [hdirac0, hbary_eq theta0] with omega hkernel hbary
    simpa [hbary] using hkernel
  intro theta
  exact (hAC theta).ae_eq hpure0











theorem d001839
    (experiment : Theta -> Measure Omega)
    (target : Theta -> ℝ)
    (terminal : Omega -> ℝ)
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa]
    (theta0 : Theta)
    (hterminal : _root_.GD.N0230.N0642.d001800.d001837 experiment target terminal)
    (hfinite :
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta0) (target theta0) terminal ≠ ∞)
    (hdom : ∀ theta,
      _root_.GD.N0230.N0642.d001800.d001823 kappa (experiment theta) (target theta) ≤
        _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal)
    (hAC : ∀ theta, experiment theta ≪ experiment theta0) :
    ∀ theta, ∀ᵐ omega ∂experiment theta,
      kappa omega = Measure.dirac (terminal omega) := by
  have hrisk0 :
      _root_.GD.N0230.N0642.d001800.d001823 kappa (experiment theta0) (target theta0) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (hdom theta0)
    exact hfinite
  have hgood0 : ∀ᵐ omega ∂experiment theta0,
      omega ∈ _root_.GD.N0230.N0642.d001800.d001825 kappa (target theta0) :=
    _root_.GD.N0230.N0642.d001800.d001830
      kappa (experiment theta0) (target theta0) hrisk0
  have hgood : ∀ theta, ∀ᵐ omega ∂experiment theta,
      omega ∈ _root_.GD.N0230.N0642.d001800.d001825 kappa (target theta0) := by
    intro theta
    exact (hAC theta).ae_le hgood0
  let rule : _root_.GD.N0230.N0642.d001800 Omega :=
    _root_.GD.N0230.N0642.d001800.d001834 kappa (target theta0)
  have hdom_rule : ∀ theta,
      rule.d001818 (experiment theta) (target theta) ≤
        _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal := by
    intro theta
    rw [rule.d001829]
    change _root_.GD.N0230.N0642.d001800.d001823
        (_root_.GD.N0230.N0642.d001800.d001831 kappa (target theta0))
        (experiment theta) (target theta) ≤
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal
    rw [_root_.GD.N0230.N0642.d001800.d001836
      kappa (experiment theta) (target theta) (target theta0) (hgood theta)]
    exact hdom theta
  have hpure : ∀ theta, ∀ᵐ omega ∂experiment theta,
      rule.kernel omega = Measure.dirac (terminal omega) :=
    _root_.GD.N0230.N0642.d001800.d001838 experiment target terminal rule theta0
      hterminal hfinite hdom_rule hAC
  intro theta
  filter_upwards
      [_root_.GD.N0230.N0642.d001800.d001835
        kappa (experiment theta) (target theta0) (hgood theta),
       hpure theta]
      with omega hrepair hpureOmega
  change _root_.GD.N0230.N0642.d001800.d001831 kappa (target theta0) omega =
    Measure.dirac (terminal omega) at hpureOmega
  exact hrepair.symm.trans hpureOmega



theorem d001840
    (experiment : Theta -> Measure Omega)
    (target : Theta -> ℝ)
    (terminal : Omega -> ℝ)
    (rule : _root_.GD.N0230.N0642.d001800 Omega)
    (theta0 : Theta)
    (hterminal : _root_.GD.N0230.N0642.d001800.d001837 experiment target terminal)
    (hfinite :
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta0) (target theta0) terminal ≠ ∞)
    (hAC : ∀ theta, experiment theta ≪ experiment theta0)
    (hne : ¬ ∀ᵐ omega ∂experiment theta0,
      rule.kernel omega = Measure.dirac (terminal omega)) :
    ∃ theta,
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal <
        rule.d001818 (experiment theta) (target theta) := by
  by_contra hno
  apply hne
  have hdom : ∀ theta,
      rule.d001818 (experiment theta) (target theta) <=
        _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal := by
    intro theta
    exact le_of_not_gt (fun hlt => hno ⟨theta, hlt⟩)
  exact _root_.GD.N0230.N0642.d001800.d001838 experiment target terminal rule theta0
    hterminal hfinite hdom hAC theta0




theorem d001841
    (experiment : Theta -> Measure Omega)
    (target : Theta -> ℝ)
    (terminal : Omega -> ℝ)
    (kappa : Kernel Omega ℝ) [IsMarkovKernel kappa]
    (theta0 : Theta)
    (hterminal : _root_.GD.N0230.N0642.d001800.d001837 experiment target terminal)
    (hfinite :
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta0) (target theta0) terminal ≠ ∞)
    (hAC : ∀ theta, experiment theta ≪ experiment theta0)
    (hne : ¬ ∀ᵐ omega ∂experiment theta0,
      kappa omega = Measure.dirac (terminal omega)) :
    ∃ theta,
      _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal <
        _root_.GD.N0230.N0642.d001800.d001823 kappa (experiment theta) (target theta) := by
  by_contra hno
  apply hne
  have hdom : ∀ theta,
      _root_.GD.N0230.N0642.d001800.d001823 kappa (experiment theta) (target theta) ≤
        _root_.GD.N0230.N0642.d001800.d001817 (experiment theta) (target theta) terminal := by
    intro theta
    exact le_of_not_gt (fun hlt => hno ⟨theta, hlt⟩)
  exact _root_.GD.N0230.N0642.d001800.d001839
    experiment target terminal kappa theta0 hterminal hfinite hdom hAC theta0

end d001800

end

end N0642
end N0230
end GD

#print axioms _root_.GD.N0230.N0642.d001800.d001821
#print axioms _root_.GD.N0230.N0642.d001800.d001838
#print axioms _root_.GD.N0230.N0642.d001800.d001840
#print axioms _root_.GD.N0230.N0642.d001800.d001839
#print axioms _root_.GD.N0230.N0642.d001800.d001841
