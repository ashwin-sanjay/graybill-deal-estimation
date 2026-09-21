import GD.Module0245
import GD.Module0097
import GD.Module0735
import GD.Module0742
import GD.Module0776


























open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0719
namespace N0833

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0829
open _root_.GD.N0232.N0719.N0828
open _root_.GD.N0232.N0719.N0849
open _root_.GD.N0232.N0719.N0850
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0107
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0708
open _root_.GD.N0230.N0712
open _root_.GD.N0230.N0655




abbrev d011834 (k : ℕ) (sizes : Fin k → ℕ) :=
  _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)




structure d011835
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) where
  p : _root_.GD.N0232.N0719.d009173 k sizes → ℝ
  q : _root_.GD.N0232.N0719.d009173 k sizes → ℝ
  p_measurable : Measurable p
  q_measurable : Measurable q
  p_fixed : ∀ shift dilation : ℝ, 0 < dilation →
    _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation p = p
  p_feasible : _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes p
  q_dominates : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta q ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes theta p
  q_ne_p : q ≠ p

variable
  {k : ℕ} {sizes : Fin k → ℕ}
  {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}



theorem d011836
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    ∀ eta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes eta
          (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation data.q) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes eta data.p := by
  intro eta
  let theta : _root_.GD.N0232.N0719.N0859.d010809 k :=
    _root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹
      (inv_pos.mpr hdilation) eta
  have heta : _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta = eta :=
    _root_.GD.N0232.N0719.N0842.d010919 shift dilation hdilation eta
  calc
    _root_.GD.N0232.N0719.N0859.d010840 k sizes eta
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation data.q) =
        ENNReal.ofReal (dilation ^ 2) *
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta data.q := by
            rw [← heta]
            exact _root_.GD.N0232.N0719.N0842.d010920
              k sizes shift dilation hdilation theta data.q
                data.q_measurable
    _ ≤ ENNReal.ofReal (dilation ^ 2) *
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta data.p :=
      mul_le_mul_left' (data.q_dominates theta) _
    _ = _root_.GD.N0232.N0719.N0859.d010840 k sizes eta
          (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation data.p) := by
            rw [← heta]
            exact (_root_.GD.N0232.N0719.N0842.d010920
              k sizes shift dilation hdilation theta data.p
                data.p_measurable).symm
    _ = _root_.GD.N0232.N0719.N0859.d010840 k sizes eta data.p := by
      rw [data.p_fixed shift dilation hdilation]



theorem d011837
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation data.q) := by
  intro theta
  exact (_root_.GD.N0232.N0719.N0833.d011836 data shift dilation hdilation theta).trans
    (data.p_feasible theta)


theorem d011835.d011838
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes data.q := by
  intro theta
  exact (data.q_dominates theta).trans (data.p_feasible theta)


def d011835.d011839
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    MemLp data.p 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  simpa [_root_.GD.N0232.N0719.N0859.d010813] using
    (_root_.GD.N0232.N0719.N0849.d011774 k sizes hk hsizes data.p
      data.p_measurable data.p_feasible)


def d011835.d011840
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0833.d011834 k sizes :=
  MemLp.toLp data.p data.d011839


def d011835.d011841
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    MemLp data.q 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  simpa [_root_.GD.N0232.N0719.N0859.d010813] using
    (_root_.GD.N0232.N0719.N0849.d011774 k sizes hk hsizes data.q
      data.q_measurable data.d011838)


def d011835.d011842
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0833.d011834 k sizes :=
  MemLp.toLp data.q data.d011841


def d011835.d011843
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 g.2.1 data.q

theorem d011835.d011844
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    Measurable (data.d011843 g) :=
  _root_.GD.N0232.N0719.N0842.d010912 k sizes g.1 g.2.1 data.q data.q_measurable

theorem d011835.d011845
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes (data.d011843 g) :=
  _root_.GD.N0232.N0719.N0833.d011837 data g.1 g.2.1 g.2.2





theorem d011846
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    Measure.QuasiMeasurePreserving
      (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation)
      (_root_.GD.N0232.N0719.d009182 k sizes)
      (_root_.GD.N0232.N0719.d009182 k sizes) := by
  refine ⟨_root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation, ?_⟩
  unfold _root_.GD.N0232.N0719.d009182
  rw [_root_.GD.N0232.N0719.d009188]
  simpa using
    (_root_.GD.N0232.N0719.d009181
      k sizes shift 0 (fun _ ↦ dilation) (fun _ ↦ 1)
      (fun _ ↦ hdilation.ne') (fun _ ↦ one_ne_zero))




theorem d011847
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    {p q : _root_.GD.N0232.N0719.d009173 k sizes → ℝ}
    (htransport :
      _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation p =ᵐ[
        _root_.GD.N0232.N0719.d009182 k sizes]
      _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation q) :
    p =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes] q := by
  have hpull :=
    (_root_.GD.N0232.N0719.N0833.d011846
      k sizes shift dilation hdilation).ae_eq htransport
  filter_upwards [hpull] with omega homega
  change
    _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation p
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) =
      _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation q
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) at homega
  rw [_root_.GD.N0232.N0719.N0842.d010913
      k sizes shift dilation hdilation.ne' p omega,
    _root_.GD.N0232.N0719.N0842.d010913
      k sizes shift dilation hdilation.ne' q omega] at homega
  exact (mul_left_cancel₀ hdilation.ne') (by linarith)




def d011835.d011848
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    MemLp (data.d011843 g) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  simpa [_root_.GD.N0232.N0719.N0859.d010813] using
    (_root_.GD.N0232.N0719.N0849.d011774 k sizes hk hsizes (data.d011843 g)
      (data.d011844 g) (data.d011845 g))



theorem d011835.d011849
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    MemLp data.q 2
      ((_root_.GD.N0232.N0719.d009182 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2.1)) := by
  have horbit : MemLp (data.d011843 g) 2
      (_root_.GD.N0232.N0719.d009182 k sizes) := by
    simpa [_root_.GD.N0232.N0719.N0859.d010813] using data.d011848 g
  have hcentered : MemLp
      (fun omega ↦ data.d011843 g omega - g.1) 2
      (_root_.GD.N0232.N0719.d009182 k sizes) :=
    horbit.sub (memLp_const g.1)
  have hscaled : MemLp
      (fun omega ↦ (g.2.1)⁻¹ *
        (data.d011843 g omega - g.1)) 2
      (_root_.GD.N0232.N0719.d009182 k sizes) :=
    hcentered.const_mul (g.2.1)⁻¹
  have hcomp : MemLp
      (data.q ∘ _root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2.1) 2
      (_root_.GD.N0232.N0719.d009182 k sizes) := by
    have hgpos : 0 < (g.2.1 : ℝ) := g.2.2
    simpa [_root_.GD.N0232.N0719.N0833.d011835.d011843, _root_.GD.N0232.N0719.N0842.d010911,
      Function.comp_def, hgpos.ne'] using hscaled
  exact (memLp_map_measure_iff
    data.q_measurable.aestronglyMeasurable
    (_root_.GD.N0232.N0719.N0842.d010908 k sizes g.1 g.2.1).aemeasurable).2 hcomp



def d011835.d011850
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) : _root_.GD.N0232.N0719.N0833.d011834 k sizes :=
  MemLp.toLp (data.d011843 g) (data.d011848 g)

theorem d011835.d011851
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    data.d011840 ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes :=
  fun theta ↦ by
    have hraw := data.p_feasible theta
    rw [_root_.GD.N0232.N0719.N0859.d010841 k sizes theta data.p data.d011839] at hraw
    simpa [_root_.GD.N0232.N0719.N0833.d011835.d011840] using hraw

theorem d011835.d011852
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    data.d011850 g ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes :=
  fun theta ↦ by
    have hraw := data.d011845 g theta
    rw [_root_.GD.N0232.N0719.N0859.d010841
      k sizes theta (data.d011843 g) (data.d011848 g)] at hraw
    simpa [_root_.GD.N0232.N0719.N0833.d011835.d011850] using hraw



theorem d011835.d011853
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (data.d011850 g) ≤
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta data.d011840 := by
  intro theta
  have hraw := _root_.GD.N0232.N0719.N0833.d011836
    data g.1 g.2.1 g.2.2 theta
  change _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (data.d011843 g) ≤
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta data.p at hraw
  rw [_root_.GD.N0232.N0719.N0859.d010841
      k sizes theta (data.d011843 g) (data.d011848 g),
    _root_.GD.N0232.N0719.N0859.d010841
      k sizes theta data.p data.d011839] at hraw
  simpa [_root_.GD.N0232.N0719.N0833.d011835.d011850,
    _root_.GD.N0232.N0719.N0833.d011835.d011840] using hraw




def d011835.d011854
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    Set (_root_.GD.N0232.N0719.N0833.d011834 k sizes) :=
  {d | ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes theta data.d011840}

theorem d011835.d011855
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    data.d011850 g ∈ data.d011854 :=
  data.d011853 g

theorem d011835.d011856
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    IsClosed data.d011854 := by
  simpa [_root_.GD.N0232.N0719.N0833.d011835.d011854, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta ↦ _root_.GD.N0232.N0719.N0859.d010821 k sizes theta data.d011840)
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))

theorem d011835.d011857
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    Convex ℝ data.d011854 := by
  simpa [_root_.GD.N0232.N0719.N0833.d011835.d011854, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta ↦ _root_.GD.N0232.N0719.N0859.d010821 k sizes theta data.d011840)
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))

theorem d011835.d011858
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    data.d011854 ⊆ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
  intro d hd theta
  exact (hd theta).trans (data.d011851 theta)




theorem d011835.d011859
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    {d : _root_.GD.N0232.N0719.N0833.d011834 k sizes} (hd : d ∈ data.d011854) :
    ‖d‖ ≤ _root_.GD.N0232.N0719.N0858.d011032 k sizes hk hsizes :=
  _root_.GD.N0232.N0719.N0858.d011034 k sizes hk hsizes d
    (data.d011858 hd)



theorem d011835.d011860
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    ‖data.d011850 g‖ ≤ _root_.GD.N0232.N0719.N0858.d011032 k sizes hk hsizes :=
  data.d011859
    (data.d011855 g)




theorem d011835.d011861
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    ‖data.d011850 g - data.d011840‖ ≤
      2 * _root_.GD.N0232.N0719.N0858.d011032 k sizes hk hsizes := by
  calc
    ‖data.d011850 g - data.d011840‖ ≤
        ‖data.d011850 g‖ + ‖data.d011840‖ := norm_sub_le _ _
    _ ≤ _root_.GD.N0232.N0719.N0858.d011032 k sizes hk hsizes +
        _root_.GD.N0232.N0719.N0858.d011032 k sizes hk hsizes :=
      add_le_add
        (data.d011860 g)
        (_root_.GD.N0232.N0719.N0858.d011034 k sizes hk hsizes
          data.d011840 data.d011851)
    _ = 2 * _root_.GD.N0232.N0719.N0858.d011032 k sizes hk hsizes := by ring


def d011835.d011862
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    Set (WeakSpace ℝ (_root_.GD.N0232.N0719.N0833.d011834 k sizes)) :=
  toWeakSpace ℝ (_root_.GD.N0232.N0719.N0833.d011834 k sizes) '' data.d011854

theorem d011835.d011863
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    IsClosed data.d011862 :=
  _root_.GD.N0230.N0708.d001175
    data.d011857 data.d011856

theorem d011835.d011864
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    data.d011862 ⊆
      toWeakSpace ℝ (_root_.GD.N0232.N0719.N0833.d011834 k sizes) ''
        _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
  rintro _ ⟨d, hd, rfl⟩
  exact ⟨d, data.d011858 hd, rfl⟩




theorem d011835.d011865
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    IsCompact data.d011862 :=
  IsCompact.of_isClosed_subset
    (_root_.GD.N0232.N0719.N0858.d011035 k sizes hk hsizes)
    data.d011863
    data.d011864

theorem d011835.d011866
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    toWeakSpace ℝ (_root_.GD.N0232.N0719.N0833.d011834 k sizes) (data.d011850 g) ∈
      data.d011862 :=
  ⟨data.d011850 g, data.d011855 g, rfl⟩



def d011835.d011867
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ g : _root_.GD.N0230.N0655.d000349,
    epsilon ≤ ‖data.d011850 g - data.d011840‖



def d011835.d011868
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) : Prop :=
  ∃ g : ℕ → _root_.GD.N0230.N0655.d000349,
    Tendsto
      (fun n ↦ ‖data.d011850 (g n) - data.d011840‖)
      atTop (nhds 0)














theorem d011835.d011869
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (hne : data.d011842 ≠ data.d011840)
    (g : ℕ → _root_.GD.N0230.N0655.d000349)
    (hzero : Tendsto
      (fun n ↦ ‖data.d011850 (g n) - data.d011840‖)
      atTop (nhds 0))
    (limitParameter : _root_.GD.N0230.N0655.d000349)
    (hparameter : Tendsto g atTop (nhds limitParameter)) : False := by
  have hLp : Tendsto (fun n ↦ data.d011850 (g n)) atTop
      (nhds data.d011840) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hzero
  have hmeasureCanonical : TendstoInMeasure
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (fun n ↦ data.d011850 (g n)) atTop data.d011840 :=
    tendstoInMeasure_of_tendsto_Lp hLp
  have hmeasureRawCanonical : TendstoInMeasure
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (fun n ↦ data.d011843 (g n)) atTop data.p :=
    TendstoInMeasure.congr
      (fun n ↦ (data.d011848 (g n)).coeFn_toLp)
      data.d011839.coeFn_toLp hmeasureCanonical
  have hmeasureRaw : TendstoInMeasure
      (_root_.GD.N0232.N0719.d009182 k sizes)
      (fun n ↦ data.d011843 (g n)) atTop data.p := by
    simpa [_root_.GD.N0232.N0719.N0859.d010813] using hmeasureRawCanonical
  have hcontinuous : TendstoInMeasure
      (_root_.GD.N0232.N0719.d009182 k sizes)
      (fun n ↦ data.d011843 (g n)) atTop
      (data.d011843 limitParameter) := by
    exact _root_.GD.N0232.N0719.N0829.d011030
      k sizes g limitParameter hparameter data.q data.q_measurable
      (by norm_num) (by norm_num)
      (data.d011849 limitParameter) (by infer_instance)
  have hlimit : data.d011843 limitParameter =ᵐ[
      _root_.GD.N0232.N0719.d009182 k sizes] data.p :=
    tendstoInMeasure_ae_unique hcontinuous hmeasureRaw
  have hpToTransport : data.p =ᵐ[
      _root_.GD.N0232.N0719.d009182 k sizes]
      _root_.GD.N0232.N0719.N0842.d010911 k sizes limitParameter.1 limitParameter.2.1 data.p :=
    Filter.EventuallyEq.of_eq
      (data.p_fixed limitParameter.1 limitParameter.2.1
        limitParameter.2.2).symm
  have htransport :
      _root_.GD.N0232.N0719.N0842.d010911 k sizes limitParameter.1 limitParameter.2.1 data.q =ᵐ[
        _root_.GD.N0232.N0719.d009182 k sizes]
      _root_.GD.N0232.N0719.N0842.d010911 k sizes limitParameter.1 limitParameter.2.1 data.p :=
    hlimit.trans hpToTransport
  have hqp : data.q =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes] data.p :=
    _root_.GD.N0232.N0719.N0833.d011847
      k sizes limitParameter.1 limitParameter.2.1
        limitParameter.2.2 htransport
  apply hne
  exact MemLp.toLp_congr data.d011841 data.d011839 <| by
    simpa [_root_.GD.N0232.N0719.N0859.d010813] using hqp



theorem d011835.d011870
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (hne : data.d011842 ≠ data.d011840)
    (g : ℕ → _root_.GD.N0230.N0655.d000349)
    (hzero : Tendsto
      (fun n ↦ ‖data.d011850 (g n) - data.d011840‖)
      atTop (nhds 0)) :
    ¬ ∃ (subseq : ℕ → ℕ) (limitParameter : _root_.GD.N0230.N0655.d000349),
      Tendsto subseq atTop atTop ∧
      Tendsto (g ∘ subseq) atTop (nhds limitParameter) := by
  rintro ⟨subseq, limitParameter, hsubseq, hparameter⟩
  exact data.d011869 hne
    (g ∘ subseq) (hzero.comp hsubseq) limitParameter hparameter














theorem d011835.d011871
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (hne : data.d011842 ≠ data.d011840)
    (g : ℕ → _root_.GD.N0230.N0655.d000349)
    (hzero : Tendsto
      (fun n ↦ ‖data.d011850 (g n) - data.d011840‖)
      atTop (nhds 0))
    (R epsilon M : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop,
      R < |(g n).1| ∨ (g n).2.1 < epsilon ∨ M < (g n).2.1 := by
  by_contra hnot
  have hfrequent : ∃ᶠ n in atTop,
      ¬ (R < |(g n).1| ∨ (g n).2.1 < epsilon ∨ M < (g n).2.1) :=
    not_eventually.mp hnot
  let coordinate : ℕ → ℝ × ℝ := fun n ↦ ((g n).1, (g n).2.1)
  have hfrequentRectangle : ∃ᶠ n in atTop,
      coordinate n ∈ Set.Icc (-R) R ×ˢ Set.Icc epsilon M := by
    apply hfrequent.mono
    intro n hn
    simp only [not_or, not_lt] at hn
    have hshift : |(g n).1| ≤ R := hn.1
    exact ⟨⟨(abs_le.mp hshift).1, (abs_le.mp hshift).2⟩,
      ⟨hn.2.1, hn.2.2⟩⟩
  have hcompact : IsCompact (Set.Icc (-R) R ×ˢ Set.Icc epsilon M) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨limit, hlimitMem, subseq, hsubseqMono, hcoordinate⟩ :=
    hcompact.tendsto_subseq' hfrequentRectangle
  have hlimitScale : 0 < limit.2 :=
    lt_of_lt_of_le hepsilon hlimitMem.2.1
  let limitParameter : _root_.GD.N0230.N0655.d000349 :=
    (limit.1, ⟨limit.2, hlimitScale⟩)
  have hparameter : Tendsto (g ∘ subseq) atTop (nhds limitParameter) := by
    apply (Prod.tendsto_iff (g ∘ subseq) limitParameter).2
    constructor
    · have hfirst := (continuous_fst.tendsto limit).comp hcoordinate
      simpa [coordinate, limitParameter, Function.comp_def] using hfirst
    · apply tendsto_subtype_rng.2
      have hsecond := (continuous_snd.tendsto limit).comp hcoordinate
      simpa [coordinate, limitParameter, Function.comp_def] using hsecond
  exact data.d011870
    hne g hzero ⟨subseq, limitParameter,
      hsubseqMono.tendsto_atTop, hparameter⟩



theorem d011835.d011872
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (hnot : ¬ data.d011867) :
    data.d011868 := by
  unfold _root_.GD.N0232.N0719.N0833.d011835.d011867 at hnot
  push Not at hnot
  have hchoice : ∀ n : ℕ, ∃ g : _root_.GD.N0230.N0655.d000349,
      ‖data.d011850 g - data.d011840‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    exact hnot (1 / ((n : ℝ) + 1)) (by positivity)
  choose g hg using hchoice
  refine ⟨g, squeeze_zero
    (fun n ↦ norm_nonneg (data.d011850 (g n) - data.d011840))
    (fun n ↦ (hg n).le) ?_⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat




theorem d011835.d011873
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    data.d011867 ∨ data.d011868 := by
  by_cases hcapacity : data.d011867
  · exact Or.inl hcapacity
  · exact Or.inr (data.d011872 hcapacity)



theorem d011835.d011874
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes) :
    ¬ data.d011868 ↔ data.d011867 := by
  constructor
  · intro hno
    rcases data.d011873 with hcap | hcoal
    · exact hcap
    · exact (hno hcoal).elim
  · rintro ⟨epsilon, hepsilon, hlower⟩ ⟨g, hzero⟩
    have hsmall : ∀ᶠ n in atTop,
        ‖data.d011850 (g n) - data.d011840‖ < epsilon :=
      (tendsto_order.1 hzero).2 epsilon hepsilon
    obtain ⟨n, hn⟩ := hsmall.exists
    exact (not_lt_of_ge (hlower (g n))) hn

end

end N0833
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0833.d011836
#print axioms _root_.GD.N0232.N0719.N0833.d011835.d011853
#print axioms _root_.GD.N0232.N0719.N0833.d011835.d011865
#print axioms _root_.GD.N0232.N0719.N0833.d011835.d011873
#print axioms _root_.GD.N0232.N0719.N0833.d011835.d011874
