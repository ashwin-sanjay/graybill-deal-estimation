import GD.Module0737
import GD.Module0768
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
























open MeasureTheory Set Filter
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace GD
namespace N0232
namespace N0719
namespace N0814

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0821
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0718



theorem d011684
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (f : Lp ℝ 2 mu) :
    ‖f‖ ^ 2 =
      ENNReal.toReal (∫⁻ omega, (‖f omega‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂mu) := by
  rw [← real_inner_self_eq_norm_sq f]
  exact (MeasureTheory.L2.inner_def f f).trans
    (MeasureTheory.L2.integral_inner_eq_sq_eLpNorm f)

theorem d011685 (x : ℝ) :
    (‖x‖₊ : ℝ≥0∞) ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  change ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2)
  rw [← ofReal_norm x, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (norm_nonneg x) 2]
  simp only [Real.norm_eq_abs, sq_abs]




theorem d011686
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (h : Omega → ℝ) (hf : MemLp h 2 mu) :
    ‖MemLp.toLp h hf‖ ^ 2 =
      ENNReal.toReal (∫⁻ omega, ENNReal.ofReal (h omega ^ 2) ∂mu) := by
  rw [_root_.GD.N0232.N0719.N0814.d011684]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hf.coeFn_toLp] with omega homega
  simpa only [homega] using _root_.GD.N0232.N0719.N0814.d011685 (h omega)


def d011687
    (k : ℕ) (sizes : Fin k → ℕ) (active : Finset (Fin k))
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    (∀ i : ↑active, _root_.GD.N0137.d008894 (sizes i.1)) :=
  fun i ↦ omega i.1

theorem d011688
    (k : ℕ) (sizes : Fin k → ℕ) (active : Finset (Fin k)) :
    Measurable (_root_.GD.N0232.N0719.N0814.d011687 k sizes active) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.1


abbrev d011689
    (k : ℕ) (sizes : Fin k → ℕ) (active : Finset (Fin k)) :
    MeasurableSpace (_root_.GD.N0232.N0719.d009173 k sizes) :=
  MeasurableSpace.comap (_root_.GD.N0232.N0719.N0814.d011687 k sizes active) inferInstance

theorem d011690
    (k : ℕ) (sizes : Fin k → ℕ) (active : Finset (Fin k)) :
    _root_.GD.N0232.N0719.N0814.d011689 k sizes active ≤
      (inferInstance : MeasurableSpace (_root_.GD.N0232.N0719.d009173 k sizes)) :=
  (_root_.GD.N0232.N0719.N0814.d011688 k sizes active).comap_le




theorem d011691
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    MemLp (fun omega ↦ (_root_.GD.N0230.N0670.d001646 p q) omega)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  have hac := _root_.GD.N0232.N0719.N0859.d010814 k sizes theta
  have hpTop := _root_.GD.N0232.N0719.N0811.d011038 k sizes hk hsizes hp theta
  have hqTop := _root_.GD.N0232.N0719.N0811.d011038 k sizes hk hsizes hq theta
  have hpTop' :
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location p ≠ ⊤ := by
    exact hpTop
  have hqTop' :
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location q ≠ ⊤ := by
    exact hqTop
  have hidentity := _root_.GD.N0230.N0670.d001647
    hac theta.location p q
  have htaxLe :
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) ≤
        ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
              (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location p +
          ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
              (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location q := by
    calc
      _root_.GD.N0230.N0602.d000117
          (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) ≤
          _root_.GD.N0230.N0602.d000117
              (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
              (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location (_root_.GD.N0230.N0718.d001528 p q) +
            _root_.GD.N0230.N0602.d000117
              (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
              (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) :=
        le_add_left le_rfl
      _ = _ := hidentity
  have htaxTop :
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ htaxLe
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpTop',
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqTop'⟩
  have hmeas : AEStronglyMeasurable
      (fun omega ↦ (_root_.GD.N0230.N0670.d001646 p q) omega) (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
    (Lp.aestronglyMeasurable (_root_.GD.N0230.N0670.d001646 p q)).mono_ac hac
  apply (memLp_two_iff_integrable_sq hmeas).2
  have hfinite :
      (∫⁻ omega, ENNReal.ofReal (((_root_.GD.N0230.N0670.d001646 p q) omega) ^ 2)
        ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) ≠ ⊤ := by
    have hrisk :
        (∫⁻ omega, ENNReal.ofReal (((_root_.GD.N0230.N0670.d001646 p q) omega) ^ 2)
          ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) =
          _root_.GD.N0230.N0602.d000117
            (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
            (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) := by
      unfold _root_.GD.N0230.N0602.d000117
      apply lintegral_congr
      intro omega
      simp only [sub_zero]
      rfl
    rw [hrisk]
    exact htaxTop
  have hint := integrable_toReal_of_lintegral_ne_top
    ((hmeas.aemeasurable.pow_const 2).ennreal_ofReal) hfinite
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint



noncomputable def d011692
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    Lp ℝ 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
  MemLp.toLp (fun omega ↦ (_root_.GD.N0230.N0670.d001646 p q) omega)
    (_root_.GD.N0232.N0719.N0814.d011691 k sizes hk hsizes theta p q hp hq)



noncomputable def d011693
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    Lp ℝ 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
  (condExpL2 ℝ ℝ (_root_.GD.N0232.N0719.N0814.d011690 k sizes active)
    (_root_.GD.N0232.N0719.N0814.d011692 k sizes hk hsizes theta p q hp hq) :
      Lp ℝ 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta))




noncomputable def d011694
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    Lp ℝ 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
  _root_.GD.N0232.N0719.N0814.d011692 k sizes hk hsizes theta p q hp hq -
    _root_.GD.N0232.N0719.N0814.d011693 k sizes hk hsizes active theta p q hp hq


theorem d011695
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    ‖_root_.GD.N0232.N0719.N0814.d011692 k sizes hk hsizes theta p q hp hq‖ ^ 2 =
      ‖_root_.GD.N0232.N0719.N0814.d011693
        k sizes hk hsizes active theta p q hp hq‖ ^ 2 +
      ‖_root_.GD.N0232.N0719.N0814.d011694
        k sizes hk hsizes active theta p q hp hq‖ ^ 2 := by
  let f := _root_.GD.N0232.N0719.N0814.d011692 k sizes hk hsizes theta p q hp hq
  let S : Submodule ℝ (Lp ℝ 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)) :=
    lpMeas ℝ ℝ (_root_.GD.N0232.N0719.N0814.d011689 k sizes active) 2
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
  letI : Fact (_root_.GD.N0232.N0719.N0814.d011689 k sizes active ≤
      (inferInstance : MeasurableSpace (_root_.GD.N0232.N0719.d009173 k sizes))) :=
    ⟨_root_.GD.N0232.N0719.N0814.d011690 k sizes active⟩
  letI : S.HasOrthogonalProjection := by
    dsimp [S]
    infer_instance
  have hproj :
      _root_.GD.N0232.N0719.N0814.d011693 k sizes hk hsizes active theta p q hp hq =
        S.starProjection f := by
    rfl
  have horth :
      _root_.GD.N0232.N0719.N0814.d011694 k sizes hk hsizes active theta p q hp hq =
        Sᗮ.starProjection f := by
    unfold _root_.GD.N0232.N0719.N0814.d011694
    change f -
      _root_.GD.N0232.N0719.N0814.d011693 k sizes hk hsizes active theta p q hp hq = _
    rw [hproj]
    nth_rewrite 1 [← S.starProjection_add_starProjection_orthogonal f]
    abel
  rw [horth, hproj]
  exact S.norm_sq_eq_add_norm_sq_starProjection f


noncomputable def d011696
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) : ℝ :=
  ‖_root_.GD.N0232.N0719.N0814.d011693 k sizes hk hsizes active theta p q hp hq‖ ^ 2 /
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta


noncomputable def d011697
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) : ℝ :=
  ‖_root_.GD.N0232.N0719.N0814.d011694
      k sizes hk hsizes active theta p q hp hq‖ ^ 2 /
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta

theorem d011698
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    0 ≤ _root_.GD.N0232.N0719.N0814.d011696
      k sizes hk hsizes active theta p q hp hq := by
  unfold _root_.GD.N0232.N0719.N0814.d011696
  exact div_nonneg (sq_nonneg _)
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta).le

theorem d011699
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    0 ≤ _root_.GD.N0232.N0719.N0814.d011697
      k sizes hk hsizes active theta p q hp hq := by
  unfold _root_.GD.N0232.N0719.N0814.d011697
  exact div_nonneg (sq_nonneg _)
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta).le


theorem d011700
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    ‖_root_.GD.N0232.N0719.N0814.d011692 k sizes hk hsizes theta p q hp hq‖ ^ 2 =
      (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)).toReal := by
  unfold _root_.GD.N0232.N0719.N0814.d011692
  rw [_root_.GD.N0232.N0719.N0814.d011686]
  unfold _root_.GD.N0230.N0602.d000117
  congr 1
  apply lintegral_congr
  intro omega
  simp only [sub_zero]
  rfl



theorem d011701
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0814.d011696 k sizes hk hsizes active theta p q hp hq ≤
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q := by
  unfold _root_.GD.N0232.N0719.N0814.d011696 _root_.GD.N0232.N0719.N0811.d011037
  apply div_le_div_of_nonneg_right _
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta).le
  calc
    ‖_root_.GD.N0232.N0719.N0814.d011693 k sizes hk hsizes active theta p q hp hq‖ ^ 2 ≤
        ‖_root_.GD.N0232.N0719.N0814.d011692 k sizes hk hsizes theta p q hp hq‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
        (norm_condExpL2_coe_le (_root_.GD.N0232.N0719.N0814.d011690 k sizes active)
          (_root_.GD.N0232.N0719.N0814.d011692 k sizes hk hsizes theta p q hp hq))
    _ = (_root_.GD.N0230.N0602.d000117
          (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)).toReal :=
      _root_.GD.N0232.N0719.N0814.d011700 k sizes hk hsizes theta p q hp hq



theorem d011702
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0814.d011696 k sizes hk hsizes active theta p q hp hq +
        _root_.GD.N0232.N0719.N0814.d011697
          k sizes hk hsizes active theta p q hp hq =
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q := by
  unfold _root_.GD.N0232.N0719.N0814.d011696 _root_.GD.N0232.N0719.N0814.d011697
    _root_.GD.N0232.N0719.N0811.d011037
  rw [← add_div]
  rw [← _root_.GD.N0232.N0719.N0814.d011695
    k sizes hk hsizes active theta p q hp hq]
  rw [_root_.GD.N0232.N0719.N0814.d011700 k sizes hk hsizes theta p q hp hq]
  rfl

theorem d011703
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0814.d011697 k sizes hk hsizes active theta p q hp hq ≤
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q := by
  rw [← _root_.GD.N0232.N0719.N0814.d011702
    k sizes hk hsizes active theta p q hp hq]
  exact le_add_of_nonneg_left
    (_root_.GD.N0232.N0719.N0814.d011698
      k sizes hk hsizes active theta p q hp hq)



theorem d011704
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hzero : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0811.d011037
        k sizes hk hsizes (thetaSeq n) p q) atTop (nhds 0)) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0814.d011696
        k sizes hk hsizes active (thetaSeq n) p q hp hq) atTop (nhds 0) := by
  exact squeeze_zero
    (fun n ↦ _root_.GD.N0232.N0719.N0814.d011698
      k sizes hk hsizes active (thetaSeq n) p q hp hq)
    (fun n ↦ _root_.GD.N0232.N0719.N0814.d011701
      k sizes hk hsizes active (thetaSeq n) p q hp hq)
    hzero



theorem d011705
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hzero : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0811.d011037
        k sizes hk hsizes (thetaSeq n) p q) atTop (nhds 0)) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0814.d011697
        k sizes hk hsizes active (thetaSeq n) p q hp hq) atTop (nhds 0) := by
  exact squeeze_zero
    (fun n ↦ _root_.GD.N0232.N0719.N0814.d011699
      k sizes hk hsizes active (thetaSeq n) p q hp hq)
    (fun n ↦ _root_.GD.N0232.N0719.N0814.d011703
      k sizes hk hsizes active (thetaSeq n) p q hp hq)
    hzero











theorem d011706
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    (_root_.GD.N0232.N0719.N0814.d011696
          k sizes hk hsizes active theta p q hp hq = 0 ∧
        _root_.GD.N0232.N0719.N0814.d011697
          k sizes hk hsizes active theta p q hp hq = 0) ↔
      p = q := by
  constructor
  · rintro ⟨htrace, hresidual⟩
    by_contra hpq
    have hzero :
        _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q = 0 := by
      rw [← _root_.GD.N0232.N0719.N0814.d011702
        k sizes hk hsizes active theta p q hp hq, htrace, hresidual,
        zero_add]
    exact (ne_of_gt (_root_.GD.N0232.N0719.N0821.d011679
      k sizes hk hsizes hp hq hpq theta)) hzero
  · intro hpq
    subst q
    have hzero :
        _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p p = 0 := by
      simp [_root_.GD.N0232.N0719.N0811.d011037, _root_.GD.N0230.N0670.d001646, _root_.GD.N0230.N0602.d000117]
    have hsum := _root_.GD.N0232.N0719.N0814.d011702
      k sizes hk hsizes active theta p p hp hq
    have htraceNonneg := _root_.GD.N0232.N0719.N0814.d011698
      k sizes hk hsizes active theta p p hp hq
    have hresidualNonneg := _root_.GD.N0232.N0719.N0814.d011699
      k sizes hk hsizes active theta p p hp hq
    rw [hzero] at hsum
    constructor <;> linarith

end

end N0814
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0814.d011691
#print axioms _root_.GD.N0232.N0719.N0814.d011695
#print axioms _root_.GD.N0232.N0719.N0814.d011701
#print axioms _root_.GD.N0232.N0719.N0814.d011702
#print axioms _root_.GD.N0232.N0719.N0814.d011704
#print axioms _root_.GD.N0232.N0719.N0814.d011705
#print axioms _root_.GD.N0232.N0719.N0814.d011706
