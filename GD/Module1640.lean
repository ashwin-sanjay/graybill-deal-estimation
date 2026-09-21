import GD.Module1637
import GD.Module0160

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0079.N0321

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N1012
open _root_.GD.N0074
open _root_.GD.N0230.N0642
open _root_.GD.N0230.N0642.d001800

variable (k : ℕ) (sizes : Fin k → ℕ)

abbrev d028002 := _root_.GD.N0232.N0719.N0900.d009094 k sizes

theorem d028003
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (f : _root_.GD.N0079.N0321.d028002 k sizes → ℝ) (hf : Measurable f)
    (hfinite : _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location f ≠ ∞) :
    MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by unfold _root_.GD.N0232.N0719.N0859.d010812; infer_instance
  have hc : MemLp (fun x => f x - θ.location) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    exact (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).1 hfinite
  have hsum := hc.add (memLp_const θ.location)
  change MemLp (fun x => f x - θ.location + θ.location) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) at hsum
  simpa only [Pi.add_apply, sub_add_cancel] using hsum

theorem d028004
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (f g : _root_.GD.N0079.N0321.d028002 k sizes → ℝ)
    (hfg : f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] g) :
    _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location f =
      _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location g := by
  apply lintegral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

theorem d028005
    (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023612 k sizes) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location d.val =
      _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location
        (_root_.GD.N0074.d023620 k sizes hsizes d).val.val +
      ∫⁻ x, ENNReal.ofReal
        ((d.val x - (_root_.GD.N0074.d023620 k sizes hsizes d).val.val x) ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by unfold _root_.GD.N0232.N0719.N0859.d010812; infer_instance
  have hd := d.property θ
  have hp := (_root_.GD.N0074.d023620 k sizes hsizes d).val.property θ
  have hdc : Integrable (fun x => (d.val x - θ.location) ^ 2) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    simpa only [Pi.sub_apply] using (hd.sub (memLp_const θ.location)).integrable_sq
  have hpc : Integrable (fun x => ((_root_.GD.N0074.d023620 k sizes hsizes d).val.val x - θ.location) ^ 2)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    simpa only [Pi.sub_apply] using (hp.sub (memLp_const θ.location)).integrable_sq
  have hdr : Integrable
      (fun x => (d.val x - (_root_.GD.N0074.d023620 k sizes hsizes d).val.val x) ^ 2) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    simpa only [Pi.sub_apply] using (hd.sub hp).integrable_sq
  have hnonneg (f : _root_.GD.N0079.N0321.d028002 k sizes → ℝ) :
      ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, 0 ≤ f x ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  unfold _root_.GD.N0230.N0642.d001800.d001817
  rw [← ofReal_integral_eq_lintegral_ofReal hdc (hnonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hpc (hnonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hdr (hnonneg _)]
  rw [show (∫ x, (d.val x - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) =
      (∫ x, ((_root_.GD.N0074.d023620 k sizes hsizes d).val.val x - θ.location) ^ 2
        ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) +
      ∫ x, (d.val x - (_root_.GD.N0074.d023620 k sizes hsizes d).val.val x) ^ 2
        ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ from
    _root_.GD.N0074.d022926 k sizes hsizes θ d.val hd θ.location]
  exact ENNReal.ofReal_add (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)

def d028006
    (κ : Kernel (_root_.GD.N0079.N0321.d028002 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞) : _root_.GD.N0074.d023612 k sizes := by
  let r := _root_.GD.N0230.N0642.d001800.d001834 κ 0
  have hgood0 : ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes,
      x ∈ _root_.GD.N0230.N0642.d001800.d001825 κ 0 :=
    _root_.GD.N0230.N0642.d001800.d001830 κ _ 0 (hfinite (_root_.GD.N0232.N0719.N0859.d010810 k))
  have hgood (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ,
      x ∈ _root_.GD.N0230.N0642.d001800.d001825 κ 0 :=
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hgood0
  have hb (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : MemLp r.d001802 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    apply _root_.GD.N0079.N0321.d028003 k sizes θ r.d001802 r.d001808
    have hr : r.d001818 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location =
        _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location := by
      rw [r.d001829]
      exact _root_.GD.N0230.N0642.d001800.d001836 κ _ θ.location 0 (hgood θ)
    have hbnd : _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location r.d001802 ≤
        _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location := by
      rw [← hr, r.d001821]
      exact le_self_add
    exact ne_top_of_le_ne_top (hfinite θ) hbnd
  exact _root_.GD.N0074.d027958 k sizes r.d001802 hb

theorem d028007
    (κ : Kernel (_root_.GD.N0079.N0321.d028002 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ((_root_.GD.N0079.N0321.d028006 k sizes κ hfinite).val : _root_.GD.N0079.N0321.d028002 k sizes → ℝ)
      =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] _root_.GD.N0230.N0642.d001800.d001802 (_root_.GD.N0230.N0642.d001800.d001834 κ 0) := by
  unfold _root_.GD.N0079.N0321.d028006
  apply _root_.GD.N0074.d027959

theorem d028008
    (κ : Kernel (_root_.GD.N0079.N0321.d028002 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location =
      _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location
        (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite).val +
      _root_.GD.N0230.N0642.d001800.d001813 (_root_.GD.N0230.N0642.d001800.d001834 κ 0) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  have hgood0 : ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes,
      x ∈ _root_.GD.N0230.N0642.d001800.d001825 κ 0 :=
    _root_.GD.N0230.N0642.d001800.d001830 κ _ 0 (hfinite (_root_.GD.N0232.N0719.N0859.d010810 k))
  have hgood := (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hgood0
  rw [← _root_.GD.N0230.N0642.d001800.d001836 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location 0 hgood]
  change _root_.GD.N0230.N0642.d001800.d001823 (_root_.GD.N0230.N0642.d001800.d001834 κ 0).kernel (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location = _
  rw [← (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001829,
    (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001821,
    ← _root_.GD.N0079.N0321.d028004 k sizes θ _ _
      (_root_.GD.N0079.N0321.d028007 k sizes κ hfinite θ)]

theorem d028009
    (hsizes : ∀ i, 2 ≤ sizes i)
    (κ : Kernel (_root_.GD.N0079.N0321.d028002 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞) :
    ∃ h : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable h ∧
      (∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp (h ∘ _root_.GD.N0074.N0308.d022071 k sizes) 2
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location =
          _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location
            (h ∘ _root_.GD.N0074.N0308.d022071 k sizes) +
          (∫⁻ x, ENNReal.ofReal
            (((_root_.GD.N0079.N0321.d028006 k sizes κ hfinite).val x -
              (_root_.GD.N0074.d023620 k sizes hsizes
                (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val.val x) ^ 2)
              ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) +
          _root_.GD.N0230.N0642.d001800.d001813 (_root_.GD.N0230.N0642.d001800.d001834 κ 0) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  let d := _root_.GD.N0079.N0321.d028006 k sizes κ hfinite
  obtain ⟨h, hm, he⟩ := _root_.GD.N0074.d023628 k sizes hsizes d
  refine ⟨h, hm, ?_, ?_⟩
  · intro θ
    exact (memLp_congr_ae (he θ)).mp ((_root_.GD.N0074.d023620 k sizes hsizes d).val.property θ)
  · intro θ
    rw [_root_.GD.N0079.N0321.d028008 k sizes κ hfinite θ,
      _root_.GD.N0079.N0321.d028005 k sizes hsizes d θ,
      _root_.GD.N0079.N0321.d028004 k sizes θ _ _ (he θ)]

theorem d028010
    (hsizes : ∀ i, 2 ≤ sizes i)
    (κ : Kernel (_root_.GD.N0079.N0321.d028002 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location
      (_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val.val ≤
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location := by
  rw [_root_.GD.N0079.N0321.d028008 k sizes κ hfinite θ,
    _root_.GD.N0079.N0321.d028005 k sizes hsizes
      (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite) θ]
  exact le_trans le_self_add le_self_add

theorem d028011
    (hsizes : ∀ i, 2 ≤ sizes i)
    (κ : Kernel (_root_.GD.N0079.N0321.d028002 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞)
    (competitor : _root_.GD.N0079.N0321.d028002 k sizes → ℝ)
    (hdom : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≤
        _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location competitor)
    (hstrict : ∃ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location <
        _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location competitor) :
    (∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location
        (_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val.val ≤
      _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location competitor) ∧
    ∃ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location
        (_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val.val <
      _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location competitor := by
  constructor
  · intro θ
    exact (_root_.GD.N0079.N0321.d028010 k sizes hsizes κ hfinite θ).trans (hdom θ)
  · obtain ⟨θ, hθ⟩ := hstrict
    exact ⟨θ, (_root_.GD.N0079.N0321.d028010 k sizes hsizes κ hfinite θ).trans_lt hθ⟩

theorem d028012
    (hsizes : ∀ i, 2 ≤ sizes i)
    (κ : Kernel (_root_.GD.N0079.N0321.d028002 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞)
    (hno : _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 ≤
      _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0
        (_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val.val) :
    ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ,
      κ x = Measure.dirac
        ((_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val.val x) := by
  let θ0 := _root_.GD.N0232.N0719.N0859.d010810 k
  let μ := _root_.GD.N0232.N0719.N0859.d010812 k sizes θ0
  let d := _root_.GD.N0079.N0321.d028006 k sizes κ hfinite
  let p := _root_.GD.N0074.d023620 k sizes hsizes d
  let r := _root_.GD.N0230.N0642.d001800.d001834 κ 0
  let a := _root_.GD.N0230.N0642.d001800.d001817 μ 0 p.val.val
  let b := ∫⁻ x, ENNReal.ofReal ((d.val x - p.val.val x) ^ 2) ∂μ
  let c := r.d001813 μ
  have ha : a ≠ ∞ := ne_top_of_le_ne_top (hfinite θ0)
    (_root_.GD.N0079.N0321.d028010 k sizes hsizes κ hfinite θ0)
  have hsum : a + (b + c) ≤ a := by
    calc
      a + (b + c) = _root_.GD.N0230.N0642.d001800.d001823 κ μ 0 := by
        have he := _root_.GD.N0079.N0321.d028008 k sizes κ hfinite θ0
        rw [_root_.GD.N0079.N0321.d028005 k sizes hsizes d θ0] at he
        change _root_.GD.N0230.N0642.d001800.d001823 κ μ 0 = (a + b) + c at he
        exact (add_assoc _ _ _).symm.trans he.symm
      _ ≤ a := hno
  have hbc : b + c = 0 :=
    _root_.GD.N0232.N0719.N1001.d001795.d001797 ha hsum
  have hb : b = 0 := bot_unique (le_trans le_self_add hbc.le)
  have hc : c = 0 := bot_unique (le_trans le_add_self hbc.le)
  have hzero : (fun x => ENNReal.ofReal ((d.val x - p.val.val x) ^ 2))
      =ᵐ[μ] fun _ => 0 := by
    apply (lintegral_eq_zero_iff' ?_).1 hb
    exact (((d.property θ0).aestronglyMeasurable.sub
      (p.val.property θ0).aestronglyMeasurable).aemeasurable.pow_const 2).ennreal_ofReal
  have hdp : (d.val : _root_.GD.N0079.N0321.d028002 k sizes → ℝ) =ᵐ[μ] p.val.val := by
    filter_upwards [hzero] with x hx
    have hz : (d.val x - p.val.val x) ^ 2 = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (sq_nonneg _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hgood0 : ∀ᵐ x ∂μ, x ∈ _root_.GD.N0230.N0642.d001800.d001825 κ 0 :=
    _root_.GD.N0230.N0642.d001800.d001830 κ μ 0 (hfinite θ0)
  have hdirac : ∀ᵐ x ∂μ, κ x = Measure.dirac (p.val.val x) := by
    filter_upwards [_root_.GD.N0230.N0642.d001800.d001835 κ μ 0 hgood0,
      r.d001814 μ hc,
      _root_.GD.N0079.N0321.d028007 k sizes κ hfinite θ0, hdp]
      with x hrepair hpure hbary hsummary
    exact hrepair.symm.trans (hpure.trans (congrArg Measure.dirac (hbary.symm.trans hsummary)))
  intro θ
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hdirac

theorem d028013
    (hsizes : ∀ i, 2 ≤ sizes i)
    (κ : Kernel (_root_.GD.N0079.N0321.d028002 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞) :
    _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0
        (_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val.val <
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 ∨
    ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ,
      κ x = Measure.dirac
        ((_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val.val x) := by
  by_cases h : _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0
        (_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val.val <
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0
  · exact Or.inl h
  · exact Or.inr (_root_.GD.N0079.N0321.d028012
      k sizes hsizes κ hfinite (le_of_not_gt h))

end
end GD.N0079.N0321

#print axioms _root_.GD.N0079.N0321.d028003
#print axioms _root_.GD.N0079.N0321.d028004
#print axioms _root_.GD.N0079.N0321.d028005
#print axioms _root_.GD.N0079.N0321.d028007
#print axioms _root_.GD.N0079.N0321.d028008
#print axioms _root_.GD.N0079.N0321.d028009
#print axioms _root_.GD.N0079.N0321.d028010
#print axioms _root_.GD.N0079.N0321.d028011
#print axioms _root_.GD.N0079.N0321.d028012
#print axioms _root_.GD.N0079.N0321.d028013
