import GD.Module1282
import GD.Module0867
import GD.Module1262
import GD.Module0791
import GD.Module1224

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0212.N0464

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0982 _root_.GD.N0232.N0719.N0862
open _root_.GD.N0212.N0462
open _root_.GD.N0232.N0720.N1290 (d004131)

noncomputable section
variable {k : ℕ}

abbrev d020727 (k : ℕ) := _root_.GD.N0232.N0719.N0873.d011295 (Fin k)

theorem d020728 (i : Fin k) :
    Continuous (fun z : _root_.GD.N0212.N0464.d020727 k × _root_.GD.N0232.N0719.N0983.d009709 k => (_root_.GD.N0232.N0719.N0983.d009710 i z.2 : ℝ)) :=
  (continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0983.d009711 i)).comp continuous_snd

theorem d020729 (i : Fin k) :
    Continuous (fun z : _root_.GD.N0212.N0464.d020727 k × _root_.GD.N0232.N0719.N0983.d009709 k => z.1.1 i) :=
  (continuous_apply i).comp (continuous_fst.comp continuous_fst)

theorem d020730 (i : Fin k) :
    Continuous (fun z : _root_.GD.N0212.N0464.d020727 k × _root_.GD.N0232.N0719.N0983.d009709 k => z.1.2 i) :=
  (continuous_apply i).comp (continuous_snd.comp continuous_fst)

theorem d020731 :
    Continuous (fun z : _root_.GD.N0212.N0464.d020727 k × _root_.GD.N0232.N0719.N0983.d009709 k => _root_.GD.N0232.N0719.N0983.d009713 z.1.1 z.2) :=
  continuous_finsetSum _ (fun i _ =>
    (_root_.GD.N0212.N0464.d020728 i).mul (_root_.GD.N0212.N0464.d020729 i))

theorem d020732 :
    Continuous (fun z : _root_.GD.N0212.N0464.d020727 k × _root_.GD.N0232.N0719.N0983.d009709 k => _root_.GD.N0232.N0719.N0983.d009714 z.1.1 z.1.2 z.2) :=
  (continuous_finsetSum _ (fun i _ =>
    (_root_.GD.N0212.N0464.d020728 i).mul (_root_.GD.N0212.N0464.d020730 i))).add
    (continuous_const.mul (continuous_finsetSum _ (fun i _ =>
      (_root_.GD.N0212.N0464.d020728 i).mul
        (((_root_.GD.N0212.N0464.d020729 i).sub _root_.GD.N0212.N0464.d020731).pow 2))))

theorem d020733 (q : ℝ) :
    ContinuousOn (fun z : _root_.GD.N0212.N0464.d020727 k × _root_.GD.N0232.N0719.N0983.d009709 k => _root_.GD.N0232.N0719.N0983.d009720 q z.1.1 z.1.2 z.2)
      (_root_.GD.N0232.N0719.N0982.d020342 ×ˢ univ) := by
  unfold _root_.GD.N0232.N0719.N0983.d009720
  exact _root_.GD.N0212.N0464.d020732.continuousOn.rpow_const
    (fun z hz => Or.inl (_root_.GD.N0232.N0719.N0983.d009718 z.1.1 z.1.2 hz.1 z.2).ne')

theorem d020734 (q : ℝ) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsFiniteMeasure μ] :
    ContinuousOn (fun x : _root_.GD.N0212.N0464.d020727 k => ∫ p, _root_.GD.N0232.N0719.N0983.d009720 q x.1 x.2 p ∂μ)
      _root_.GD.N0232.N0719.N0982.d020342 :=
  continuousOn_integral_of_compact_support
    (μ := μ) (f := fun (x : _root_.GD.N0212.N0464.d020727 k) (p : _root_.GD.N0232.N0719.N0983.d009709 k) => _root_.GD.N0232.N0719.N0983.d009720 q x.1 x.2 p)
    (s := _root_.GD.N0232.N0719.N0982.d020342) (k := Set.univ)
    isCompact_univ (_root_.GD.N0212.N0464.d020733 q)
    (fun _ p _ hp => (hp (mem_univ p)).elim)

theorem d020735 (q : ℝ) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsFiniteMeasure μ] :
    ContinuousOn (fun x : _root_.GD.N0212.N0464.d020727 k => ∫ p, _root_.GD.N0232.N0719.N0983.d009713 x.1 p * _root_.GD.N0232.N0719.N0983.d009720 q x.1 x.2 p ∂μ)
      _root_.GD.N0232.N0719.N0982.d020342 :=
  continuousOn_integral_of_compact_support
    (μ := μ) (f := fun (x : _root_.GD.N0212.N0464.d020727 k) (p : _root_.GD.N0232.N0719.N0983.d009709 k) =>
      _root_.GD.N0232.N0719.N0983.d009713 x.1 p * _root_.GD.N0232.N0719.N0983.d009720 q x.1 x.2 p)
    (s := _root_.GD.N0232.N0719.N0982.d020342) (k := Set.univ)
    isCompact_univ
    (_root_.GD.N0212.N0464.d020731.continuousOn.mul (_root_.GD.N0212.N0464.d020733 q))
    (fun _ p _ hp => (hp (mem_univ p)).elim)



theorem d020736 (q : ℝ) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
    [IsProbabilityMeasure μ] :
    ContinuousOn (_root_.GD.N0212.N0462.d020723 q μ) _root_.GD.N0232.N0719.N0982.d020342 := by
  change ContinuousOn (fun x : _root_.GD.N0212.N0464.d020727 k =>
    (∫ p, _root_.GD.N0232.N0719.N0983.d009713 x.1 p * _root_.GD.N0232.N0719.N0983.d009720 q x.1 x.2 p ∂μ) /
      (∫ p, _root_.GD.N0232.N0719.N0983.d009720 q x.1 x.2 p ∂μ)) _root_.GD.N0232.N0719.N0982.d020342
  exact (_root_.GD.N0212.N0464.d020735 q μ).div (_root_.GD.N0212.N0464.d020734 q μ)
    (fun x hx => (_root_.GD.N0232.N0719.N0983.d009728 q x.1 x.2 hx μ).ne')

theorem d020737 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, _root_.GD.N0232.N0719.N0986.d020362 sizes z ∈ _root_.GD.N0232.N0719.N0982.d020342 := by
  have hr : ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, ∀ i : Fin k,
      0 < _root_.GD.N0232.N0719.N0836.d011973 i z :=
    ae_all_iff.2 (fun i =>
      _root_.GD.N0232.N0719.N0832.d012011 k sizes hn θ i)
  filter_upwards [hr] with z hz
  intro i
  change 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i
  rw [_root_.GD.N0232.N0719.N0986.d020364]
  exact div_pos (hz i) (mul_pos (by norm_num) (by exact_mod_cast (show 0 < sizes i by have := hn i; omega)))

def d020738 (q : ℝ) (sizes : Fin k → ℕ)
    (z : _root_.GD.N0232.N0719.d009173 k sizes) (p : _root_.GD.N0232.N0719.N0983.d009709 k) : ℝ :=
  _root_.GD.N0232.N0719.N0983.d009720 q (_root_.GD.N0232.N0719.N0986.d020362 sizes z).1 (_root_.GD.N0232.N0719.N0986.d020362 sizes z).2 p

theorem d020739 (q : ℝ) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure μ] :
    _root_.GD.N0232.N0719.N0862.d013365 sizes μ _root_.GD.N0232.N0719.N0983.d009710 (_root_.GD.N0212.N0464.d020738 q sizes) := by
  have hr := _root_.GD.N0212.N0464.d020737 sizes hn (_root_.GD.N0232.N0719.N0859.d010810 k)
  change ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1), _ at hr
  filter_upwards [hr] with z hz
  exact ⟨_root_.GD.N0232.N0719.N0983.d009726 q _ _ hz μ, _root_.GD.N0232.N0719.N0983.d009728 q _ _ hz μ,
    ae_of_all _ (fun p => (_root_.GD.N0232.N0719.N0983.d009722 q _ _ hz p).le),
    fun i => _root_.GD.N0232.N0719.N0983.d009727 q _ _ hz μ i⟩

theorem d020740 (q : ℝ) (sizes : Fin k → ℕ)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsFiniteMeasure μ]
    (z : _root_.GD.N0232.N0719.d009173 k sizes) (hz : _root_.GD.N0232.N0719.N0986.d020362 sizes z ∈ _root_.GD.N0232.N0719.N0982.d020342) :
    _root_.GD.N0212.N0462.d020723 q μ (_root_.GD.N0232.N0719.N0986.d020362 sizes z) =
      ∑ i, _root_.GD.N0232.N0719.N0862.d013361 μ _root_.GD.N0232.N0719.N0983.d009710 (_root_.GD.N0212.N0464.d020738 q sizes z) i * _root_.GD.N0232.N0719.N0900.d009102 k sizes z i := by
  rw [_root_.GD.N0212.N0462.d020723, _root_.GD.N0232.N0719.N0983.d009730 q _ _ hz μ]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact _root_.GD.N0232.N0719.N0986.d020363 sizes z i



theorem d020741 (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hfm : Measurable f)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes))
    (s : Fin k → ℝ) (hs : ∀ i, 0 < s i) :
    MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 s) ∧
      (∫ z, f z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s) ≤
        ∫ z, _root_.GD.N0232.N0719.N0900.d009111 k sizes z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s := by
  let θ : _root_.GD.N0232.N0719.N0859.d010809 k := ⟨0, s, hs⟩
  have hb := _root_.GD.N0232.N0719.N0859.d010817 k sizes hk hn θ
  have hbi : Integrable (fun z => _root_.GD.N0232.N0719.N0900.d009111 k sizes z ^ 2)
      (_root_.GD.N0232.N0719.d009176 k sizes 0 s) := by
    apply (memLp_two_iff_integrable_sq (_root_.GD.N0232.N0719.N0900.d009122 k sizes).aestronglyMeasurable).mp
    simpa only [_root_.GD.N0232.N0719.N0859.d010815, _root_.GD.N0232.N0719.N0859.d010812, θ, sub_zero] using hb
  have hbase : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
      (_root_.GD.N0232.N0719.N0900.d009111 k sizes) =
      ENNReal.ofReal (∫ z, _root_.GD.N0232.N0719.N0900.d009111 k sizes z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s) := by
    simpa only [_root_.GD.N0232.N0719.N0859.d010840, _root_.GD.N0232.N0719.N0859.d010812,
      θ, sub_zero] using (ofReal_integral_eq_lintegral_ofReal hbi (ae_of_all _ fun _ => sq_nonneg _)).symm
  have h := _root_.GD.N0232.N0719.N0974.d019823 sizes θ f hfm _
    (integral_nonneg fun _ => sq_nonneg _) ((hcap θ).trans_eq hbase)
  simpa only [_root_.GD.N0232.N0719.N0859.d010812, θ, sub_zero] using h



theorem d020742 (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (q : ℝ) (μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes))
    (hrep : ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      f z = _root_.GD.N0212.N0462.d020723 q (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) (_root_.GD.N0232.N0719.N0986.d020362 sizes z)) :
    ∀ i : Fin k, ∀ c : ℝ, c < 1 →
      ¬ (∀ᵐ z : _root_.GD.N0232.N0720.N1290.d004131 ∂_root_.GD.N0232.N0719.N1006.d013356
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) _root_.GD.N0232.N0719.N0983.d009710 i, (z : ℝ) ≤ c) := by
  apply _root_.GD.N0232.N0719.N0862.d013367 sizes hn (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
    _root_.GD.N0232.N0719.N0983.d009710 (fun i => (_root_.GD.N0232.N0719.N0983.d009711 i).measurable) (_root_.GD.N0212.N0464.d020738 q sizes)
    (_root_.GD.N0212.N0464.d020739 q sizes hn (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)))
    (ae_of_all _ _root_.GD.N0232.N0719.N0983.d009712) f hfm
    (fun s hs => (_root_.GD.N0212.N0464.d020741 hk sizes hn f hfm hcap s hs).1)
    (fun s hs => (_root_.GD.N0212.N0464.d020741 hk sizes hn f hfm hcap s hs).2)
  have hr := _root_.GD.N0212.N0464.d020737 sizes hn (_root_.GD.N0232.N0719.N0859.d010810 k)
  change ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1), _ at hr
  filter_upwards [hrep, hr] with z hz hrz
  exact hz.trans (_root_.GD.N0212.N0464.d020740 q sizes (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) z hrz)

end
end GD.N0212.N0464

#print axioms _root_.GD.N0212.N0464.d020736
#print axioms _root_.GD.N0212.N0464.d020739
#print axioms _root_.GD.N0212.N0464.d020742
