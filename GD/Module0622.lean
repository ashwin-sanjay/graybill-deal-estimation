import GD.Module0615
import GD.Module0597














open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0119

noncomputable section

open _root_.GD.N0118
open _root_.GD.N0137

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]




def d009065
    (s : Finset ι)
    (center₁ center₂ width coeff : ι → ℝ) :
    ℝ × ℝ → ℝ :=
  fun p =>
    ∑ i ∈ s,
      coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) (width i) p

theorem d009066
    (s : Finset ι)
    (center₁ center₂ width coeff : ι → ℝ) :
    Measurable (_root_.GD.N0119.d009065 s center₁ center₂ width coeff) := by
  unfold _root_.GD.N0119.d009065
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.mul
    (_root_.GD.N0118.d008590 (center₁ i) (center₂ i) (width i))


theorem d009067
    (c w x : ℝ) (hw : 0 < w) :
    |_root_.GD.N0118.d008582 c w x| ≤ 1 / w := by
  by_cases hL : x ∈ Ioc (c - w) c
  · have hR : x ∉ Ioc c (c + w) := by
      intro hx
      linarith [hL.2, hx.1]
    rw [show _root_.GD.N0118.d008582 c w x = _root_.GD.N0118.d008580 c w x by
      simp [_root_.GD.N0118.d008582, hL, hR]]
    unfold _root_.GD.N0118.d008580
    rw [abs_of_nonneg (div_nonneg (by linarith [hL.1])
      (sq_nonneg w))]
    rw [div_le_div_iff₀ (sq_pos_of_pos hw) hw]
    nlinarith [hL.2]
  · by_cases hR : x ∈ Ioc c (c + w)
    · rw [show _root_.GD.N0118.d008582 c w x = _root_.GD.N0118.d008581 c w x by
        simp [_root_.GD.N0118.d008582, hL, hR]]
      unfold _root_.GD.N0118.d008581
      rw [abs_of_nonneg (div_nonneg (by linarith [hR.2])
        (sq_nonneg w))]
      rw [div_le_div_iff₀ (sq_pos_of_pos hw) hw]
      nlinarith [hR.1]
    · rw [show _root_.GD.N0118.d008582 c w x = 0 by simp [_root_.GD.N0118.d008582, hL, hR], abs_zero]
      exact one_div_nonneg.mpr hw.le


theorem d009068
    (c₁ c₂ w : ℝ) (p : ℝ × ℝ) (hw : 0 < w) :
    |_root_.GD.N0118.d008583 c₁ c₂ w p| ≤ 1 / w ^ 2 := by
  unfold _root_.GD.N0118.d008583
  rw [abs_mul]
  calc
    |_root_.GD.N0118.d008582 c₁ w p.1| * |_root_.GD.N0118.d008582 c₂ w p.2|
        ≤ (1 / w) * (1 / w) :=
      mul_le_mul
        (_root_.GD.N0119.d009067 c₁ w p.1 hw)
        (_root_.GD.N0119.d009067 c₂ w p.2 hw)
        (abs_nonneg _) (le_of_lt (one_div_pos.mpr hw))
    _ = 1 / w ^ 2 := by ring



theorem d009069
    (s : Finset ι)
    (center₁ center₂ width coeff : ι → ℝ)
    (hwidth : ∀ i ∈ s, 0 < width i)
    (p : ℝ × ℝ) :
    |_root_.GD.N0119.d009065 s center₁ center₂ width coeff p|
      ≤ ∑ i ∈ s, |coeff i| / (width i) ^ 2 := by
  unfold _root_.GD.N0119.d009065
  calc
    |∑ i ∈ s,
        coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) (width i) p|
        ≤ ∑ i ∈ s,
          |coeff i *
            _root_.GD.N0118.d008583 (center₁ i) (center₂ i) (width i) p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |coeff i| / (width i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      calc
        |coeff i| *
            |_root_.GD.N0118.d008583 (center₁ i) (center₂ i) (width i) p|
            ≤ |coeff i| * (1 / (width i) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (_root_.GD.N0119.d009068 _ _ _ _ (hwidth i hi))
            (abs_nonneg _)
        _ = |coeff i| / (width i) ^ 2 := by ring



theorem d009070
    (s : Finset ι)
    (center₁ center₂ width coeff : ι → ℝ)
    (hwidth : ∀ i ∈ s, 0 < width i) :
    Measurable (_root_.GD.N0119.d009065 s center₁ center₂ width coeff)
      ∧ ∀ p,
        |_root_.GD.N0119.d009065 s center₁ center₂ width coeff p|
          ≤ ∑ i ∈ s, |coeff i| / (width i) ^ 2 :=
  ⟨_root_.GD.N0119.d009066 _ _ _ _ _,
    _root_.GD.N0119.d009069 _ _ _ _ _ hwidth⟩





theorem d009071
    {P : Measure Ω} {p : ℝ≥0∞}
    {f g : Ω → ℝ} {C : ℝ}
    (hf : MemLp f p P)
    (hg : AEStronglyMeasurable g P)
    (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂P, |g ω| ≤ C) :
    MemLp (fun ω => f ω * g ω) p P := by
  have hgTop : MemLp g ∞ P :=
    memLp_top_of_bound hg C hbound
  simpa [mul_comm] using hf.mul' hgTop



theorem d009072
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  unfold gammaMeasure gammaPDF
  rw [ae_withDensity_iff (measurable_gammaPDFReal a r).ennreal_ofReal]
  have hzero : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hzero] with x hx hpdf
  have hxnonneg : 0 ≤ x := by
    by_contra h
    simp [gammaPDFReal, not_le.mpr (lt_of_not_ge h)] at hpdf
  exact lt_of_le_of_ne hxnonneg hx.symm

theorem d009073
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∀ᵐ p ∂_root_.GD.N0125.d008840 α β,
      0 < p.2.1 ∧ 0 < p.2.2 := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaMeasure β β) :=
    isProbabilityMeasure_gammaMeasure hβ hβ
  have hx := _root_.GD.N0119.d009072 hα hα
  have hy := _root_.GD.N0119.d009072 hβ hβ
  have hxy :
      ∀ᵐ p ∂(gammaMeasure α α).prod (gammaMeasure β β),
        0 < p.1 ∧ 0 < p.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by
      exact (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_const measurable_snd))]
    filter_upwards [hx] with x hx'
    filter_upwards [hy] with y hy'
    exact ⟨hx', hy'⟩
  unfold _root_.GD.N0125.d008840
  rw [Measure.ae_prod_iff_ae_ae (by
    exact
      (measurableSet_lt measurable_const measurable_snd.fst).inter
        (measurableSet_lt measurable_const measurable_snd.snd))]
  filter_upwards with z
  exact hxy

theorem d009074
    {e rx ry : ℝ}
    (he0 : 0 < e) (he1 : e < 1)
    (hrx : 0 < rx) (hry : 0 < ry) :
    e * ry / ((1 - e) * rx + e * ry) ∈ Icc (0 : ℝ) 1 := by
  have hleft : 0 < (1 - e) * rx := mul_pos (sub_pos.mpr he1) hrx
  have hright : 0 < e * ry := mul_pos he0 hry
  have hden : 0 < (1 - e) * rx + e * ry := add_pos hleft hright
  constructor
  · exact div_nonneg hright.le hden.le
  · rw [div_le_one hden]
    linarith



theorem d009075
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    ∀ᵐ ω ∂_root_.GD.N0137.d008914 m n,
      0 < _root_.GD.N0137.d008933 m n ω ∧ 0 < _root_.GD.N0137.d008934 m n ω := by
  let α : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let β : ℝ := (((n - 1 : ℕ) : ℝ) / 2)
  have hα : 0 < α := by
    dsimp [α]
    exact _root_.GD.N0137.d008900 hm
  have hβ : 0 < β := by
    dsimp [β]
    exact _root_.GD.N0137.d008900 hn
  have hRawLaw :
      HasLaw (_root_.GD.N0137.d008935 m n e)
        (_root_.GD.N0125.d008840 α β)
        (_root_.GD.N0137.d008914 m n) := by
    refine ⟨(_root_.GD.N0137.d008937 m n e).aemeasurable, ?_⟩
    exact _root_.GD.N0137.d008938
      m n hm hn he0.le he1.le
  have hpos :
      ∀ᵐ p ∂_root_.GD.N0125.d008840 α β,
        0 < p.2.1 ∧ 0 < p.2.2 :=
    _root_.GD.N0119.d009073 hα hβ
  have hpull :
      ∀ᵐ ω ∂_root_.GD.N0137.d008914 m n,
        0 < (_root_.GD.N0137.d008935 m n e ω).2.1
          ∧ 0 < (_root_.GD.N0137.d008935 m n e ω).2.2 :=
    (hRawLaw.ae_iff (by fun_prop)).2 hpos
  simpa [_root_.GD.N0137.d008935] using hpull


theorem d009076
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    ∀ᵐ ω ∂_root_.GD.N0137.d008914 m n,
      0 <
        (1 - e) * _root_.GD.N0137.d008933 m n ω + e * _root_.GD.N0137.d008934 m n ω := by
  filter_upwards
      [_root_.GD.N0119.d009075 m n hm hn he0 he1] with ω hω
  exact add_pos
    (mul_pos (sub_pos.mpr he1) hω.1)
    (mul_pos he0 hω.2)

theorem d009077
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    ∀ᵐ ω ∂_root_.GD.N0137.d008914 m n,
      _root_.GD.N0137.d008943 m n e ω ∈ Icc (0 : ℝ) 1 := by
  filter_upwards
      [_root_.GD.N0119.d009075 m n hm hn he0 he1] with ω hω
  simpa [_root_.GD.N0137.d008943] using
    _root_.GD.N0119.d009074 he0 he1 hω.1 hω.2

theorem d009078
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    MemLp (_root_.GD.N0137.d008932 m n e) 2 (_root_.GD.N0137.d008914 m n) := by
  let α : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let β : ℝ := (((n - 1 : ℕ) : ℝ) / 2)
  have hα : 0 < α := by
    dsimp [α]
    exact _root_.GD.N0137.d008900 hm
  have hβ : 0 < β := by
    dsimp [β]
    exact _root_.GD.N0137.d008900 hn
  let μR : Measure (ℝ × ℝ) :=
    (gammaMeasure α α).prod (gammaMeasure β β)
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaMeasure β β) :=
    isProbabilityMeasure_gammaMeasure hβ hβ
  have hRaw :
      HasLaw (_root_.GD.N0137.d008935 m n e)
        ((gaussianReal 0 1).prod μR)
        (_root_.GD.N0137.d008914 m n) := by
    refine ⟨(_root_.GD.N0137.d008937 m n e).aemeasurable, ?_⟩
    have hRawEq :=
      _root_.GD.N0137.d008938 m n hm hn he0 he1
    change
      (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008935 m n e) =
        _root_.GD.N0125.d008840 α β at hRawEq
    simpa [_root_.GD.N0125.d008840, μR] using hRawEq
  have hFst :
      HasLaw (Prod.fst : ℝ × (ℝ × ℝ) → ℝ)
        (gaussianReal 0 1)
        ((gaussianReal 0 1).prod μR) :=
    (measurePreserving_fst
      (μ := gaussianReal 0 1) (ν := μR)).hasLaw
  have hZ :
      HasLaw (_root_.GD.N0137.d008932 m n e)
        (gaussianReal 0 1) (_root_.GD.N0137.d008914 m n) := by
    simpa [Function.comp_def, _root_.GD.N0137.d008935] using hFst.comp hRaw
  exact hZ.hasGaussianLaw.memLp_two

theorem d009079
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    MemLp (_root_.GD.N0137.d008942 m n e Sigma) 2 (_root_.GD.N0137.d008914 m n) := by
  unfold _root_.GD.N0137.d008942
  exact
    (_root_.GD.N0119.d009078 m n hm hn he0 he1).const_mul
      (Real.sqrt Sigma)

theorem d009080
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    MemLp
      (fun ω =>
        _root_.GD.N0137.d008942 m n e Sigma ω * (_root_.GD.N0137.d008943 m n e ω - e))
      2 (_root_.GD.N0137.d008914 m n) := by
  have hD :=
    _root_.GD.N0119.d009079 m n hm hn he0.le he1.le
      (Sigma := Sigma)
  apply _root_.GD.N0119.d009071 (C := 1) hD
  · exact
      ((_root_.GD.N0137.d008946 m n e Sigma).snd.fst.sub
        measurable_const).aestronglyMeasurable
  · norm_num
  · filter_upwards
      [_root_.GD.N0119.d009077 m n hm hn he0 he1] with ω hL
    rw [abs_le]
    constructor <;> linarith [hL.1, hL.2]

theorem d009081
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma B : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (q : ℝ × ℝ → ℝ)
    (hq : Measurable q)
    (hB : 0 ≤ B)
    (hqBound : ∀ p, |q p| ≤ B) :
    MemLp
      (fun ω =>
        _root_.GD.N0137.d008942 m n e Sigma ω *
          q (_root_.GD.N0137.d008943 m n e ω, _root_.GD.N0137.d008944 m n e ω))
      2 (_root_.GD.N0137.d008914 m n) := by
  have hD :=
    _root_.GD.N0119.d009079 m n hm hn he0 he1
      (Sigma := Sigma)
  apply _root_.GD.N0119.d009071 hD
  · exact
      (hq.comp
        ((_root_.GD.N0137.d008946 m n e Sigma).snd.fst.prodMk
          (_root_.GD.N0137.d008946 m n e Sigma).snd.snd)).aestronglyMeasurable
  · exact hB
  · exact ae_of_all _ fun ω =>
      hqBound (_root_.GD.N0137.d008943 m n e ω, _root_.GD.N0137.d008944 m n e ω)



theorem d009082
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma B : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (q : ℝ × ℝ → ℝ)
    (hq : Measurable q)
    (hB : 0 ≤ B)
    (hqBound : ∀ p, |q p| ≤ B) :
    MemLp
        (fun ω =>
          _root_.GD.N0137.d008942 m n e Sigma ω * (_root_.GD.N0137.d008943 m n e ω - e))
        2 (_root_.GD.N0137.d008914 m n)
      ∧
    MemLp
        (fun ω =>
          _root_.GD.N0137.d008942 m n e Sigma ω *
            q (_root_.GD.N0137.d008943 m n e ω, _root_.GD.N0137.d008944 m n e ω))
        2 (_root_.GD.N0137.d008914 m n) :=
  ⟨_root_.GD.N0119.d009080 m n hm hn he0 he1,
    _root_.GD.N0119.d009081 m n hm hn he0.le he1.le
      q hq hB hqBound⟩


theorem d009083
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (s : Finset ι)
    (center₁ center₂ width coeff : ι → ℝ)
    (hwidth : ∀ i ∈ s, 0 < width i) :
    MemLp
      (fun ω =>
        _root_.GD.N0137.d008942 m n e Sigma ω *
          _root_.GD.N0119.d009065 s center₁ center₂ width coeff
            (_root_.GD.N0137.d008943 m n e ω, _root_.GD.N0137.d008944 m n e ω))
      2 (_root_.GD.N0137.d008914 m n) := by
  apply _root_.GD.N0119.d009081
    m n hm hn he0 he1
    (_root_.GD.N0119.d009065 s center₁ center₂ width coeff)
    (_root_.GD.N0119.d009066 _ _ _ _ _)
    (Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _)
      (sq_nonneg _))
  exact _root_.GD.N0119.d009069 _ _ _ _ _ hwidth

end

end GD.N0119
