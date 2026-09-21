import GD.Module0706















open MeasureTheory
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0918

noncomputable section

open _root_.GD.N0232.N0719.N0917
open _root_.GD.N0232.N0719.N0916
open _root_.GD.N0232.N0719.N0867
open _root_.GD.N0232.N0719.N0868
open _root_.GD.N0232.N0719.N1007
open _root_.GD.N0232.N0719.N0928





theorem d010422
    {J : Type*} [Fintype J]
    (weight evidence action : J → ℝ) (center : ℝ)
    (hdenom : _root_.GD.N0232.N0719.N1007.d009826 weight evidence ≠ 0) :
    _root_.GD.N0232.N0719.N1007.d009828 weight evidence action - center =
      (∑ j, weight j * evidence j * (action j - center)) /
        _root_.GD.N0232.N0719.N1007.d009826 weight evidence := by
  have hdenom' : (∑ j, weight j * evidence j) ≠ 0 := by
    simpa [_root_.GD.N0232.N0719.N1007.d009826] using hdenom
  unfold _root_.GD.N0232.N0719.N1007.d009828 _root_.GD.N0232.N0719.N1007.d009827 _root_.GD.N0232.N0719.N1007.d009826
  field_simp [hdenom']
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring



theorem d010423
    {J : Type*} [Fintype J]
    (weight evidence action : J → ℝ) (center bound : ℝ)
    (hmass : ∀ j, 0 ≤ weight j * evidence j)
    (hdenom : 0 < _root_.GD.N0232.N0719.N1007.d009826 weight evidence)
    (hbound : ∀ j, |action j - center| ≤ bound) :
    |_root_.GD.N0232.N0719.N1007.d009828 weight evidence action - center| ≤ bound := by
  rw [_root_.GD.N0232.N0719.N0918.d010422 weight evidence action center hdenom.ne',
    abs_div, abs_of_pos hdenom]
  apply (div_le_iff₀ hdenom).2
  calc
    |∑ j, weight j * evidence j * (action j - center)| ≤
        ∑ j, |weight j * evidence j * (action j - center)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, (weight j * evidence j) * |action j - center| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, abs_of_nonneg (hmass j)]
    _ ≤ ∑ j, (weight j * evidence j) * bound := by
      exact Finset.sum_le_sum fun j hj ↦
        mul_le_mul_of_nonneg_left (hbound j) (hmass j)
    _ = _root_.GD.N0232.N0719.N1007.d009826 weight evidence * bound := by
      unfold _root_.GD.N0232.N0719.N1007.d009826
      rw [Finset.sum_mul]
    _ = bound * _root_.GD.N0232.N0719.N1007.d009826 weight evidence := mul_comm _ _





theorem d010424
    {k : ℕ} (target : ℝ) (y : Fin k → ℝ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    _root_.GD.N0232.N0719.N0910.d010278 target (_root_.GD.N0232.N0719.N0917.d009870 y face) ≤
      _root_.GD.N0232.N0719.N0910.d010278 target y := by
  unfold _root_.GD.N0232.N0719.N0910.d010278 _root_.GD.N0232.N0719.N0917.d009870 _root_.GD.N0232.N0719.N0917.d009869
  have hsum :
      (∑ j : Fin face.1.card,
          |y ((face.1.orderIsoOfFin rfl j).1) - target|) =
        ∑ i : face.1, |y i.1 - target| := by
    exact Fintype.sum_equiv (face.1.orderIsoOfFin rfl).toEquiv
      _ _ (fun _ ↦ rfl)
  have hattach :
      (∑ i : face.1, |y i.1 - target|) =
        ∑ i ∈ face.1, |y i - target| := by
    exact (Finset.sum_subtype face.1 (fun _ ↦ Iff.rfl)
      (fun i ↦ |y i - target|)).symm
  rw [hsum, hattach]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ face.1)
    (fun i hi hnot ↦ abs_nonneg (y i - target))



theorem d010425
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (commonPower : ℝ) (hcommon : 0 < commonPower)
    (target : ℝ) (u : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hpos : _root_.GD.N0232.N0719.N0867.d010301 u) (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    |_root_.GD.N0232.N0719.N0917.d009874 sizes u.mean u.meanVariance commonPower face - target| ≤
      _root_.GD.N0232.N0719.N0910.d010278 target u.mean := by
  let uface : _root_.GD.N0232.N0719.N0900.d009096 face.1.card :=
    { mean := _root_.GD.N0232.N0719.N0917.d009870 u.mean face
      meanVariance := _root_.GD.N0232.N0719.N0917.d009870 u.meanVariance face }
  have hfacepos : _root_.GD.N0232.N0719.N0867.d010301 uface := by
    intro j
    exact hpos (_root_.GD.N0232.N0719.N0917.d009869 face j)
  have hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 (_root_.GD.N0232.N0719.N0917.d009871 sizes face)
      (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face) := by
    rw [_root_.GD.N0232.N0719.N0917.d009872, _root_.GD.N0232.N0719.N1007.d009823]
    exact hcommon
  have hface :=
    _root_.GD.N0232.N0719.N0867.d010312
      (Finset.card_pos.mpr face.2) (_root_.GD.N0232.N0719.N0917.d009871 sizes face)
      (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face) target
      (_root_.GD.N0232.N0719.N0917.d009889 sizes hsizes face) hpower uface hfacepos
  calc
    |_root_.GD.N0232.N0719.N0917.d009874 sizes u.mean u.meanVariance commonPower face - target| ≤
        _root_.GD.N0232.N0719.N0910.d010278 target
          (_root_.GD.N0232.N0719.N0917.d009870 u.mean face) := by
      simpa [_root_.GD.N0232.N0719.N0917.d009874, uface] using hface
    _ ≤ _root_.GD.N0232.N0719.N0910.d010278 target u.mean :=
      _root_.GD.N0232.N0719.N0918.d010424 target u.mean face





theorem d010426
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (target : ℝ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) (hpos : _root_.GD.N0232.N0719.N0867.d010301 u) :
    |_root_.GD.N0232.N0719.N0916.d010415 sizes u - target| ≤
      _root_.GD.N0232.N0719.N0910.d010278 target u.mean := by
  have hcommon : 0 < _root_.GD.N0232.N0719.N0917.d009879 sizes :=
    _root_.GD.N0232.N0719.N0917.d009888 hk sizes
      (fun i ↦ le_trans (by norm_num) (hsizes i))
  let evidence : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ :=
    _root_.GD.N0232.N0719.N0917.d009873 sizes u.mean u.meanVariance (_root_.GD.N0232.N0719.N0917.d009879 sizes)
  let action : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ :=
    _root_.GD.N0232.N0719.N0917.d009874 sizes u.mean u.meanVariance (_root_.GD.N0232.N0719.N0917.d009879 sizes)
  have hevidence : ∀ face, 0 < evidence face := by
    intro face
    exact _root_.GD.N0232.N0719.N0917.d009890 sizes hsizes u.mean u.meanVariance hpos
      (_root_.GD.N0232.N0719.N0917.d009879 sizes) hcommon face
  have hdenom : 0 < _root_.GD.N0232.N0719.N1007.d009826 (fun _ : _root_.GD.N0232.N0719.N0917.d009868 k ↦ 1) evidence := by
    simpa [evidence, _root_.GD.N0232.N0719.N0917.d009875] using
      _root_.GD.N0232.N0719.N0917.d009891 hk sizes hsizes u.mean u.meanVariance hpos
        (_root_.GD.N0232.N0719.N0917.d009879 sizes) hcommon (fun _ ↦ 1)
        (fun _ ↦ by norm_num)
  have hbound : ∀ face,
      |action face - target| ≤
        _root_.GD.N0232.N0719.N0910.d010278 target u.mean := by
    intro face
    exact _root_.GD.N0232.N0719.N0918.d010425 sizes hsizes
      (_root_.GD.N0232.N0719.N0917.d009879 sizes) hcommon target u hpos face
  unfold _root_.GD.N0232.N0719.N0916.d010415
    _root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0917.d009878
    _root_.GD.N0232.N0719.N0917.d009877
  exact _root_.GD.N0232.N0719.N0918.d010423
    (fun _ : _root_.GD.N0232.N0719.N0917.d009868 k ↦ 1) evidence action target
      (_root_.GD.N0232.N0719.N0910.d010278 target u.mean)
      (fun face ↦ by simpa using (hevidence face).le)
      hdenom hbound



theorem d010427
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (target : ℝ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) :
    |_root_.GD.N0232.N0719.N0916.d010417 sizes u - target| ≤
      _root_.GD.N0232.N0719.N0910.d010278 target u.mean := by
  by_cases hpos : _root_.GD.N0232.N0719.N0867.d010301 u
  · rw [_root_.GD.N0232.N0719.N0916.d010418 sizes u hpos]
    exact _root_.GD.N0232.N0719.N0918.d010426
      hk sizes hsizes target u hpos
  · rw [_root_.GD.N0232.N0719.N0916.d010419 sizes u hpos]
    exact _root_.GD.N0232.N0719.N0910.d010281 hk target u




theorem d010428
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    MemLp
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
        _root_.GD.N0232.N0719.N0916.d010417 sizes
          (_root_.GD.N0232.N0719.N0933.d009305 k z) - location)
      2
      ((_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)) := by
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) :=
    _root_.GD.N0232.N0719.N0910.d010289
      sizes hsizes scales
  have hmajorant :=
    (_root_.GD.N0232.N0719.N0910.d010291
      sizes hsizes location scales).comp_fst
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)
  apply hmajorant.mono'
  · exact
      ((_root_.GD.N0232.N0719.N0916.d010420 sizes).comp
        (_root_.GD.N0232.N0719.N0933.d009306 k)).sub
          measurable_const |>.aestronglyMeasurable
  · filter_upwards with z
    simpa [_root_.GD.N0232.N0719.N0933.d009305, Real.norm_eq_abs] using
      _root_.GD.N0232.N0719.N0918.d010427
        hk sizes hsizes location (_root_.GD.N0232.N0719.N0933.d009305 k z)


def d010429
    {k : ℕ} (sizes : Fin k → ℕ)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0916.d010417 sizes
    (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)

@[fun_prop]
theorem d010430
    {k : ℕ} (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0918.d010429 sizes) := by
  exact (_root_.GD.N0232.N0719.N0916.d010420 sizes).comp
    (_root_.GD.N0232.N0719.N0900.d009115 k sizes)


theorem d010431
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    MemLp
      (fun omega : _root_.GD.N0232.N0719.N0900.d009094 k sizes ↦
        _root_.GD.N0232.N0719.N0918.d010429 sizes omega - location)
      2 (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  let split := _root_.GD.N0232.N0719.N0933.d009304 k sizes
  let productLaw :=
    (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
      (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)
  have hmp : MeasurePreserving split
      (_root_.GD.N0232.N0719.d009176 k sizes location scales) productLaw := by
    refine ⟨_root_.GD.N0232.N0719.N0933.d009308 k sizes, ?_⟩
    exact _root_.GD.N0232.N0719.N0933.d009309
      k sizes hsizes location scales
  have h :=
    (_root_.GD.N0232.N0719.N0918.d010428
      hk sizes hsizes location scales).comp_measurePreserving hmp
  simpa [split, productLaw, _root_.GD.N0232.N0719.N0918.d010429,
    Function.comp_def,
    _root_.GD.N0232.N0719.N0933.d009307] using h

end

end N0918
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0918.d010423
#print axioms _root_.GD.N0232.N0719.N0918.d010427
#print axioms _root_.GD.N0232.N0719.N0918.d010428
#print axioms _root_.GD.N0232.N0719.N0918.d010431
