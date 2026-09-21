import GD.Module0795
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

















































open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace GD
namespace N0232
namespace N0719
namespace N0838

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0952
open _root_.GD.N0232.N0719.N0959
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0819






def d012096
    {k : ℕ} (sizes : Fin k → ℕ) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  ∑ i, (sizes i : ℝ) / theta.scale i ^ 2


def d012097
    {k : ℕ} (sizes : Fin k → ℕ) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  (_root_.GD.N0232.N0719.N0838.d012096 sizes theta)⁻¹

theorem d012098
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0838.d012096 sizes theta := by
  let i : Fin k := ⟨0, hk⟩
  unfold _root_.GD.N0232.N0719.N0838.d012096
  exact Finset.sum_pos'
    (fun j _ ↦ div_nonneg (by positivity) (sq_nonneg _))
    ⟨i, Finset.mem_univ i,
      div_pos (by exact_mod_cast hsizes i)
        (sq_pos_of_pos (theta.scale_pos i))⟩

theorem d012099
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0838.d012097 sizes theta := by
  unfold _root_.GD.N0232.N0719.N0838.d012097
  exact inv_pos.mpr (_root_.GD.N0232.N0719.N0838.d012098 hk sizes hsizes theta)


theorem d012100
    {k : ℕ} (sizes : Fin k → ℕ)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0838.d012096 sizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      (dilation ^ 2)⁻¹ * _root_.GD.N0232.N0719.N0838.d012096 sizes theta := by
  unfold _root_.GD.N0232.N0719.N0838.d012096
  simp only [_root_.GD.N0232.N0719.N0845.d010883, mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hdilation.ne', (theta.scale_pos i).ne']
  try ring



theorem d012101
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0838.d012097 sizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      dilation ^ 2 * _root_.GD.N0232.N0719.N0838.d012097 sizes theta := by
  have hprecision := _root_.GD.N0232.N0719.N0838.d012098 hk sizes hsizes theta
  unfold _root_.GD.N0232.N0719.N0838.d012097
  rw [_root_.GD.N0232.N0719.N0838.d012100]
  field_simp [hdilation.ne', hprecision.ne']



theorem d012102
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0838.d012097 sizes theta =
      _root_.GD.N0232.N0719.N0845.d010886 theta ^ 2 *
        _root_.GD.N0232.N0719.N0838.d012097 sizes (_root_.GD.N0232.N0719.N0845.d010890 hk theta) := by
  calc
    _root_.GD.N0232.N0719.N0838.d012097 sizes theta =
        _root_.GD.N0232.N0719.N0838.d012097 sizes
          (_root_.GD.N0232.N0719.N0845.d010881 theta.location (_root_.GD.N0232.N0719.N0845.d010886 theta)
            (_root_.GD.N0232.N0719.N0845.d010887 hk theta) (_root_.GD.N0232.N0719.N0845.d010890 hk theta)) := by
      rw [_root_.GD.N0232.N0719.N0952.d012065 hk theta]
    _ = _root_.GD.N0232.N0719.N0845.d010886 theta ^ 2 *
        _root_.GD.N0232.N0719.N0838.d012097 sizes (_root_.GD.N0232.N0719.N0845.d010890 hk theta) :=
      _root_.GD.N0232.N0719.N0838.d012101 hk sizes hsizes
        theta.location (_root_.GD.N0232.N0719.N0845.d010886 theta) (_root_.GD.N0232.N0719.N0845.d010887 hk theta)
        (_root_.GD.N0232.N0719.N0845.d010890 hk theta)



theorem d012103
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Real.sqrt (_root_.GD.N0232.N0719.N0838.d012097 sizes theta) =
      _root_.GD.N0232.N0719.N0845.d010886 theta *
        Real.sqrt (_root_.GD.N0232.N0719.N0838.d012097 sizes (_root_.GD.N0232.N0719.N0845.d010890 hk theta)) := by
  rw [_root_.GD.N0232.N0719.N0838.d012102 hk sizes hsizes]
  rw [Real.sqrt_mul (sq_nonneg (_root_.GD.N0232.N0719.N0845.d010886 theta))]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (_root_.GD.N0232.N0719.N0845.d010887 hk theta)]








theorem d012104
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) :
    _root_.GD.N0232.N0719.N0838.d012097 sizes
        (_root_.GD.N0232.N0719.N0959.d011933 hk w hw) =
      1 / ((∑ i, (sizes i : ℝ) * w i) *
        _root_.GD.N0232.N0719.N0959.d011923 w ^ 2) := by
  have hdenom : _root_.GD.N0232.N0719.N0959.d011923 w ≠ 0 :=
    (_root_.GD.N0232.N0719.N0959.d011925 hk hw).ne'
  unfold _root_.GD.N0232.N0719.N0838.d012097 _root_.GD.N0232.N0719.N0838.d012096
  simp_rw [show ∀ i : Fin k,
      (sizes i : ℝ) /
          (_root_.GD.N0232.N0719.N0959.d011933 hk w hw).scale i ^ 2 =
        _root_.GD.N0232.N0719.N0959.d011923 w ^ 2 * ((sizes i : ℝ) * w i) by
    intro i
    have h :=
      _root_.GD.N0232.N0719.N0959.d011937 hk w hw i
    unfold _root_.GD.N0232.N0719.N0815.d010924 at h
    rw [div_eq_mul_one_div, h]
    ring]
  rw [← Finset.mul_sum]
  ring




theorem d012105
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) :
    _root_.GD.N0232.N0719.N0838.d012096 sizes
        (_root_.GD.N0232.N0719.N0959.d011933 hk w hw) =
      (∑ i, (sizes i : ℝ) * w i) *
        _root_.GD.N0232.N0719.N0959.d011923 w ^ 2 := by
  unfold _root_.GD.N0232.N0719.N0838.d012096
  simp_rw [show ∀ i : Fin k,
      (sizes i : ℝ) /
          (_root_.GD.N0232.N0719.N0959.d011933 hk w hw).scale i ^ 2 =
        _root_.GD.N0232.N0719.N0959.d011923 w ^ 2 * ((sizes i : ℝ) * w i) by
    intro i
    have h :=
      _root_.GD.N0232.N0719.N0959.d011937 hk w hw i
    unfold _root_.GD.N0232.N0719.N0815.d010924 at h
    rw [div_eq_mul_one_div, h]
    ring]
  rw [← Finset.mul_sum]
  ring



theorem d012106
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 0 < sizes i)
    (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    1 ≤ ∑ i, (sizes i : ℝ) * w i := by
  calc
    1 = ∑ i, 1 * w i := by simp [hsum]
    _ ≤ ∑ i, (sizes i : ℝ) * w i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (by
        exact_mod_cast (show 1 ≤ sizes i from hsizes i)) (hw i)




theorem d012107
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = 1) :
    _root_.GD.N0232.N0719.N0838.d012097 sizes
        (_root_.GD.N0232.N0719.N0959.d011933 hk w hw) ≤
      (_root_.GD.N0232.N0719.N0959.d011923 w ^ 2)⁻¹ := by
  rw [_root_.GD.N0232.N0719.N0838.d012104
    hk sizes hsizes w hw]
  have hmass : 1 ≤ ∑ i, (sizes i : ℝ) * w i :=
    _root_.GD.N0232.N0719.N0838.d012106 sizes hsizes w
      (fun i ↦ (hw i).le) hsum
  have hdenom : 0 < _root_.GD.N0232.N0719.N0959.d011923 w ^ 2 :=
    sq_pos_of_pos (_root_.GD.N0232.N0719.N0959.d011925 hk hw)
  rw [show (_root_.GD.N0232.N0719.N0959.d011923 w ^ 2)⁻¹ =
      1 / _root_.GD.N0232.N0719.N0959.d011923 w ^ 2 by simp [one_div]]
  exact one_div_le_one_div_of_le hdenom (by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmass) hdenom.le])




theorem d012108
    {k : ℕ} (wSeq : ℕ → Fin k → ℝ)
    (hwSeq : ∀ n i, 0 < wSeq n i) (j : Fin k)
    (hzero : Tendsto (fun n ↦ wSeq n j) atTop (nhds 0)) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0959.d011923 (wSeq n))
      atTop atTop := by
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (wSeq n j))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hzero
  have hsqrtWithin : Tendsto (fun n ↦ Real.sqrt (wSeq n j))
      atTop (nhdsWithin 0 (Ioi 0)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hsqrt,
      Filter.Eventually.of_forall
        (fun n ↦ Real.sqrt_pos.2 (hwSeq n j))⟩
  have hinvTop : Tendsto
      (fun n ↦ (Real.sqrt (wSeq n j))⁻¹) atTop atTop :=
    hsqrtWithin.inv_tendsto_nhdsGT_zero
  exact tendsto_atTop_mono (fun n ↦ by
    unfold _root_.GD.N0232.N0719.N0959.d011923
    exact Finset.single_le_sum
      (fun i _ ↦ inv_nonneg.mpr (Real.sqrt_nonneg _))
      (Finset.mem_univ j)) hinvTop




theorem d012109
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i)
    (wSeq : ℕ → Fin k → ℝ) (hwSeq : ∀ n i, 0 < wSeq n i)
    (hsum : ∀ n, ∑ i, wSeq n i = 1)
    (j : Fin k) (hzero : Tendsto (fun n ↦ wSeq n j) atTop (nhds 0)) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0838.d012097 sizes
        (_root_.GD.N0232.N0719.N0959.d011933 hk (wSeq n) (hwSeq n)))
      atTop (nhds 0) := by
  have hdenom :=
    _root_.GD.N0232.N0719.N0838.d012108
      wSeq hwSeq j hzero
  have hdenomSq : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0959.d011923 (wSeq n) ^ 2)
      atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hdenom
  have hinv : Tendsto
      (fun n ↦ (_root_.GD.N0232.N0719.N0959.d011923 (wSeq n) ^ 2)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hdenomSq
  exact squeeze_zero
    (fun n ↦ (_root_.GD.N0232.N0719.N0838.d012099 hk sizes hsizes _).le)
    (fun n ↦ _root_.GD.N0232.N0719.N0838.d012107
      hk sizes hsizes (wSeq n) (hwSeq n) (hsum n))
    hinv






def d012110 (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    _root_.GD.N0232.N0719.N0859.d010809 2 where
  location := 0
  scale := fun i ↦ if i = 0 then epsilon else 1
  scale_pos := by
    intro i
    fin_cases i
    · simpa using hepsilon
    · simp

@[simp] theorem d012111
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (_root_.GD.N0232.N0719.N0838.d012110 epsilon hepsilon).scale 0 = epsilon := by
  simp [_root_.GD.N0232.N0719.N0838.d012110]

@[simp] theorem d012112
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (_root_.GD.N0232.N0719.N0838.d012110 epsilon hepsilon).scale 1 = 1 := by
  simp [_root_.GD.N0232.N0719.N0838.d012110]



theorem d012113
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    _root_.GD.N0232.N0719.N0845.d010886 (_root_.GD.N0232.N0719.N0838.d012110 epsilon hepsilon) =
      1 + epsilon := by
  unfold _root_.GD.N0232.N0719.N0845.d010886
  rw [Fin.sum_univ_two]
  simp [add_comm]


theorem d012114
    (sizes : Fin 2 → ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    _root_.GD.N0232.N0719.N0838.d012097 sizes (_root_.GD.N0232.N0719.N0838.d012110 epsilon hepsilon) =
      epsilon ^ 2 /
        ((sizes 0 : ℝ) + (sizes 1 : ℝ) * epsilon ^ 2) := by
  unfold _root_.GD.N0232.N0719.N0838.d012097 _root_.GD.N0232.N0719.N0838.d012096
  rw [Fin.sum_univ_two]
  simp only [_root_.GD.N0232.N0719.N0838.d012111,
    _root_.GD.N0232.N0719.N0838.d012112, one_pow, div_one]
  field_simp [hepsilon.ne']
  try ring



theorem d012115
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    _root_.GD.N0232.N0719.N0819.d011729
        (_root_.GD.N0232.N0719.N0838.d012110 epsilon hepsilon) 0 =
      1 / (1 + epsilon ^ 2) := by
  unfold _root_.GD.N0232.N0719.N0819.d011729 _root_.GD.N0232.N0719.N0815.d010926 _root_.GD.N0232.N0719.N0815.d010924
  rw [Fin.sum_univ_two]
  simp only [_root_.GD.N0232.N0719.N0838.d012111,
    _root_.GD.N0232.N0719.N0838.d012112, one_pow, div_one]
  field_simp [hepsilon.ne']
  try ring



theorem d012116
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    _root_.GD.N0232.N0719.N0819.d011729
        (_root_.GD.N0232.N0719.N0838.d012110 epsilon hepsilon) 1 =
      epsilon ^ 2 / (1 + epsilon ^ 2) := by
  unfold _root_.GD.N0232.N0719.N0819.d011729 _root_.GD.N0232.N0719.N0815.d010926 _root_.GD.N0232.N0719.N0815.d010924
  rw [Fin.sum_univ_two]
  simp only [_root_.GD.N0232.N0719.N0838.d012111,
    _root_.GD.N0232.N0719.N0838.d012112, one_pow, div_one]
  field_simp [hepsilon.ne']
  try ring


def d012117 (n : ℕ) : ℝ := (((n + 1 : ℕ) : ℝ))⁻¹

theorem d012118 (n : ℕ) : 0 < _root_.GD.N0232.N0719.N0838.d012117 n := by
  unfold _root_.GD.N0232.N0719.N0838.d012117
  positivity

theorem d012119 :
    Tendsto _root_.GD.N0232.N0719.N0838.d012117 atTop (nhds 0) := by
  unfold _root_.GD.N0232.N0719.N0838.d012117
  convert
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right
        atTop (1 : ℝ) tendsto_natCast_atTop_atTop) using 1
  ext n
  simp

theorem d012120 :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886
        (_root_.GD.N0232.N0719.N0838.d012110 (_root_.GD.N0232.N0719.N0838.d012117 n)
          (_root_.GD.N0232.N0719.N0838.d012118 n)))
      atTop (nhds 1) := by
  rw [show (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886
      (_root_.GD.N0232.N0719.N0838.d012110 (_root_.GD.N0232.N0719.N0838.d012117 n)
        (_root_.GD.N0232.N0719.N0838.d012118 n))) =
      (fun n ↦ 1 + _root_.GD.N0232.N0719.N0838.d012117 n) by
    funext n
    exact _root_.GD.N0232.N0719.N0838.d012113 _ _]
  simpa using tendsto_const_nhds.add _root_.GD.N0232.N0719.N0838.d012119




theorem d012121
    (sizes : Fin 2 → ℕ) (hsizes : ∀ i, 0 < sizes i) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0838.d012097 sizes
        (_root_.GD.N0232.N0719.N0838.d012110 (_root_.GD.N0232.N0719.N0838.d012117 n)
          (_root_.GD.N0232.N0719.N0838.d012118 n)))
      atTop (nhds 0) := by
  have hupper : ∀ n,
      _root_.GD.N0232.N0719.N0838.d012097 sizes
          (_root_.GD.N0232.N0719.N0838.d012110 (_root_.GD.N0232.N0719.N0838.d012117 n)
            (_root_.GD.N0232.N0719.N0838.d012118 n)) ≤ _root_.GD.N0232.N0719.N0838.d012117 n ^ 2 := by
    intro n
    rw [_root_.GD.N0232.N0719.N0838.d012114]
    apply div_le_self (sq_nonneg (_root_.GD.N0232.N0719.N0838.d012117 n))
    have hs0 : 1 ≤ (sizes 0 : ℝ) := by
      exact_mod_cast hsizes 0
    have hs1 : 0 ≤ (sizes 1 : ℝ) * _root_.GD.N0232.N0719.N0838.d012117 n ^ 2 := by
      positivity
    linarith
  have hpow : Tendsto (fun n : ℕ ↦ _root_.GD.N0232.N0719.N0838.d012117 n ^ 2)
      atTop (nhds 0) := by
    simpa using _root_.GD.N0232.N0719.N0838.d012119.pow 2
  exact squeeze_zero
    (fun n ↦ (_root_.GD.N0232.N0719.N0838.d012099 (by norm_num) sizes hsizes _).le)
    hupper
    hpow



theorem d012122 :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729
        (_root_.GD.N0232.N0719.N0838.d012110 (_root_.GD.N0232.N0719.N0838.d012117 n)
          (_root_.GD.N0232.N0719.N0838.d012118 n)))
      atTop (nhds (fun i : Fin 2 ↦ if i = 0 then 1 else 0)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hden : Tendsto (fun n : ℕ ↦ 1 + _root_.GD.N0232.N0719.N0838.d012117 n ^ 2)
      atTop (nhds 1) := by
    simpa using
      tendsto_const_nhds.add (_root_.GD.N0232.N0719.N0838.d012119.pow 2)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with hi | hi <;> subst hi
  · rw [show (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729
          (_root_.GD.N0232.N0719.N0838.d012110 (_root_.GD.N0232.N0719.N0838.d012117 n)
            (_root_.GD.N0232.N0719.N0838.d012118 n)) 0) =
        (fun n ↦ 1 / (1 + _root_.GD.N0232.N0719.N0838.d012117 n ^ 2)) by
      funext n
      exact _root_.GD.N0232.N0719.N0838.d012115
        _ _]
    have hdiv : Tendsto (fun n : ℕ ↦ 1 / (1 + _root_.GD.N0232.N0719.N0838.d012117 n ^ 2))
        atTop (nhds (1 / 1)) :=
      tendsto_const_nhds.div hden (by norm_num)
    simpa using hdiv
  · rw [show (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729
          (_root_.GD.N0232.N0719.N0838.d012110 (_root_.GD.N0232.N0719.N0838.d012117 n)
            (_root_.GD.N0232.N0719.N0838.d012118 n)) 1) =
        (fun n ↦ _root_.GD.N0232.N0719.N0838.d012117 n ^ 2 /
          (1 + _root_.GD.N0232.N0719.N0838.d012117 n ^ 2)) by
      funext n
      exact _root_.GD.N0232.N0719.N0838.d012116
        _ _]
    have hnum : Tendsto (fun n : ℕ ↦ _root_.GD.N0232.N0719.N0838.d012117 n ^ 2)
        atTop (nhds 0) := by
      simpa using _root_.GD.N0232.N0719.N0838.d012119.pow 2
    have hdiv : Tendsto (fun n : ℕ ↦ _root_.GD.N0232.N0719.N0838.d012117 n ^ 2 /
        (1 + _root_.GD.N0232.N0719.N0838.d012117 n ^ 2)) atTop (nhds (0 / 1)) :=
      hnum.div hden (by norm_num)
    simpa using hdiv




theorem d012123
    (sizes : Fin 2 → ℕ) (hsizes : ∀ i, 0 < sizes i) :
    ∃ thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 2,
      Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq n)) atTop (nhds 1) ∧
      Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0838.d012097 sizes (thetaSeq n))
        atTop (nhds 0) ∧
      Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n))
        atTop (nhds (fun i : Fin 2 ↦ if i = 0 then 1 else 0)) := by
  refine ⟨fun n ↦ _root_.GD.N0232.N0719.N0838.d012110 (_root_.GD.N0232.N0719.N0838.d012117 n)
    (_root_.GD.N0232.N0719.N0838.d012118 n),
    _root_.GD.N0232.N0719.N0838.d012120,
    _root_.GD.N0232.N0719.N0838.d012121 sizes hsizes,
    _root_.GD.N0232.N0719.N0838.d012122⟩





def d012124
    {k : ℕ} (sizes : Fin k → ℕ) (shape : Fin k → ℝ) : ℝ :=
  ∑ i, (sizes i : ℝ) / shape i ^ 2



def d012125
    {k : ℕ} (sizes : Fin k → ℕ) (shape : Fin k → ℝ)
    (radial : ℝ) : ℝ :=
  radial ^ 2 / _root_.GD.N0232.N0719.N0838.d012124 sizes shape

theorem d012126
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) (shape : Fin k → ℝ)
    (hshape : ∀ i, 0 < shape i) :
    0 < _root_.GD.N0232.N0719.N0838.d012124 sizes shape := by
  let i : Fin k := ⟨0, hk⟩
  unfold _root_.GD.N0232.N0719.N0838.d012124
  exact Finset.sum_pos'
    (fun j _ ↦ div_nonneg (by positivity) (sq_nonneg _))
    ⟨i, Finset.mem_univ i,
      div_pos (by exact_mod_cast hsizes i) (sq_pos_of_pos (hshape i))⟩



theorem d012127
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) (shape : Fin k → ℝ)
    (hshape : ∀ i, 0 < shape i) (radial : ℝ) :
    _root_.GD.N0232.N0719.N0838.d012125 sizes shape radial = 0 ↔ radial = 0 := by
  unfold _root_.GD.N0232.N0719.N0838.d012125
  rw [div_eq_zero_iff]
  simp [(_root_.GD.N0232.N0719.N0838.d012126 hk sizes hsizes shape hshape).ne']



theorem d012128
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) (shape : Fin k → ℝ)
    (hshape : ∀ i, 0 < shape i)
    (location radial : ℝ) (hradial : 0 < radial) :
    _root_.GD.N0232.N0719.N0838.d012097 sizes
        { location := location
          scale := fun i ↦ radial * shape i
          scale_pos := fun i ↦ mul_pos hradial (hshape i) } =
      _root_.GD.N0232.N0719.N0838.d012125 sizes shape radial := by
  have hden := _root_.GD.N0232.N0719.N0838.d012126 hk sizes hsizes shape hshape
  unfold _root_.GD.N0232.N0719.N0838.d012097 _root_.GD.N0232.N0719.N0838.d012096 _root_.GD.N0232.N0719.N0838.d012125
    _root_.GD.N0232.N0719.N0838.d012124
  rw [show
      (∑ i, (sizes i : ℝ) / (radial * shape i) ^ 2) =
        (radial ^ 2)⁻¹ * ∑ i, (sizes i : ℝ) / shape i ^ 2 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hradial.ne', (hshape i).ne']
    try ring]
  field_simp [hradial.ne', hden.ne']
  try ring





theorem d012129
    (decision : ℝ → ℝ)
    (htranslate : ∀ shift mu,
      decision (shift + mu) = shift + decision mu)
    (hdilate : ∀ dilation, 0 < dilation →
      decision 0 = dilation * decision 0) :
    ∀ mu, decision mu = mu := by
  have hzero : decision 0 = 0 := by
    have htwo := hdilate 2 (by norm_num)
    linarith
  intro mu
  simpa [hzero] using htranslate mu 0



theorem d012130
    (decision : ℝ → ℝ)
    (hdom : ∀ mu, (decision mu - mu) ^ 2 ≤ 0) :
    ∀ mu, decision mu = mu := by
  intro mu
  have hz : (decision mu - mu) ^ 2 = 0 :=
    le_antisymm (hdom mu) (sq_nonneg _)
  nlinarith [sq_eq_zero_iff.mp hz]








theorem d012131
    (cutoff : ℝ → ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (htrace : ∀ q ∈ Ioo (0 : ℝ) epsilon, 1 ≤ |cutoff q|) :
    ¬ IntegrableOn
      (fun q : ℝ ↦ q ^ (-(5 : ℝ) / 2) * cutoff q ^ 2)
      (Ioo 0 epsilon) := by
  intro hfinite
  have hpower : IntegrableOn (fun q : ℝ ↦ q ^ (-(5 : ℝ) / 2))
      (Ioo 0 epsilon) := by
    apply hfinite.mono'
    · exact ContinuousOn.aestronglyMeasurable
        (continuousOn_id.rpow_const (fun q hq ↦ Or.inl hq.1.ne'))
        measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
      have hqnonneg : 0 ≤ q ^ (-(5 : ℝ) / 2) :=
        Real.rpow_nonneg (le_of_lt hq.1) _
      have hcutoffSq : 1 ≤ cutoff q ^ 2 := by
        rw [← sq_abs]
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
          (htrace q hq) 2
      rw [Real.norm_eq_abs, abs_of_nonneg hqnonneg]
      exact le_mul_of_one_le_right hqnonneg hcutoffSq
  have hexponent :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hepsilon).mp hpower
  norm_num at hexponent



theorem d012132
    (cutoff : ℝ → ℝ) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : 0 < c)
    (htrace : ∀ q ∈ Ioo (0 : ℝ) epsilon, c ≤ |cutoff q|) :
    ¬ IntegrableOn
      (fun q : ℝ ↦ q ^ (-(5 : ℝ) / 2) * cutoff q ^ 2)
      (Ioo 0 epsilon) := by
  intro hfinite
  have hunitTrace : ∀ q ∈ Ioo (0 : ℝ) epsilon,
      1 ≤ |cutoff q / c| := by
    intro q hq
    rw [abs_div, abs_of_pos hc]
    exact (le_div_iff₀ hc).2 (by simpa using htrace q hq)
  apply _root_.GD.N0232.N0719.N0838.d012131
    (fun q ↦ cutoff q / c) hepsilon hunitTrace
  have hscaled := hfinite.const_mul ((c ^ 2)⁻¹)
  apply hscaled.congr
  filter_upwards [] with q
  field_simp [hc.ne']
  try ring

end

end N0838
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0838.d012101
#print axioms _root_.GD.N0232.N0719.N0838.d012102
#print axioms _root_.GD.N0232.N0719.N0838.d012104
#print axioms _root_.GD.N0232.N0719.N0838.d012109
#print axioms _root_.GD.N0232.N0719.N0838.d012123
#print axioms _root_.GD.N0232.N0719.N0838.d012127
#print axioms _root_.GD.N0232.N0719.N0838.d012129
#print axioms _root_.GD.N0232.N0719.N0838.d012130
#print axioms _root_.GD.N0232.N0719.N0838.d012131
#print axioms _root_.GD.N0232.N0719.N0838.d012132
