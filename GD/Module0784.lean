import GD.Module0773
import GD.Module0726
import GD.Module0748
import Mathlib.Analysis.Real.Sqrt


















open Filter Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0959

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0819




theorem d011922
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0845.d010890 hk theta) =
      _root_.GD.N0232.N0719.N0819.d011729 theta := by
  unfold _root_.GD.N0232.N0719.N0845.d010890
  exact _root_.GD.N0232.N0719.N0819.d011731 hk
    (-(theta.location / _root_.GD.N0232.N0719.N0845.d010886 theta))
    (_root_.GD.N0232.N0719.N0845.d010886 theta)⁻¹
    (inv_pos.mpr (_root_.GD.N0232.N0719.N0845.d010887 hk theta)) theta



def d011923 {k : ℕ} (w : Fin k → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (w i))⁻¹


def d011924 {k : ℕ}
    (w : Fin k → ℝ) (i : Fin k) : ℝ :=
  (Real.sqrt (w i))⁻¹ / _root_.GD.N0232.N0719.N0959.d011923 w


theorem d011925
    {k : ℕ} (hk : 0 < k) {w : Fin k → ℝ}
    (hw : ∀ i, 0 < w i) :
    0 < _root_.GD.N0232.N0719.N0959.d011923 w := by
  let i : Fin k := ⟨0, hk⟩
  unfold _root_.GD.N0232.N0719.N0959.d011923
  exact Finset.sum_pos'
    (fun j _ ↦ (inv_pos.mpr ((Real.sqrt_pos.2 (hw j)))).le)
    ⟨i, Finset.mem_univ i,
      inv_pos.mpr (Real.sqrt_pos.2 (hw i))⟩


theorem d011926
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0819.d011729 theta i := by
  exact div_pos (_root_.GD.N0232.N0719.N0815.d010925 theta i)
    (_root_.GD.N0232.N0719.N0815.d010927 hk theta)



theorem d011927
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (Real.sqrt (_root_.GD.N0232.N0719.N0819.d011729 theta i))⁻¹ =
      theta.scale i * Real.sqrt (_root_.GD.N0232.N0719.N0815.d010926 theta) := by
  have hscale : 0 < theta.scale i := theta.scale_pos i
  have hprecision : 0 < _root_.GD.N0232.N0719.N0815.d010926 theta := _root_.GD.N0232.N0719.N0815.d010927 hk theta
  unfold _root_.GD.N0232.N0719.N0819.d011729 _root_.GD.N0232.N0719.N0815.d010924
  rw [Real.sqrt_div (by positivity : 0 ≤ 1 / theta.scale i ^ 2)]
  rw [show (1 / theta.scale i ^ 2) = (theta.scale i ^ 2)⁻¹ by
    simp [one_div]]
  rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  field_simp [hscale.ne', (Real.sqrt_pos.2 hprecision).ne']


theorem d011928
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0959.d011923 (_root_.GD.N0232.N0719.N0819.d011729 theta) =
      _root_.GD.N0232.N0719.N0845.d010886 theta * Real.sqrt (_root_.GD.N0232.N0719.N0815.d010926 theta) := by
  unfold _root_.GD.N0232.N0719.N0959.d011923 _root_.GD.N0232.N0719.N0845.d010886
  simp_rw [_root_.GD.N0232.N0719.N0959.d011927 hk theta]
  exact (Finset.sum_mul ..).symm


theorem d011929
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0845.d010890 hk theta).scale i =
      _root_.GD.N0232.N0719.N0959.d011924 (_root_.GD.N0232.N0719.N0819.d011729 theta) i := by
  rw [_root_.GD.N0232.N0719.N0845.d010892]
  unfold _root_.GD.N0232.N0719.N0959.d011924
  rw [_root_.GD.N0232.N0719.N0959.d011927 hk theta,
    _root_.GD.N0232.N0719.N0959.d011928 hk theta]
  have htotalScale : _root_.GD.N0232.N0719.N0845.d010886 theta ≠ 0 :=
    (_root_.GD.N0232.N0719.N0845.d010887 hk theta).ne'
  have htotalPrecisionSqrt : Real.sqrt (_root_.GD.N0232.N0719.N0815.d010926 theta) ≠ 0 :=
    (Real.sqrt_pos.2 (_root_.GD.N0232.N0719.N0815.d010927 hk theta)).ne'
  field_simp [htotalScale, htotalPrecisionSqrt]



theorem d011930
    {k : ℕ} (hk : 0 < k) {theta eta : _root_.GD.N0232.N0719.N0859.d010809 k}
    (hweight : _root_.GD.N0232.N0719.N0819.d011729 theta =
      _root_.GD.N0232.N0719.N0819.d011729 eta) :
    _root_.GD.N0232.N0719.N0845.d010890 hk theta = _root_.GD.N0232.N0719.N0845.d010890 hk eta := by
  apply _root_.GD.N0232.N0719.N0845.d010880
  · simp
  · intro i
    rw [_root_.GD.N0232.N0719.N0959.d011929 hk theta i,
      _root_.GD.N0232.N0719.N0959.d011929 hk eta i,
      hweight]




theorem d011931
    {k : ℕ} (hk : 0 < k) (theta eta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0819.d011729 theta = _root_.GD.N0232.N0719.N0819.d011729 eta ↔
      _root_.GD.N0232.N0719.N0845.d010890 hk theta = _root_.GD.N0232.N0719.N0845.d010890 hk eta := by
  constructor
  · exact _root_.GD.N0232.N0719.N0959.d011930 hk
  · intro hnormalize
    rw [← _root_.GD.N0232.N0719.N0959.d011922 hk theta,
      ← _root_.GD.N0232.N0719.N0959.d011922 hk eta,
      hnormalize]

theorem d011932
    {k : ℕ} (hk : 0 < k) (theta eta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0819.d011729 theta = _root_.GD.N0232.N0719.N0819.d011729 eta ↔
      ∃ (shift dilation : ℝ) (hdilation : 0 < dilation),
        _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta = eta := by
  rw [_root_.GD.N0232.N0719.N0959.d011931 hk,
    ← _root_.GD.N0232.N0719.N0845.d010896 hk theta eta]



def d011933
    {k : ℕ} (hk : 0 < k) (w : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := 0
  scale := fun i ↦ _root_.GD.N0232.N0719.N0959.d011924 w i
  scale_pos := fun i ↦ div_pos
    (inv_pos.mpr (Real.sqrt_pos.2 (hw i)))
    (_root_.GD.N0232.N0719.N0959.d011925 hk hw)

@[simp] theorem d011934
    {k : ℕ} (hk : 0 < k) (w : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) :
    (_root_.GD.N0232.N0719.N0959.d011933 hk w hw).location = 0 := rfl

@[simp] theorem d011935
    {k : ℕ} (hk : 0 < k) (w : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0959.d011933 hk w hw).scale i =
      _root_.GD.N0232.N0719.N0959.d011924 w i := rfl


theorem d011936
    {k : ℕ} (hk : 0 < k) (w : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) :
    _root_.GD.N0232.N0719.N0845.d010886 (_root_.GD.N0232.N0719.N0959.d011933 hk w hw) = 1 := by
  change (∑ i, _root_.GD.N0232.N0719.N0959.d011924 w i) = 1
  unfold _root_.GD.N0232.N0719.N0959.d011924 _root_.GD.N0232.N0719.N0959.d011923
  rw [← Finset.sum_div]
  exact div_self (_root_.GD.N0232.N0719.N0959.d011925 hk hw).ne'



theorem d011937
    {k : ℕ} (hk : 0 < k) (w : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) (i : Fin k) :
    _root_.GD.N0232.N0719.N0815.d010924 (_root_.GD.N0232.N0719.N0959.d011933 hk w hw) i =
      _root_.GD.N0232.N0719.N0959.d011923 w ^ 2 * w i := by
  have hsqrt : Real.sqrt (w i) ≠ 0 :=
    (Real.sqrt_pos.2 (hw i)).ne'
  have hdenom : _root_.GD.N0232.N0719.N0959.d011923 w ≠ 0 :=
    (_root_.GD.N0232.N0719.N0959.d011925 hk hw).ne'
  unfold _root_.GD.N0232.N0719.N0815.d010924
  rw [_root_.GD.N0232.N0719.N0959.d011935]
  unfold _root_.GD.N0232.N0719.N0959.d011924
  field_simp [hsqrt, hdenom]
  nlinarith [Real.sq_sqrt (hw i).le]



theorem d011938
    {k : ℕ} (hk : 0 < k) (w : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    _root_.GD.N0232.N0719.N0815.d010926 (_root_.GD.N0232.N0719.N0959.d011933 hk w hw) =
      _root_.GD.N0232.N0719.N0959.d011923 w ^ 2 := by
  unfold _root_.GD.N0232.N0719.N0815.d010926
  simp_rw [_root_.GD.N0232.N0719.N0959.d011937
    hk w hw]
  rw [← Finset.mul_sum, hsum, mul_one]


theorem d011939
    {k : ℕ} (hk : 0 < k) (w : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    _root_.GD.N0232.N0719.N0819.d011729
        (_root_.GD.N0232.N0719.N0959.d011933 hk w hw) = w := by
  funext i
  unfold _root_.GD.N0232.N0719.N0819.d011729
  rw [_root_.GD.N0232.N0719.N0959.d011937 hk w hw,
    _root_.GD.N0232.N0719.N0959.d011938 hk w hw hsum]
  exact mul_div_cancel_left₀ (w i)
    (pow_ne_zero 2 (_root_.GD.N0232.N0719.N0959.d011925 hk hw).ne')



theorem d011940
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0959.d011933 hk
        (_root_.GD.N0232.N0719.N0819.d011729 theta)
        (_root_.GD.N0232.N0719.N0959.d011926 hk theta) =
      _root_.GD.N0232.N0719.N0845.d010890 hk theta := by
  apply _root_.GD.N0232.N0719.N0845.d010880
  · simp
  · intro i
    exact (_root_.GD.N0232.N0719.N0959.d011929
      hk theta i).symm



theorem d011941
    {k : ℕ} {wSeq : ℕ → Fin k → ℝ} {w : Fin k → ℝ}
    (hk : 0 < k)
    (hconv : Tendsto wSeq atTop (nhds w))
    (hw : ∀ i, 0 < w i) (i : Fin k) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0959.d011924 (wSeq n) i)
      atTop (nhds (_root_.GD.N0232.N0719.N0959.d011924 w i)) := by
  have hinv : ∀ j : Fin k,
      Tendsto (fun n ↦ (Real.sqrt (wSeq n j))⁻¹)
        atTop (nhds ((Real.sqrt (w j))⁻¹)) := by
    intro j
    exact ((Real.continuous_sqrt.tendsto (w j)).comp
      (tendsto_pi_nhds.mp hconv j)).inv₀
        (Real.sqrt_pos.2 (hw j)).ne'
  have hdenom : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0959.d011923 (wSeq n))
      atTop (nhds (_root_.GD.N0232.N0719.N0959.d011923 w)) := by
    unfold _root_.GD.N0232.N0719.N0959.d011923
    exact tendsto_finsetSum Finset.univ (fun j _ ↦ hinv j)
  unfold _root_.GD.N0232.N0719.N0959.d011924
  exact (hinv i).div hdenom
    (_root_.GD.N0232.N0719.N0959.d011925 hk hw).ne'







theorem d011942
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (w : Fin k → ℝ)
    (hconv : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n))
      atTop (nhds w))
    (hw : ∀ i, 0 < w i) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010890 hk (thetaSeq n))
      atTop (nhds (_root_.GD.N0232.N0719.N0959.d011933 hk w hw)) := by
  rw [(_root_.GD.N0232.N0719.N0859.d011199 k).tendsto_nhds_iff]
  change Tendsto
    (fun n ↦ ((_root_.GD.N0232.N0719.N0845.d010890 hk (thetaSeq n)).location,
      (_root_.GD.N0232.N0719.N0845.d010890 hk (thetaSeq n)).scale))
    atTop
    (nhds ((_root_.GD.N0232.N0719.N0959.d011933 hk w hw).location,
      (_root_.GD.N0232.N0719.N0959.d011933 hk w hw).scale))
  simp only [_root_.GD.N0232.N0719.N0845.d010891,
    _root_.GD.N0232.N0719.N0959.d011934]
  apply tendsto_const_nhds.prodMk_nhds
  apply tendsto_pi_nhds.mpr
  intro i
  rw [show (fun n ↦ (_root_.GD.N0232.N0719.N0845.d010890 hk (thetaSeq n)).scale i) =
      (fun n ↦ _root_.GD.N0232.N0719.N0959.d011924
        (_root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n)) i) by
    funext n
    exact _root_.GD.N0232.N0719.N0959.d011929
      hk (thetaSeq n) i]
  exact _root_.GD.N0232.N0719.N0959.d011941 hk hconv hw i

end

end N0959
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0959.d011930
#print axioms _root_.GD.N0232.N0719.N0959.d011932
#print axioms _root_.GD.N0232.N0719.N0959.d011942
