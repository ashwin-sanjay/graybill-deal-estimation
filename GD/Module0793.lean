import GD.Module0774
import GD.Module0784




















open Filter Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0958

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0819
open _root_.GD.N0232.N0719.N0820
open _root_.GD.N0232.N0719.N0959


def d012032 {k : ℕ}
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  ∑ i ∈ active, theta.scale i


def d012033 {k : ℕ}
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : ℝ :=
  theta.scale i / _root_.GD.N0232.N0719.N0958.d012032 active theta


def d012034 {k : ℕ}
    (active : Finset (Fin k)) (w : Fin k → ℝ) : ℝ :=
  ∑ i ∈ active, (Real.sqrt (w i))⁻¹


def d012035 {k : ℕ}
    (active : Finset (Fin k)) (w : Fin k → ℝ)
    (i : Fin k) : ℝ :=
  (Real.sqrt (w i))⁻¹ /
    _root_.GD.N0232.N0719.N0958.d012034 active w



theorem d012036
    {k : ℕ} {active : Finset (Fin k)} (hactive : active.Nonempty)
    {w : Fin k → ℝ} (hw : ∀ i ∈ active, 0 < w i) :
    0 < _root_.GD.N0232.N0719.N0958.d012034 active w := by
  obtain ⟨i, hi⟩ := hactive
  unfold _root_.GD.N0232.N0719.N0958.d012034
  exact Finset.sum_pos'
    (fun j hj ↦ (inv_pos.mpr (Real.sqrt_pos.2 (hw j hj))).le)
    ⟨i, hi, inv_pos.mpr (Real.sqrt_pos.2 (hw i hi))⟩


theorem d012037
    {k : ℕ} (hk : 0 < k) (active : Finset (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0958.d012034 active
        (_root_.GD.N0232.N0719.N0819.d011729 theta) =
      _root_.GD.N0232.N0719.N0958.d012032 active theta *
        Real.sqrt (_root_.GD.N0232.N0719.N0815.d010926 theta) := by
  unfold _root_.GD.N0232.N0719.N0958.d012034 _root_.GD.N0232.N0719.N0958.d012032
  simp_rw [_root_.GD.N0232.N0719.N0959.d011927 hk theta]
  exact (Finset.sum_mul ..).symm


theorem d012038
    {k : ℕ} (hk : 0 < k) (active : Finset (Fin k))
    (hactive : active.Nonempty) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (i : Fin k) :
    _root_.GD.N0232.N0719.N0958.d012033 active theta i =
      _root_.GD.N0232.N0719.N0958.d012035 active
        (_root_.GD.N0232.N0719.N0819.d011729 theta) i := by
  have hactiveScale : _root_.GD.N0232.N0719.N0958.d012032 active theta ≠ 0 := by
    unfold _root_.GD.N0232.N0719.N0958.d012032
    exact (Finset.sum_pos'
      (fun j _ ↦ (theta.scale_pos j).le)
      (by
        obtain ⟨j, hj⟩ := hactive
        exact ⟨j, hj, theta.scale_pos j⟩)).ne'
  have hprecisionSqrt : Real.sqrt (_root_.GD.N0232.N0719.N0815.d010926 theta) ≠ 0 :=
    (Real.sqrt_pos.2 (_root_.GD.N0232.N0719.N0815.d010927 hk theta)).ne'
  unfold _root_.GD.N0232.N0719.N0958.d012033 _root_.GD.N0232.N0719.N0958.d012035
  rw [_root_.GD.N0232.N0719.N0959.d011927 hk theta,
    _root_.GD.N0232.N0719.N0958.d012037
      hk active theta]
  field_simp [hactiveScale, hprecisionSqrt]



theorem d012039
    {k : ℕ} {active : Finset (Fin k)}
    {wSeq : ℕ → Fin k → ℝ} {w : Fin k → ℝ}
    (hactive : active.Nonempty)
    (hconv : Tendsto wSeq atTop (nhds w))
    (hw : ∀ i ∈ active, 0 < w i)
    (i : Fin k) (hi : i ∈ active) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0958.d012035 active (wSeq n) i)
      atTop (nhds (_root_.GD.N0232.N0719.N0958.d012035 active w i)) := by
  have hinv : ∀ j ∈ active,
      Tendsto (fun n ↦ (Real.sqrt (wSeq n j))⁻¹)
        atTop (nhds ((Real.sqrt (w j))⁻¹)) := by
    intro j hj
    exact ((Real.continuous_sqrt.tendsto (w j)).comp
      (tendsto_pi_nhds.mp hconv j)).inv₀
        (Real.sqrt_pos.2 (hw j hj)).ne'
  have hdenom : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0958.d012034 active (wSeq n))
      atTop (nhds (_root_.GD.N0232.N0719.N0958.d012034 active w)) := by
    unfold _root_.GD.N0232.N0719.N0958.d012034
    exact tendsto_finsetSum active (fun j hj ↦ hinv j hj)
  unfold _root_.GD.N0232.N0719.N0958.d012035
  exact (hinv i hi).div hdenom
    (_root_.GD.N0232.N0719.N0958.d012036 hactive hw).ne'



theorem d012040
    {k : ℕ} {active : Finset (Fin k)}
    {wSeq : ℕ → Fin k → ℝ} {w : Fin k → ℝ}
    (hactive : active.Nonempty)
    (hconv : Tendsto wSeq atTop (nhds w))
    (hw : ∀ i ∈ active, 0 < w i)
    (hwSeq : ∀ n i, 0 < wSeq n i)
    (j : Fin k) (hwj : w j = 0) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0958.d012035 active (wSeq n) j)
      atTop atTop := by
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (wSeq n j))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, hwj, Real.sqrt_zero] using
      ((Real.continuous_sqrt.tendsto (w j)).comp
        (tendsto_pi_nhds.mp hconv j))
  have hsqrtWithin : Tendsto (fun n ↦ Real.sqrt (wSeq n j))
      atTop (nhdsWithin 0 (Ioi 0)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hsqrt,
      Filter.Eventually.of_forall (fun n ↦ Real.sqrt_pos.2 (hwSeq n j))⟩
  have hinvTop : Tendsto
      (fun n ↦ (Real.sqrt (wSeq n j))⁻¹) atTop atTop :=
    hsqrtWithin.inv_tendsto_nhdsGT_zero
  have hinv : ∀ i ∈ active,
      Tendsto (fun n ↦ (Real.sqrt (wSeq n i))⁻¹)
        atTop (nhds ((Real.sqrt (w i))⁻¹)) := by
    intro i hi
    exact ((Real.continuous_sqrt.tendsto (w i)).comp
      (tendsto_pi_nhds.mp hconv i)).inv₀
        (Real.sqrt_pos.2 (hw i hi)).ne'
  have hdenom : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0958.d012034 active (wSeq n))
      atTop (nhds (_root_.GD.N0232.N0719.N0958.d012034 active w)) := by
    unfold _root_.GD.N0232.N0719.N0958.d012034
    exact tendsto_finsetSum active (fun i hi ↦ hinv i hi)
  have hdenomInv : Tendsto
      (fun n ↦ (_root_.GD.N0232.N0719.N0958.d012034 active (wSeq n))⁻¹)
      atTop (nhds ((_root_.GD.N0232.N0719.N0958.d012034 active w)⁻¹)) :=
    hdenom.inv₀ (_root_.GD.N0232.N0719.N0958.d012036 hactive hw).ne'
  have hproduct : Tendsto
      (fun n ↦ (Real.sqrt (wSeq n j))⁻¹ *
        (_root_.GD.N0232.N0719.N0958.d012034 active (wSeq n))⁻¹)
      atTop atTop :=
    hinvTop.atTop_mul_pos
      (inv_pos.mpr (_root_.GD.N0232.N0719.N0958.d012036 hactive hw))
      hdenomInv
  simpa [_root_.GD.N0232.N0719.N0958.d012035, div_eq_mul_inv] using hproduct







theorem d012041
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (i : Fin k) (hi : i ∈ z.1.active) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0958.d012033 z.1.active (z.1.thetaSeq n) i)
      atTop
      (nhds (_root_.GD.N0232.N0719.N0958.d012035 z.1.active z.1.w i)) := by
  rcases z.2 with
    ⟨_hp, _hq, _hne, _hw, hsupport, hactive, _hdepth,
      hweights, _hinactive, _hlower, _htax, _hpGap, _hqGap⟩
  have hpos : ∀ j ∈ z.1.active, 0 < z.1.w j := by
    intro j hj
    rw [hsupport] at hj
    exact (_root_.GD.N0232.N0719.N0819.d011734 z.1.w j).1 hj
  have hcoordinate := _root_.GD.N0232.N0719.N0958.d012039
    hactive hweights hpos i hi
  have hfun :
      (fun n ↦ _root_.GD.N0232.N0719.N0958.d012033 z.1.active (z.1.thetaSeq n) i) =
        (fun n ↦ _root_.GD.N0232.N0719.N0958.d012035 z.1.active
          (_root_.GD.N0232.N0719.N0819.d011729 (z.1.thetaSeq n)) i) := by
    funext n
    exact _root_.GD.N0232.N0719.N0958.d012038
      (by omega : 0 < k) z.1.active hactive (z.1.thetaSeq n) i
  rw [hfun]
  exact hcoordinate







theorem d012042
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (j : Fin k) (hj : j ∉ z.1.active) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0958.d012033 z.1.active (z.1.thetaSeq n) j)
      atTop atTop := by
  rcases z.2 with
    ⟨_hp, _hq, _hne, hwSimplex, hsupport, hactive, _hdepth,
      hweights, _hinactive, _hlower, _htax, _hpGap, _hqGap⟩
  have hpos : ∀ i ∈ z.1.active, 0 < z.1.w i := by
    intro i hi
    rw [hsupport] at hi
    exact (_root_.GD.N0232.N0719.N0819.d011734 z.1.w i).1 hi
  have hwjNonpos : ¬ 0 < z.1.w j := by
    intro hwj
    apply hj
    rw [hsupport]
    exact (_root_.GD.N0232.N0719.N0819.d011734 z.1.w j).2 hwj
  have hwj : z.1.w j = 0 :=
    le_antisymm (le_of_not_gt hwjNonpos) (hwSimplex.1 j)
  have hcoordinate :=
    _root_.GD.N0232.N0719.N0958.d012040
      hactive hweights hpos
      (fun n i ↦ _root_.GD.N0232.N0719.N0959.d011926
        (by omega : 0 < k) (z.1.thetaSeq n) i)
      j hwj
  have hfun :
      (fun n ↦ _root_.GD.N0232.N0719.N0958.d012033 z.1.active (z.1.thetaSeq n) j) =
        (fun n ↦ _root_.GD.N0232.N0719.N0958.d012035 z.1.active
          (_root_.GD.N0232.N0719.N0819.d011729 (z.1.thetaSeq n)) j) := by
    funext n
    exact _root_.GD.N0232.N0719.N0958.d012038
      (by omega : 0 < k) z.1.active hactive (z.1.thetaSeq n) j
  rw [hfun]
  exact hcoordinate




theorem d012043
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) :
    (∀ i, i ∈ z.1.active →
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0958.d012033 z.1.active (z.1.thetaSeq n) i)
        atTop
        (nhds (_root_.GD.N0232.N0719.N0958.d012035 z.1.active z.1.w i))) ∧
      (∀ j, j ∉ z.1.active →
        Tendsto
          (fun n ↦ _root_.GD.N0232.N0719.N0958.d012033 z.1.active (z.1.thetaSeq n) j)
          atTop atTop) := by
  exact ⟨
    fun i hi ↦ _root_.GD.N0232.N0719.N0958.d012041 z i hi,
    fun j hj ↦
      _root_.GD.N0232.N0719.N0958.d012042 z j hj⟩

end

end N0958
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0958.d012038
#print axioms _root_.GD.N0232.N0719.N0958.d012039
#print axioms _root_.GD.N0232.N0719.N0958.d012041
#print axioms _root_.GD.N0232.N0719.N0958.d012042
#print axioms _root_.GD.N0232.N0719.N0958.d012043
