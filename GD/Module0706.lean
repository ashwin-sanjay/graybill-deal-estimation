import GD.Module0675
import GD.Module0700














namespace GD
namespace N0232
namespace N0719
namespace N0916

noncomputable section

open _root_.GD.N0232.N0719.N0917
open _root_.GD.N0232.N0719.N0867
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N1007
open _root_.GD.N0232.N0719.N0866



@[fun_prop]
theorem d010408
    {k : ℕ} (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    Measurable (fun x : Fin k → ℝ ↦ _root_.GD.N0232.N0719.N0917.d009870 x face) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply (_root_.GD.N0232.N0719.N0917.d009869 face j)

@[fun_prop]
theorem d010409
    {k : ℕ} (sizes : Fin k → ℕ) (commonPower : ℝ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
      _root_.GD.N0232.N0719.N0917.d009873 sizes z.1 z.2 commonPower face) := by
  have hrestrict : Measurable
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
        (_root_.GD.N0232.N0719.N0917.d009870 z.1 face, _root_.GD.N0232.N0719.N0917.d009870 z.2 face)) := by
    exact ((_root_.GD.N0232.N0719.N0916.d010408 face).comp measurable_fst).prodMk
      ((_root_.GD.N0232.N0719.N0916.d010408 face).comp measurable_snd)
  simpa [_root_.GD.N0232.N0719.N0917.d009873, Function.comp_def] using
    (_root_.GD.N0232.N0719.N0867.d010298 (Finset.card_pos.mpr face.2)
      (_root_.GD.N0232.N0719.N0917.d009871 sizes face) (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face)).comp
      hrestrict

@[fun_prop]
theorem d010410
    {k : ℕ} (sizes : Fin k → ℕ) (commonPower : ℝ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
      _root_.GD.N0232.N0719.N0917.d009874 sizes z.1 z.2 commonPower face) := by
  have hrestrict : Measurable
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
        (_root_.GD.N0232.N0719.N0917.d009870 z.1 face, _root_.GD.N0232.N0719.N0917.d009870 z.2 face)) := by
    exact ((_root_.GD.N0232.N0719.N0916.d010408 face).comp measurable_fst).prodMk
      ((_root_.GD.N0232.N0719.N0916.d010408 face).comp measurable_snd)
  simpa [_root_.GD.N0232.N0719.N0917.d009874, Function.comp_def] using
    (_root_.GD.N0232.N0719.N0867.d010300
      (Finset.card_pos.mpr face.2) (_root_.GD.N0232.N0719.N0917.d009871 sizes face)
      (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face)).comp hrestrict

@[fun_prop]
theorem d010411
    {k : ℕ} (sizes : Fin k → ℕ) (commonPower : ℝ)
    (weight : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
      _root_.GD.N0232.N0719.N0917.d009875 sizes z.1 z.2 commonPower weight) := by
  unfold _root_.GD.N0232.N0719.N0917.d009875 _root_.GD.N0232.N0719.N1007.d009826
  fun_prop

@[fun_prop]
theorem d010412
    {k : ℕ} (sizes : Fin k → ℕ) (commonPower : ℝ)
    (weight : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
      _root_.GD.N0232.N0719.N0917.d009876 sizes z.1 z.2 commonPower weight) := by
  unfold _root_.GD.N0232.N0719.N0917.d009876 _root_.GD.N0232.N0719.N1007.d009827
  fun_prop

@[fun_prop]
theorem d010413
    {k : ℕ} (sizes : Fin k → ℕ) (commonPower : ℝ)
    (weight : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
      _root_.GD.N0232.N0719.N0917.d009877 sizes z.1 z.2 commonPower weight) := by
  unfold _root_.GD.N0232.N0719.N0917.d009877 _root_.GD.N0232.N0719.N1007.d009828
  exact (_root_.GD.N0232.N0719.N0916.d010412 sizes commonPower weight).div
    (_root_.GD.N0232.N0719.N0916.d010411 sizes commonPower weight)

@[fun_prop]
theorem d010414
    {k : ℕ} (sizes : Fin k → ℕ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
      _root_.GD.N0232.N0719.N0917.d009880 sizes z.1 z.2) := by
  unfold _root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0917.d009878
  exact _root_.GD.N0232.N0719.N0916.d010413 sizes
    (_root_.GD.N0232.N0719.N0917.d009879 sizes) (fun _ ↦ 1)




def d010415
    {k : ℕ} (sizes : Fin k → ℕ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  _root_.GD.N0232.N0719.N0917.d009880 sizes u.mean u.meanVariance

@[fun_prop]
theorem d010416
    {k : ℕ} (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0916.d010415 sizes) := by
  let dataRule : ((Fin k → ℝ) × (Fin k → ℝ)) → ℝ := fun z ↦
    _root_.GD.N0232.N0719.N0917.d009880 sizes z.1 z.2
  have hdata : Measurable dataRule :=
    _root_.GD.N0232.N0719.N0916.d010414 sizes
  have hcoordinates : Measurable
      (_root_.GD.N0232.N0719.N0900.d009097 : _root_.GD.N0232.N0719.N0900.d009096 k →
        (Fin k → ℝ) × (Fin k → ℝ)) :=
    comap_measurable _root_.GD.N0232.N0719.N0900.d009097
  change Measurable
    (dataRule ∘ (_root_.GD.N0232.N0719.N0900.d009097 :
      _root_.GD.N0232.N0719.N0900.d009096 k → (Fin k → ℝ) × (Fin k → ℝ)))
  exact hdata.comp hcoordinates



def d010417
    {k : ℕ} (sizes : Fin k → ℕ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ := by
  classical
  exact if _root_.GD.N0232.N0719.N0867.d010301 u then
      _root_.GD.N0232.N0719.N0916.d010415 sizes u
    else _root_.GD.N0232.N0719.N0900.d009110 u

@[simp]
theorem d010418
    {k : ℕ} (sizes : Fin k → ℕ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) (hu : _root_.GD.N0232.N0719.N0867.d010301 u) :
    _root_.GD.N0232.N0719.N0916.d010417 sizes u =
      _root_.GD.N0232.N0719.N0916.d010415 sizes u := by
  classical
  simp [_root_.GD.N0232.N0719.N0916.d010417, hu]

@[simp]
theorem d010419
    {k : ℕ} (sizes : Fin k → ℕ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) (hu : ¬ _root_.GD.N0232.N0719.N0867.d010301 u) :
    _root_.GD.N0232.N0719.N0916.d010417 sizes u =
      _root_.GD.N0232.N0719.N0900.d009110 u := by
  classical
  simp [_root_.GD.N0232.N0719.N0916.d010417, hu]

@[fun_prop]
theorem d010420
    {k : ℕ} (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0916.d010417 sizes) := by
  classical
  change Measurable (fun u : _root_.GD.N0232.N0719.N0900.d009096 k ↦
    if _root_.GD.N0232.N0719.N0867.d010301 u then
      _root_.GD.N0232.N0719.N0916.d010415 sizes u
    else _root_.GD.N0232.N0719.N0900.d009110 u)
  exact Measurable.ite (_root_.GD.N0232.N0719.N0867.d010303 k)
    (_root_.GD.N0232.N0719.N0916.d010416 sizes)
    _root_.GD.N0232.N0719.N0900.d009121



theorem d010421
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (b : ℝ) {l : ℝ} (hl : 0 < l)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0916.d010417 sizes
        (_root_.GD.N0232.N0719.N0900.d009101 b l u) =
      b + l * _root_.GD.N0232.N0719.N0916.d010417 sizes u := by
  have hposiff := _root_.GD.N0232.N0719.N0867.d010310 b hl u
  by_cases hpos : _root_.GD.N0232.N0719.N0867.d010301 u
  · have hpos' : _root_.GD.N0232.N0719.N0867.d010301
        (_root_.GD.N0232.N0719.N0900.d009101 b l u) := hposiff.mpr hpos
    rw [_root_.GD.N0232.N0719.N0916.d010418 sizes _ hpos',
      _root_.GD.N0232.N0719.N0916.d010418 sizes u hpos]
    unfold _root_.GD.N0232.N0719.N0916.d010415
    change _root_.GD.N0232.N0719.N0917.d009880 sizes
        (_root_.GD.N0232.N0719.N0866.d009655 b l u.mean)
        (_root_.GD.N0232.N0719.N0866.d009656 l u.meanVariance) = _
    exact _root_.GD.N0232.N0719.N0917.d009896 hk sizes hsizes
      u.mean u.meanVariance hpos b l hl
  · have hpos' : ¬ _root_.GD.N0232.N0719.N0867.d010301
        (_root_.GD.N0232.N0719.N0900.d009101 b l u) := fun h ↦ hpos (hposiff.mp h)
    rw [_root_.GD.N0232.N0719.N0916.d010419 sizes _ hpos',
      _root_.GD.N0232.N0719.N0916.d010419 sizes u hpos]
    exact _root_.GD.N0232.N0719.N0900.d009145 hk b hl.ne' u

end

end N0916
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0916.d010413
#print axioms _root_.GD.N0232.N0719.N0916.d010420
#print axioms _root_.GD.N0232.N0719.N0916.d010421
