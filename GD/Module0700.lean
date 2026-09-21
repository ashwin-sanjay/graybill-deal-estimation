import GD.Module0655
import GD.Module0656
import GD.Module0699





















open MeasureTheory Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0867

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0866
open _root_.GD.N0232.N0719.N0868



@[fun_prop]
theorem d010298
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
      _root_.GD.N0232.N0719.N0929.d009647 hk shape z.1 z.2 s) := by
  unfold _root_.GD.N0232.N0719.N0929.d009647
  let f : ((Fin k → ℝ) × (Fin k → ℝ)) ×
      _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun z ↦ _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk z.2) z.1.1 z.1.2 s
  have hf : StronglyMeasurable f := by
    unfold f _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0928.d009406
      _root_.GD.N0232.N0719.N0928.d009405 _root_.GD.N0232.N0719.N0928.d009409 _root_.GD.N0232.N0719.N0928.d009415
      _root_.GD.N0232.N0719.N0928.d009408
    fun_prop
  simpa [f] using (hf.integral_prod_right'
    (ν := volume.restrict
      (_root_.GD.N0232.N0719.N0955.d009607 k))).measurable

@[fun_prop]
theorem d010299
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
      _root_.GD.N0232.N0719.N0929.d009652 hk shape z.1 z.2 s) := by
  unfold _root_.GD.N0232.N0719.N0929.d009652
  let f : ((Fin k → ℝ) × (Fin k → ℝ)) ×
      _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun z ↦ _root_.GD.N0232.N0719.N0928.d009437 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk z.2) z.1.1 z.1.2 s *
      _root_.GD.N0232.N0719.N0928.d009405
        (_root_.GD.N0232.N0719.N0853.d009567 hk z.2) z.1.1
  have hf : StronglyMeasurable f := by
    unfold f _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0928.d009406
      _root_.GD.N0232.N0719.N0928.d009405 _root_.GD.N0232.N0719.N0928.d009409 _root_.GD.N0232.N0719.N0928.d009415
      _root_.GD.N0232.N0719.N0928.d009408
    fun_prop
  simpa [f] using (hf.integral_prod_right'
    (ν := volume.restrict
      (_root_.GD.N0232.N0719.N0955.d009607 k))).measurable

@[fun_prop]
theorem d010300
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
      _root_.GD.N0232.N0719.N0929.d009653 hk shape z.1 z.2 s) := by
  unfold _root_.GD.N0232.N0719.N0929.d009653
  exact (_root_.GD.N0232.N0719.N0867.d010299 hk shape s).div
    (_root_.GD.N0232.N0719.N0867.d010298 hk shape s)




def d010301 {k : ℕ} (u : _root_.GD.N0232.N0719.N0900.d009096 k) : Prop :=
  ∀ i, 0 < u.meanVariance i



def d010302 (k : ℕ) : Set (_root_.GD.N0232.N0719.N0900.d009096 k) :=
  {u | _root_.GD.N0232.N0719.N0867.d010301 u}

theorem d010303 (k : ℕ) :
    MeasurableSet (_root_.GD.N0232.N0719.N0867.d010302 k) := by
  rw [show _root_.GD.N0232.N0719.N0867.d010302 k =
      ⋂ i : Fin k, {u : _root_.GD.N0232.N0719.N0900.d009096 k | 0 < u.meanVariance i} by
    ext u
    simp [_root_.GD.N0232.N0719.N0867.d010302, _root_.GD.N0232.N0719.N0867.d010301]]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_lt measurable_const
      (_root_.GD.N0232.N0719.N0900.d009100 i)



def d010304
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  _root_.GD.N0232.N0719.N0929.d009653 hk shape u.mean u.meanVariance s

@[fun_prop]
theorem d010305
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0867.d010304 hk shape s) := by
  let dataRule : ((Fin k → ℝ) × (Fin k → ℝ)) → ℝ := fun z ↦
    _root_.GD.N0232.N0719.N0929.d009653 hk shape z.1 z.2 s
  have hdata : Measurable dataRule :=
    _root_.GD.N0232.N0719.N0867.d010300 hk shape s
  have hcoordinates : Measurable
      (_root_.GD.N0232.N0719.N0900.d009097 : _root_.GD.N0232.N0719.N0900.d009096 k →
        (Fin k → ℝ) × (Fin k → ℝ)) :=
    comap_measurable _root_.GD.N0232.N0719.N0900.d009097
  change Measurable
    (dataRule ∘ (_root_.GD.N0232.N0719.N0900.d009097 :
      _root_.GD.N0232.N0719.N0900.d009096 k → (Fin k → ℝ) × (Fin k → ℝ)))
  exact hdata.comp hcoordinates




def d010306
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ := by
  classical
  exact if _root_.GD.N0232.N0719.N0867.d010301 u then
      _root_.GD.N0232.N0719.N0867.d010304 hk shape s u
    else _root_.GD.N0232.N0719.N0900.d009110 u

@[simp]
theorem d010307
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) (hu : _root_.GD.N0232.N0719.N0867.d010301 u) :
    _root_.GD.N0232.N0719.N0867.d010306 hk shape s u =
      _root_.GD.N0232.N0719.N0867.d010304 hk shape s u := by
  classical
  simp [_root_.GD.N0232.N0719.N0867.d010306, hu]

@[simp]
theorem d010308
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) (hu : ¬ _root_.GD.N0232.N0719.N0867.d010301 u) :
    _root_.GD.N0232.N0719.N0867.d010306 hk shape s u =
      _root_.GD.N0232.N0719.N0900.d009110 u := by
  classical
  simp [_root_.GD.N0232.N0719.N0867.d010306, hu]

@[fun_prop]
theorem d010309
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0867.d010306 hk shape s) := by
  classical
  change Measurable (fun u : _root_.GD.N0232.N0719.N0900.d009096 k ↦
    if _root_.GD.N0232.N0719.N0867.d010301 u then
      _root_.GD.N0232.N0719.N0867.d010304 hk shape s u
    else _root_.GD.N0232.N0719.N0900.d009110 u)
  exact Measurable.ite (_root_.GD.N0232.N0719.N0867.d010303 k)
    (_root_.GD.N0232.N0719.N0867.d010305 hk shape s)
    _root_.GD.N0232.N0719.N0900.d009121

theorem d010310
    {k : ℕ} (b : ℝ) {l : ℝ} (hl : 0 < l)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0867.d010301 (_root_.GD.N0232.N0719.N0900.d009101 b l u) ↔
      _root_.GD.N0232.N0719.N0867.d010301 u := by
  unfold _root_.GD.N0232.N0719.N0867.d010301 _root_.GD.N0232.N0719.N0900.d009101
  constructor
  · intro h i
    have hi := h i
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hl)).mp hi
  · intro h i
    exact mul_pos (sq_pos_of_pos hl) (h i)


theorem d010311
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) (s b : ℝ) {l : ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (hl : 0 < l) (u : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0867.d010306 hk shape s
        (_root_.GD.N0232.N0719.N0900.d009101 b l u) =
      b + l * _root_.GD.N0232.N0719.N0867.d010306 hk shape s u := by
  have hposiff := _root_.GD.N0232.N0719.N0867.d010310 b hl u
  by_cases hpos : _root_.GD.N0232.N0719.N0867.d010301 u
  · have hpos' : _root_.GD.N0232.N0719.N0867.d010301
        (_root_.GD.N0232.N0719.N0900.d009101 b l u) := hposiff.mpr hpos
    rw [_root_.GD.N0232.N0719.N0867.d010307
      hk shape s _ hpos',
      _root_.GD.N0232.N0719.N0867.d010307 hk shape s u hpos]
    unfold _root_.GD.N0232.N0719.N0867.d010304
    change _root_.GD.N0232.N0719.N0929.d009653 hk shape
        (_root_.GD.N0232.N0719.N0866.d009655 b l u.mean) (_root_.GD.N0232.N0719.N0866.d009656 l u.meanVariance) s = _
    exact _root_.GD.N0232.N0719.N0866.d009663 hk shape u.mean u.meanVariance
      s b l hshape hpos hpower hl
  · have hpos' : ¬ _root_.GD.N0232.N0719.N0867.d010301
        (_root_.GD.N0232.N0719.N0900.d009101 b l u) := fun h ↦ hpos (hposiff.mp h)
    rw [_root_.GD.N0232.N0719.N0867.d010308
      hk shape s _ hpos',
      _root_.GD.N0232.N0719.N0867.d010308 hk shape s u hpos]
    exact _root_.GD.N0232.N0719.N0900.d009145 hk b hl.ne' u



theorem d010312
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) (s target : ℝ)
    (hshape : ∀ i, 0 < shape i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hpos : _root_.GD.N0232.N0719.N0867.d010301 u) :
    |_root_.GD.N0232.N0719.N0929.d009653 hk shape u.mean u.meanVariance s - target| ≤
      _root_.GD.N0232.N0719.N0910.d010278 target u.mean := by
  have hbound := _root_.GD.N0232.N0719.N0868.d009671 hk shape
    (_root_.GD.N0232.N0719.N0866.d009655 (-target) 1 u.mean) (_root_.GD.N0232.N0719.N0866.d009656 1 u.meanVariance) s
    hshape (by
      intro i
      simpa [_root_.GD.N0232.N0719.N0866.d009656] using hpos i) hpower
  have hcov := _root_.GD.N0232.N0719.N0866.d009663 hk shape u.mean
    u.meanVariance s (-target) 1 hshape hpos hpower zero_lt_one
  rw [hcov] at hbound
  simpa [_root_.GD.N0232.N0719.N0910.d010278, _root_.GD.N0232.N0719.N0866.d009655, _root_.GD.N0232.N0719.N0866.d009656,
    sub_eq_add_neg, add_comm] using hbound



theorem d010313
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) (s target : ℝ)
    (hshape : ∀ i, 0 < shape i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (u : _root_.GD.N0232.N0719.N0900.d009096 k) :
    |_root_.GD.N0232.N0719.N0867.d010306 hk shape s u - target| ≤
      _root_.GD.N0232.N0719.N0910.d010278 target u.mean := by
  by_cases hpos : _root_.GD.N0232.N0719.N0867.d010301 u
  · rw [_root_.GD.N0232.N0719.N0867.d010307 hk shape s u hpos]
    unfold _root_.GD.N0232.N0719.N0867.d010304
    exact _root_.GD.N0232.N0719.N0867.d010312
      hk shape s target hshape hpower u hpos
  · rw [_root_.GD.N0232.N0719.N0867.d010308 hk shape s u hpos]
    exact _root_.GD.N0232.N0719.N0910.d010281 hk target u





theorem d010314
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    MemLp
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
        _root_.GD.N0232.N0719.N0867.d010306 hk shape s
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
      ((_root_.GD.N0232.N0719.N0867.d010309 hk shape s).comp
        (_root_.GD.N0232.N0719.N0933.d009306 k)).sub
          measurable_const |>.aestronglyMeasurable
  · filter_upwards with z
    simpa [_root_.GD.N0232.N0719.N0933.d009305, Real.norm_eq_abs] using
      _root_.GD.N0232.N0719.N0867.d010313
        hk shape s location hshape hpower
          (_root_.GD.N0232.N0719.N0933.d009305 k z)





def d010315
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ)
    (sizes : Fin k → ℕ) (omega : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0867.d010306 hk shape s
    (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)

@[fun_prop]
theorem d010316
    {k : ℕ} (hk : 0 < k) (shape : Fin k → ℝ) (s : ℝ)
    (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0867.d010315 hk shape s sizes) := by
  exact (_root_.GD.N0232.N0719.N0867.d010309 hk shape s).comp
    (_root_.GD.N0232.N0719.N0900.d009115 k sizes)


theorem d010317
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) (s b : ℝ) {l : ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (hl : 0 < l)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 0 < sizes i)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N0867.d010315 hk shape s sizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes b l omega) =
      b + l * _root_.GD.N0232.N0719.N0867.d010315 hk shape s sizes omega := by
  unfold _root_.GD.N0232.N0719.N0867.d010315
  rw [_root_.GD.N0232.N0719.N0900.d009139
    hsizes b l omega]
  exact _root_.GD.N0232.N0719.N0867.d010311
    hk shape s b hshape hpower hl _



theorem d010318
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    MemLp
      (fun omega : _root_.GD.N0232.N0719.N0900.d009094 k sizes ↦
        _root_.GD.N0232.N0719.N0867.d010315 hk shape s sizes omega - location)
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
    (_root_.GD.N0232.N0719.N0867.d010314 hk shape s hshape
      hpower sizes hsizes location scales).comp_measurePreserving hmp
  simpa [split, productLaw, _root_.GD.N0232.N0719.N0867.d010315,
    Function.comp_def,
    _root_.GD.N0232.N0719.N0933.d009307] using h

end

end N0867
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0867.d010309
#print axioms _root_.GD.N0232.N0719.N0867.d010311
#print axioms _root_.GD.N0232.N0719.N0867.d010314
#print axioms _root_.GD.N0232.N0719.N0867.d010316
#print axioms _root_.GD.N0232.N0719.N0867.d010317
#print axioms _root_.GD.N0232.N0719.N0867.d010318
