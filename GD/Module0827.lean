import GD.Module0826















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1606
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1611 _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0933

abbrev d012618 := _root_.GD.N0106.N0428.N0765.N1611.d012588


def d012619 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1606.d012618) : ℝ × ℝ :=
  (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x, _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / eta)


def d012620 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1606.d012618) : ℝ × (ℝ × ℝ) :=
  (_root_.GD.N0106.N0428.N0765.N1611.d012591 x, _root_.GD.N0106.N0428.N0765.N1606.d012619 eta x)

@[fun_prop] theorem d012621 (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1606.d012619 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1606.d012619
  fun_prop

@[fun_prop] theorem d012622 (eta : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1606.d012620 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1606.d012620
  fun_prop


theorem d012623 (scale : ℝ) :
    _root_.GD.N0232.N0719.N0933.d009289 11 scale =
      (gammaMeasure 5 5).map (_root_.GD.N0232.N0719.N0933.d009287 11 scale) := by
  unfold _root_.GD.N0232.N0719.N0933.d009289
  norm_num

theorem d012624 (scale : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009289 11 scale) := by
  rw [_root_.GD.N0106.N0428.N0765.N1606.d012623]
  letI : IsProbabilityMeasure (gammaMeasure 5 5) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  exact Measure.isProbabilityMeasure_map (_root_.GD.N0232.N0719.N0933.d009294 11 scale).aemeasurable


theorem d012625 (scale : ℝ) (hscale : 0 < scale) :
    (_root_.GD.N0232.N0719.N0933.d009289 11 scale).map (fun t : ℝ => 110 * t / scale ^ 2) =
      _root_.GD.N0121.d006346 10 := by
  rw [_root_.GD.N0106.N0428.N0765.N1606.d012623, Measure.map_map (by fun_prop)
    (_root_.GD.N0232.N0719.N0933.d009294 11 scale)]
  have hfun : (fun t : ℝ => 110 * t / scale ^ 2) ∘ _root_.GD.N0232.N0719.N0933.d009287 11 scale =
      (fun q : ℝ => 10 * q) := by
    funext q
    dsimp [_root_.GD.N0232.N0719.N0933.d009287]
    field_simp [hscale.ne']
    <;> ring
  rw [hfun, _root_.GD.N0232.N0719.N0954.d009354
    (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)
    (by norm_num : (0 : ℝ) < 10)]
  norm_num [_root_.GD.N0121.d006346]


theorem d012626 (scales : Fin 2 → ℝ) (hscales : ∀ i, 0 < scales i) :
    (_root_.GD.N0232.N0719.N0933.d009301 2 (fun _ => 11) scales).map
      (fun t => (110 * t 0 / scales 0 ^ 2, 110 * t 1 / scales 1 ^ 2)) =
      (_root_.GD.N0121.d006346 10).prod
        (_root_.GD.N0121.d006346 10) := by
  letI (i : Fin 2) : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009289 11 (scales i)) :=
    _root_.GD.N0106.N0428.N0765.N1606.d012624 (scales i)
  have hp := (measurePreserving_piFinTwo
    (fun i : Fin 2 => _root_.GD.N0232.N0719.N0933.d009289 11 (scales i))).map_eq
  change (_root_.GD.N0232.N0719.N0933.d009301 2 (fun _ => 11) scales).map
    (fun t => (t 0, t 1)) =
    (_root_.GD.N0232.N0719.N0933.d009289 11 (scales 0)).prod
      (_root_.GD.N0232.N0719.N0933.d009289 11 (scales 1)) at hp
  have hfun : (fun t : Fin 2 → ℝ =>
      (110 * t 0 / scales 0 ^ 2, 110 * t 1 / scales 1 ^ 2)) =
      Prod.map (fun t : ℝ => 110 * t / scales 0 ^ 2)
        (fun t : ℝ => 110 * t / scales 1 ^ 2) ∘ (fun t => (t 0, t 1)) := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), hp,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    _root_.GD.N0106.N0428.N0765.N1606.d012625 _ (hscales 0), _root_.GD.N0106.N0428.N0765.N1606.d012625 _ (hscales 1)]


theorem d012627 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0232.N0719.N0933.d009300 2 (fun _ => 11) location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map
      (fun y => y 1 - y 0) =
      gaussianReal 0 ⟨(1 + eta) / 11, by positivity⟩ := by
  let v0 : ℝ≥0 := ⟨1 / 11, by norm_num⟩
  let v1 : ℝ≥0 := ⟨eta / 11, by positivity⟩
  let Q := (gaussianReal location v0).prod (gaussianReal location v1)
  have hmean0 : _root_.GD.N0232.N0719.N0933.d009288 11 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta 0) =
      gaussianReal location v0 := by
    rw [_root_.GD.N0232.N0719.N0933.d009297 (by norm_num : 0 < 11)]
    apply congrArg (gaussianReal location)
    ext
    change _root_.GD.N0106.N0428.N0765.N1611.d012614 eta 0 ^ 2 / (11 : ℝ) = 1 / 11
    norm_num [_root_.GD.N0106.N0428.N0765.N1611.d012614]
  have hmean1 : _root_.GD.N0232.N0719.N0933.d009288 11 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta 1) =
      gaussianReal location v1 := by
    rw [_root_.GD.N0232.N0719.N0933.d009297 (by norm_num : 0 < 11)]
    apply congrArg (gaussianReal location)
    ext
    change _root_.GD.N0106.N0428.N0765.N1611.d012614 eta 1 ^ 2 / (11 : ℝ) = eta / 11
    norm_num [_root_.GD.N0106.N0428.N0765.N1611.d012614, Real.sq_sqrt heta.le]
  have hp := (measurePreserving_piFinTwo
    (fun i : Fin 2 => _root_.GD.N0232.N0719.N0933.d009288 11 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta i))).map_eq
  change (_root_.GD.N0232.N0719.N0933.d009300 2 (fun _ => 11) location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map
    (fun y => (y 0, y 1)) =
    (_root_.GD.N0232.N0719.N0933.d009288 11 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta 0)).prod
      (_root_.GD.N0232.N0719.N0933.d009288 11 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta 1)) at hp
  rw [hmean0, hmean1] at hp
  have hneg : Q.map (fun p : ℝ × ℝ => -p.1) = gaussianReal (-location) v0 := by
    change ((gaussianReal location v0).prod (gaussianReal location v1)).map
      ((fun z : ℝ => -z) ∘ Prod.fst) = _
    rw [← Measure.map_map measurable_neg measurable_fst,
      measurePreserving_fst.map_eq, gaussianReal_map_neg]
  have hsnd : Q.map (fun p : ℝ × ℝ => p.2) = gaussianReal location v1 :=
    measurePreserving_snd.map_eq
  have hind : IndepFun (fun p : ℝ × ℝ => -p.1) (fun p => p.2) Q :=
    indepFun_prod measurable_neg measurable_id
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind hneg hsnd
  have hv : v0 + v1 = (⟨(1 + eta) / 11, by positivity⟩ : ℝ≥0) := by
    ext
    change 1 / 11 + eta / 11 = (1 + eta) / 11
    ring
  rw [neg_add_cancel, hv] at hsum
  have hdiff : Q.map (fun p : ℝ × ℝ => p.2 - p.1) =
      gaussianReal 0 ⟨(1 + eta) / 11, by positivity⟩ := by
    convert hsum using 1
    congr 1
    funext p
    change p.2 - p.1 = -p.1 + p.2
    ring
  have hfun : (fun y : Fin 2 → ℝ => y 1 - y 0) =
      (fun p : ℝ × ℝ => p.2 - p.1) ∘ (fun y => (y 0, y 1)) := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), hp]
  exact hdiff


theorem d012628 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map (_root_.GD.N0106.N0428.N0765.N1606.d012620 eta) =
      (gaussianReal 0 ⟨(1 + eta) / 11, by positivity⟩).prod
        ((_root_.GD.N0121.d006346 10).prod
          (_root_.GD.N0121.d006346 10)) := by
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009300 2 (fun _ => 11) location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) := by
    unfold _root_.GD.N0232.N0719.N0933.d009300
    infer_instance
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009301 2 (fun _ => 11) (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) :=
    _root_.GD.N0232.N0719.N0910.d010289
      (fun _ => 11) (by intro i; norm_num) _
  have hfun : _root_.GD.N0106.N0428.N0765.N1606.d012620 eta =
      Prod.map (fun y : Fin 2 → ℝ => y 1 - y 0)
        (fun t : Fin 2 → ℝ =>
          (110 * t 0 / _root_.GD.N0106.N0428.N0765.N1611.d012614 eta 0 ^ 2,
            110 * t 1 / _root_.GD.N0106.N0428.N0765.N1611.d012614 eta 1 ^ 2)) ∘
        _root_.GD.N0232.N0719.N0933.d009304 2 (fun _ => 11) := by
    funext x
    apply Prod.ext
    · change _root_.GD.N0106.N0428.N0765.N1611.d012591 x =
        (_root_.GD.N0232.N0719.N0933.d009304 2 (fun _ => 11) x).1 1 -
          (_root_.GD.N0232.N0719.N0933.d009304 2 (fun _ => 11) x).1 0
      rw [_root_.GD.N0106.N0428.N0765.N1611.d012603, _root_.GD.N0106.N0428.N0765.N1611.d012603]
      rfl
    · change (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x, _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / eta) =
        (110 * (_root_.GD.N0232.N0719.N0933.d009304 2 (fun _ => 11) x).2 0 /
            _root_.GD.N0106.N0428.N0765.N1611.d012614 eta 0 ^ 2,
          110 * (_root_.GD.N0232.N0719.N0933.d009304 2 (fun _ => 11) x).2 1 /
            _root_.GD.N0106.N0428.N0765.N1611.d012614 eta 1 ^ 2)
      rw [_root_.GD.N0106.N0428.N0765.N1611.d012602, _root_.GD.N0106.N0428.N0765.N1611.d012602]
      apply Prod.ext <;> norm_num [_root_.GD.N0106.N0428.N0765.N1611.d012614, Real.sq_sqrt heta.le] <;> ring
  rw [hfun, ← Measure.map_map (by fun_prop)
    (_root_.GD.N0232.N0719.N0933.d009308 2 (fun _ => 11)),
    (_root_.GD.N0106.N0428.N0765.N1611.d012604 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map_eq,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    _root_.GD.N0106.N0428.N0765.N1606.d012627 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1606.d012626 _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)]


theorem d012629 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map (_root_.GD.N0106.N0428.N0765.N1606.d012619 eta) =
      (_root_.GD.N0121.d006346 10).prod
        (_root_.GD.N0121.d006346 10) := by
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 10) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hfun : _root_.GD.N0106.N0428.N0765.N1606.d012619 eta = Prod.snd ∘ _root_.GD.N0106.N0428.N0765.N1606.d012620 eta := rfl
  rw [hfun, ← Measure.map_map measurable_snd (_root_.GD.N0106.N0428.N0765.N1606.d012622 eta),
    _root_.GD.N0106.N0428.N0765.N1606.d012628 location eta heta]
  exact measurePreserving_snd.map_eq


theorem d012630 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map _root_.GD.N0106.N0428.N0765.N1611.d012591 =
      gaussianReal 0 ⟨(1 + eta) / 11, by positivity⟩ := by
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 10) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hfun : _root_.GD.N0106.N0428.N0765.N1611.d012591 = Prod.fst ∘ _root_.GD.N0106.N0428.N0765.N1606.d012620 eta := rfl
  rw [hfun, ← Measure.map_map measurable_fst (_root_.GD.N0106.N0428.N0765.N1606.d012622 eta),
    _root_.GD.N0106.N0428.N0765.N1606.d012628 location eta heta]
  exact measurePreserving_fst.map_eq


theorem d012631 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map (_root_.GD.N0106.N0428.N0765.N1611.d012590 0) =
      _root_.GD.N0121.d006346 10 := by
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 10) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hfun : _root_.GD.N0106.N0428.N0765.N1611.d012590 0 = Prod.fst ∘ _root_.GD.N0106.N0428.N0765.N1606.d012619 eta := rfl
  rw [hfun, ← Measure.map_map measurable_fst (_root_.GD.N0106.N0428.N0765.N1606.d012621 eta),
    _root_.GD.N0106.N0428.N0765.N1606.d012629 location eta heta]
  exact measurePreserving_fst.map_eq


theorem d012632 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / eta) =
      _root_.GD.N0121.d006346 10 := by
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 10) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hfun : (fun x : _root_.GD.N0106.N0428.N0765.N1606.d012618 => _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / eta) =
      Prod.snd ∘ _root_.GD.N0106.N0428.N0765.N1606.d012619 eta := rfl
  rw [hfun, ← Measure.map_map measurable_snd (_root_.GD.N0106.N0428.N0765.N1606.d012621 eta),
    _root_.GD.N0106.N0428.N0765.N1606.d012629 location eta heta]
  exact measurePreserving_snd.map_eq


theorem d012633 (location eta : ℝ) (heta : 0 < eta) :
    IndepFun _root_.GD.N0106.N0428.N0765.N1611.d012591 (_root_.GD.N0106.N0428.N0765.N1606.d012619 eta) (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1611.d012595 _root_.GD.N0232.N0719.d009176
    infer_instance
  apply (indepFun_iff_map_prod_eq_prod_map_map _root_.GD.N0106.N0428.N0765.N1611.d012598.aemeasurable
    (_root_.GD.N0106.N0428.N0765.N1606.d012621 eta).aemeasurable).2
  change (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map (_root_.GD.N0106.N0428.N0765.N1606.d012620 eta) = _
  rw [_root_.GD.N0106.N0428.N0765.N1606.d012628 location eta heta, _root_.GD.N0106.N0428.N0765.N1606.d012630 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1606.d012629 location eta heta]


theorem d012634 (location eta : ℝ) (heta : 0 < eta) :
    IndepFun (_root_.GD.N0106.N0428.N0765.N1611.d012590 0) (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / eta)
      (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1611.d012595 _root_.GD.N0232.N0719.d009176
    infer_instance
  apply (indepFun_iff_map_prod_eq_prod_map_map (_root_.GD.N0106.N0428.N0765.N1611.d012597 0).aemeasurable
    ((_root_.GD.N0106.N0428.N0765.N1611.d012597 1).div_const eta).aemeasurable).2
  change (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map (_root_.GD.N0106.N0428.N0765.N1606.d012619 eta) = _
  rw [_root_.GD.N0106.N0428.N0765.N1606.d012629 location eta heta, _root_.GD.N0106.N0428.N0765.N1606.d012631 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1606.d012632 location eta heta]


theorem d012635 (x : _root_.GD.N0106.N0428.N0765.N1606.d012618) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0900.d009104 2 (fun _ => 11) x) 1 =
      _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x + _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) := by
  let s := _root_.GD.N0232.N0719.N0900.d009104 2 (fun _ => 11) x
  have hv (i : Fin 2) : s.meanVariance i = _root_.GD.N0106.N0428.N0765.N1611.d012590 i x / 110 := by
    change (_root_.GD.N0232.N0719.N0933.d009304 2 (fun _ => 11) x).2 i = _
    exact _root_.GD.N0106.N0428.N0765.N1611.d012602 x i
  have hprec (i : Fin 2) : _root_.GD.N0232.N0719.N0900.d009106 s i = (_root_.GD.N0106.N0428.N0765.N1611.d012590 i x / 110)⁻¹ := by
    unfold _root_.GD.N0232.N0719.N0900.d009106
    rw [hv, _root_.GD.N0232.N0719.N0900.d009127 (div_pos (hx i) (by norm_num))]
  have htotal : _root_.GD.N0232.N0719.N0900.d009107 s =
      (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / 110)⁻¹ + (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / 110)⁻¹ := by
    simp only [_root_.GD.N0232.N0719.N0900.d009107, Fin.sum_univ_two, hprec]
  have ht : 0 < _root_.GD.N0232.N0719.N0900.d009107 s := by
    rw [htotal]
    exact add_pos (inv_pos.mpr (div_pos (hx 0) (by norm_num)))
      (inv_pos.mpr (div_pos (hx 1) (by norm_num)))
  change _root_.GD.N0232.N0719.N0900.d009108 s 1 = _
  rw [_root_.GD.N0232.N0719.N0900.d009108, if_neg ht.ne', hprec, htotal]
  have hsum : _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x + _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x ≠ 0 := (add_pos (hx 0) (hx 1)).ne'
  field_simp [(hx 0).ne', (hx 1).ne', hsum]
  <;> rw [add_comm (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x), div_self hsum]


theorem d012636 (x : _root_.GD.N0106.N0428.N0765.N1606.d012618) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11) x =
      _root_.GD.N0106.N0428.N0765.N1611.d012589 0 x + _root_.GD.N0106.N0428.N0765.N1611.d012591 x * (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x + _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x)) := by
  let s := _root_.GD.N0232.N0719.N0900.d009104 2 (fun _ => 11) x
  have hw := _root_.GD.N0232.N0719.N0900.d009131 (by norm_num : 0 < 2) s
  rw [Fin.sum_univ_two] at hw
  have h1 := _root_.GD.N0106.N0428.N0765.N1606.d012635 x hx
  change _root_.GD.N0232.N0719.N0900.d009108 s 1 = _ at h1
  change (∑ i : Fin 2, _root_.GD.N0232.N0719.N0900.d009108 s i * s.mean i) = _
  rw [Fin.sum_univ_two]
  change _root_.GD.N0232.N0719.N0900.d009108 s 0 * _root_.GD.N0106.N0428.N0765.N1611.d012589 0 x + _root_.GD.N0232.N0719.N0900.d009108 s 1 * _root_.GD.N0106.N0428.N0765.N1611.d012589 1 x = _
  rw [h1] at hw ⊢
  have h0 : _root_.GD.N0232.N0719.N0900.d009108 s 0 =
      1 - _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x + _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) := by linarith only [hw]
  rw [h0]
  dsimp [_root_.GD.N0106.N0428.N0765.N1611.d012591]
  ring



theorem d012637 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).map (_root_.GD.N0106.N0428.N0765.N1606.d012620 eta) =
        (gaussianReal 0 ⟨(1 + eta) / 11, by positivity⟩).prod
          ((_root_.GD.N0121.d006346 10).prod
            (_root_.GD.N0121.d006346 10)) ∧
      IndepFun _root_.GD.N0106.N0428.N0765.N1611.d012591 (_root_.GD.N0106.N0428.N0765.N1606.d012619 eta) (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) ∧
      IndepFun (_root_.GD.N0106.N0428.N0765.N1611.d012590 0) (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / eta)
        (_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)) ∧
      Measurable _root_.GD.N0106.N0428.N0765.N1611.d012593 ∧
      (∀ᵐ x ∂_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta), x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) ∧
      _root_.GD.N0106.N0428.N0765.N1611.d012612 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta) < ⊤ ∧
      (∀ x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594, _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11) x =
        _root_.GD.N0106.N0428.N0765.N1611.d012589 0 x + _root_.GD.N0106.N0428.N0765.N1611.d012591 x * (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x + _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x))) := by
  obtain ⟨hm, hp, hr⟩ := _root_.GD.N0106.N0428.N0765.N1611.d012617 location eta heta
  exact ⟨_root_.GD.N0106.N0428.N0765.N1606.d012628 location eta heta, _root_.GD.N0106.N0428.N0765.N1606.d012633 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1606.d012634 location eta heta, hm, hp, hr, _root_.GD.N0106.N0428.N0765.N1606.d012636⟩

end
end GD.N0106.N0428.N0765.N1606

#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012625
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012626
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012627
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012628
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012629
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012630
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012631
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012632
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012633
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012634
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012635
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012636
#print axioms _root_.GD.N0106.N0428.N0765.N1606.d012637
