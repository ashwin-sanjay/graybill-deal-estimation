import GD.Module0286
import GD.Module0838

set_option warningAsError true










open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0791

noncomputable section

open _root_.GD.N0235
open _root_.GD.N0228.N0547.N0778 _root_.GD.N0228.N0547.N0779


def d012848 (p : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) :=
  (p.2.1, (p.1, p.2.2))

@[fun_prop]
theorem d012849 : Measurable _root_.GD.N0228.N0547.N0791.d012848 := by
  unfold _root_.GD.N0228.N0547.N0791.d012848
  fun_prop



theorem d012850
    (mu nu tau : Measure ℝ) [SFinite mu] [SFinite nu] [SFinite tau] :
    (mu.prod (nu.prod tau)).map _root_.GD.N0228.N0547.N0791.d012848 =
      nu.prod (mu.prod tau) := by
  let assoc : ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
    MeasurableEquiv.prodAssoc
  let unassoc : (ℝ × (ℝ × ℝ)) ≃ᵐ ((ℝ × ℝ) × ℝ) := assoc.symm
  let middleSwap : ((ℝ × ℝ) × ℝ) → ((ℝ × ℝ) × ℝ) :=
    Prod.map Prod.swap id
  have hMiddleMeas : Measurable middleSwap := by
    unfold middleSwap
    fun_prop
  have hUnassoc :
      (mu.prod (nu.prod tau)).map unassoc = (mu.prod nu).prod tau := by
    exact (MeasurePreserving.symm assoc
      (measurePreserving_prodAssoc mu nu tau)).map_eq
  have hMiddle :
      ((mu.prod nu).prod tau).map middleSwap =
        (nu.prod mu).prod tau := by
    calc
      ((mu.prod nu).prod tau).map middleSwap =
          ((mu.prod nu).map Prod.swap).prod (tau.map id) := by
        exact (Measure.map_prod_map (mu.prod nu) tau
          measurable_swap measurable_id).symm
      _ = (nu.prod mu).prod tau := by
        rw [Measure.prod_swap, Measure.map_id]
  have hfun : _root_.GD.N0228.N0547.N0791.d012848 = assoc ∘ middleSwap ∘ unassoc := by
    funext p
    rfl
  calc
    (mu.prod (nu.prod tau)).map _root_.GD.N0228.N0547.N0791.d012848 =
        (((mu.prod (nu.prod tau)).map unassoc).map middleSwap).map assoc := by
      rw [Measure.map_map hMiddleMeas unassoc.measurable,
        Measure.map_map assoc.measurable
          (hMiddleMeas.comp unassoc.measurable), hfun]
    _ = (((mu.prod nu).prod tau).map middleSwap).map assoc := by
      rw [hUnassoc]
    _ = ((nu.prod mu).prod tau).map assoc := by
      rw [hMiddle]
    _ = nu.prod (mu.prod tau) := Measure.prodAssoc_prod



def d012851 (p : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) :=
  (p.1, _root_.GD.N0155.d006306 p.2)

@[fun_prop]
theorem d012852 : Measurable _root_.GD.N0228.N0547.N0791.d012851 := by
  unfold _root_.GD.N0228.N0547.N0791.d012851 _root_.GD.N0155.d006306
  fun_prop



def d012853 (p : ℝ × (ℝ × ℝ)) : (ℝ × ℝ) × ℝ :=
  ((p.1, p.2.1), p.2.2)

@[fun_prop]
theorem d012854 : Measurable _root_.GD.N0228.N0547.N0791.d012853 := by
  unfold _root_.GD.N0228.N0547.N0791.d012853
  fun_prop

theorem d012855
    (mu nu tau : Measure ℝ) [SFinite nu] [SFinite tau] :
    (mu.prod (nu.prod tau)).map _root_.GD.N0228.N0547.N0791.d012853 =
      (mu.prod nu).prod tau := by
  let assoc : ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
    MeasurableEquiv.prodAssoc
  have hfun : _root_.GD.N0228.N0547.N0791.d012853 = assoc.symm := by
    rfl
  rw [hfun]
  exact (MeasurePreserving.symm assoc
    (measurePreserving_prodAssoc mu nu tau)).map_eq




theorem d012856
    {a b c r : ℝ} (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    ((gammaMeasure a r).prod
      ((gammaMeasure b r).prod (gammaMeasure c r))).map _root_.GD.N0228.N0547.N0791.d012851 =
      (gammaMeasure a r).prod
        ((betaMeasure b c).prod (gammaMeasure (b + c) r)) := by
  letI : IsProbabilityMeasure (gammaMeasure b r) :=
    isProbabilityMeasure_gammaMeasure hb hr
  letI : IsProbabilityMeasure (gammaMeasure c r) :=
    isProbabilityMeasure_gammaMeasure hc hr
  calc
    ((gammaMeasure a r).prod
      ((gammaMeasure b r).prod (gammaMeasure c r))).map _root_.GD.N0228.N0547.N0791.d012851 =
        ((gammaMeasure a r).map id).prod
          (((gammaMeasure b r).prod (gammaMeasure c r)).map
            _root_.GD.N0155.d006306) := by
      exact (Measure.map_prod_map (gammaMeasure a r)
        ((gammaMeasure b r).prod (gammaMeasure c r))
        measurable_id _root_.GD.N0228.N0547.N0779.d012805).symm
    _ = (gammaMeasure a r).prod
        ((betaMeasure b c).prod (gammaMeasure (b + c) r)) := by
      rw [Measure.map_id,
        _root_.GD.N0228.N0547.N0779.d012813 hb hc hr]



theorem d012857
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    ((betaMeasure b c).prod
      ((gammaMeasure a r).prod (gammaMeasure (b + c) r))).map
        _root_.GD.N0228.N0547.N0791.d012851 =
      (betaMeasure b c).prod
        ((betaMeasure a (b + c)).prod (gammaMeasure (a + (b + c)) r)) := by
  letI : IsProbabilityMeasure (betaMeasure b c) :=
    isProbabilityMeasureBeta hb hc
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaMeasure (b + c) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos hb hc) hr
  calc
    ((betaMeasure b c).prod
      ((gammaMeasure a r).prod (gammaMeasure (b + c) r))).map
        _root_.GD.N0228.N0547.N0791.d012851 =
      ((betaMeasure b c).map id).prod
        (((gammaMeasure a r).prod (gammaMeasure (b + c) r)).map
          _root_.GD.N0155.d006306) := by
      exact (Measure.map_prod_map (betaMeasure b c)
        ((gammaMeasure a r).prod (gammaMeasure (b + c) r))
        measurable_id _root_.GD.N0228.N0547.N0779.d012805).symm
    _ = (betaMeasure b c).prod
        ((betaMeasure a (b + c)).prod
          (gammaMeasure (a + (b + c)) r)) := by
      rw [Measure.map_id,
        _root_.GD.N0228.N0547.N0779.d012813 ha (add_pos hb hc) hr]




def d012858 (p : ℝ × (ℝ × ℝ)) : (ℝ × ℝ) × ℝ :=
  _root_.GD.N0228.N0547.N0791.d012853
    (_root_.GD.N0228.N0547.N0791.d012848
      (_root_.GD.N0228.N0547.N0791.d012851
        (_root_.GD.N0228.N0547.N0791.d012848 (_root_.GD.N0228.N0547.N0791.d012851 p))))

@[fun_prop]
theorem d012859 :
    Measurable _root_.GD.N0228.N0547.N0791.d012858 := by
  unfold _root_.GD.N0228.N0547.N0791.d012858
  fun_prop




theorem d012860
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    ((gammaMeasure a r).prod
      ((gammaMeasure b r).prod (gammaMeasure c r))).map
        _root_.GD.N0228.N0547.N0791.d012858 =
      ((betaMeasure a (b + c)).prod (betaMeasure b c)).prod
        (gammaMeasure (a + b + c) r) := by
  let source := (gammaMeasure a r).prod
    ((gammaMeasure b r).prod (gammaMeasure c r))
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaMeasure (b + c) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos hb hc) hr
  letI : IsProbabilityMeasure (gammaMeasure (a + (b + c)) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha (add_pos hb hc)) hr
  letI : IsProbabilityMeasure (betaMeasure b c) :=
    isProbabilityMeasureBeta hb hc
  letI : IsProbabilityMeasure (betaMeasure a (b + c)) :=
    isProbabilityMeasureBeta ha (add_pos hb hc)
  have hcompose : source.map _root_.GD.N0228.N0547.N0791.d012858 =
      (((((source.map _root_.GD.N0228.N0547.N0791.d012851).map _root_.GD.N0228.N0547.N0791.d012848).map
        _root_.GD.N0228.N0547.N0791.d012851).map _root_.GD.N0228.N0547.N0791.d012848).map _root_.GD.N0228.N0547.N0791.d012853) := by
    have hfun : _root_.GD.N0228.N0547.N0791.d012858 =
        _root_.GD.N0228.N0547.N0791.d012853 ∘
          (_root_.GD.N0228.N0547.N0791.d012848 ∘
            (_root_.GD.N0228.N0547.N0791.d012851 ∘ (_root_.GD.N0228.N0547.N0791.d012848 ∘ _root_.GD.N0228.N0547.N0791.d012851))) := by
      rfl
    rw [hfun]
    rw [← Measure.map_map _root_.GD.N0228.N0547.N0791.d012854
      (_root_.GD.N0228.N0547.N0791.d012849.comp
        (_root_.GD.N0228.N0547.N0791.d012852.comp
          (_root_.GD.N0228.N0547.N0791.d012849.comp _root_.GD.N0228.N0547.N0791.d012852)))]
    rw [← Measure.map_map _root_.GD.N0228.N0547.N0791.d012849
      (_root_.GD.N0228.N0547.N0791.d012852.comp
        (_root_.GD.N0228.N0547.N0791.d012849.comp _root_.GD.N0228.N0547.N0791.d012852))]
    rw [← Measure.map_map _root_.GD.N0228.N0547.N0791.d012852
      (_root_.GD.N0228.N0547.N0791.d012849.comp _root_.GD.N0228.N0547.N0791.d012852)]
    rw [← Measure.map_map _root_.GD.N0228.N0547.N0791.d012849
      _root_.GD.N0228.N0547.N0791.d012852]
  rw [hcompose]
  rw [_root_.GD.N0228.N0547.N0791.d012856 ha hb hc hr]
  rw [_root_.GD.N0228.N0547.N0791.d012850]
  rw [_root_.GD.N0228.N0547.N0791.d012857 ha hb hc hr]
  rw [_root_.GD.N0228.N0547.N0791.d012850]
  rw [_root_.GD.N0228.N0547.N0791.d012855]
  rw [show a + (b + c) = a + b + c by ring]



def d012861 (p : ℝ × (ℝ × ℝ)) : (Fin 3 → ℝ) × ℝ :=
  (_root_.GD.N0235.d004247 (_root_.GD.N0228.N0547.N0791.d012858 p).1,
    (_root_.GD.N0228.N0547.N0791.d012858 p).2)

@[fun_prop]
theorem d012862 :
    Measurable _root_.GD.N0228.N0547.N0791.d012861 := by
  unfold _root_.GD.N0228.N0547.N0791.d012861
  fun_prop



theorem d012863
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    ((gammaMeasure a r).prod
      ((gammaMeasure b r).prod (gammaMeasure c r))).map
        _root_.GD.N0228.N0547.N0791.d012861 =
      (_root_.GD.N0235.d004250 a b c).prod
        (gammaMeasure (a + b + c) r) := by
  letI : IsProbabilityMeasure (betaMeasure a (b + c)) :=
    isProbabilityMeasureBeta ha (add_pos hb hc)
  letI : IsProbabilityMeasure (betaMeasure b c) :=
    isProbabilityMeasureBeta hb hc
  letI : IsProbabilityMeasure (gammaMeasure (a + b + c) r) :=
    isProbabilityMeasure_gammaMeasure (by positivity) hr
  let source := (gammaMeasure a r).prod
    ((gammaMeasure b r).prod (gammaMeasure c r))
  calc
    source.map _root_.GD.N0228.N0547.N0791.d012861 =
        (source.map _root_.GD.N0228.N0547.N0791.d012858).map
          (Prod.map _root_.GD.N0235.d004247 id) := by
      rw [Measure.map_map
        (_root_.GD.N0235.d004248.prodMap measurable_id)
        _root_.GD.N0228.N0547.N0791.d012859]
      rfl
    _ = (((betaMeasure a (b + c)).prod (betaMeasure b c)).prod
          (gammaMeasure (a + b + c) r)).map
            (Prod.map _root_.GD.N0235.d004247 id) := by
      rw [_root_.GD.N0228.N0547.N0791.d012860 ha hb hc hr]
    _ = (((betaMeasure a (b + c)).prod (betaMeasure b c)).map
          _root_.GD.N0235.d004247).prod
            ((gammaMeasure (a + b + c) r).map id) := by
      exact (Measure.map_prod_map
        ((betaMeasure a (b + c)).prod (betaMeasure b c))
        (gammaMeasure (a + b + c) r)
        _root_.GD.N0235.d004248 measurable_id).symm
    _ = (_root_.GD.N0235.d004250 a b c).prod
        (gammaMeasure (a + b + c) r) := by
      rw [Measure.map_id]
      rfl


def d012864 (p : ℝ × (ℝ × ℝ)) : ℝ :=
  p.1 + (p.2.1 + p.2.2)

@[fun_prop]
theorem d012865 : Measurable _root_.GD.N0228.N0547.N0791.d012864 := by
  unfold _root_.GD.N0228.N0547.N0791.d012864
  fun_prop



def d012866 (p : ℝ × (ℝ × ℝ)) : Fin 3 → ℝ :=
  ![p.1 / _root_.GD.N0228.N0547.N0791.d012864 p,
    p.2.1 / _root_.GD.N0228.N0547.N0791.d012864 p,
    p.2.2 / _root_.GD.N0228.N0547.N0791.d012864 p]

@[fun_prop]
theorem d012867 : Measurable _root_.GD.N0228.N0547.N0791.d012866 := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [_root_.GD.N0228.N0547.N0791.d012866] <;> fun_prop


def d012868 (p : ℝ × (ℝ × ℝ)) :
    (Fin 3 → ℝ) × ℝ :=
  (_root_.GD.N0228.N0547.N0791.d012866 p, _root_.GD.N0228.N0547.N0791.d012864 p)

@[fun_prop]
theorem d012869 :
    Measurable _root_.GD.N0228.N0547.N0791.d012868 := by
  unfold _root_.GD.N0228.N0547.N0791.d012868
  fun_prop



theorem d012870
    {p : ℝ × (ℝ × ℝ)}
    (hx : 0 < p.1) (hy : 0 < p.2.1) (hz : 0 < p.2.2) :
    _root_.GD.N0228.N0547.N0791.d012861 p = _root_.GD.N0228.N0547.N0791.d012868 p := by
  have hyz : p.2.1 + p.2.2 ≠ 0 := ne_of_gt (add_pos hy hz)
  have hxyz : _root_.GD.N0228.N0547.N0791.d012864 p ≠ 0 := by
    exact ne_of_gt (add_pos hx (add_pos hy hz))
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [_root_.GD.N0228.N0547.N0791.d012861, _root_.GD.N0228.N0547.N0791.d012858, _root_.GD.N0228.N0547.N0791.d012853,
        _root_.GD.N0228.N0547.N0791.d012848, _root_.GD.N0228.N0547.N0791.d012851, _root_.GD.N0155.d006306,
        _root_.GD.N0228.N0547.N0791.d012868, _root_.GD.N0228.N0547.N0791.d012866, _root_.GD.N0228.N0547.N0791.d012864,
        _root_.GD.N0235.d004247] <;>
      field_simp [hyz, hxyz] <;>
      ring
  · simp [_root_.GD.N0228.N0547.N0791.d012861, _root_.GD.N0228.N0547.N0791.d012858, _root_.GD.N0228.N0547.N0791.d012853,
      _root_.GD.N0228.N0547.N0791.d012848, _root_.GD.N0228.N0547.N0791.d012851, _root_.GD.N0155.d006306,
      _root_.GD.N0228.N0547.N0791.d012868, _root_.GD.N0228.N0547.N0791.d012864]



theorem d012871
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    ∀ᵐ p ∂(gammaMeasure a r).prod
      ((gammaMeasure b r).prod (gammaMeasure c r)),
      0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 := by
  have houter : MeasurableSet
      (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) :=
    measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi)
  apply (Measure.ae_prod_iff_ae_ae houter).2
  filter_upwards
    [_root_.GD.N0232.N0720.N1091.d012773
      ha hr] with x hx
  have hinner : MeasurableSet
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hbc : ∀ᵐ yz ∂(gammaMeasure b r).prod (gammaMeasure c r),
      yz ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae hinner).2
    filter_upwards
      [_root_.GD.N0232.N0720.N1091.d012773
        hb hr] with y hy
    filter_upwards
      [_root_.GD.N0232.N0720.N1091.d012773
        hc hr] with z hz
    exact ⟨hy, hz⟩
  filter_upwards [hbc] with yz hyz
  exact ⟨hx, hyz.1, hyz.2⟩





theorem d012872
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    ((gammaMeasure a r).prod
      ((gammaMeasure b r).prod (gammaMeasure c r))).map
        _root_.GD.N0228.N0547.N0791.d012868 =
      (_root_.GD.N0235.d004250 a b c).prod
        (gammaMeasure (a + b + c) r) := by
  let source := (gammaMeasure a r).prod
    ((gammaMeasure b r).prod (gammaMeasure c r))
  have heq : ∀ᵐ p ∂source,
      _root_.GD.N0228.N0547.N0791.d012868 p = _root_.GD.N0228.N0547.N0791.d012861 p := by
    filter_upwards [_root_.GD.N0228.N0547.N0791.d012871 ha hb hc hr] with p hp
    exact (_root_.GD.N0228.N0547.N0791.d012870
      hp.1 hp.2.1 hp.2.2).symm
  calc
    source.map _root_.GD.N0228.N0547.N0791.d012868 = source.map _root_.GD.N0228.N0547.N0791.d012861 :=
      Measure.map_congr heq
    _ = (_root_.GD.N0235.d004250 a b c).prod
        (gammaMeasure (a + b + c) r) :=
      _root_.GD.N0228.N0547.N0791.d012863 ha hb hc hr



theorem d012873
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    ((gammaMeasure a r).prod
      ((gammaMeasure b r).prod (gammaMeasure c r))).map
        _root_.GD.N0228.N0547.N0791.d012866 =
      _root_.GD.N0235.d004250 a b c := by
  letI : IsProbabilityMeasure (gammaMeasure (a + b + c) r) :=
    isProbabilityMeasure_gammaMeasure (by positivity) hr
  let source := (gammaMeasure a r).prod
    ((gammaMeasure b r).prod (gammaMeasure c r))
  calc
    source.map _root_.GD.N0228.N0547.N0791.d012866 =
        (source.map _root_.GD.N0228.N0547.N0791.d012868).map Prod.fst := by
      rw [Measure.map_map measurable_fst _root_.GD.N0228.N0547.N0791.d012869]
      rfl
    _ = ((_root_.GD.N0235.d004250 a b c).prod
          (gammaMeasure (a + b + c) r)).map Prod.fst := by
      rw [_root_.GD.N0228.N0547.N0791.d012872 ha hb hc hr]
    _ = _root_.GD.N0235.d004250 a b c := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]

end

end GD.N0228.N0547.N0791

#print axioms _root_.GD.N0228.N0547.N0791.d012856
#print axioms _root_.GD.N0228.N0547.N0791.d012860
#print axioms _root_.GD.N0228.N0547.N0791.d012863
#print axioms _root_.GD.N0228.N0547.N0791.d012872
#print axioms _root_.GD.N0228.N0547.N0791.d012873
