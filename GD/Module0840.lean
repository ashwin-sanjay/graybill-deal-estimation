import GD.Module0839
import GD.Module0234

set_option warningAsError true










open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0786

noncomputable section

open _root_.GD.N0228.N0547.N0778 _root_.GD.N0228.N0547.N0779
  _root_.GD.N0228.N0547.N0788 _root_.GD.N0228.N0547.N0784



def d012825 (p : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) :=
  (p.1, _root_.GD.N0228.N0547.N0778.d009366 p.2)

@[fun_prop]
theorem d012826 : Measurable _root_.GD.N0228.N0547.N0786.d012825 := by
  unfold _root_.GD.N0228.N0547.N0786.d012825
  fun_prop


def d012827 (p : ℝ × (ℝ × ℝ)) : (ℝ × ℝ) × ℝ :=
  ((p.1, p.2.1), p.2.2)

@[fun_prop]
theorem d012828 :
    Measurable _root_.GD.N0228.N0547.N0786.d012827 := by
  unfold _root_.GD.N0228.N0547.N0786.d012827
  fun_prop



def d012829 (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (p.1 * Real.sqrt (p.2.1 * p.2.2), (1 - p.2.1) * p.2.2)

@[fun_prop]
theorem d012830 :
    Measurable _root_.GD.N0228.N0547.N0786.d012829 := by
  unfold _root_.GD.N0228.N0547.N0786.d012829
  fun_prop

theorem d012831 :
    _root_.GD.N0228.N0547.N0786.d012829 =
      Prod.map _root_.GD.N0228.N0547.N0788.d006357 id ∘
        _root_.GD.N0228.N0547.N0786.d012827 ∘ _root_.GD.N0228.N0547.N0786.d012825 := by
  rfl



theorem d012832
    {d : ℕ} (hd : 1 < d) :
    ((_root_.GD.N0228.N0547.N0788.d006356).prod
      ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
        (_root_.GD.N0228.N0547.N0778.d009365 d))).map _root_.GD.N0228.N0547.N0786.d012825 =
      (_root_.GD.N0228.N0547.N0788.d006356).prod
        ((_root_.GD.N0228.N0547.N0778.d009365 1).prod
          (gammaMeasure (((d : ℝ) - 1) / 2) (1 / 2))) := by
  have hshape : 0 < ((d : ℝ) - 1) / 2 := by
    have hdR : (1 : ℝ) < d := by exact_mod_cast hd
    positivity
  letI : IsProbabilityMeasure
      (betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)) :=
    isProbabilityMeasureBeta (by norm_num) hshape
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 d) := by
    unfold _root_.GD.N0228.N0547.N0778.d009365
    exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  calc
    ((_root_.GD.N0228.N0547.N0788.d006356).prod
      ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
        (_root_.GD.N0228.N0547.N0778.d009365 d))).map _root_.GD.N0228.N0547.N0786.d012825 =
        ((_root_.GD.N0228.N0547.N0788.d006356).map id).prod
          (((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
            (_root_.GD.N0228.N0547.N0778.d009365 d)).map _root_.GD.N0228.N0547.N0778.d009366) := by
      exact (Measure.map_prod_map (_root_.GD.N0228.N0547.N0788.d006356)
        ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
          (_root_.GD.N0228.N0547.N0778.d009365 d)) measurable_id _root_.GD.N0228.N0547.N0778.d009368).symm
    _ = (_root_.GD.N0228.N0547.N0788.d006356).prod
        ((_root_.GD.N0228.N0547.N0778.d009365 1).prod
          (gammaMeasure (((d : ℝ) - 1) / 2) (1 / 2))) := by
      rw [Measure.map_id, _root_.GD.N0228.N0547.N0779.d012814 hd]



theorem d012833
    (mu nu tau : Measure ℝ) [SFinite nu] [SFinite tau] :
    (mu.prod (nu.prod tau)).map _root_.GD.N0228.N0547.N0786.d012827 =
      (mu.prod nu).prod tau := by
  let assoc : ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
    MeasurableEquiv.prodAssoc
  have hforward : MeasurePreserving assoc
      ((mu.prod nu).prod tau) (mu.prod (nu.prod tau)) :=
    measurePreserving_prodAssoc mu nu tau
  have hback : MeasurePreserving assoc.symm
      (mu.prod (nu.prod tau)) ((mu.prod nu).prod tau) :=
    MeasurePreserving.symm assoc hforward
  have hfun : _root_.GD.N0228.N0547.N0786.d012827 = assoc.symm := by
    rfl
  rw [hfun]
  exact hback.map_eq




theorem d012834
    {d : ℕ} (hd : 1 < d) :
    ((_root_.GD.N0228.N0547.N0788.d006356).prod
      ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
        (_root_.GD.N0228.N0547.N0778.d009365 d))).map _root_.GD.N0228.N0547.N0786.d012829 =
      (gaussianReal 0 1).prod
        (gammaMeasure (((d : ℝ) - 1) / 2) (1 / 2)) := by
  have hshape : 0 < ((d : ℝ) - 1) / 2 := by
    have hdR : (1 : ℝ) < d := by exact_mod_cast hd
    positivity
  let complement := gammaMeasure (((d : ℝ) - 1) / 2) (1 / 2)
  letI : IsProbabilityMeasure complement :=
    isProbabilityMeasure_gammaMeasure hshape (by norm_num)
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 1) := by
    unfold _root_.GD.N0228.N0547.N0778.d009365
    exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  let source := (_root_.GD.N0228.N0547.N0788.d006356).prod
    ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod (_root_.GD.N0228.N0547.N0778.d009365 d))
  calc
    source.map _root_.GD.N0228.N0547.N0786.d012829 =
        ((source.map _root_.GD.N0228.N0547.N0786.d012825).map _root_.GD.N0228.N0547.N0786.d012827).map
          (Prod.map _root_.GD.N0228.N0547.N0788.d006357 id) := by
      rw [Measure.map_map _root_.GD.N0228.N0547.N0786.d012828
          _root_.GD.N0228.N0547.N0786.d012826,
        Measure.map_map
          (_root_.GD.N0228.N0547.N0788.d006358.prodMap measurable_id)
          (_root_.GD.N0228.N0547.N0786.d012828.comp _root_.GD.N0228.N0547.N0786.d012826)]
      rw [_root_.GD.N0228.N0547.N0786.d012831]
    _ = ((((_root_.GD.N0228.N0547.N0788.d006356).prod (_root_.GD.N0228.N0547.N0778.d009365 1)).prod complement).map
          (Prod.map _root_.GD.N0228.N0547.N0788.d006357 id)) := by
      rw [_root_.GD.N0228.N0547.N0786.d012832 hd]
      rw [_root_.GD.N0228.N0547.N0786.d012833]
    _ = (((_root_.GD.N0228.N0547.N0788.d006356).prod (_root_.GD.N0228.N0547.N0778.d009365 1)).map
          _root_.GD.N0228.N0547.N0788.d006357).prod (complement.map id) := by
      exact (Measure.map_prod_map
        ((_root_.GD.N0228.N0547.N0788.d006356).prod (_root_.GD.N0228.N0547.N0778.d009365 1)) complement
        _root_.GD.N0228.N0547.N0788.d006358 measurable_id).symm
    _ = (gaussianReal 0 1).prod complement := by
      rw [Measure.map_id]
      simpa only [_root_.GD.N0228.N0547.N0778.d009365, _root_.GD.N0121.d006346] using
        congrArg (fun m : Measure ℝ => m.prod complement)
          _root_.GD.N0228.N0547.N0788.d006371




def d012835 (d : ℕ) : Measure (ℝ × (ℝ × ℝ)) :=
  (_root_.GD.N0228.N0547.N0788.d006356).prod
    ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod (_root_.GD.N0228.N0547.N0778.d009365 d))



def d012836
    (p : (ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ))) : ℝ × ℝ :=
  (_root_.GD.N0228.N0547.N0784.d012819 p.1, _root_.GD.N0228.N0547.N0784.d012819 p.2)

@[fun_prop]
theorem d012837 :
    Measurable _root_.GD.N0228.N0547.N0786.d012836 := by
  unfold _root_.GD.N0228.N0547.N0786.d012836
  fun_prop



theorem d012838
    {d₁ d₂ : ℕ} (hd₁ : 1 < d₁) (hd₂ : 1 < d₂) :
    ((_root_.GD.N0228.N0547.N0786.d012835 d₁).prod (_root_.GD.N0228.N0547.N0786.d012835 d₂)).map
        _root_.GD.N0228.N0547.N0786.d012836 =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have hshape₁ : 0 < ((d₁ : ℝ) - 1) / 2 := by
    have hdR : (1 : ℝ) < d₁ := by exact_mod_cast hd₁
    positivity
  have hshape₂ : 0 < ((d₂ : ℝ) - 1) / 2 := by
    have hdR : (1 : ℝ) < d₂ := by exact_mod_cast hd₂
    positivity
  letI : IsProbabilityMeasure
      (betaMeasure (1 / 2) (((d₁ : ℝ) - 1) / 2)) :=
    isProbabilityMeasureBeta (by norm_num) hshape₁
  letI : IsProbabilityMeasure
      (betaMeasure (1 / 2) (((d₂ : ℝ) - 1) / 2)) :=
    isProbabilityMeasureBeta (by norm_num) hshape₂
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 d₁) := by
    unfold _root_.GD.N0228.N0547.N0778.d009365
    exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 d₂) := by
    unfold _root_.GD.N0228.N0547.N0778.d009365
    exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0786.d012835 d₁) := by
    unfold _root_.GD.N0228.N0547.N0786.d012835
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0786.d012835 d₂) := by
    unfold _root_.GD.N0228.N0547.N0786.d012835
    infer_instance
  calc
    ((_root_.GD.N0228.N0547.N0786.d012835 d₁).prod (_root_.GD.N0228.N0547.N0786.d012835 d₂)).map
        _root_.GD.N0228.N0547.N0786.d012836 =
      ((_root_.GD.N0228.N0547.N0786.d012835 d₁).map _root_.GD.N0228.N0547.N0784.d012819).prod
        ((_root_.GD.N0228.N0547.N0786.d012835 d₂).map _root_.GD.N0228.N0547.N0784.d012819) := by
      exact (Measure.map_prod_map
        (_root_.GD.N0228.N0547.N0786.d012835 d₁) (_root_.GD.N0228.N0547.N0786.d012835 d₂)
        _root_.GD.N0228.N0547.N0784.d012820
        _root_.GD.N0228.N0547.N0784.d012820).symm
    _ = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
      rw [show _root_.GD.N0228.N0547.N0786.d012835 d₁ =
          (_root_.GD.N0228.N0547.N0788.d006356).prod
            ((betaMeasure (1 / 2) (((d₁ : ℝ) - 1) / 2)).prod
              (_root_.GD.N0228.N0547.N0778.d009365 d₁)) by rfl,
        show _root_.GD.N0228.N0547.N0786.d012835 d₂ =
          (_root_.GD.N0228.N0547.N0788.d006356).prod
            ((betaMeasure (1 / 2) (((d₂ : ℝ) - 1) / 2)).prod
              (_root_.GD.N0228.N0547.N0778.d009365 d₂)) by rfl,
        _root_.GD.N0228.N0547.N0784.d012824 hd₁,
        _root_.GD.N0228.N0547.N0784.d012824 hd₂]




theorem d012839
    {d₁ d₂ : ℕ} (hd₁ : 1 < d₁) (hd₂ : 1 < d₂)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ((_root_.GD.N0228.N0547.N0786.d012835 d₁).prod (_root_.GD.N0228.N0547.N0786.d012835 d₂))
        {omega |
          |_root_.GD.N0228.N0547.N0784.d012819 omega.1| ≤
            _root_.GD.N0228.N0547.N0782.d003367 p *
              |_root_.GD.N0228.N0547.N0784.d012819 omega.2|} =
      ENNReal.ofReal p := by
  have hevent : MeasurableSet
      (_root_.GD.N0228.N0547.N0782.d003372
        (_root_.GD.N0228.N0547.N0782.d003367 p)) :=
    _root_.GD.N0228.N0547.N0782.d003375 _
  change
    ((_root_.GD.N0228.N0547.N0786.d012835 d₁).prod (_root_.GD.N0228.N0547.N0786.d012835 d₂))
      (_root_.GD.N0228.N0547.N0786.d012836 ⁻¹'
        _root_.GD.N0228.N0547.N0782.d003372
          (_root_.GD.N0228.N0547.N0782.d003367 p)) = _
  rw [← Measure.map_apply _root_.GD.N0228.N0547.N0786.d012837 hevent]
  rw [_root_.GD.N0228.N0547.N0786.d012838 hd₁ hd₂]
  exact _root_.GD.N0228.N0547.N0780.d003406
    1 (by norm_num) p hp0 hp1

end


end GD.N0228.N0547.N0786

#print axioms _root_.GD.N0228.N0547.N0786.d012832
#print axioms _root_.GD.N0228.N0547.N0786.d012833
#print axioms _root_.GD.N0228.N0547.N0786.d012834
#print axioms _root_.GD.N0228.N0547.N0786.d012838
#print axioms _root_.GD.N0228.N0547.N0786.d012839
