import GD.Module0840

set_option warningAsError true











open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0785

noncomputable section

open _root_.GD.N0228.N0547.N0778 _root_.GD.N0228.N0547.N0788 _root_.GD.N0228.N0547.N0784
  _root_.GD.N0228.N0547.N0786


def d012840 : Measure (ℝ × (ℝ × ℝ)) :=
  _root_.GD.N0228.N0547.N0788.d006356.prod ((Measure.dirac (1 : ℝ)).prod (_root_.GD.N0228.N0547.N0778.d009365 1))



theorem d012841 :
    ((Measure.dirac (1 : ℝ)).prod (_root_.GD.N0228.N0547.N0778.d009365 1)).map
        _root_.GD.N0228.N0547.N0784.d012815 =
      _root_.GD.N0228.N0547.N0778.d009365 1 := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 1) := by
    unfold _root_.GD.N0228.N0547.N0778.d009365
    exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  calc
    ((Measure.dirac (1 : ℝ)).prod (_root_.GD.N0228.N0547.N0778.d009365 1)).map
        _root_.GD.N0228.N0547.N0784.d012815 =
        ((_root_.GD.N0228.N0547.N0778.d009365 1).map (Prod.mk (1 : ℝ))).map
          _root_.GD.N0228.N0547.N0784.d012815 := by
      rw [Measure.dirac_prod]
    _ = (_root_.GD.N0228.N0547.N0778.d009365 1).map
        (_root_.GD.N0228.N0547.N0784.d012815 ∘ Prod.mk (1 : ℝ)) := by
      rw [Measure.map_map _root_.GD.N0228.N0547.N0784.d012816
        measurable_prodMk_left]
    _ = (_root_.GD.N0228.N0547.N0778.d009365 1).map id := by
      congr 1
      funext q
      simp [_root_.GD.N0228.N0547.N0784.d012815]
    _ = _root_.GD.N0228.N0547.N0778.d009365 1 := Measure.map_id



theorem d012842 :
    _root_.GD.N0228.N0547.N0785.d012840.map _root_.GD.N0228.N0547.N0784.d012819 =
      gaussianReal 0 1 := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 1) := by
    unfold _root_.GD.N0228.N0547.N0778.d009365
    exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have henergy : _root_.GD.N0228.N0547.N0785.d012840.map _root_.GD.N0228.N0547.N0784.d012817 =
      _root_.GD.N0228.N0547.N0788.d006356.prod (_root_.GD.N0228.N0547.N0778.d009365 1) := by
    calc
      _root_.GD.N0228.N0547.N0785.d012840.map _root_.GD.N0228.N0547.N0784.d012817 =
          (_root_.GD.N0228.N0547.N0788.d006356.map id).prod
            (((Measure.dirac (1 : ℝ)).prod (_root_.GD.N0228.N0547.N0778.d009365 1)).map
              _root_.GD.N0228.N0547.N0784.d012815) := by
        exact (Measure.map_prod_map _root_.GD.N0228.N0547.N0788.d006356
          ((Measure.dirac (1 : ℝ)).prod (_root_.GD.N0228.N0547.N0778.d009365 1))
          measurable_id _root_.GD.N0228.N0547.N0784.d012816).symm
      _ = _root_.GD.N0228.N0547.N0788.d006356.prod (_root_.GD.N0228.N0547.N0778.d009365 1) := by
        rw [Measure.map_id, _root_.GD.N0228.N0547.N0785.d012841]
  calc
    _root_.GD.N0228.N0547.N0785.d012840.map _root_.GD.N0228.N0547.N0784.d012819 =
        (_root_.GD.N0228.N0547.N0785.d012840.map _root_.GD.N0228.N0547.N0784.d012817).map _root_.GD.N0228.N0547.N0788.d006357 := by
      rw [Measure.map_map _root_.GD.N0228.N0547.N0788.d006358 _root_.GD.N0228.N0547.N0784.d012818,
        _root_.GD.N0228.N0547.N0784.d012821]
    _ = (_root_.GD.N0228.N0547.N0788.d006356.prod (_root_.GD.N0228.N0547.N0778.d009365 1)).map _root_.GD.N0228.N0547.N0788.d006357 := by
      rw [henergy]
    _ = gaussianReal 0 1 := by
      simpa only [_root_.GD.N0228.N0547.N0778.d009365, _root_.GD.N0121.d006346] using
        _root_.GD.N0228.N0547.N0788.d006371




def d012843 (d : ℕ) : Measure (ℝ × (ℝ × ℝ)) :=
  if d = 1 then _root_.GD.N0228.N0547.N0785.d012840 else _root_.GD.N0228.N0547.N0786.d012835 d



theorem d012844
    {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (_root_.GD.N0228.N0547.N0785.d012843 d) := by
  by_cases hboundary : d = 1
  · subst d
    rw [_root_.GD.N0228.N0547.N0785.d012843, if_pos rfl]
    unfold _root_.GD.N0228.N0547.N0785.d012840
    letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 1) := by
      unfold _root_.GD.N0228.N0547.N0778.d009365
      exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
    infer_instance
  · have hdLarge : 1 < d := by omega
    rw [_root_.GD.N0228.N0547.N0785.d012843, if_neg hboundary]
    unfold _root_.GD.N0228.N0547.N0786.d012835
    have hshape : 0 < ((d : ℝ) - 1) / 2 := by
      have hdR : (1 : ℝ) < d := by exact_mod_cast hdLarge
      positivity
    letI : IsProbabilityMeasure
        (betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)) :=
      isProbabilityMeasureBeta (by norm_num) hshape
    letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 d) := by
      unfold _root_.GD.N0228.N0547.N0778.d009365
      exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
    infer_instance



theorem d012845
    {d : ℕ} (hd : 0 < d) :
    (_root_.GD.N0228.N0547.N0785.d012843 d).map _root_.GD.N0228.N0547.N0784.d012819 =
      gaussianReal 0 1 := by
  by_cases hboundary : d = 1
  · rw [_root_.GD.N0228.N0547.N0785.d012843, if_pos hboundary]
    exact _root_.GD.N0228.N0547.N0785.d012842
  · have hdLarge : 1 < d := by omega
    rw [_root_.GD.N0228.N0547.N0785.d012843, if_neg hboundary]
    exact _root_.GD.N0228.N0547.N0784.d012824 hdLarge



theorem d012846
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
      (_root_.GD.N0228.N0547.N0785.d012843 d₂)).map _root_.GD.N0228.N0547.N0786.d012836 =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0785.d012843 d₁) :=
    _root_.GD.N0228.N0547.N0785.d012844 hd₁
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0785.d012843 d₂) :=
    _root_.GD.N0228.N0547.N0785.d012844 hd₂
  calc
    ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
      (_root_.GD.N0228.N0547.N0785.d012843 d₂)).map _root_.GD.N0228.N0547.N0786.d012836 =
        ((_root_.GD.N0228.N0547.N0785.d012843 d₁).map _root_.GD.N0228.N0547.N0784.d012819).prod
          ((_root_.GD.N0228.N0547.N0785.d012843 d₂).map _root_.GD.N0228.N0547.N0784.d012819) := by
      exact (Measure.map_prod_map
        (_root_.GD.N0228.N0547.N0785.d012843 d₁)
        (_root_.GD.N0228.N0547.N0785.d012843 d₂)
        _root_.GD.N0228.N0547.N0784.d012820
        _root_.GD.N0228.N0547.N0784.d012820).symm
    _ = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
      rw [_root_.GD.N0228.N0547.N0785.d012845 hd₁,
        _root_.GD.N0228.N0547.N0785.d012845 hd₂]




theorem d012847
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
      (_root_.GD.N0228.N0547.N0785.d012843 d₂))
        {ω |
          |_root_.GD.N0228.N0547.N0784.d012819 ω.1| ≤
            _root_.GD.N0228.N0547.N0782.d003367 p *
              |_root_.GD.N0228.N0547.N0784.d012819 ω.2|} =
      ENNReal.ofReal p := by
  have hevent : MeasurableSet
      (_root_.GD.N0228.N0547.N0782.d003372
        (_root_.GD.N0228.N0547.N0782.d003367 p)) :=
    _root_.GD.N0228.N0547.N0782.d003375 _
  change
    ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
      (_root_.GD.N0228.N0547.N0785.d012843 d₂))
      (_root_.GD.N0228.N0547.N0786.d012836 ⁻¹'
        _root_.GD.N0228.N0547.N0782.d003372
          (_root_.GD.N0228.N0547.N0782.d003367 p)) = _
  rw [← Measure.map_apply _root_.GD.N0228.N0547.N0786.d012837 hevent]
  rw [_root_.GD.N0228.N0547.N0785.d012846 hd₁ hd₂]
  exact _root_.GD.N0228.N0547.N0780.d003406
    1 (by norm_num) p hp0 hp1

end

end GD.N0228.N0547.N0785

#print axioms _root_.GD.N0228.N0547.N0785.d012841
#print axioms _root_.GD.N0228.N0547.N0785.d012842
#print axioms _root_.GD.N0228.N0547.N0785.d012845
#print axioms _root_.GD.N0228.N0547.N0785.d012846
#print axioms _root_.GD.N0228.N0547.N0785.d012847
