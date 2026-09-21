import GD.Module0841
import GD.Module0843
import GD.Module0234

set_option autoImplicit false
set_option warningAsError true
















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0789

noncomputable section

open _root_.GD.N0228.N0547.N0784
  _root_.GD.N0228.N0547.N0786
  _root_.GD.N0228.N0547.N0785
  _root_.GD.N0228.N0547.N0797


def d012877 (rho : ℝ)
    (z : (ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ))) : ℝ :=
  _root_.GD.N0228.N0547.N0797.d012874 rho (_root_.GD.N0228.N0547.N0786.d012836 z)

@[fun_prop]
theorem d012878 (rho : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0789.d012877 rho) := by
  unfold _root_.GD.N0228.N0547.N0789.d012877
  fun_prop



theorem d012879
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
      (_root_.GD.N0228.N0547.N0785.d012843 d₂)).map
        (_root_.GD.N0228.N0547.N0789.d012877 rho) =
      gaussianReal 0 1 := by
  calc
    ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
      (_root_.GD.N0228.N0547.N0785.d012843 d₂)).map
        (_root_.GD.N0228.N0547.N0789.d012877 rho) =
        (((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
          (_root_.GD.N0228.N0547.N0785.d012843 d₂)).map
            _root_.GD.N0228.N0547.N0786.d012836).map
              (_root_.GD.N0228.N0547.N0797.d012874 rho) := by
      rw [Measure.map_map
        (_root_.GD.N0228.N0547.N0797.d012875 rho)
        _root_.GD.N0228.N0547.N0786.d012837]
      rfl
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          (_root_.GD.N0228.N0547.N0797.d012874 rho) := by
      rw [_root_.GD.N0228.N0547.N0785.d012846 hd₁ hd₂]
    _ = gaussianReal 0 1 :=
      _root_.GD.N0228.N0547.N0797.d012876 hrho0 hrho1



def d012880 (rho : ℝ)
    (z : ℝ × ((ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ)))) : ℝ × ℝ :=
  (z.1, _root_.GD.N0228.N0547.N0789.d012877 rho z.2)

@[fun_prop]
theorem d012881 (rho : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0789.d012880 rho) := by
  unfold _root_.GD.N0228.N0547.N0789.d012880
  fun_prop



theorem d012882
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    ((gaussianReal 0 1).prod
      ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
        (_root_.GD.N0228.N0547.N0785.d012843 d₂))).map
          (_root_.GD.N0228.N0547.N0789.d012880 rho) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0785.d012843 d₁) :=
    _root_.GD.N0228.N0547.N0785.d012844 hd₁
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0785.d012843 d₂) :=
    _root_.GD.N0228.N0547.N0785.d012844 hd₂
  letI : IsProbabilityMeasure
      ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
        (_root_.GD.N0228.N0547.N0785.d012843 d₂)) := by
    infer_instance
  calc
    ((gaussianReal 0 1).prod
      ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
        (_root_.GD.N0228.N0547.N0785.d012843 d₂))).map
          (_root_.GD.N0228.N0547.N0789.d012880 rho) =
        ((gaussianReal 0 1).map id).prod
          (((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
            (_root_.GD.N0228.N0547.N0785.d012843 d₂)).map
              (_root_.GD.N0228.N0547.N0789.d012877 rho)) := by
      exact (Measure.map_prod_map (gaussianReal 0 1)
        ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
          (_root_.GD.N0228.N0547.N0785.d012843 d₂))
        measurable_id
        (_root_.GD.N0228.N0547.N0789.d012878 rho)).symm
    _ = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
      rw [Measure.map_id,
        _root_.GD.N0228.N0547.N0789.d012879 hd₁ hd₂ hrho0 hrho1]



theorem d012883
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {rho p : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ((gaussianReal 0 1).prod
      ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
        (_root_.GD.N0228.N0547.N0785.d012843 d₂)))
      {z | |z.1| ≤ _root_.GD.N0228.N0547.N0782.d003367 p *
        |_root_.GD.N0228.N0547.N0789.d012877 rho z.2|} =
      ENNReal.ofReal p := by
  let event := _root_.GD.N0228.N0547.N0782.d003372
    (_root_.GD.N0228.N0547.N0782.d003367 p)
  calc
    ((gaussianReal 0 1).prod
      ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
        (_root_.GD.N0228.N0547.N0785.d012843 d₂)))
      {z | |z.1| ≤ _root_.GD.N0228.N0547.N0782.d003367 p *
        |_root_.GD.N0228.N0547.N0789.d012877 rho z.2|} =
        (((gaussianReal 0 1).prod
          ((_root_.GD.N0228.N0547.N0785.d012843 d₁).prod
            (_root_.GD.N0228.N0547.N0785.d012843 d₂))).map
              (_root_.GD.N0228.N0547.N0789.d012880 rho)) event := by
      rw [Measure.map_apply (_root_.GD.N0228.N0547.N0789.d012881 rho)
        (_root_.GD.N0228.N0547.N0782.d003375 _)]
      rfl
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)) event := by
      rw [_root_.GD.N0228.N0547.N0789.d012882 hd₁ hd₂ hrho0 hrho1]
    _ = ENNReal.ofReal p :=
      _root_.GD.N0228.N0547.N0780.d003406
        1 (by norm_num) p hp0 hp1

end

end GD.N0228.N0547.N0789

#print axioms _root_.GD.N0228.N0547.N0789.d012879
#print axioms _root_.GD.N0228.N0547.N0789.d012882
#print axioms _root_.GD.N0228.N0547.N0789.d012883
