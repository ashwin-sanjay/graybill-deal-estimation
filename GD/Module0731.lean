import GD.Module0016
import GD.Module0029
import GD.Module0630
import GD.Module0727
import GD.Module0632














open Filter MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0828

noncomputable section

open _root_.GD.N0232.N0719.N0900 _root_.GD.N0107
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0230.N0655
open _root_.GD.N0230.N0590

variable (k : ℕ) (sizes : Fin k → ℕ)



theorem d010987
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    Integrable
      (_root_.GD.N0232.N0719.N0932.d009219 k sizes location scale)
      (_root_.GD.N0232.N0719.d009182 k sizes) := by
  rw [_root_.GD.N0232.N0719.N0932.d009222]
  unfold _root_.GD.N0232.N0719.N0932.d009219
  exact Integrable.fintype_prod_dep fun i ↦
    _root_.GD.N0232.N0719.N0932.d009216
      (sizes i) location (scale i) (hscale i).ne'



theorem d010988
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    (∫ omega,
      _root_.GD.N0232.N0719.N0932.d009219 k sizes location scale omega
        ∂_root_.GD.N0232.N0719.d009182 k sizes) = 1 := by
  let density := _root_.GD.N0232.N0719.N0932.d009219 k sizes location scale
  have hint : Integrable density (_root_.GD.N0232.N0719.d009182 k sizes) :=
    _root_.GD.N0232.N0719.N0828.d010987 k sizes location scale hscale
  have hnonneg : ∀ omega, 0 ≤ density omega :=
    _root_.GD.N0232.N0719.N0932.d009221 k sizes location scale
  have hlaw := _root_.GD.N0232.N0719.N0932.d009223
    k sizes location scale hscale
  have hmeasure := congrArg (fun mu : Measure (_root_.GD.N0232.N0719.d009173 k sizes) ↦ mu Set.univ) hlaw
  have hlintegral :
      (∫⁻ omega, ENNReal.ofReal (density omega) ∂_root_.GD.N0232.N0719.d009182 k sizes) = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ] at hmeasure
    simpa using hmeasure.symm
  have hofReal : ENNReal.ofReal
      (∫ omega, density omega ∂_root_.GD.N0232.N0719.d009182 k sizes) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all (_root_.GD.N0232.N0719.d009182 k sizes) hnonneg)]
    exact hlintegral
  exact ENNReal.ofReal_eq_one.mp hofReal



def d010989
  (g : _root_.GD.N0230.N0655.d000349) : _root_.GD.N0232.N0719.N0932.d009224 k :=
  (_root_.GD.N0232.N0719.N0842.d010906 g.1 (g.2 : ℝ),
    fun _ ↦ ⟨((g.2 : ℝ)⁻¹),
      show 0 < (g.2 : ℝ)⁻¹ from inv_pos.mpr g.2.property⟩)

@[fun_prop]
theorem d010990 :
    Continuous (_root_.GD.N0232.N0719.N0828.d010989 k) := by
  have hscale : Continuous
      (fun g : _root_.GD.N0230.N0655.d000349 ↦ (g.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hscaleNe : ∀ g : _root_.GD.N0230.N0655.d000349, (g.2 : ℝ) ≠ 0 :=
    fun g ↦ ne_of_gt g.2.property
  have hinv : Continuous
      (fun g : _root_.GD.N0230.N0655.d000349 ↦ ((g.2 : ℝ)⁻¹)) :=
    hscale.inv₀ hscaleNe
  apply Continuous.prodMk
  · unfold _root_.GD.N0232.N0719.N0842.d010906
    exact (hinv.mul continuous_fst).neg
  · apply continuous_pi
    intro i
    exact hinv.subtype_mk _


def d010991
    (g : _root_.GD.N0230.N0655.d000349) (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0932.d009219 k sizes
    (_root_.GD.N0232.N0719.N0828.d010989 k g).1
    (fun i ↦ (_root_.GD.N0232.N0719.N0828.d010989 k g).2 i) omega

@[fun_prop]
theorem d010992
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    Continuous (fun g : _root_.GD.N0230.N0655.d000349 ↦
      _root_.GD.N0232.N0719.N0828.d010991 k sizes g omega) := by
  exact (_root_.GD.N0232.N0719.N0932.d009227
    k sizes omega).comp (_root_.GD.N0232.N0719.N0828.d010990 k)

theorem d010993
    (g : _root_.GD.N0230.N0655.d000349) :
    Measurable (_root_.GD.N0232.N0719.N0828.d010991 k sizes g) := by
  exact _root_.GD.N0232.N0719.N0932.d009220 _ _ _ _

theorem d010994
    (g : _root_.GD.N0230.N0655.d000349) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0828.d010991 k sizes g omega := by
  exact _root_.GD.N0232.N0719.N0932.d009221 _ _ _ _ _

theorem d010995
    (g : _root_.GD.N0230.N0655.d000349) :
    Integrable (_root_.GD.N0232.N0719.N0828.d010991 k sizes g)
      (_root_.GD.N0232.N0719.d009182 k sizes) := by
  apply _root_.GD.N0232.N0719.N0828.d010987
  intro i
  exact ((_root_.GD.N0232.N0719.N0828.d010989 k g).2 i).property

theorem d010996
    (g : _root_.GD.N0230.N0655.d000349) :
    (∫ omega, _root_.GD.N0232.N0719.N0828.d010991 k sizes g omega
      ∂_root_.GD.N0232.N0719.d009182 k sizes) = 1 := by
  apply _root_.GD.N0232.N0719.N0828.d010988
  intro i
  exact ((_root_.GD.N0232.N0719.N0828.d010989 k g).2 i).property



theorem d010997
    (g : _root_.GD.N0230.N0655.d000349) :
    (_root_.GD.N0232.N0719.d009182 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2) =
      _root_.GD.N0232.N0719.d009176 k sizes
        (_root_.GD.N0232.N0719.N0828.d010989 k g).1
        (fun i ↦ (_root_.GD.N0232.N0719.N0828.d010989 k g).2 i) := by
  unfold _root_.GD.N0232.N0719.d009182 _root_.GD.N0232.N0719.N0842.d010907 _root_.GD.N0232.N0719.N0828.d010989
  simpa using _root_.GD.N0232.N0719.d009188
    k sizes (_root_.GD.N0232.N0719.N0842.d010906 g.1 (g.2 : ℝ)) ((g.2 : ℝ)⁻¹)
      0 (fun _ ↦ 1)



theorem d010998
    (g : _root_.GD.N0230.N0655.d000349) :
    (_root_.GD.N0232.N0719.d009182 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2) =
      (_root_.GD.N0232.N0719.d009182 k sizes).withDensity
        (fun omega ↦ ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0828.d010991 k sizes g omega)) := by
  rw [_root_.GD.N0232.N0719.N0828.d010997]
  exact _root_.GD.N0232.N0719.N0932.d009223
    k sizes
      (_root_.GD.N0232.N0719.N0828.d010989 k g).1
      (fun i ↦ (_root_.GD.N0232.N0719.N0828.d010989 k g).2 i)
      (fun i ↦ (_root_.GD.N0232.N0719.N0828.d010989 k g).2 i |>.property)



theorem d010999
    (parameter : ℕ → _root_.GD.N0230.N0655.d000349)
    (limitParameter : _root_.GD.N0230.N0655.d000349)
    (hparameter : Tendsto parameter atTop (nhds limitParameter))
    (s : Set (_root_.GD.N0232.N0719.d009173 k sizes)) (hs : MeasurableSet s)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ n in atTop,
      (_root_.GD.N0232.N0719.d009182 k sizes).real
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes
            (parameter n).1 (parameter n).2 ⁻¹' s) <
        (_root_.GD.N0232.N0719.d009182 k sizes).real
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes
            limitParameter.1 limitParameter.2 ⁻¹' s) + delta := by
  have hmap (g : _root_.GD.N0230.N0655.d000349) :
      (_root_.GD.N0232.N0719.d009182 k sizes).real
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2 ⁻¹' s) =
        ((_root_.GD.N0232.N0719.d009182 k sizes).map
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2)).real s := by
    change ((_root_.GD.N0232.N0719.d009182 k sizes)
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2 ⁻¹' s)).toReal =
      (((_root_.GD.N0232.N0719.d009182 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2)) s).toReal
    rw [Measure.map_apply
      (_root_.GD.N0232.N0719.N0842.d010908 k sizes _ _) hs]
  simp_rw [hmap]
  simp_rw [_root_.GD.N0232.N0719.N0828.d010998]
  apply _root_.GD.N0230.N0590.d000145
  · intro n
    exact _root_.GD.N0232.N0719.N0828.d010993 k sizes (parameter n)
  · exact _root_.GD.N0232.N0719.N0828.d010993 k sizes limitParameter
  · intro n
    exact _root_.GD.N0232.N0719.N0828.d010995 k sizes (parameter n)
  · exact _root_.GD.N0232.N0719.N0828.d010995 k sizes limitParameter
  · intro n omega
    exact _root_.GD.N0232.N0719.N0828.d010994 k sizes (parameter n) omega
  · exact _root_.GD.N0232.N0719.N0828.d010994 k sizes limitParameter
  · intro omega
    exact (_root_.GD.N0232.N0719.N0828.d010992
      k sizes omega).continuousAt.tendsto.comp hparameter
  · simpa only [_root_.GD.N0232.N0719.N0828.d010996]
      using (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) from
        tendsto_const_nhds)
  · exact hs
  · exact hdelta

end

end N0828
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0828.d010987
#print axioms _root_.GD.N0232.N0719.N0828.d010988
#print axioms _root_.GD.N0232.N0719.N0828.d010997
#print axioms _root_.GD.N0232.N0719.N0828.d010999
