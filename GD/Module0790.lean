import GD.Module0789
import GD.Module0787
import GD.Module0630
import GD.Module0760


















open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace GD
namespace N0232
namespace N0719
namespace N0831

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0835
open _root_.GD.N0232.N0719.N0836
open _root_.GD.N0232.N0719.N0830
open _root_.GD.N0232.N0719.N0834
open _root_.GD.N0232.N0719.N0865



def d011994
    {k : ℕ} {sizes : Fin k → ℕ}
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0836.d011973 i omega /
    (((sizes i - 1 : ℕ) : ℝ) * (theta.scale i) ^ 2)

@[fun_prop]
theorem d011995
    {k : ℕ} {sizes : Fin k → ℕ}
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    Measurable
      (_root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes) theta i) := by
  unfold _root_.GD.N0232.N0719.N0831.d011994
  fun_prop

theorem d011996
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes) theta i omega := by
  unfold _root_.GD.N0232.N0719.N0831.d011994
  exact div_nonneg
    (_root_.GD.N0232.N0719.N0900.d009123
      (lt_of_lt_of_le (by norm_num) (hsizes i)) (omega i))
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))


def d011997
    {k : ℕ} {sizes : Fin k → ℕ}
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    Measure (_root_.GD.N0232.N0719.d009173 k sizes) :=
  (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta).withDensity fun omega ↦
    ENNReal.ofReal
      (_root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes) theta i omega)



theorem d011998
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0836.d011973 i
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) =
      dilation ^ 2 * _root_.GD.N0232.N0719.N0836.d011973 i omega := by
  unfold _root_.GD.N0232.N0719.N0836.d011973 _root_.GD.N0232.N0719.N0900.d009095
  exact _root_.GD.N0107.d009088
    (lt_of_lt_of_le (by norm_num) (hsizes i))
    shift dilation (omega i)



theorem d011999
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes)
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) =
      _root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes) theta i omega := by
  unfold _root_.GD.N0232.N0719.N0831.d011994
  rw [_root_.GD.N0232.N0719.N0831.d011998 hsizes]
  simp only [_root_.GD.N0232.N0719.N0845.d010883]
  have hn : ((sizes i - 1 : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < sizes i - 1 := Nat.sub_pos_iff_lt.mpr
      (lt_of_lt_of_le (by norm_num) (hsizes i))
    exact_mod_cast hpos.ne'
  have hs : theta.scale i ≠ 0 := (theta.scale_pos i).ne'
  field_simp [hn, hdilation.ne', hs]


theorem d012000
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (∫ omega : _root_.GD.N0232.N0719.d009173 k sizes,
        _root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes) theta i omega
      ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) = 1 := by
  unfold _root_.GD.N0232.N0719.N0831.d011994 _root_.GD.N0232.N0719.N0859.d010812
  rw [integral_div,
    _root_.GD.N0232.N0719.N0836.d011977
      k sizes hsizes theta.location theta.scale i]
  have hn : ((sizes i - 1 : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < sizes i - 1 := Nat.sub_pos_iff_lt.mpr
      (lt_of_lt_of_le (by norm_num) (hsizes i))
    exact_mod_cast hpos.ne'
  have hs : theta.scale i ≠ 0 := (theta.scale_pos i).ne'
  field_simp [hn, hs]


theorem d012001
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes) theta i Set.univ = 1 := by
  unfold _root_.GD.N0232.N0719.N0831.d011997
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (by
      unfold _root_.GD.N0232.N0719.N0831.d011994 _root_.GD.N0232.N0719.N0859.d010812
      exact (_root_.GD.N0232.N0719.N0836.d011983
        k sizes hsizes theta.location theta.scale i).div_const _)
    (ae_of_all _ fun omega ↦
      _root_.GD.N0232.N0719.N0831.d011996
        (sizes := sizes) hsizes theta i omega)]
  rw [_root_.GD.N0232.N0719.N0831.d012000
    (sizes := sizes) hsizes theta i]
  simp




theorem d012002
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes) theta i).map
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation) =
      _root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes)
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i := by
  let T := _root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation
  have hT : Measurable T :=
    _root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation
  have hlaw :
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta).map T =
        _root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) := by
    unfold _root_.GD.N0232.N0719.N0859.d010812
    exact _root_.GD.N0232.N0719.d009188
      k sizes shift dilation theta.location theta.scale
  rw [_root_.GD.N0232.N0719.N0831.d011997, _root_.GD.N0232.N0719.N0831.d011997, ← hlaw]
  ext s hs
  rw [Measure.map_apply hT hs]
  rw [withDensity_apply _ (hT hs)]
  rw [withDensity_apply _ hs]
  rw [setLIntegral_map hs
    ((_root_.GD.N0232.N0719.N0831.d011995
      (sizes := sizes)
      (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i).ennreal_ofReal)
    hT]
  apply setLIntegral_congr_fun (hT hs)
  intro omega homega
  change ENNReal.ofReal
      (_root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes) theta i omega) =
    ENNReal.ofReal
      (_root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes)
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega))
  rw [_root_.GD.N0232.N0719.N0831.d011999
    (sizes := sizes) hsizes shift dilation hdilation theta i omega]






theorem d012003
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349)
    (i : Fin k) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0836.d011985 k sizes hk hsizes g i omega =
      _root_.GD.N0232.N0719.N0865.d011217 k sizes
          (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) omega *
        _root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes)
          (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i omega := by
  unfold _root_.GD.N0232.N0719.N0836.d011985 _root_.GD.N0232.N0719.N0830.d011754
    _root_.GD.N0232.N0719.N0831.d011994
  rw [_root_.GD.N0232.N0719.N0834.d011970]
  simp only [_root_.GD.N0232.N0719.N0834.d011969]
  have hn : ((sizes i - 1 : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < sizes i - 1 := Nat.sub_pos_iff_lt.mpr
      (lt_of_lt_of_le (by norm_num) (hsizes i))
    exact_mod_cast hpos.ne'
  have hr : (g.2.1 : ℝ) ≠ 0 := g.2.2.ne'
  have hcap :
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ 0 :=
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)).ne'
  field_simp [hn, hr, hcap]




theorem d012004
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349)
    (i : Fin k) :
    _root_.GD.N0232.N0719.N0836.d011990 k sizes hk hsizes g i =
      _root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes)
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i := by
  unfold _root_.GD.N0232.N0719.N0836.d011990 _root_.GD.N0232.N0719.N0831.d011997
  rw [_root_.GD.N0232.N0719.N0865.d011220]
  rw [← withDensity_mul
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
    ((_root_.GD.N0232.N0719.N0865.d011218 k sizes
      (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g)).ennreal_ofReal)
    ((_root_.GD.N0232.N0719.N0831.d011995 (sizes := sizes)
      (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i).ennreal_ofReal)]
  apply withDensity_congr_ae
  filter_upwards with omega
  simp only [Pi.mul_apply]
  rw [_root_.GD.N0232.N0719.N0831.d012003
    k sizes hk hsizes g i omega]
  exact ENNReal.ofReal_mul
    (_root_.GD.N0232.N0719.N0865.d011219 k sizes
      (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) omega)




theorem d012005
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349)
    (i : Fin k) :
    (_root_.GD.N0232.N0719.N0836.d011990 k sizes hk hsizes g i).map
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes g.1 g.2.1) =
      _root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes)
        (_root_.GD.N0232.N0719.N0859.d010810 k) i := by
  rw [_root_.GD.N0232.N0719.N0831.d012004]
  rw [_root_.GD.N0232.N0719.N0831.d012002
    (sizes := sizes) hsizes g.1 g.2.1 g.2.2
      (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i]
  rw [_root_.GD.N0232.N0719.N0835.d011954]





def d012006
    {k : ℕ} {sizes : Fin k → ℕ}
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : Measure (_root_.GD.N0232.N0719.N0900.d009096 k) :=
  (_root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes) theta i).map
    (_root_.GD.N0232.N0719.N0900.d009104 k sizes)

@[fun_prop]
theorem d012007
    {k : ℕ} (shift dilation : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0900.d009101 shift dilation : _root_.GD.N0232.N0719.N0900.d009096 k → _root_.GD.N0232.N0719.N0900.d009096 k) := by
  rw [measurable_comap_iff]
  change Measurable
    (fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦
      ((fun i ↦ shift + dilation * s.mean i),
        fun i ↦ dilation ^ 2 * s.meanVariance i))
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    fun_prop
  · apply measurable_pi_lambda
    intro i
    fun_prop



theorem d012008
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0831.d012006 (sizes := sizes) theta i).map
        (_root_.GD.N0232.N0719.N0900.d009101 shift dilation) =
      _root_.GD.N0232.N0719.N0831.d012006 (sizes := sizes)
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i := by
  have hsizes0 : ∀ j, 0 < sizes j := fun j ↦
    lt_of_lt_of_le (by norm_num) (hsizes j)
  have hraw : Measurable (_root_.GD.N0232.N0719.N0900.d009104 k sizes) :=
    _root_.GD.N0232.N0719.N0900.d009115 k sizes
  have haff : Measurable
      (_root_.GD.N0232.N0719.N0900.d009101 shift dilation : _root_.GD.N0232.N0719.N0900.d009096 k → _root_.GD.N0232.N0719.N0900.d009096 k) :=
    _root_.GD.N0232.N0719.N0831.d012007 shift dilation
  unfold _root_.GD.N0232.N0719.N0831.d012006
  rw [Measure.map_map haff hraw]
  rw [show _root_.GD.N0232.N0719.N0900.d009101 shift dilation ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes =
      _root_.GD.N0232.N0719.N0900.d009104 k sizes ∘ _root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation by
    funext omega
    exact (_root_.GD.N0232.N0719.N0900.d009139
      hsizes0 shift dilation omega).symm]
  rw [← Measure.map_map hraw
    (_root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation)]
  rw [_root_.GD.N0232.N0719.N0831.d012002
    (sizes := sizes) hsizes shift dilation hdilation theta i]

end

end N0831
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0831.d012002
#print axioms _root_.GD.N0232.N0719.N0831.d012005
#print axioms _root_.GD.N0232.N0719.N0831.d012008
