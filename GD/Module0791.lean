import GD.Module0790


















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0832

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0835
open _root_.GD.N0232.N0719.N0834
open _root_.GD.N0232.N0719.N0836
open _root_.GD.N0232.N0719.N0831
open _root_.GD.N0232.N0719.N0910
open _root_.GD.N0230.N0655






theorem d012009
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ x ∂_root_.GD.N0137.d008895 n,
      0 < @_root_.GD.N0126.d006422 (Fin n) _ x := by
  let a : ℝ := ((n - 1 : ℕ) : ℝ) / 2
  have ha : 0 < a := _root_.GD.N0137.d008900 hn
  have hgamma : ∀ᵐ x ∂gammaMeasure a a, 0 < x :=
    _root_.GD.N0232.N0719.N0910.d010286 ha ha
  have hmap :
      (_root_.GD.N0137.d008895 n).map (_root_.GD.N0137.d008897 n) =
        gammaMeasure a a := by
    simpa [a] using _root_.GD.N0137.d008902 n hn
  have hnormalized :
      ∀ᵐ x ∂_root_.GD.N0137.d008895 n, 0 < _root_.GD.N0137.d008897 n x := by
    apply (ae_map_iff
      (_root_.GD.N0137.d008899 n).aemeasurable
      measurableSet_Ioi).1
    rw [hmap]
    exact hgamma
  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by
    dsimp [a] at ha
    nlinarith [ha]
  filter_upwards [hnormalized] with x hx
  unfold _root_.GD.N0137.d008897 at hx
  exact (div_pos_iff_of_pos_right hn1).mp hx



theorem d012010
    (n : ℕ) (hn : 2 ≤ n)
    (location scale : ℝ) (hscale : 0 < scale) :
    ∀ᵐ x ∂_root_.GD.N0232.N0719.d009174 n location scale,
      0 < @_root_.GD.N0126.d006422 (Fin n) _ x := by
  let positiveSet : Set (_root_.GD.N0137.d008894 n) :=
    {x | 0 < @_root_.GD.N0126.d006422 (Fin n) _ x}
  have hresidual : Measurable
      (fun x : _root_.GD.N0137.d008894 n ↦
        @_root_.GD.N0126.d006422 (Fin n) _ x) := by
    unfold _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
      _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
    fun_prop
  have hset : MeasurableSet positiveSet :=
    measurableSet_lt measurable_const hresidual
  unfold _root_.GD.N0232.N0719.d009174
  apply (ae_map_iff
    (_root_.GD.N0107.d009020 n location scale).aemeasurable hset).2
  filter_upwards [_root_.GD.N0232.N0719.N0832.d012009 n hn] with x hx
  rw [_root_.GD.N0107.d009088
    (lt_of_lt_of_le (by norm_num) hn) location scale x]
  exact mul_pos (sq_pos_of_pos hscale) hx



theorem d012011
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta,
      0 < _root_.GD.N0232.N0719.N0836.d011973 (sizes := sizes) i omega := by
  unfold _root_.GD.N0232.N0719.N0859.d010812 _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N0836.d011973
  exact
    (measurePreserving_eval
      (fun j ↦ _root_.GD.N0232.N0719.d009174
        (sizes j) theta.location (theta.scale j)) i).quasiMeasurePreserving.ae
      (_root_.GD.N0232.N0719.N0832.d012010
        (sizes i) (hsizes i) theta.location (theta.scale i)
          (theta.scale_pos i))






def d012012
    {k : ℕ} {sizes : Fin k → ℕ}
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  (d omega - theta.location) ^ 2 /
    _root_.GD.N0232.N0719.N0836.d011973 (sizes := sizes) i omega

@[fun_prop]
theorem d012013
    {k : ℕ} {sizes : Fin k → ℕ}
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    Measurable
      (_root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes) theta i d) := by
  unfold _root_.GD.N0232.N0719.N0832.d012012
  fun_prop

theorem d012014
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes) theta i d omega := by
  unfold _root_.GD.N0232.N0719.N0832.d012012
  exact div_nonneg (sq_nonneg _)
    (_root_.GD.N0232.N0719.N0900.d009123
      (lt_of_lt_of_le (by norm_num) (hsizes i)) (omega i))




theorem d012015
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes)
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d)
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) =
      _root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes) theta i d omega := by
  unfold _root_.GD.N0232.N0719.N0832.d012012
  rw [_root_.GD.N0232.N0719.N0842.d010913
    k sizes shift dilation hdilation.ne' d omega]
  rw [_root_.GD.N0232.N0719.N0831.d011998 hsizes]
  simp only [_root_.GD.N0232.N0719.N0845.d010882]
  have hreal :
      ((shift + dilation * d omega) -
          (shift + dilation * theta.location)) ^ 2 =
        dilation ^ 2 * (d omega - theta.location) ^ 2 := by
    ring
  rw [hreal]
  field_simp [hdilation.ne']





theorem d012016
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    (∫⁻ omega,
        ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes)
            (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) omega)
      ∂_root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes)
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i) =
      ∫⁻ omega,
        ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes) theta i d omega)
      ∂_root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes) theta i := by
  rw [← _root_.GD.N0232.N0719.N0831.d012002
    (sizes := sizes) hsizes shift dilation hdilation theta i]
  rw [lintegral_map]
  · apply lintegral_congr
    intro omega
    rw [_root_.GD.N0232.N0719.N0832.d012015
      (sizes := sizes) hsizes shift dilation hdilation theta i d omega]
  · exact
      (_root_.GD.N0232.N0719.N0832.d012013 (sizes := sizes)
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d)
        (_root_.GD.N0232.N0719.N0842.d010912 k sizes shift dilation d hd)).ennreal_ofReal
  · exact _root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation




theorem d012017
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d =
      ENNReal.ofReal
          (((sizes i - 1 : ℕ) : ℝ) * (theta.scale i) ^ 2) *
        ∫⁻ omega,
          ENNReal.ofReal
            (_root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes) theta i d omega)
          ∂_root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes) theta i := by
  let D : ℝ := ((sizes i - 1 : ℕ) : ℝ) * (theta.scale i) ^ 2
  have ha : 0 < (((sizes i - 1 : ℕ) : ℝ) / 2) :=
    _root_.GD.N0137.d008900 (hsizes i)
  have hn1 : 0 < ((sizes i - 1 : ℕ) : ℝ) := by
    nlinarith [ha]
  have hD : 0 < D := mul_pos hn1 (sq_pos_of_pos (theta.scale_pos i))
  have hscale : theta.scale i ≠ 0 := ne_of_gt (theta.scale_pos i)
  have hweightMeas :=
    (_root_.GD.N0232.N0719.N0831.d011995
      (sizes := sizes) theta i).ennreal_ofReal
  have herrorMeas :=
    (_root_.GD.N0232.N0719.N0832.d012013
      (sizes := sizes) theta i d hd).ennreal_ofReal
  unfold _root_.GD.N0232.N0719.N0831.d011997
  rw [lintegral_withDensity_eq_lintegral_mul
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) hweightMeas herrorMeas]
  change _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d =
    ENNReal.ofReal D *
      ∫⁻ omega,
        ENNReal.ofReal
            (_root_.GD.N0232.N0719.N0831.d011994 (sizes := sizes) theta i omega) *
          ENNReal.ofReal
            (_root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes) theta i d omega)
        ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta
  rw [← lintegral_const_mul
    (ENNReal.ofReal D) (hweightMeas.mul herrorMeas)]
  unfold _root_.GD.N0232.N0719.N0859.d010840
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0232.N0719.N0832.d012011
    k sizes hsizes theta i] with omega hresidual
  have hweightNonneg := _root_.GD.N0232.N0719.N0831.d011996
    (sizes := sizes) hsizes theta i omega
  rw [← ENNReal.ofReal_mul hweightNonneg]
  rw [← ENNReal.ofReal_mul hD.le]
  apply congrArg ENNReal.ofReal
  unfold D _root_.GD.N0232.N0719.N0831.d011994 _root_.GD.N0232.N0719.N0832.d012012
  field_simp [hresidual.ne', hscale]






theorem d012018
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    ENNReal.ofReal
        (((sizes i - 1 : ℕ) : ℝ) *
          ((_root_.GD.N0232.N0719.N0835.d011953 (k := k) g).scale i) ^ 2) /
        _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) =
      ENNReal.ofReal
        (((sizes i - 1 : ℕ) : ℝ) /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)) := by
  unfold _root_.GD.N0232.N0719.N0858.d010852
  rw [← ENNReal.ofReal_div_of_pos
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g))]
  apply congrArg ENNReal.ofReal
  rw [_root_.GD.N0232.N0719.N0834.d011970]
  simp only [_root_.GD.N0232.N0719.N0834.d011969]
  have hr : (g.2.1 : ℝ) ≠ 0 := g.2.2.ne'
  have hcap :
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ 0 :=
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)).ne'
  field_simp [hr, hcap]




theorem d012019
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) d /
        _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) =
      ENNReal.ofReal
          (((sizes i - 1 : ℕ) : ℝ) /
            _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)) *
        ∫⁻ omega,
          ENNReal.ofReal
            (_root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes)
              (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i d omega)
          ∂_root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes)
            (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i := by
  rw [_root_.GD.N0232.N0719.N0832.d012017
    k sizes hsizes (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i d hd]
  rw [show ∀ a b c : ENNReal, (a * b) / c = (a / c) * b by
    intro a b c
    simp only [div_eq_mul_inv]
    ac_rfl]
  rw [_root_.GD.N0232.N0719.N0832.d012018
    k sizes hk hsizes g i]




theorem d012020
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) d /
        _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) =
      ENNReal.ofReal
          (((sizes i - 1 : ℕ) : ℝ) /
            _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)) *
        ∫⁻ omega,
          ENNReal.ofReal
            (_root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes)
              (_root_.GD.N0232.N0719.N0859.d010810 k) i
              (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 g.2.1 d) omega)
          ∂_root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes)
            (_root_.GD.N0232.N0719.N0859.d010810 k) i := by
  rw [_root_.GD.N0232.N0719.N0832.d012019
    k sizes hk hsizes g i d hd]
  have hcarrier := _root_.GD.N0232.N0719.N0832.d012016
    (sizes := sizes) hsizes g.1 g.2.1 g.2.2
      (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i d hd
  rw [_root_.GD.N0232.N0719.N0835.d011954] at hcarrier
  rw [hcarrier]




theorem d012021
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d)
    (hfixed : _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 g.2.1 d = d) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) d /
        _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) =
      ENNReal.ofReal
          (((sizes i - 1 : ℕ) : ℝ) /
            _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)) *
        ∫⁻ omega,
          ENNReal.ofReal
            (_root_.GD.N0232.N0719.N0832.d012012 (sizes := sizes)
              (_root_.GD.N0232.N0719.N0859.d010810 k) i d omega)
          ∂_root_.GD.N0232.N0719.N0831.d011997 (sizes := sizes)
            (_root_.GD.N0232.N0719.N0859.d010810 k) i := by
  rw [_root_.GD.N0232.N0719.N0832.d012020
    k sizes hk hsizes g i d hd]
  rw [hfixed]

end

end N0832
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0832.d012011
#print axioms _root_.GD.N0232.N0719.N0832.d012017
#print axioms _root_.GD.N0232.N0719.N0832.d012019
#print axioms _root_.GD.N0232.N0719.N0832.d012015
#print axioms _root_.GD.N0232.N0719.N0832.d012020
