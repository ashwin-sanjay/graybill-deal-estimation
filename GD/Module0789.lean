import GD.Module0788














open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace GD
namespace N0232
namespace N0719
namespace N0836

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0865
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0830
open _root_.GD.N0232.N0719.N0835
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0960
open _root_.GD.N0230.N0655


theorem d011981
    (n : ℕ) (hn : 2 ≤ n) :
    Integrable
      (fun x : _root_.GD.N0137.d008894 n ↦
        @_root_.GD.N0126.d006422 (Fin n) _ x)
      (_root_.GD.N0137.d008895 n) := by
  let a : ℝ := ((n - 1 : ℕ) : ℝ) / 2
  have ha : 0 < a := _root_.GD.N0137.d008900 hn
  have hmap :
      (_root_.GD.N0137.d008895 n).map (_root_.GD.N0137.d008897 n) =
        gammaMeasure a a := by
    simpa [a] using _root_.GD.N0137.d008902 n hn
  have hid : Integrable (fun x : ℝ ↦ x) (gammaMeasure a a) :=
    _root_.GD.N0232.N0719.N0960.d009683 ha ha
  have hnormalized :
      Integrable (_root_.GD.N0137.d008897 n) (_root_.GD.N0137.d008895 n) := by
    have hmapIntegrable :
        Integrable (fun x : ℝ ↦ x)
          ((_root_.GD.N0137.d008895 n).map (_root_.GD.N0137.d008897 n)) := by
      simpa [hmap] using hid
    have hcomp :=
      (integrable_map_measure
        (g := fun x : ℝ ↦ x)
        (f := _root_.GD.N0137.d008897 n)
        (by fun_prop)
        (_root_.GD.N0137.d008899 n).aemeasurable).1
        hmapIntegrable
    simpa [Function.comp_def] using hcomp
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - 1 ≠ 0)
  apply hnormalized.const_mul ((n - 1 : ℕ) : ℝ) |>.congr
  filter_upwards with x
  unfold _root_.GD.N0137.d008897
  field_simp [hn1]



theorem d011982
    (n : ℕ) (hn : 2 ≤ n) (location scale : ℝ) :
    Integrable
      (fun x : _root_.GD.N0137.d008894 n ↦
        @_root_.GD.N0126.d006422 (Fin n) _ x)
      (_root_.GD.N0232.N0719.d009174 n location scale) := by
  unfold _root_.GD.N0232.N0719.d009174
  rw [integrable_map_measure
    (by
      unfold _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
        _root_.GD.N0126.d006420
      fun_prop : AEStronglyMeasurable
        (fun x : _root_.GD.N0137.d008894 n ↦
          @_root_.GD.N0126.d006422 (Fin n) _ x)
        ((_root_.GD.N0137.d008895 n).map (_root_.GD.N0107.d009018 n location scale)))
    (_root_.GD.N0107.d009020 n location scale).aemeasurable]
  have h :=
    (_root_.GD.N0232.N0719.N0836.d011981 n hn).const_mul (scale ^ 2)
  apply h.congr
  filter_upwards with x
  simp only [Function.comp_apply]
  symm
  exact _root_.GD.N0107.d009088 (by omega : 0 < n) location scale x



theorem d011983
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ) (i : Fin k) :
    Integrable (_root_.GD.N0232.N0719.N0836.d011973 i)
      (_root_.GD.N0232.N0719.d009176 k sizes location scale) := by
  unfold _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N0836.d011973
  exact integrable_comp_eval
    (_root_.GD.N0232.N0719.N0836.d011982
      (sizes i) (hsizes i) location (scale i))



theorem d011984
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    Integrable
      (fun omega : _root_.GD.N0232.N0719.d009173 k sizes ↦
        _root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega *
          _root_.GD.N0232.N0719.N0836.d011973 i omega)
      (_root_.GD.N0232.N0719.d009182 k sizes) := by
  have hresidual := _root_.GD.N0232.N0719.N0836.d011983
    k sizes hsizes theta.location theta.scale i
  have hlaw := _root_.GD.N0232.N0719.N0932.d009223
    k sizes theta.location theta.scale theta.scale_pos
  rw [hlaw] at hresidual
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0719.N0932.d009220
      k sizes theta.location theta.scale).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at hresidual
  apply hresidual.congr
  filter_upwards with omega
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0719.N0932.d009221
      k sizes theta.location theta.scale omega)]
  simp only [smul_eq_mul]
  change
    _root_.GD.N0232.N0719.N0932.d009219
        k sizes theta.location theta.scale omega * _root_.GD.N0232.N0719.N0836.d011973 i omega =
      _root_.GD.N0232.N0719.N0932.d009219
        k sizes theta.location theta.scale omega * _root_.GD.N0232.N0719.N0836.d011973 i omega
  rfl


def d011985
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  (_root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) /
      (sizes i - 1 : ℕ)) *
    (_root_.GD.N0232.N0719.N0836.d011973 i omega *
      _root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) omega)

@[fun_prop]
theorem d011986
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    Measurable
      (_root_.GD.N0232.N0719.N0836.d011985 k sizes hk hsizes g i) := by
  unfold _root_.GD.N0232.N0719.N0836.d011985
  fun_prop

theorem d011987
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0836.d011985 k sizes hk hsizes g i omega := by
  have hi1 : 1 < sizes i :=
    lt_of_lt_of_le (by norm_num) (hsizes i)
  have hi0 : 0 < sizes i := Nat.zero_lt_of_lt hi1
  unfold _root_.GD.N0232.N0719.N0836.d011985
  exact mul_nonneg
    (div_nonneg
      (_root_.GD.N0232.N0719.N0858.d010853
        k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)).le
      (Nat.cast_nonneg _))
    (mul_nonneg
      (_root_.GD.N0232.N0719.N0900.d009123 hi0 (omega i))
      (_root_.GD.N0232.N0719.N0830.d011756
        k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) omega))

theorem d011988
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    Integrable
      (_root_.GD.N0232.N0719.N0836.d011985 k sizes hk hsizes g i)
      (_root_.GD.N0232.N0719.d009182 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0836.d011985 _root_.GD.N0232.N0719.N0830.d011754
  have hbase := _root_.GD.N0232.N0719.N0836.d011984
    k sizes hsizes (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i
  have hcap :
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) ≠ 0 :=
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g)).ne'
  have hdiv : Integrable
      (fun omega : _root_.GD.N0232.N0719.d009173 k sizes ↦
        (_root_.GD.N0232.N0719.N0865.d011217 k sizes
          (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) omega *
            _root_.GD.N0232.N0719.N0836.d011973 i omega) /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
            (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g))
      (_root_.GD.N0232.N0719.d009182 k sizes) := hbase.div_const _
  apply (hdiv.const_mul
    (_root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) /
      (sizes i - 1 : ℕ))).congr
  filter_upwards with omega
  field_simp [hcap]


theorem d011989
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    (∫ omega : _root_.GD.N0232.N0719.d009173 k sizes,
        _root_.GD.N0232.N0719.N0836.d011985 k sizes hk hsizes g i omega
      ∂_root_.GD.N0232.N0719.d009182 k sizes) = 1 := by
  unfold _root_.GD.N0232.N0719.N0836.d011985
  rw [integral_const_mul,
    _root_.GD.N0232.N0719.N0836.d011980
      k sizes hk hsizes g i]
  have hn1 : ((sizes i - 1 : ℕ) : ℝ) ≠ 0 := by
    have hi1 : 1 < sizes i :=
      lt_of_lt_of_le (by norm_num) (hsizes i)
    have hnNat : 0 < sizes i - 1 := Nat.sub_pos_iff_lt.mpr hi1
    exact_mod_cast hnNat.ne'
  have hcap :
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ 0 :=
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)).ne'
  field_simp [hn1, hcap]


def d011990
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    Measure (_root_.GD.N0232.N0719.d009173 k sizes) :=
  (_root_.GD.N0232.N0719.d009182 k sizes).withDensity fun omega ↦
    ENNReal.ofReal
      (_root_.GD.N0232.N0719.N0836.d011985 k sizes hk hsizes g i omega)



theorem d011991
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    _root_.GD.N0232.N0719.N0836.d011990 k sizes hk hsizes g i Set.univ = 1 := by
  unfold _root_.GD.N0232.N0719.N0836.d011990
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0232.N0719.N0836.d011988 k sizes hk hsizes g i)
    (ae_of_all _ fun omega ↦
      _root_.GD.N0232.N0719.N0836.d011987
        k sizes hk hsizes g i omega)]
  rw [_root_.GD.N0232.N0719.N0836.d011989]
  simp

noncomputable instance d011992
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0836.d011990 k sizes hk hsizes g i) :=
  ⟨_root_.GD.N0232.N0719.N0836.d011991 k sizes hk hsizes g i⟩




theorem d011993
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ≥0∞) :
    (∫⁻ omega, f omega
      ∂_root_.GD.N0232.N0719.N0836.d011990 k sizes hk hsizes g i) =
      ∫⁻ omega,
        ENNReal.ofReal
            (_root_.GD.N0232.N0719.N0836.d011985 k sizes hk hsizes g i omega) *
          f omega
        ∂_root_.GD.N0232.N0719.d009182 k sizes := by
  unfold _root_.GD.N0232.N0719.N0836.d011990
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable
    (_root_.GD.N0232.N0719.d009182 k sizes)
    (_root_.GD.N0232.N0719.N0836.d011986
      k sizes hk hsizes g i).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rfl

end

end N0836
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0836.d011991
#print axioms _root_.GD.N0232.N0719.N0836.d011993
