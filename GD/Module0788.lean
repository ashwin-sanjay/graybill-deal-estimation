import GD.Module0775
import GD.Module0786
import GD.Module0658













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


def d011973
    {k : ℕ} {sizes : Fin k → ℕ} (i : Fin k)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  @_root_.GD.N0126.d006422 (Fin (sizes i)) _ (omega i)

@[fun_prop]
theorem d011974
    {k : ℕ} {sizes : Fin k → ℕ} (i : Fin k) :
    Measurable (_root_.GD.N0232.N0719.N0836.d011973 (sizes := sizes) i) := by
  unfold _root_.GD.N0232.N0719.N0836.d011973 _root_.GD.N0126.d006422
    _root_.GD.N0126.d006421 _root_.GD.N0126.d006420
    _root_.GD.N0126.d006419
  fun_prop



theorem d011975
    (n : ℕ) (hn : 2 ≤ n) :
    (∫ x : _root_.GD.N0137.d008894 n,
        @_root_.GD.N0126.d006422 (Fin n) _ x
      ∂_root_.GD.N0137.d008895 n) = (n - 1 : ℕ) := by
  let a : ℝ := ((n - 1 : ℕ) : ℝ) / 2
  have ha : 0 < a := _root_.GD.N0137.d008900 hn
  have hLaw : HasLaw (_root_.GD.N0137.d008897 n)
      (gammaMeasure a a) (_root_.GD.N0137.d008895 n) := ⟨
    (_root_.GD.N0137.d008899 n).aemeasurable,
    by simpa [a] using _root_.GD.N0137.d008902 n hn⟩
  have hmean :
      (∫ x : _root_.GD.N0137.d008894 n, _root_.GD.N0137.d008897 n x
        ∂_root_.GD.N0137.d008895 n) = 1 := by
    rw [hLaw.integral_eq, _root_.GD.N0232.N0719.N0960.d009682 ha ha]
    field_simp [ha.ne']
  unfold _root_.GD.N0137.d008897 at hmean
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - 1 ≠ 0)
  rw [integral_div] at hmean
  field_simp [hn1] at hmean ⊢
  exact hmean



theorem d011976
    (n : ℕ) (hn : 2 ≤ n) (location scale : ℝ) :
    (∫ x : _root_.GD.N0137.d008894 n,
        @_root_.GD.N0126.d006422 (Fin n) _ x
      ∂_root_.GD.N0232.N0719.d009174 n location scale) =
      (n - 1 : ℕ) * scale ^ 2 := by
  unfold _root_.GD.N0232.N0719.d009174
  rw [integral_map_of_stronglyMeasurable
    (_root_.GD.N0107.d009020 n location scale)
    (by
      unfold _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
        _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
      fun_prop : StronglyMeasurable
        (fun x : _root_.GD.N0137.d008894 n ↦
          @_root_.GD.N0126.d006422 (Fin n) _ x))]
  simp_rw [_root_.GD.N0107.d009088
    (by omega : 0 < n) location scale]
  rw [integral_const_mul, _root_.GD.N0232.N0719.N0836.d011975 n hn]
  ring



theorem d011977
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ) (i : Fin k) :
    (∫ omega : _root_.GD.N0232.N0719.d009173 k sizes,
        _root_.GD.N0232.N0719.N0836.d011973 i omega
      ∂_root_.GD.N0232.N0719.d009176 k sizes location scale) =
      (sizes i - 1 : ℕ) * (scale i) ^ 2 := by
  unfold _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N0836.d011973
  rw [integral_comp_eval
    (X := fun j : Fin k ↦ _root_.GD.N0137.d008894 (sizes j))
    (μ := fun j : Fin k ↦ _root_.GD.N0232.N0719.d009174
      (sizes j) location (scale j))
    (i := i)
    (f := fun x : _root_.GD.N0137.d008894 (sizes i) ↦
      @_root_.GD.N0126.d006422 (Fin (sizes i)) _ x)
    (by
      unfold _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
        _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
      fun_prop : AEStronglyMeasurable
        (fun x : _root_.GD.N0137.d008894 (sizes i) ↦
          @_root_.GD.N0126.d006422 (Fin (sizes i)) _ x)
        (_root_.GD.N0232.N0719.d009174 (sizes i) location (scale i)))]
  exact _root_.GD.N0232.N0719.N0836.d011976
    (sizes i) (hsizes i) location (scale i)



theorem d011978
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (∫ omega : _root_.GD.N0232.N0719.d009173 k sizes,
        _root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega * _root_.GD.N0232.N0719.N0836.d011973 i omega
      ∂_root_.GD.N0232.N0719.d009182 k sizes) =
      (sizes i - 1 : ℕ) * (theta.scale i) ^ 2 := by
  have hlaw := _root_.GD.N0232.N0719.N0932.d009223
    k sizes theta.location theta.scale theta.scale_pos
  rw [← _root_.GD.N0232.N0719.N0836.d011977
    k sizes hsizes theta.location theta.scale i, hlaw]
  change
    (∫ omega : _root_.GD.N0232.N0719.d009173 k sizes,
        _root_.GD.N0232.N0719.N0932.d009219
            k sizes theta.location theta.scale omega *
          _root_.GD.N0232.N0719.N0836.d011973 i omega
      ∂_root_.GD.N0232.N0719.d009182 k sizes) =
      ∫ omega : _root_.GD.N0232.N0719.d009173 k sizes,
        _root_.GD.N0232.N0719.N0836.d011973 i omega
      ∂(_root_.GD.N0232.N0719.d009182 k sizes).withDensity (fun omega ↦
        ENNReal.ofReal (_root_.GD.N0232.N0719.N0932.d009219
          k sizes theta.location theta.scale omega))
  rw [integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0232.N0719.N0932.d009220
      k sizes theta.location theta.scale).ennreal_ofReal
    (by simp)]
  apply integral_congr_ae
  filter_upwards with omega
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0719.N0932.d009221
      k sizes theta.location theta.scale omega)]
  simp only [smul_eq_mul]



theorem d011979
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (∫ omega : _root_.GD.N0232.N0719.d009173 k sizes,
        _root_.GD.N0232.N0719.N0836.d011973 i omega *
          _root_.GD.N0232.N0719.N0830.d011754
            k sizes hk hsizes theta omega
      ∂_root_.GD.N0232.N0719.d009182 k sizes) =
      ((sizes i - 1 : ℕ) * (theta.scale i) ^ 2) /
        _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta := by
  unfold _root_.GD.N0232.N0719.N0830.d011754
  rw [show (fun omega ↦
      _root_.GD.N0232.N0719.N0836.d011973 i omega *
        (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta)) =
      fun omega ↦
        (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega *
          _root_.GD.N0232.N0719.N0836.d011973 i omega) /
            _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta by
    funext omega
    ring]
  rw [integral_div,
    _root_.GD.N0232.N0719.N0836.d011978
      k sizes hsizes theta i]




theorem d011980
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    (∫ omega : _root_.GD.N0232.N0719.d009173 k sizes,
        _root_.GD.N0232.N0719.N0836.d011973 i omega *
          _root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes
            (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) omega
      ∂_root_.GD.N0232.N0719.d009182 k sizes) =
      (sizes i - 1 : ℕ) /
        _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) := by
  rw [_root_.GD.N0232.N0719.N0836.d011979
    k sizes hk hsizes]
  unfold _root_.GD.N0232.N0719.N0835.d011953
  rw [_root_.GD.N0232.N0719.N0845.d010897]
  simp only [_root_.GD.N0232.N0719.N0845.d010883]
  simp only [_root_.GD.N0232.N0719.N0859.d010810, mul_one]
  have hr : (g.2.1 : ℝ) ≠ 0 := g.2.2.ne'
  have hcap :
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ 0 :=
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)).ne'
  field_simp [hr, hcap]

end

end N0836
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0836.d011980
