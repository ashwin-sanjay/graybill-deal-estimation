import GD.Module0630
import GD.Module0719










open MeasureTheory Set

namespace GD
namespace N0232
namespace N0719
namespace N0837

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1018
open _root_.GD.N0232.N0719.N1015
open _root_.GD.N0232.N0719.N1024


theorem d010742
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (triangle : Fin 3 ↪ Fin k)
    (shift location : ℝ) (dilation : ℝ) (hdilation : dilation ≠ 0)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N1015.d010078 (shift + dilation * location)
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) *
        _root_.GD.N0232.N0719.N1015.d010079 triangle
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) =
      dilation ^ 2 *
        (_root_.GD.N0232.N0719.N1015.d010078 location omega * _root_.GD.N0232.N0719.N1015.d010079 triangle omega) := by
  have hbase := _root_.GD.N0232.N0719.N0900.d009146
    hk hsizes shift hdilation omega
  have hsummary := _root_.GD.N0232.N0719.N0900.d009139
    hsizes shift dilation omega
  have hcorrection := _root_.GD.N0232.N0719.N1018.d010057
    hk triangle shift hdilation (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)
  unfold _root_.GD.N0232.N0719.N1015.d010078
    _root_.GD.N0232.N0719.N1015.d010079
  rw [hbase, hsummary, hcorrection]
  ring



theorem d010743
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (triangle : Fin 3 ↪ Fin k)
    (shift location : ℝ) (dilation : ℝ) (hdilation : dilation ≠ 0)
    (scales : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N1015.d010080
        (_root_.GD.N0232.N0719.d009176 k sizes
          (shift + dilation * location)
          (fun i ↦ dilation * scales i))
        (shift + dilation * location) triangle =
      dilation ^ 2 *
        _root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
          location triangle := by
  have hmap := _root_.GD.N0232.N0719.d009188
    k sizes shift dilation location scales
  unfold _root_.GD.N0232.N0719.N1015.d010080
  rw [← hmap]
  rw [integral_map_of_stronglyMeasurable
    (μ := _root_.GD.N0232.N0719.d009176 k sizes location scales)
    (φ := _root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation)
    (f := fun omega ↦
      _root_.GD.N0232.N0719.N1015.d010078 (shift + dilation * location) omega *
        _root_.GD.N0232.N0719.N1015.d010079 triangle omega)
    (_root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation)
    ((((_root_.GD.N0232.N0719.N0900.d009122 k sizes).sub measurable_const).mul
      ((_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k sizes))).stronglyMeasurable)]
  calc
    (∫ omega,
        _root_.GD.N0232.N0719.N1015.d010078 (shift + dilation * location)
            (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) *
          _root_.GD.N0232.N0719.N1015.d010079 triangle
            (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega)
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) =
      ∫ omega,
        dilation ^ 2 *
          (_root_.GD.N0232.N0719.N1015.d010078 location omega * _root_.GD.N0232.N0719.N1015.d010079 triangle omega)
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales := by
          apply integral_congr_ae
          filter_upwards [] with omega
          exact _root_.GD.N0232.N0719.N0837.d010742
            k sizes hk hsizes triangle shift location dilation hdilation omega
    _ = dilation ^ 2 *
        ∫ omega, _root_.GD.N0232.N0719.N1015.d010078 location omega * _root_.GD.N0232.N0719.N1015.d010079 triangle omega
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales := by
      rw [integral_const_mul]



theorem d010744
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk3 : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (dilation : ℝ) (hdilation : dilation ≠ 0)
    (scales : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 (fun i ↦ dilation * scales i) =
      dilation ^ 2 * _root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales := by
  have hk : 0 < k := by omega
  have hsizes0 : ∀ i, 0 < sizes i := fun i ↦
    lt_of_lt_of_le (by norm_num : 0 < 2) (hsizes i)
  simpa [_root_.GD.N0232.N0719.N1024.d010712, _root_.GD.N0232.N0719.N1024.d010711] using
    (_root_.GD.N0232.N0719.N0837.d010743 k sizes hk hsizes0 (_root_.GD.N0232.N0719.N1024.d010710 hk3)
      0 0 dilation hdilation scales)

end

end N0837
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0837.d010742
#print axioms _root_.GD.N0232.N0719.N0837.d010743
#print axioms _root_.GD.N0232.N0719.N0837.d010744
