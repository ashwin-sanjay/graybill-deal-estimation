import GD.Module1137
import GD.Module1072
















namespace GD
namespace N0232
namespace N0720
namespace N1123

noncomputable section

open MeasureTheory
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1121
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1482





theorem d018312
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate
        (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) = 0 := by
  unfold _root_.GD.N0232.N0720.N1131.d017154 _root_.GD.N0232.N0720.N1130.d017075
  apply integral_eq_zero_of_ae
  filter_upwards [_root_.GD.N0232.N0720.N1126.d016427
    candidate.packet candidate.weight candidate.weight_nonneg] with omega hcoe
  rw [hcoe, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
  rfl



theorem d018313
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hqFinite : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate q = 0 ↔
      _root_.GD.N0232.N0720.N1130.d017075 m n candidate = q := by
  constructor
  · intro htax
    have hle :=
      _root_.GD.N0232.N0720.N1121.d018304
        m n candidate q hqFinite
    have hsq : ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖ ^ 2 = 0 := by
      apply le_antisymm
      · simpa only [htax] using hle
      · exact sq_nonneg _
    have hnorm : ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖ = 0 := by
      nlinarith [norm_nonneg (_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro heq
    rw [← heq]
    exact _root_.GD.N0232.N0720.N1123.d018312
      m n candidate







theorem d018314
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1121.d018305 m n candidate = 0 ↔
      _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) = 0 := by
  let r := _root_.GD.N0232.N0720.N1130.d017075 m n candidate
  constructor
  · intro htax
    have hle :=
      _root_.GD.N0232.N0720.N1121.d018307
        m n candidate
    exact le_antisymm (by simpa only [htax] using hle)
      (_root_.GD.N0232.N0720.N1122.d017963 (m := m) (n := n) r)
  · intro hresidual
    have hscaleFinite : _root_.GD.N0232.N0720.N1159.d014637 m n
        (_root_.GD.N0232.N0720.N1146.d015228 m n r) := by
      have hrFinite : _root_.GD.N0232.N0720.N1159.d014637 m n r := by
        exact _root_.GD.N0232.N0720.N1126.d016428
          candidate.packet candidate.weight candidate.weight_nonneg
      change _root_.GD.N0232.N0720.N1159.d014637 m n
        (_root_.GD.N0232.N0720.N1146.d015212 m n
          (_root_.GD.N0232.N0720.N1146.d015221 m n) r)
      rw [_root_.GD.N0232.N0720.N1146.d015218
        m n (_root_.GD.N0232.N0720.N1146.d015221 m n) r hrFinite]
      exact _root_.GD.N0232.N0720.N1482.d015158 _root_.GD.N0232.N0720.N1482.d015130 r hrFinite
    have hshiftFinite : _root_.GD.N0232.N0720.N1159.d014637 m n
        (_root_.GD.N0232.N0720.N1146.d015229 m n r) := by
      have hrFinite : _root_.GD.N0232.N0720.N1159.d014637 m n r := by
        exact _root_.GD.N0232.N0720.N1126.d016428
          candidate.packet candidate.weight candidate.weight_nonneg
      change _root_.GD.N0232.N0720.N1159.d014637 m n
        (_root_.GD.N0232.N0720.N1146.d015212 m n
          (_root_.GD.N0232.N0720.N1146.d015222 m n) r)
      rw [_root_.GD.N0232.N0720.N1146.d015218
        m n (_root_.GD.N0232.N0720.N1146.d015222 m n) r hrFinite]
      exact _root_.GD.N0232.N0720.N1482.d015158
        _root_.GD.N0232.N0720.N1482.d015131 r hrFinite
    have hscaleSq :
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n r - r‖ ^ 2 = 0 := by
      unfold _root_.GD.N0232.N0720.N1122.d017962 at hresidual
      have hnonneg :
          0 ≤ ‖_root_.GD.N0232.N0720.N1146.d015229 m n r - r‖ ^ 2 :=
        sq_nonneg _
      nlinarith [sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n r - r‖]
    have hshiftSq :
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n r - r‖ ^ 2 = 0 := by
      unfold _root_.GD.N0232.N0720.N1122.d017962 at hresidual
      have hnonneg :
          0 ≤ ‖_root_.GD.N0232.N0720.N1146.d015228 m n r - r‖ ^ 2 :=
        sq_nonneg _
      nlinarith [sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n r - r‖]
    have hscale :
        _root_.GD.N0232.N0720.N1146.d015228 m n r = r := by
      have hnorm :
          ‖_root_.GD.N0232.N0720.N1146.d015228 m n r - r‖ = 0 := by
        nlinarith [norm_nonneg
          (_root_.GD.N0232.N0720.N1146.d015228 m n r - r)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have hshift :
        _root_.GD.N0232.N0720.N1146.d015229 m n r = r := by
      have hnorm :
          ‖_root_.GD.N0232.N0720.N1146.d015229 m n r - r‖ = 0 := by
        nlinarith [norm_nonneg
          (_root_.GD.N0232.N0720.N1146.d015229 m n r - r)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    unfold _root_.GD.N0232.N0720.N1121.d018305
    have hscaleTax :=
      (_root_.GD.N0232.N0720.N1123.d018313
        m n candidate (_root_.GD.N0232.N0720.N1146.d015228 m n r)
          hscaleFinite).2 hscale.symm
    have hshiftTax :=
      (_root_.GD.N0232.N0720.N1123.d018313
        m n candidate (_root_.GD.N0232.N0720.N1146.d015229 m n r)
          hshiftFinite).2 hshift.symm
    rw [hscaleTax, hshiftTax, zero_add]






theorem d018315
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1121.d018305 m n candidate = 0 ↔
      _root_.GD.N0232.N0720.N1146.d015228 m n
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) =
        _root_.GD.N0232.N0720.N1130.d017075 m n candidate ∧
      _root_.GD.N0232.N0720.N1146.d015229 m n
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) =
        _root_.GD.N0232.N0720.N1130.d017075 m n candidate := by
  let r := _root_.GD.N0232.N0720.N1130.d017075 m n candidate
  rw [_root_.GD.N0232.N0720.N1123.d018314]
  change _root_.GD.N0232.N0720.N1122.d017962 m n r = 0 ↔ _
  unfold _root_.GD.N0232.N0720.N1122.d017962
  constructor
  · intro hzero
    have hscaleSq :
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n r - r‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n r - r‖]
    have hshiftSq :
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n r - r‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n r - r‖]
    constructor
    · apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg
        (_root_.GD.N0232.N0720.N1146.d015228 m n r - r)]
    · apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg
        (_root_.GD.N0232.N0720.N1146.d015229 m n r - r)]
  · rintro ⟨hscale, hshift⟩
    rw [hscale, hshift, sub_self, norm_zero]
    norm_num

end

end N1123
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1123.d018313
#print axioms _root_.GD.N0232.N0720.N1123.d018314
#print axioms _root_.GD.N0232.N0720.N1123.d018315
