import GD.Module0034
import GD.Module1003























open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1170

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1174
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0658


def d015973
    (f : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ :=
  f z.1 - f z.2




def d015974
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (f g : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  (∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
      _root_.GD.N0232.N0720.N1174.d015960 rho x z *
        (_root_.GD.N0232.N0720.N1170.d015973 f z * _root_.GD.N0232.N0720.N1170.d015973 g z) ∂
        (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)) /
    (2 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x)




def d015975
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (f : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  (∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
      _root_.GD.N0232.N0720.N1174.d015960 rho x z * _root_.GD.N0232.N0720.N1170.d015973 f z ^ 2 ∂
        (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)) /
    (2 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x)



def d015976
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (f g : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1170.d015975 rho f x *
      _root_.GD.N0232.N0720.N1170.d015975 rho g x -
    _root_.GD.N0232.N0720.N1170.d015974 rho f g x ^ 2




theorem d015977
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1170.d015974 rho _root_.GD.N0232.N0720.N1173.d015938 weight x =
      _root_.GD.N0232.N0720.N1173.d015946 rho weight x /
        (2 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x) := by
  unfold _root_.GD.N0232.N0720.N1170.d015974
    _root_.GD.N0232.N0720.N1173.d015946 _root_.GD.N0232.N0720.N1174.d015960
    _root_.GD.N0232.N0720.N1170.d015973
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  ring






theorem d015978
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hfullMoment : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * _root_.GD.N0232.N0720.N1173.d015938 theta)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hcutoff : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * weight theta)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hcutoffMoment : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x *
        (_root_.GD.N0232.N0720.N1173.d015938 theta * weight theta))
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hfullEvidence : _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ≠ 0) :
    _root_.GD.N0232.N0720.N1173.d015945 rho weight x =
      _root_.GD.N0232.N0720.N1170.d015974 rho _root_.GD.N0232.N0720.N1173.d015938 weight x := by
  rw [_root_.GD.N0232.N0720.N1170.d015977]
  exact _root_.GD.N0232.N0720.N1173.d015953
    rho weight x hfull hfullMoment hcutoff hcutoffMoment hfullEvidence




theorem d015979
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hfullMoment : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * _root_.GD.N0232.N0720.N1173.d015938 theta)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hcutoff : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * weight theta)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hcutoffMoment : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x *
        (_root_.GD.N0232.N0720.N1173.d015938 theta * weight theta))
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hfullEvidence : _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ≠ 0)
    (hcutoffEvidence : _root_.GD.N0232.N0720.N1173.d015940 rho weight x ≠ 0) :
    _root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1173.d015939 weight)
          (_root_.GD.N0232.N0720.N1173.d015944 rho) (_root_.GD.N0232.N0720.N1173.d015943 rho weight) x =
      _root_.GD.N0232.N0720.N1170.d015974 rho _root_.GD.N0232.N0720.N1173.d015938 weight x ^ 2 /
        _root_.GD.N0232.N0720.N1173.d015940 rho weight x := by
  have hw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho) := by
    simpa only [_root_.GD.N0232.N0720.N1173.d015939] using hcutoff
  have htw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho) := by
    simpa only [_root_.GD.N0232.N0720.N1173.d015939, mul_assoc, mul_left_comm, mul_comm] using
      hcutoffMoment
  rw [_root_.GD.N0232.N0720.N1173.d015955
    rho weight x hw htw hcutoffEvidence]
  rw [_root_.GD.N0232.N0720.N1170.d015978
    rho weight x hfull hfullMoment hcutoff hcutoffMoment hfullEvidence]





theorem d015980
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (f g : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfSq : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z * _root_.GD.N0232.N0720.N1170.d015973 f z ^ 2)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hfg : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z *
          (_root_.GD.N0232.N0720.N1170.d015973 f z * _root_.GD.N0232.N0720.N1170.d015973 g z))
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hgSq : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z * _root_.GD.N0232.N0720.N1170.d015973 g z ^ 2)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hfullEvidence : 0 < _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x) :
    _root_.GD.N0232.N0720.N1170.d015974 rho f g x ^ 2 ≤
      _root_.GD.N0232.N0720.N1170.d015975 rho f x *
        _root_.GD.N0232.N0720.N1170.d015975 rho g x := by
  let pairMeasure :=
    (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)
  let density : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 → ℝ :=
    fun z ↦ _root_.GD.N0232.N0720.N1174.d015960 rho x z
  let df : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 → ℝ := _root_.GD.N0232.N0720.N1170.d015973 f
  let dg : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 → ℝ := _root_.GD.N0232.N0720.N1170.d015973 g
  let M : ℝ := _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x
  let A : ℝ := ∫ z, density z * df z ^ 2 ∂pairMeasure
  let B : ℝ := ∫ z, density z * dg z ^ 2 ∂pairMeasure
  let C : ℝ := ∫ z, density z * (df z * dg z) ∂pairMeasure
  have hdensity : 0 ≤ᵐ[pairMeasure] density := by
    filter_upwards [] with z
    exact mul_nonneg
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.1) x)
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.2) x)
  have hcs := _root_.GD.N0230.N0658.d000405
    pairMeasure density df dg hdensity hfSq hfg hgSq
  change C ^ 2 ≤ A * B at hcs
  change (C / (2 * M)) ^ 2 ≤
    (A / (2 * M)) * (B / (2 * M))
  have hden : 0 < (2 * M) ^ 2 := by
    exact sq_pos_of_pos (mul_pos (by norm_num) hfullEvidence)
  calc
    (C / (2 * M)) ^ 2 = C ^ 2 / (2 * M) ^ 2 := by rw [div_pow]
    _ ≤ (A * B) / (2 * M) ^ 2 :=
      (div_le_div_iff_of_pos_right hden).2 hcs
    _ = (A / (2 * M)) * (B / (2 * M)) := by
      field_simp [ne_of_gt hfullEvidence]




theorem d015981
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (f g : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfSq : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z * _root_.GD.N0232.N0720.N1170.d015973 f z ^ 2)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hfg : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z *
          (_root_.GD.N0232.N0720.N1170.d015973 f z * _root_.GD.N0232.N0720.N1170.d015973 g z))
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hgSq : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z * _root_.GD.N0232.N0720.N1170.d015973 g z ^ 2)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hfullEvidence : 0 < _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x) :
    0 ≤ _root_.GD.N0232.N0720.N1170.d015976 rho f g x := by
  exact sub_nonneg.mpr
    (_root_.GD.N0232.N0720.N1170.d015980
      rho f g x hfSq hfg hgSq hfullEvidence)

end

end N1170
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1170.d015978
#print axioms _root_.GD.N0232.N0720.N1170.d015979
#print axioms _root_.GD.N0232.N0720.N1170.d015980
#print axioms _root_.GD.N0232.N0720.N1170.d015981
