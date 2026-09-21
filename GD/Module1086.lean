import GD.Module0932
import GD.Module1026
import GD.Module1084
import GD.Module0822




















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1177

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1490
open _root_.GD.N0232.N0720.N1491
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1497
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0719.N0867
open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0720.N1034
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

private abbrev d017401 : Fin 2 → ℝ :=
  _root_.GD.N0232.N0719.N0954.d009355 (_root_.GD.N0232.N0720.N1034.d012430 2 2)

private abbrev d017402 : ℝ := _root_.GD.N0232.N0720.N1034.d012428 4

private theorem d017403 : ∀ i, 0 < _root_.GD.N0232.N0720.N1177.d017401 i := by
  apply _root_.GD.N0232.N0719.N0954.d009358
  intro i
  fin_cases i <;> norm_num [_root_.GD.N0232.N0720.N1034.d012430]

private theorem d017404 :
    0 < _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0720.N1177.d017401 _root_.GD.N0232.N0720.N1177.d017402 := by
  rw [_root_.GD.N0232.N0720.N1034.d012431
    2 2 (by norm_num) (by norm_num) 4]
  norm_num [_root_.GD.N0232.N0720.N1034.d012429]





theorem d017405
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x =
      _root_.GD.N0232.N0720.N1493.d016110 (_root_.GD.N0232.N0720.N1467.d012542 2 2 x) := by
  unfold _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1173.d015942 _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088
    _root_.GD.N0232.N0720.N1173.d015939
  simp only [mul_one]
  rw [_root_.GD.N0232.N0720.N1490.d016356 x ht,
    _root_.GD.N0232.N0720.N1490.d016355 x ht]
  rfl



def d017406 : _root_.GD.N0232.N0720.N1173.d015936 → ℝ :=
  _root_.GD.N0232.N0720.N1497.d012557 2 2 _root_.GD.N0232.N0720.N1177.d017401 _root_.GD.N0232.N0720.N1177.d017402

@[fun_prop]
theorem d017407 : Measurable _root_.GD.N0232.N0720.N1177.d017406 := by
  exact _root_.GD.N0232.N0720.N1497.d012558 2 2 _root_.GD.N0232.N0720.N1177.d017401 _root_.GD.N0232.N0720.N1177.d017402



theorem d017408
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x = _root_.GD.N0232.N0720.N1177.d017406 x := by
  rw [_root_.GD.N0232.N0720.N1177.d017405 x ht,
    _root_.GD.N0232.N0720.N1493.d016114
      (_root_.GD.N0232.N0720.N1467.d012542 2 2 x) ht]
  unfold _root_.GD.N0232.N0720.N1177.d017406 _root_.GD.N0232.N0720.N1497.d012557
    _root_.GD.N0232.N0719.N0867.d010315
  rw [_root_.GD.N0232.N0719.N0867.d010307
    (hu := by
      change ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i
      exact ht)]
  rfl





theorem d017409 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp (fun x ↦ _root_.GD.N0232.N0720.N1177.d017406 x - theta.location) 2
      (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
  simpa [_root_.GD.N0232.N0720.N1177.d017406, _root_.GD.N0232.N0720.N1080.d014171] using
    _root_.GD.N0232.N0720.N1497.d012560
      2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1177.d017401 _root_.GD.N0232.N0720.N1177.d017402
      _root_.GD.N0232.N0720.N1177.d017403 _root_.GD.N0232.N0720.N1177.d017404 theta.location theta.scale₁ theta.scale₂



theorem d017410 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta,
      ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i := by
  exact (_root_.GD.N0232.N0720.N1080.d014173 2 2 theta).ae_le
    _root_.GD.N0232.N0720.N1491.d017394



theorem d017411 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 theta]
      _root_.GD.N0232.N0720.N1177.d017406 := by
  filter_upwards [_root_.GD.N0232.N0720.N1177.d017410 theta] with x hx
  exact _root_.GD.N0232.N0720.N1177.d017408 x hx


theorem d017412
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1177.d017406 (g • x) = g • _root_.GD.N0232.N0720.N1177.d017406 x := by
  simpa [_root_.GD.N0232.N0720.N1177.d017406,
    _root_.GD.N0232.N0720.N1214.d014259] using
    _root_.GD.N0232.N0720.N1497.d012559
      2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1177.d017401 _root_.GD.N0232.N0720.N1177.d017402 g.shift
      _root_.GD.N0232.N0720.N1177.d017403 _root_.GD.N0232.N0720.N1177.d017404 g.d009240 x




def d017413 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  MemLp.toLp _root_.GD.N0232.N0720.N1177.d017406 (by
    have h := _root_.GD.N0232.N0720.N1177.d017409 _root_.GD.N0232.N0720.N1080.d014169
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using h)



theorem d017414 :
    _root_.GD.N0232.N0720.N1159.d014652 2 2
      _root_.GD.N0232.N0720.N1177.d017413 := by
  let href : MemLp _root_.GD.N0232.N0720.N1177.d017406 2 (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    have h := _root_.GD.N0232.N0720.N1177.d017409 _root_.GD.N0232.N0720.N1080.d014169
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using h
  have hclassReference :
      _root_.GD.N0232.N0720.N1177.d017406 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
        _root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1177.d017413 := by
    have hcoe :
        (fun x ↦ _root_.GD.N0232.N0720.N1177.d017413 x) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
          _root_.GD.N0232.N0720.N1177.d017406 := by
      simpa [_root_.GD.N0232.N0720.N1177.d017413] using href.coeFn_toLp
    exact hcoe.symm.trans
      (_root_.GD.N0232.N0720.N1214.d014267 2 2 _root_.GD.N0232.N0720.N1177.d017413).symm
  refine ⟨_root_.GD.N0232.N0720.N1177.d017406, _root_.GD.N0232.N0720.N1177.d017407, ?_, ?_⟩
  · intro theta
    exact (_root_.GD.N0232.N0720.N1080.d014173 2 2 theta).ae_le hclassReference
  · exact _root_.GD.N0232.N0720.N1177.d017412


theorem d017415 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1177.d017413 =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
          (fun x ↦ _root_.GD.N0232.N0720.N1177.d017406 x - theta.location)) := by
  apply _root_.GD.N0232.N0720.N1080.d014183
    2 2 (_root_.GD.N0232.N0720.N1080.d014173 2 2 theta)
  exact _root_.GD.N0232.N0720.N1177.d017409 theta


theorem d017416 :
    _root_.GD.N0232.N0720.N1159.d014637 2 2 _root_.GD.N0232.N0720.N1177.d017413 := by
  intro theta
  rw [_root_.GD.N0232.N0720.N1177.d017415 theta]
  exact ENNReal.ofReal_ne_top


theorem d017417 :
    _root_.GD.N0232.N0720.N1159.d014638 2 2 _root_.GD.N0232.N0720.N1177.d017413 :=
  _root_.GD.N0232.N0720.N1159.d014653
    2 2 _root_.GD.N0232.N0720.N1177.d017413
      _root_.GD.N0232.N0720.N1177.d017414




def d017418 : _root_.GD.N0232.N0720.N1159.d014639 2 2 where
  value := _root_.GD.N0232.N0720.N1177.d017413
  finiteRisk := _root_.GD.N0232.N0720.N1177.d017416
  riskCharacter := _root_.GD.N0232.N0720.N1177.d017417

@[simp]
theorem d017419 :
    _root_.GD.N0232.N0720.N1177.d017418.value = _root_.GD.N0232.N0720.N1177.d017413 := rfl






def d017420 : Prop :=
  _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) _root_.GD.N0232.N0720.N1177.d017413
    (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num))




def d017421 : Prop :=
  ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
    _root_.GD.N0232.N0720.N1080.d014182 2 2 theta (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) ≤
      _root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1177.d017413




theorem d017422
    (hcounterexample : _root_.GD.N0232.N0720.N1177.d017421) :
    ¬ _root_.GD.N0232.N0720.N1177.d017420 := by
  intro hstrict
  obtain ⟨theta, htheta⟩ := hcounterexample
  exact (not_lt_of_ge htheta) (hstrict theta)



theorem d017423 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
        _root_.GD.N0232.N0720.N1177.d017418.value
        (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) ↔
      _root_.GD.N0232.N0720.N1177.d017420 := by
  rfl



def d017424
    (hstrict : _root_.GD.N0232.N0720.N1177.d017420) :
    _root_.GD.N0232.N0720.N1159.d014639 2 2 :=
  _root_.GD.N0232.N0720.N1159.d014657
    2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1177.d017413
    _root_.GD.N0232.N0720.N1177.d017414 hstrict

@[simp]
theorem d017425
    (hstrict : _root_.GD.N0232.N0720.N1177.d017420) :
    (_root_.GD.N0232.N0720.N1177.d017424 hstrict).value = _root_.GD.N0232.N0720.N1177.d017413 := rfl

end

end N1177
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1177.d017408
#print axioms _root_.GD.N0232.N0720.N1177.d017411
#print axioms _root_.GD.N0232.N0720.N1177.d017416
#print axioms _root_.GD.N0232.N0720.N1177.d017417
#print axioms _root_.GD.N0232.N0720.N1177.d017422
#print axioms _root_.GD.N0232.N0720.N1177.d017423
