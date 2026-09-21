import GD.Module0044
import GD.Module0956
















open Filter MeasureTheory Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1165

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1072
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0639
open _root_.GD.N0230.N0640
open _root_.GD.N0230.N0646
open _root_.GD.N0230.N0670

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



theorem d015021
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (h : _root_.GD.N0232.N0720.N1025.d014302 m n) :
    _root_.GD.N0230.N0640.d000272 (_root_.GD.N0232.N0720.N1080.d014172 m n)
        (_root_.GD.N0232.N0720.N1499.d015001 m n theta) h =
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) 0 h := by
  have hrisk := _root_.GD.N0230.N0591.d000130
    (_root_.GD.N0232.N0720.N1499.d015001 m n theta) 0 h
    (_root_.GD.N0232.N0720.N1499.d015006 m n theta)
    (_root_.GD.N0232.N0720.N1499.d015002 m n theta)
    (_root_.GD.N0232.N0720.N1499.d015003 m n theta)
  simpa [_root_.GD.N0230.N0640.d000272, _root_.GD.N0230.N0591.d000126] using hrisk.symm



theorem d015022
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (htheta : Tendsto thetaSeq atTop (nhds theta))
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1499.d015001 m n (thetaSeq j) omega)
      atTop (nhds (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega)) :=
  (_root_.GD.N0232.N0720.N1499.d015007 m n omega).tendsto theta |>.comp htheta



theorem d015023
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ)
    (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfraction : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) atTop (nhds t))
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1499.d015001 m n
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j)) omega)
      atTop
      (nhds (_root_.GD.N0232.N0720.N1499.d015001 m n
        (_root_.GD.N0232.N0720.N1072.d015011 m n hm hn t ht₀ ht₁) omega)) := by
  exact _root_.GD.N0232.N0720.N1165.d015022 m n
    (fun j ↦ _root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))
    (_root_.GD.N0232.N0720.N1072.d015011 m n hm hn t ht₀ ht₁)
    (_root_.GD.N0232.N0720.N1072.d015020
      m n hm hn thetaSeq t ht₀ ht₁ hfraction) omega

include hm hn in






theorem d015024
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ)
    (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfraction : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) atTop (nhds t))
    (hSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014302 m n) (h : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hweak : _root_.GD.N0230.N0646.d000537 hSeq h)
    (hbounded : ∃ C : ℝ, ∀ j, ‖hSeq j‖ ≤ C)
    (henergy : Tendsto
      (fun j ↦ _root_.GD.N0230.N0640.d000272 (_root_.GD.N0232.N0720.N1080.d014172 m n)
        (_root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) (hSeq j))
      atTop (nhds 0)) :
    h = 0 := by
  let thetaLimit := _root_.GD.N0232.N0720.N1072.d015011 m n hm hn t ht₀ ht₁
  let densitySeq : ℕ → _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun j ↦
    _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))
  let density : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
    _root_.GD.N0232.N0720.N1499.d015001 m n thetaLimit
  have hdensitySeq : ∀ j, Measurable (densitySeq j) := fun j ↦
    _root_.GD.N0232.N0720.N1499.d015002 m n _
  have hnonnegSeq : ∀ j omega, 0 ≤ densitySeq j omega := fun j omega ↦
    _root_.GD.N0232.N0720.N1499.d015003 m n _ omega
  have hdensity : Measurable density :=
    _root_.GD.N0232.N0720.N1499.d015002 m n _
  have hnonneg : ∀ omega, 0 ≤ density omega := fun omega ↦
    _root_.GD.N0232.N0720.N1499.d015003 m n _ omega
  have hpositive : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, 0 < density omega :=
    Filter.Eventually.of_forall fun omega ↦
      _root_.GD.N0232.N0720.N1499.d015005 m n _ omega
  have hpointwise : ∀ omega,
      Tendsto (fun j ↦ densitySeq j omega) atTop (nhds (density omega)) := by
    intro omega
    exact _root_.GD.N0232.N0720.N1165.d015023
      m n hm hn thetaSeq t ht₀ ht₁ hfraction omega
  have htests : _root_.GD.N0230.N0639.d000570 (_root_.GD.N0232.N0720.N1080.d014172 m n)
      densitySeq density hdensitySeq hnonnegSeq hdensity hnonneg 1
      (by norm_num) :=
    _root_.GD.N0230.N0639.d000572 (_root_.GD.N0232.N0720.N1080.d014172 m n)
      densitySeq density hdensitySeq hnonnegSeq hdensity hnonneg 1
      (by norm_num) hpointwise
  apply _root_.GD.N0230.N0639.d000573
    (_root_.GD.N0232.N0720.N1080.d014172 m n) densitySeq density hdensitySeq hnonnegSeq
    hdensity hnonneg hpositive hSeq h hweak hbounded 1 (by norm_num)
    htests
  simpa only [densitySeq] using henergy


theorem d015025
    {pSeq qSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014302 m n} {p q : _root_.GD.N0232.N0720.N1025.d014302 m n}
    (hp : _root_.GD.N0230.N0646.d000537 pSeq p) (hq : _root_.GD.N0230.N0646.d000537 qSeq q) :
    _root_.GD.N0230.N0646.d000537
      (fun j ↦ _root_.GD.N0230.N0670.d001646 (pSeq j) (qSeq j))
      (_root_.GD.N0230.N0670.d001646 p q) := by
  intro z
  have hsub := (_root_.GD.N0230.N0646.d000537.d000540 hp hq) z
  have hscaled := hsub.const_mul (1 / 2 : ℝ)
  simpa only [_root_.GD.N0230.N0670.d001646, inner_smul_left, conj_trivial,
    one_div] using hscaled

include hm hn in






theorem d015026
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ)
    (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfraction : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) atTop (nhds t))
    (pSeq qSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014302 m n) (p q : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hpweak : _root_.GD.N0230.N0646.d000537 pSeq p) (hqweak : _root_.GD.N0230.N0646.d000537 qSeq q)
    (hbounded : ∃ C : ℝ, ∀ j,
      ‖_root_.GD.N0230.N0670.d001646 (pSeq j) (qSeq j)‖ ≤ C)
    (henergy : Tendsto
      (fun j ↦ _root_.GD.N0230.N0640.d000272 (_root_.GD.N0232.N0720.N1080.d014172 m n)
        (_root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j)))
        (_root_.GD.N0230.N0670.d001646 (pSeq j) (qSeq j)))
      atTop (nhds 0)) :
    p = q := by
  have hzero : _root_.GD.N0230.N0670.d001646 p q = 0 :=
    _root_.GD.N0232.N0720.N1165.d015024
      m n hm hn thetaSeq t ht₀ ht₁ hfraction
      (fun j ↦ _root_.GD.N0230.N0670.d001646 (pSeq j) (qSeq j))
      (_root_.GD.N0230.N0670.d001646 p q)
      (_root_.GD.N0232.N0720.N1165.d015025 m n hpweak hqweak)
      hbounded henergy
  unfold _root_.GD.N0230.N0670.d001646 at hzero
  have hpq : p - q = 0 :=
    (smul_eq_zero.mp hzero).resolve_left (by norm_num)
  exact sub_eq_zero.mp hpq

end

end N1165
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1165.d015021
#print axioms _root_.GD.N0232.N0720.N1165.d015024
#print axioms _root_.GD.N0232.N0720.N1165.d015026
