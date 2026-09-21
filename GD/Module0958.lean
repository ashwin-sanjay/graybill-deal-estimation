import GD.Module0957
import GD.Module0924
import Mathlib.MeasureTheory.Measure.SeparableMeasure



























open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1071

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1070
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1165
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1092
open _root_.GD.N0107
open _root_.GD.N0137
open _root_.GD.N0141
open _root_.GD.N0230.N0567
open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0640
open _root_.GD.N0230.N0646
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0718
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)





theorem d015027
    (p q : _root_.GD.N0232.N0720.N1025.d014302 m n) :
    _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0230.N0718.d001528 p q) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0230.N0718.d001528 (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014265 m n q) := by
  filter_upwards [
      _root_.GD.N0232.N0720.N1214.d014267 m n (_root_.GD.N0230.N0718.d001528 p q),
      _root_.GD.N0232.N0720.N1214.d014267 m n p,
      _root_.GD.N0232.N0720.N1214.d014267 m n q,
      Lp.coeFn_add ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q),
      Lp.coeFn_smul (1 / 2 : ℝ) p,
      Lp.coeFn_smul (1 / 2 : ℝ) q] with
      omega hmid hp hq hadd hsmulP hsmulQ
  rw [hmid]
  simp only [_root_.GD.N0230.N0718.d001528, hadd, hsmulP, hsmulQ, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, hp, hq]




theorem d015028
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p q : _root_.GD.N0232.N0720.N1025.d014302 m n) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0230.N0718.d001528 p q))
      =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0230.N0718.d001528
          (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
          (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n q)) := by
  let eta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  have hmidReference := _root_.GD.N0232.N0720.N1071.d015027 m n p q
  have hmidEta :
      _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0230.N0718.d001528 p q) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n eta]
        _root_.GD.N0230.N0718.d001528 (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014265 m n q) :=
    (_root_.GD.N0232.N0720.N1080.d014173 m n eta).ae_eq hmidReference
  have hqmp : Measure.QuasiMeasurePreserving
      (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g⁻¹ • omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n eta) := by
    refine ⟨?_, ?_⟩
    · simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
        (_root_.GD.N0107.d009026
          m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239)
    · have hmap :
          (_root_.GD.N0232.N0720.N1080.d014172 m n).map (fun omega ↦ g⁻¹ • omega) =
            _root_.GD.N0232.N0720.N1080.d014171 m n eta := by
        simpa only [_root_.GD.N0232.N0720.N1080.d014172, eta,
          _root_.GD.N0232.N0720.N1214.d014259] using
          (_root_.GD.N0232.N0720.N1215.d014282 m n g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
      exact hmap ▸ Measure.AbsolutelyContinuous.rfl
  have hpull := hqmp.ae_eq_comp hmidEta
  filter_upwards [hpull] with omega homega
  have homega' :
      _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0230.N0718.d001528 p q) (g⁻¹ • omega) =
        _root_.GD.N0230.N0718.d001528 (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014265 m n q)
          (g⁻¹ • omega) := by
    simpa only [Function.comp_apply] using homega
  unfold _root_.GD.N0232.N0720.N1214.d014261
  rw [homega']
  simp only [_root_.GD.N0230.N0718.d001528, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    _root_.GD.N0232.N0719.N0946.d009229.d009244]
  ring




theorem d015029
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    {p q : _root_.GD.N0232.N0720.N1025.d014302 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g (_root_.GD.N0230.N0718.d001528 p q)
        (_root_.GD.N0232.N0720.N1080.d014189 m n hm hn hp hq
          (by norm_num) (by norm_num) (by norm_num)) =
      _root_.GD.N0230.N0718.d001528
        (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp)
        (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g q hq) := by
  let hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0232.N0720.N1080.d014189 m n hm hn hp hq
      (by norm_num) (by norm_num) (by norm_num)
  let fp := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)
  let fq := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n q)
  let fmid := _root_.GD.N0232.N0720.N1214.d014261 m n g
    (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0230.N0718.d001528 p q))
  let hpLp : MemLp fp 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p hp
  let hqLp : MemLp fq 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g q hq
  let hmidLp : MemLp fmid 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g (_root_.GD.N0230.N0718.d001528 p q) hmid
  let hsumLp : MemLp
      (_root_.GD.N0230.N0718.d001528 fp fq) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (hpLp.const_smul (1 / 2 : ℝ)).add
      (hqLp.const_smul (1 / 2 : ℝ))
  have hraw : fmid =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0230.N0718.d001528 fp fq := by
    simpa only [fmid, fp, fq] using
      _root_.GD.N0232.N0720.N1071.d015028 m n g p q
  change MemLp.toLp fmid hmidLp =
    _root_.GD.N0230.N0718.d001528 (MemLp.toLp fp hpLp) (MemLp.toLp fq hqLp)
  calc
    MemLp.toLp fmid hmidLp =
        MemLp.toLp (_root_.GD.N0230.N0718.d001528 fp fq) hsumLp :=
      MemLp.toLp_congr hmidLp hsumLp hraw
    _ = MemLp.toLp ((1 / 2 : ℝ) • fp) (hpLp.const_smul (1 / 2 : ℝ)) +
          MemLp.toLp ((1 / 2 : ℝ) • fq) (hqLp.const_smul (1 / 2 : ℝ)) :=
      MemLp.toLp_add
        (hpLp.const_smul (1 / 2 : ℝ))
        (hqLp.const_smul (1 / 2 : ℝ))
    _ = (1 / 2 : ℝ) • MemLp.toLp fp hpLp +
          (1 / 2 : ℝ) • MemLp.toLp fq hqLp := by
      rw [MemLp.toLp_const_smul, MemLp.toLp_const_smul]
    _ = _root_.GD.N0230.N0718.d001528 (MemLp.toLp fp hpLp) (MemLp.toLp fq hqLp) := rfl


theorem d015030
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g
      ⟨_root_.GD.N0230.N0718.d001528 p.1 q.1,
        _root_.GD.N0232.N0720.N1025.d014312 m n hm hn p.2 q.2
          (by norm_num) (by norm_num) (by norm_num)⟩).1 =
      _root_.GD.N0230.N0718.d001528
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q).1 := by
  apply (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm.injective
  rw [_root_.GD.N0232.N0720.N1066.d014337 m n hm hn]
  simp only [_root_.GD.N0232.N0720.N1025.d014317, _root_.GD.N0232.N0720.N1025.d014309,
    _root_.GD.N0232.N0720.N1025.d014308, Equiv.apply_symm_apply]
  exact _root_.GD.N0232.N0720.N1071.d015029 m n hm hn g
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).2
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2



theorem d015031
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    (_root_.GD.N0232.N0720.N1067.d014417 m n hm hn theta p q).1 =
      _root_.GD.N0230.N0718.d001528
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1 := by
  exact _root_.GD.N0232.N0720.N1071.d015030 m n hm hn
    (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹ p q





theorem d015032
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1067.d014418 m n hm hn theta p q =
      (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n)
          (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1067.d014402 theta)) 0
          (_root_.GD.N0230.N0670.d001646
            ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
              (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1)
            ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
              (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1)) /
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)).toReal := by
  let P := _root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p
  let Q := _root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q
  have hmid : _root_.GD.N0230.N0718.d001528 P.1 Q.1 ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1025.d014312 m n hm hn P.2 Q.2
      (by norm_num) (by norm_num) (by norm_num)
  have htax :
      _root_.GD.N0232.N0720.N1067.d014418 m n hm hn theta p q =
        _root_.GD.N0232.N0720.N1070.d014386 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta) P.1 Q.1 := by
    unfold _root_.GD.N0232.N0720.N1067.d014418 _root_.GD.N0232.N0720.N1070.d014386 _root_.GD.N0230.N0567.d001641
    rw [_root_.GD.N0230.N0567.d001633
        (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) (_root_.GD.N0232.N0720.N1067.d014402 theta) P.2,
      _root_.GD.N0230.N0567.d001633
        (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) (_root_.GD.N0232.N0720.N1067.d014402 theta) Q.2,
      _root_.GD.N0230.N0567.d001633
        (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) (_root_.GD.N0232.N0720.N1067.d014402 theta) hmid]
    change
      (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta) P.1 +
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta) Q.1) / 2 -
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)
            (_root_.GD.N0232.N0720.N1067.d014417 m n hm hn theta p q).1 =
        (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta) P.1 +
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta) Q.1) / 2 -
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)
            (_root_.GD.N0230.N0718.d001528 P.1 Q.1)
    rw [_root_.GD.N0232.N0720.N1071.d015031 m n hm hn theta p q]
  rw [htax]
  exact _root_.GD.N0232.N0720.N1070.d014387
    m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta) P.2 Q.2



theorem d015033
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1067.d014418 m n hm hn theta p q =
      (_root_.GD.N0230.N0640.d000272
          (_root_.GD.N0232.N0720.N1080.d014172 m n)
          (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1067.d014402 theta))
          (_root_.GD.N0230.N0670.d001646
            ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
              (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1)
            ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
              (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1)) /
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)).toReal := by
  rw [_root_.GD.N0232.N0720.N1071.d015032
    m n hm hn theta p q]
  rw [_root_.GD.N0232.N0720.N1165.d015021]



theorem d015034
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    (_root_.GD.N0230.N0640.d000272
        (_root_.GD.N0232.N0720.N1080.d014172 m n)
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1067.d014402 theta))
        (_root_.GD.N0230.N0670.d001646
          ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
            (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1)
          ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
            (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1))).toReal =
      (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)).toReal *
        _root_.GD.N0232.N0720.N1067.d014418 m n hm hn theta p q := by
  have h := _root_.GD.N0232.N0720.N1071.d015033
    m n hm hn theta p q
  rw [ENNReal.toReal_div] at h
  have hcap : 0 <
      (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)).toReal :=
    ENNReal.toReal_pos
      (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta))
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta))
  rw [h]
  field_simp [hcap.ne']





theorem d015035
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0230.N0640.d000272
        (_root_.GD.N0232.N0720.N1080.d014172 m n)
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1067.d014402 theta))
        (_root_.GD.N0230.N0670.d001646
          ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
            (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1)
          ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
            (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1)) ≠ ⊤ := by
  let P := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
    (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1
  let Q := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
    (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1
  have hPmem : P ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn _).1
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).2
  have hQmem : Q ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn _).1
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).2
  have hdomFinite :
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1067.d014402 theta) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)]
    exact ENNReal.ofReal_ne_top
  have hPFinite : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1067.d014402 theta) P ≠ ⊤ :=
    ne_top_of_le_ne_top hdomFinite (hPmem (_root_.GD.N0232.N0720.N1067.d014402 theta))
  have hQFinite : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1067.d014402 theta) Q ≠ ⊤ :=
    ne_top_of_le_ne_top hdomFinite (hQmem (_root_.GD.N0232.N0720.N1067.d014402 theta))
  rw [_root_.GD.N0232.N0720.N1165.d015021]
  have hidentity := _root_.GD.N0230.N0670.d001647
    (_root_.GD.N0232.N0720.N1080.d014173 m n (_root_.GD.N0232.N0720.N1067.d014402 theta))
    (_root_.GD.N0232.N0720.N1067.d014402 theta).location P Q
  have hle :
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n)
          (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1067.d014402 theta)) 0 (_root_.GD.N0230.N0670.d001646 P Q) ≤
        ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1067.d014402 theta) P +
          ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1067.d014402 theta) Q := by
    change
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n)
          (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1067.d014402 theta)) 0 (_root_.GD.N0230.N0670.d001646 P Q) ≤
        ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n)
              (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1067.d014402 theta))
              (_root_.GD.N0232.N0720.N1067.d014402 theta).location P +
          ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n)
              (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1067.d014402 theta))
              (_root_.GD.N0232.N0720.N1067.d014402 theta).location Q
    rw [← hidentity]
    exact le_add_left le_rfl
  apply ne_top_of_le_ne_top _ hle
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPFinite,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQFinite⟩




theorem d015036
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    ‖_root_.GD.N0230.N0670.d001646
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
          (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
          (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1)‖ ≤
      _root_.GD.N0232.N0720.N1080.d014248 m n hm hn := by
  let P := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
    (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1
  let Q := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
    (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1
  have hPmem : P ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn _).1
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).2
  have hQmem : Q ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn _).1
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).2
  have hP := _root_.GD.N0232.N0720.N1080.d014250
    m n hm hn P hPmem
  have hQ := _root_.GD.N0232.N0720.N1080.d014250
    m n hm hn Q hQmem
  change ‖_root_.GD.N0230.N0670.d001646 P Q‖ ≤ _root_.GD.N0232.N0720.N1080.d014248 m n hm hn
  calc
    ‖_root_.GD.N0230.N0670.d001646 P Q‖ = (1 / 2 : ℝ) * ‖P - Q‖ := by
      unfold _root_.GD.N0230.N0670.d001646
      rw [norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖P‖ + ‖Q‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le P Q) (by norm_num)
    _ ≤ _root_.GD.N0232.N0720.N1080.d014248 m n hm hn := by linarith



theorem d015037
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    ‖(toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1‖ ≤
      _root_.GD.N0232.N0720.N1080.d014248 m n hm hn := by
  let P := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
    (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1
  have hPmem : P ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn _).1
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).2
  exact _root_.GD.N0232.N0720.N1080.d014250
    m n hm hn P hPmem





theorem d015038
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168)
    (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    ∃ extraction : ℕ → ℕ,
      Tendsto extraction atTop atTop ∧
      ∃ pLimit qLimit : _root_.GD.N0232.N0720.N1025.d014302 m n,
        _root_.GD.N0230.N0646.d000537
          (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
            (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn
              (thetaSeq (extraction j)) p).1)
          pLimit ∧
        _root_.GD.N0230.N0646.d000537
          (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
            (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn
              (thetaSeq (extraction j)) q).1)
          qLimit := by
  let pSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014302 m n := fun j ↦
    (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) p).1
  let qSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014302 m n := fun j ↦
    (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) q).1
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  letI : MeasurableSpace.CountablyGenerated (_root_.GD.N0232.N0720.N1080.d014170 m n) := by
    infer_instance
  letI : SFinite (_root_.GD.N0232.N0720.N1080.d014172 m n) := inferInstance
  letI : IsSeparable (_root_.GD.N0232.N0720.N1080.d014172 m n) := inferInstance
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  letI : SecondCountableTopology (_root_.GD.N0232.N0720.N1025.d014302 m n) := inferInstance
  letI : TopologicalSpace.SeparableSpace (_root_.GD.N0232.N0720.N1025.d014302 m n) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  have hpBounded : Bornology.IsBounded (Set.range pSeq) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨_root_.GD.N0232.N0720.N1080.d014248 m n hm hn, ?_⟩
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    exact _root_.GD.N0232.N0720.N1071.d015037
      m n hm hn (thetaSeq j) p
  obtain ⟨k, hk, pLimit, hpweak⟩ :=
    _root_.GD.N0230.N0646.d000550
      (E := _root_.GD.N0232.N0720.N1025.d014302 m n) pSeq hpBounded
  have hqBounded : Bornology.IsBounded
      (Set.range (fun j ↦ qSeq (k j))) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨_root_.GD.N0232.N0720.N1080.d014248 m n hm hn, ?_⟩
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    exact _root_.GD.N0232.N0720.N1071.d015037
      m n hm hn (thetaSeq (k j)) q
  obtain ⟨l, hl, qLimit, hqweak⟩ :=
    _root_.GD.N0230.N0646.d000550
      (E := _root_.GD.N0232.N0720.N1025.d014302 m n) (fun j ↦ qSeq (k j)) hqBounded
  have hpweak' : _root_.GD.N0230.N0646.d000537 (fun j ↦ pSeq (k (l j))) pLimit := by
    intro z
    exact (hpweak z).comp hl
  refine ⟨fun j ↦ k (l j), hk.comp hl, pLimit, qLimit, ?_, ?_⟩
  · simpa only [pSeq] using hpweak'
  · simpa only [qSeq] using hqweak













theorem d015039
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ)
    (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfraction : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) atTop (nhds t))
    (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (htax : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014418 m n hm hn (thetaSeq j) p q)
      atTop (nhds 0))
    (hcapBound : ∃ C : ℝ, ∀ j,
      (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))).toReal ≤ C)
    (pLimit qLimit : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hpweak : _root_.GD.N0230.N0646.d000537
      (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) p).1)
      pLimit)
    (hqweak : _root_.GD.N0230.N0646.d000537
      (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) q).1)
      qLimit) :
    pLimit = qLimit := by
  let energy : ℕ → ENNReal := fun j ↦
    _root_.GD.N0230.N0640.d000272
      (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j)))
      (_root_.GD.N0230.N0670.d001646
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
          (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) p).1)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
          (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) q).1))
  have henergyReal : Tendsto (fun j ↦ (energy j).toReal)
      atTop (nhds 0) := by
    obtain ⟨C, hC⟩ := hcapBound
    have htaxNonnegative : ∀ j,
        0 ≤ _root_.GD.N0232.N0720.N1067.d014418 m n hm hn (thetaSeq j) p q := by
      intro j
      rw [_root_.GD.N0232.N0720.N1071.d015033
        m n hm hn (thetaSeq j) p q]
      exact ENNReal.toReal_nonneg
    refine squeeze_zero'
      (g := fun j ↦ C *
        _root_.GD.N0232.N0720.N1067.d014418 m n hm hn (thetaSeq j) p q)
      (Filter.Eventually.of_forall fun j ↦ ?_)
      (Filter.Eventually.of_forall fun j ↦ ?_) ?_
    · dsimp only [energy]
      rw [_root_.GD.N0232.N0720.N1071.d015034
          m n hm hn (thetaSeq j) p q]
      exact mul_nonneg ENNReal.toReal_nonneg (htaxNonnegative j)
    · dsimp only [energy]
      rw [_root_.GD.N0232.N0720.N1071.d015034
          m n hm hn (thetaSeq j) p q]
      exact mul_le_mul_of_nonneg_right (hC j) (htaxNonnegative j)
    · simpa only [mul_zero] using htax.const_mul C
  have henergyFinite : ∀ j, energy j ≠ ⊤ := by
    intro j
    simpa only [energy] using
      _root_.GD.N0232.N0720.N1071.d015035 m n hm hn (thetaSeq j) p q
  have henergy : Tendsto energy atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff henergyFinite).1 henergyReal
  have hbounded : ∃ C : ℝ, ∀ j,
      ‖_root_.GD.N0230.N0670.d001646
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
          (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) p).1)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
          (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) q).1)‖ ≤ C :=
    ⟨_root_.GD.N0232.N0720.N1080.d014248 m n hm hn, fun j ↦
      _root_.GD.N0232.N0720.N1071.d015036
        m n hm hn (thetaSeq j) p q⟩
  exact _root_.GD.N0232.N0720.N1165.d015026
    m n hm hn thetaSeq t ht₀ ht₁ hfraction
    (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) p).1)
    (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) q).1)
    pLimit qLimit hpweak hqweak hbounded henergy




theorem d015040
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ)
    (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfraction : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) atTop (nhds t))
    (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (htax : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014418 m n hm hn (thetaSeq j) p q)
      atTop (nhds 0))
    (pLimit qLimit : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hpweak : _root_.GD.N0230.N0646.d000537
      (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) p).1)
      pLimit)
    (hqweak : _root_.GD.N0230.N0646.d000537
      (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn (thetaSeq j) q).1)
      qLimit) :
    pLimit = qLimit := by
  exact _root_.GD.N0232.N0720.N1071.d015039
    m n hm hn thetaSeq t ht₀ ht₁ hfraction p q htax
    (_root_.GD.N0232.N0720.N1071.d014429 m n hm hn thetaSeq)
    pLimit qLimit hpweak hqweak











theorem d015041
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ)
    (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfraction : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) atTop (nhds t))
    (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (htax : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014418 m n hm hn (thetaSeq j) p q)
      atTop (nhds 0)) :
    ∃ extraction : ℕ → ℕ,
      Tendsto extraction atTop atTop ∧
      ∃ r : _root_.GD.N0232.N0720.N1025.d014302 m n,
        _root_.GD.N0230.N0646.d000537
          (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
            (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn
              (thetaSeq (extraction j)) p).1) r ∧
        _root_.GD.N0230.N0646.d000537
          (fun j ↦ (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
            (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn
              (thetaSeq (extraction j)) q).1) r := by
  obtain ⟨extraction, hextraction, pLimit, qLimit, hpweak, hqweak⟩ :=
    _root_.GD.N0232.N0720.N1071.d015038
      m n hm hn thetaSeq p q
  have hfraction' : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq (extraction j))))
      atTop (nhds t) := hfraction.comp hextraction
  have htax' : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014418 m n hm hn
        (thetaSeq (extraction j)) p q)
      atTop (nhds 0) := htax.comp hextraction
  have hlimits : pLimit = qLimit :=
    _root_.GD.N0232.N0720.N1071.d015040
      m n hm hn (fun j ↦ thetaSeq (extraction j)) t ht₀ ht₁
      hfraction' p q htax' pLimit qLimit hpweak hqweak
  refine ⟨extraction, hextraction, qLimit, ?_, hqweak⟩
  simpa only [hlimits] using hpweak

end

end N1071
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1071.d015029
#print axioms _root_.GD.N0232.N0720.N1071.d015030
#print axioms _root_.GD.N0232.N0720.N1071.d014431
#print axioms _root_.GD.N0232.N0720.N1071.d014428
#print axioms _root_.GD.N0232.N0720.N1071.d015033
#print axioms _root_.GD.N0232.N0720.N1071.d015034
#print axioms _root_.GD.N0232.N0720.N1071.d015040
#print axioms _root_.GD.N0232.N0720.N1071.d015041
