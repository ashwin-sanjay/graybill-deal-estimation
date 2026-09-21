import GD.Module0057
import GD.Module0917



























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1081

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0609
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)





noncomputable def d014614 : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
  ⟨_root_.GD.N0232.N0720.N1080.d014191 m n hm hn,
    (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).1⟩






noncomputable def d014615
    (g : _root_.GD.N0232.N0719.N0946.d009229) : ℝ :=
  ‖(_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
      (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1‖ ^ 2 -
    ‖(_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1‖ ^ 2



theorem d014616
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1081.d014615 m n hm hn g =
      (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
          (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
            (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1).toReal -
        (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
          (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1).toReal := by
  rw [_root_.GD.N0232.N0720.N1080.d014190, _root_.GD.N0232.N0720.N1080.d014190]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]
  simp [_root_.GD.N0232.N0720.N1081.d014615]



theorem d014617
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
        (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
          (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1 =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1 := by
  have h := _root_.GD.N0232.N0720.N1215.d014290
    m n hm hn g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1
      (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).2
  simpa [_root_.GD.N0232.N0720.N1215.d014298] using h




theorem d014618
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) d) :
    ‖d - _root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 ≤
      ‖d‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 := by
  simpa only [_root_.GD.N0232.N0720.N1080.d014191, zero_sub, norm_neg] using
    (_root_.GD.N0230.N0609.d000701
      (_root_.GD.N0232.N0720.N1080.d014182 m n) _root_.GD.N0232.N0720.N1080.d014169
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
      (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) d
      (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014188 m n hm hn)
      (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014189 m n hm hn)
      (_root_.GD.N0232.N0720.N1080.d014190 m n) hd)



theorem d014619
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) d) :
    _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) +
        ENNReal.ofReal (‖d - _root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2) ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 d := by
  simpa only [_root_.GD.N0232.N0720.N1080.d014191] using
    (_root_.GD.N0230.N0609.d000702
      (_root_.GD.N0232.N0720.N1080.d014182 m n) _root_.GD.N0232.N0720.N1080.d014169
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
      (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) d
      (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014188 m n hm hn)
      (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014189 m n hm hn)
      (_root_.GD.N0232.N0720.N1080.d014190 m n) hd)




theorem d014620
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
          (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1 +
        ENNReal.ofReal
          (‖(_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
              (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1 -
              (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1‖ ^ 2) ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
        (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
          (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1 := by
  simpa only [_root_.GD.N0232.N0720.N1081.d014614] using
    (_root_.GD.N0232.N0720.N1081.d014619 m n hm hn
      (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
        (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1
      (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
        (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).2)



theorem d014621
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    ‖(_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
        (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1 -
        (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1081.d014615 m n hm hn g := by
  simpa only [_root_.GD.N0232.N0720.N1081.d014614, _root_.GD.N0232.N0720.N1081.d014615] using
    (_root_.GD.N0232.N0720.N1081.d014618 m n hm hn
      (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
        (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1
      (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
        (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).2)


theorem d014622
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    0 ≤ _root_.GD.N0232.N0720.N1081.d014615 m n hm hn g := by
  exact le_trans (sq_nonneg _)
    (_root_.GD.N0232.N0720.N1081.d014621 m n hm hn g)



theorem d014623
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1081.d014615 m n hm hn g = 0 ↔
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
        (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn) =
          _root_.GD.N0232.N0720.N1081.d014614 m n hm hn := by
  constructor
  · intro hzero
    have hsq :
        ‖(_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
            (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1 -
            (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1‖ ^ 2 ≤ 0 := by
      simpa [hzero] using
        _root_.GD.N0232.N0720.N1081.d014621 m n hm hn g
    have hnorm :
        ‖(_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
            (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1 -
            (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1‖ = 0 := by
      nlinarith [norm_nonneg
        ((_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
            (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1 -
          (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn).1)]
    apply Subtype.ext
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro hfixed
    have hvalue := congrArg Subtype.val hfixed
    simp [_root_.GD.N0232.N0720.N1081.d014615, hvalue]






def d014624
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) : Prop :=
  ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
    Measurable repaired ∧
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      repaired =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1214.d014265 m n p.1) ∧
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired







theorem d014625
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    {d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hde : d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] e) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g e := by
  let eta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  have hdeEta : d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n eta] e :=
    (_root_.GD.N0232.N0720.N1080.d014173 m n eta).ae_eq hde
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
  have hpull := hqmp.ae_eq_comp hdeEta
  filter_upwards [hpull] with omega homega
  unfold _root_.GD.N0232.N0720.N1214.d014261
  apply congrArg (fun y : ℝ ↦ g • y)
  simpa only [Function.comp_apply] using homega



theorem d014626
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hrep : _root_.GD.N0232.N0720.N1081.d014624 m n hm hn p) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g p = p := by
  obtain ⟨repaired, _hrepairedMeasurable, hrepairedClass,
    hrepairedEquivariant⟩ := hrep
  intro g
  have hrepairedReference :
      repaired =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n p.1 := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172] using hrepairedClass _root_.GD.N0232.N0720.N1080.d014169
  have htransportCongr :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p.1) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014261 m n g repaired :=
    _root_.GD.N0232.N0720.N1081.d014625 m n g hrepairedReference.symm
  have htransportRepaired : _root_.GD.N0232.N0720.N1214.d014261 m n g repaired = repaired := by
    funext omega
    calc
      _root_.GD.N0232.N0720.N1214.d014261 m n g repaired omega =
          g • repaired (g⁻¹ • omega) := rfl
      _ = repaired (g • (g⁻¹ • omega)) := by
        symm
        exact hrepairedEquivariant g (g⁻¹ • omega)
      _ = repaired omega := by rw [smul_inv_smul]
  have htransportFixed :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p.1) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p.1 := by
    filter_upwards [htransportCongr, hrepairedReference] with omega hcongr hclass
    calc
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p.1) omega =
          _root_.GD.N0232.N0720.N1214.d014261 m n g repaired omega := hcongr
      _ = repaired omega := congrFun htransportRepaired omega
      _ = _root_.GD.N0232.N0720.N1214.d014265 m n p.1 omega := hclass
  apply Subtype.ext
  change
    MemLp.toLp
        (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p.1))
        (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p.1 p.2) = p.1
  calc
    MemLp.toLp
          (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p.1))
          (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p.1 p.2) =
        MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p.1)
          (_root_.GD.N0232.N0720.N1214.d014268 m n p.1) :=
      MemLp.toLp_congr
        (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p.1 p.2)
        (_root_.GD.N0232.N0720.N1214.d014268 m n p.1) htransportFixed
    _ = p.1 := _root_.GD.N0232.N0720.N1214.d014269 m n p.1


theorem d014627
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    (∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g p = p) ↔
      _root_.GD.N0232.N0720.N1081.d014624 m n hm hn p := by
  constructor
  · intro hfixed
    exact
      _root_.GD.N0232.N0720.N1215.d014299
        m n hm hn p hfixed
  · exact _root_.GD.N0232.N0720.N1081.d014626
      m n hm hn p




theorem d014628
    : (∀ g : _root_.GD.N0232.N0719.N0946.d009229,
        _root_.GD.N0232.N0720.N1081.d014615 m n hm hn g = 0) ↔
      _root_.GD.N0232.N0720.N1081.d014624 m n hm hn
        (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn) := by
  constructor
  · intro hzero
    apply
      (_root_.GD.N0232.N0720.N1081.d014627
        m n hm hn (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).1
    intro g
    exact
      (_root_.GD.N0232.N0720.N1081.d014623 m n hm hn g).1
        (hzero g)
  · intro hrep g
    apply (_root_.GD.N0232.N0720.N1081.d014623 m n hm hn g).2
    exact
      (_root_.GD.N0232.N0720.N1081.d014627
        m n hm hn (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)).2 hrep g





theorem
    d014629
    (hzero : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1081.d014615 m n hm hn g = 0) :
    ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable repaired ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired <
          _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      (∀ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
        Measurable d →
        (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
            _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired) →
        ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] repaired) := by
  apply
    _root_.GD.N0232.N0720.N1215.d014300
      m n hm hn (_root_.GD.N0232.N0720.N1081.d014614 m n hm hn)
  · simpa [_root_.GD.N0232.N0720.N1081.d014614] using
      (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).2.1
  · intro g
    exact
      (_root_.GD.N0232.N0720.N1081.d014623 m n hm hn g).1
        (hzero g)

end

end N1081
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1081.d014621
#print axioms _root_.GD.N0232.N0720.N1081.d014623
#print axioms _root_.GD.N0232.N0720.N1081.d014627
#print axioms _root_.GD.N0232.N0720.N1081.d014628
#print axioms _root_.GD.N0232.N0720.N1081.d014629
