import GD.Module1092
import GD.Module1088
import GD.Module0226





















open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1186

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1166
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1190
open _root_.GD.N0232.N0720.N1491
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0233.N0727

abbrev d017584 :=
  _root_.GD.N0232.N0720.N1173.d015933

abbrev d017585 :=
  _root_.GD.N0232.N0720.N1173.d015936






def d017586
    (evidence : _root_.GD.N0232.N0720.N1186.d017585 → ℝ) (x : _root_.GD.N0232.N0720.N1186.d017585) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / evidence x)

theorem d017587
    {evidence : _root_.GD.N0232.N0720.N1186.d017585 → ℝ} (hevidence : Measurable evidence) :
    Measurable (_root_.GD.N0232.N0720.N1186.d017586 evidence) := by
  exact (measurable_const.div hevidence).ennreal_ofReal

theorem d017588
    (evidence : _root_.GD.N0232.N0720.N1186.d017585 → ℝ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0232.N0720.N1186.d017586 evidence x < ∞ := by
  filter_upwards [] with x
  simp [_root_.GD.N0232.N0720.N1186.d017586]


def d017589
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (base : _root_.GD.N0232.N0720.N1186.d017584 → ℝ) : Measure _root_.GD.N0232.N0720.N1186.d017585 :=
  (_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity
    (_root_.GD.N0232.N0720.N1186.d017586 (_root_.GD.N0232.N0720.N1173.d015940 rho base))


abbrev d017590
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (base : _root_.GD.N0232.N0720.N1186.d017584 → ℝ) :=
  Lp ℝ 2 (_root_.GD.N0232.N0720.N1186.d017589 rho base)





def d017591
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1186.d017585 → ℝ)
    (base weight : _root_.GD.N0232.N0720.N1186.d017584 → ℝ)
    (hmem : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 rho candidate weight) 2
      (_root_.GD.N0232.N0720.N1186.d017589 rho base)) :
    _root_.GD.N0232.N0720.N1186.d017590 rho base :=
  hmem.toLp (_root_.GD.N0232.N0720.N1185.d017512 rho candidate weight)

theorem d017592
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1186.d017585 → ℝ)
    (base weight : _root_.GD.N0232.N0720.N1186.d017584 → ℝ)
    (hmem : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 rho candidate weight) 2
      (_root_.GD.N0232.N0720.N1186.d017589 rho base)) :
    (fun x ↦ _root_.GD.N0232.N0720.N1186.d017591 rho candidate base weight hmem x) =ᵐ[
        _root_.GD.N0232.N0720.N1186.d017589 rho base]
      _root_.GD.N0232.N0720.N1185.d017512 rho candidate weight :=
  hmem.coeFn_toLp


def d017593
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1186.d017585 → ℝ)
    (base : _root_.GD.N0232.N0720.N1186.d017584 → ℝ)
    (hbase : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 rho candidate base) 2
      (_root_.GD.N0232.N0720.N1186.d017589 rho base)) :
    _root_.GD.N0232.N0720.N1186.d017590 rho base :=
  -_root_.GD.N0232.N0720.N1186.d017591 rho candidate base base hbase






theorem d017594
    (evidence baseCurrent reservoirCurrent : _root_.GD.N0232.N0720.N1186.d017585 → ℝ)
    (hevidenceMeasurable : Measurable evidence)
    (hevidencePos : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2, 0 < evidence x)
    (hbase : MemLp baseCurrent 2
      ((_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity
        (_root_.GD.N0232.N0720.N1186.d017586 evidence)))
    (hreservoir : MemLp reservoirCurrent 2
      ((_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity
        (_root_.GD.N0232.N0720.N1186.d017586 evidence))) :
    ‖hbase.toLp baseCurrent + hreservoir.toLp reservoirCurrent‖ ^ 2 =
      ∫ x, (baseCurrent x + reservoirCurrent x) ^ 2 / evidence x
        ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
  let weightedLaw : Measure _root_.GD.N0232.N0720.N1186.d017585 :=
    (_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity (_root_.GD.N0232.N0720.N1186.d017586 evidence)
  have hcoe :
      ∀ᵐ x ∂weightedLaw,
        (hbase.toLp baseCurrent + hreservoir.toLp reservoirCurrent) x =
          baseCurrent x + reservoirCurrent x := by
    filter_upwards [Lp.coeFn_add
        (hbase.toLp baseCurrent) (hreservoir.toLp reservoirCurrent),
      hbase.coeFn_toLp, hreservoir.coeFn_toLp] with x hadd hb hr
    rw [hadd, Pi.add_apply, hb, hr]
  have hsq :
      ∀ᵐ x ∂weightedLaw,
        ((hbase.toLp baseCurrent +
            hreservoir.toLp reservoirCurrent) x) ^ 2 =
          (baseCurrent x + reservoirCurrent x) ^ 2 := by
    filter_upwards [hcoe] with x hx
    rw [hx]
  rw [_root_.GD.N0233.N0727.d003206]
  change (∫ x,
      ((hbase.toLp baseCurrent + hreservoir.toLp reservoirCurrent) x) ^ 2
        ∂weightedLaw) = _
  rw [integral_congr_ae hsq]
  unfold weightedLaw
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (_root_.GD.N0232.N0720.N1186.d017587 hevidenceMeasurable).aemeasurable
    (_root_.GD.N0232.N0720.N1186.d017588 evidence)]
  apply integral_congr_ae
  filter_upwards [hevidencePos] with x hx
  unfold _root_.GD.N0232.N0720.N1186.d017586
  rw [ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le)]
  simp only [smul_eq_mul]
  field_simp [hx.ne']



theorem d017595
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1186.d017585 → ℝ)
    (base reservoir : _root_.GD.N0232.N0720.N1186.d017584 → ℝ)
    (hevidenceMeasurable : Measurable (_root_.GD.N0232.N0720.N1173.d015940 rho base))
    (hevidencePos : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho base x)
    (hbase : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 rho candidate base) 2
      (_root_.GD.N0232.N0720.N1186.d017589 rho base))
    (hreservoir : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 rho candidate reservoir) 2
      (_root_.GD.N0232.N0720.N1186.d017589 rho base)) :
    ‖_root_.GD.N0232.N0720.N1186.d017591 rho candidate base base hbase +
        _root_.GD.N0232.N0720.N1186.d017591 rho candidate base reservoir hreservoir‖ ^ 2 =
      _root_.GD.N0232.N0720.N1185.d017521 rho candidate base reservoir := by
  unfold _root_.GD.N0232.N0720.N1186.d017591 _root_.GD.N0232.N0720.N1186.d017589
    _root_.GD.N0232.N0720.N1185.d017521
  exact _root_.GD.N0232.N0720.N1186.d017594
    (_root_.GD.N0232.N0720.N1173.d015940 rho base)
    (_root_.GD.N0232.N0720.N1185.d017512 rho candidate base)
    (_root_.GD.N0232.N0720.N1185.d017512 rho candidate reservoir)
    hevidenceMeasurable hevidencePos hbase hreservoir



theorem d017596
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1186.d017585 → ℝ)
    (base reservoir : _root_.GD.N0232.N0720.N1186.d017584 → ℝ)
    (hevidenceMeasurable : Measurable (_root_.GD.N0232.N0720.N1173.d015940 rho base))
    (hevidencePos : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho base x)
    (hbase : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 rho candidate base) 2
      (_root_.GD.N0232.N0720.N1186.d017589 rho base))
    (hreservoir : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 rho candidate reservoir) 2
      (_root_.GD.N0232.N0720.N1186.d017589 rho base)) :
    ‖_root_.GD.N0232.N0720.N1186.d017591 rho candidate base reservoir hreservoir -
        _root_.GD.N0232.N0720.N1186.d017593 rho candidate base hbase‖ ^ 2 =
      _root_.GD.N0232.N0720.N1185.d017521 rho candidate base reservoir := by
  unfold _root_.GD.N0232.N0720.N1186.d017593
  rw [sub_neg_eq_add, add_comm]
  exact _root_.GD.N0232.N0720.N1186.d017595
    rho candidate base reservoir hevidenceMeasurable hevidencePos
      hbase hreservoir




abbrev d017597 (k : ℕ) : Measure _root_.GD.N0232.N0720.N1186.d017585 :=
  _root_.GD.N0232.N0720.N1186.d017589 _root_.GD.N0232.N0720.N1493.d016104
    (_root_.GD.N0232.N0720.N1166.d017432 k)


abbrev d017598 (k : ℕ) :=
  _root_.GD.N0232.N0720.N1186.d017590 _root_.GD.N0232.N0720.N1493.d016104
    (_root_.GD.N0232.N0720.N1166.d017432 k)

theorem d017599 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1166.d017432 k)) :=
  _root_.GD.N0232.N0720.N1166.d017449 k

theorem d017600 (k : ℕ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1166.d017432 k) x := by
  filter_upwards [_root_.GD.N0232.N0720.N1491.d017394] with x hx
  exact _root_.GD.N0232.N0720.N1166.d017464 k x hx






theorem d017601
    (k : ℕ) (reservoir : _root_.GD.N0232.N0720.N1186.d017584 → ℝ)
    (hbase : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k)) 2
      (_root_.GD.N0232.N0720.N1186.d017597 k))
    (hreservoir : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 reservoir) 2
      (_root_.GD.N0232.N0720.N1186.d017597 k)) :
    ‖_root_.GD.N0232.N0720.N1186.d017591 _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
          (_root_.GD.N0232.N0720.N1166.d017432 k) reservoir hreservoir -
        _root_.GD.N0232.N0720.N1186.d017593 _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
          (_root_.GD.N0232.N0720.N1166.d017432 k) hbase‖ ^ 2 =
      _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) reservoir := by
  exact _root_.GD.N0232.N0720.N1186.d017596
    _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
      (_root_.GD.N0232.N0720.N1166.d017432 k) reservoir
      (_root_.GD.N0232.N0720.N1186.d017599 k)
      (_root_.GD.N0232.N0720.N1186.d017600 k) hbase hreservoir

#print axioms _root_.GD.N0232.N0720.N1186.d017594
#print axioms _root_.GD.N0232.N0720.N1186.d017596
#print axioms _root_.GD.N0232.N0720.N1186.d017601

end
end N1186
end N0720
end N0232
end GD
