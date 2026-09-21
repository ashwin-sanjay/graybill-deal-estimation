import GD.Module1094
import GD.Module1097
import GD.Module1099
import GD.Module1059
import GD.Module1058
import Mathlib.Tactic









open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD.N0232.N0720.N1362

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1166
open _root_.GD.N0232.N0720.N1168
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1186
open _root_.GD.N0232.N0720.N1188
open _root_.GD.N0232.N0720.N1190
open _root_.GD.N0232.N0720.N1192
open _root_.GD.N0232.N0720.N1397
open _root_.GD.N0232.N0720.N1405
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1347
open _root_.GD.N0232.N0720.N1348
open _root_.GD.N0232.N0720.N1361
open _root_.GD.N0232.N0720.N1365
open _root_.GD.N0232.N0720.N1367
open _root_.GD.N0232.N0720.N1275
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1485
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0602

noncomputable local instance d017687 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d017688 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩

private noncomputable local instance d017689 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

private noncomputable local instance d017690 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 2 2 _root_.GD.N0232.N0720.N1080.d014169) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance






theorem N1759.d017691
    {Xi Y : Type*}
    [TopologicalSpace Xi] [MeasurableSpace Xi] [OpensMeasurableSpace Xi]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (prior : ℕ → Measure Xi)
    (hfinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (f : Xi → Y) (hf : Continuous f) (hsurj : Function.Surjective f) :
    _root_.GD.N0232.N0720.N1111.d016605 (fun k ↦ (prior k).map f) := by
  intro y U hU
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨V, hVU, hVopen, hfxV⟩ := mem_nhds_iff.mp hU
  have hpre : f ⁻¹' V ∈ nhds x :=
    (hf.isOpen_preimage V hVopen).mem_nhds hfxV
  obtain ⟨a, ha, N, hN⟩ := hretain x (f ⁻¹' V) hpre
  refine ⟨a, ha, N, ?_⟩
  intro k hk
  letI : IsFiniteMeasure (prior k) := hfinite k
  have hmapV : (prior k).map f V = prior k (f ⁻¹' V) := by
    rw [Measure.map_apply hf.measurable hVopen.measurableSet]
  have hmono : (prior k).map f V ≤ (prior k).map f U := measure_mono hVU
  have hmapFinite : IsFiniteMeasure ((prior k).map f) := by infer_instance
  calc
    a ≤ (prior k (f ⁻¹' V)).toReal := hN k hk
    _ = ((prior k).map f V).toReal := by rw [hmapV]
    _ ≤ ((prior k).map f U).toReal :=
      (ENNReal.toReal_le_toReal
        (measure_ne_top ((prior k).map f) V)
        (measure_ne_top ((prior k).map f) U)).2 hmono



def d017692 (k : ℕ) : Measure _root_.GD.N0232.N0720.N1080.d014168 :=
  (_root_.GD.N0232.N0720.N1166.d017433 k).map _root_.GD.N0232.N0720.N1173.d015935

private theorem d017693 : Continuous _root_.GD.N0232.N0720.N1173.d015935 := by
  unfold _root_.GD.N0232.N0720.N1173.d015935
  exact _root_.GD.N0232.N0720.N1486.d015877
    2 2 (by norm_num) (by norm_num)

private theorem d017694 : Measurable _root_.GD.N0232.N0720.N1173.d015935 :=
  _root_.GD.N0232.N0720.N1362.d017693.measurable

noncomputable instance d017695 (k : ℕ) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1362.d017692 k) := by
  unfold _root_.GD.N0232.N0720.N1362.d017692
  infer_instance

theorem d017696 :
    _root_.GD.N0232.N0720.N1111.d016605 _root_.GD.N0232.N0720.N1362.d017692 := by
  exact _root_.GD.N0232.N0720.N1362.N1759.d017691
    _root_.GD.N0232.N0720.N1166.d017433
    (fun k ↦ _root_.GD.N0232.N0720.N1166.d017441 k)
    _root_.GD.N0232.N0720.N1166.d017442
    _root_.GD.N0232.N0720.N1173.d015935
    _root_.GD.N0232.N0720.N1362.d017693
    (_root_.GD.N0232.N0720.N1486.d015893 2 2 (by norm_num) (by norm_num))



private theorem d017697
    (a b : Set.Ioi (0 : ℝ)) : IsCompact (Set.Icc a b) := by
  let lift : Set.Icc (a : ℝ) (b : ℝ) → Set.Ioi (0 : ℝ) :=
    fun x ↦ ⟨x, lt_of_lt_of_le a.property x.property.1⟩
  have hlift : Continuous lift := Continuous.subtype_mk continuous_subtype_val _
  have himage : lift '' Set.univ = Set.Icc a b := by
    ext q
    constructor
    · rintro ⟨x, -, rfl⟩
      exact x.property
    · intro hq
      let x : Set.Icc (a : ℝ) (b : ℝ) := ⟨q, hq⟩
      exact ⟨x, Set.mem_univ x, Subtype.ext rfl⟩
  rw [← himage]
  exact isCompact_univ.image hlift

private theorem d017698
    (a b : Set.Ioo (0 : ℝ) 1) : IsCompact (Set.Icc a b) := by
  let lift : Set.Icc (a : ℝ) (b : ℝ) → Set.Ioo (0 : ℝ) 1 :=
    fun x ↦ ⟨x, lt_of_lt_of_le a.property.1 x.property.1,
      lt_of_le_of_lt x.property.2 b.property.2⟩
  have hlift : Continuous lift := Continuous.subtype_mk continuous_subtype_val _
  have himage : lift '' Set.univ = Set.Icc a b := by
    ext z
    constructor
    · rintro ⟨x, -, rfl⟩
      exact x.property
    · intro hz
      let x : Set.Icc (a : ℝ) (b : ℝ) := ⟨z, hz⟩
      exact ⟨x, Set.mem_univ x, Subtype.ext rfl⟩
  rw [← himage]
  exact isCompact_univ.image hlift

theorem d017699 (k : ℕ) :
    IsCompact (_root_.GD.N0232.N0720.N1485.d017359 k) := by
  unfold _root_.GD.N0232.N0720.N1485.d017359 _root_.GD.N0232.N0720.N1485.d017341 _root_.GD.N0232.N0720.N1485.d017342
    _root_.GD.N0232.N0720.N1485.d017354
  exact isCompact_Icc.prod
    ((_root_.GD.N0232.N0720.N1362.d017697 _ _).prod
      (_root_.GD.N0232.N0720.N1362.d017698 _ _))

private theorem d017700 (k : ℕ) :
    _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1485.d017359 (k + 1)) ≠ ∞ := by
  have hfinite := measure_ne_top (_root_.GD.N0232.N0720.N1166.d017433 k) Set.univ
  rw [_root_.GD.N0232.N0720.N1166.d017439] at hfinite
  simpa [Measure.restrict_apply,
    _root_.GD.N0232.N0720.N1485.d017360] using hfinite




theorem d017701
    (k : ℕ) {f : _root_.GD.N0232.N0720.N1486.d015856 → ℝ} (hf : Continuous f) :
    Integrable f (_root_.GD.N0232.N0720.N1166.d017433 k) := by
  have hon : IntegrableOn f (_root_.GD.N0232.N0720.N1485.d017359 (k + 1))
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) :=
    hf.continuousOn.integrableOn_of_subset_isCompact
      (_root_.GD.N0232.N0720.N1362.d017699 (k + 1))
      (_root_.GD.N0232.N0720.N1485.d017360 (k + 1))
      Subset.rfl (_root_.GD.N0232.N0720.N1362.d017700 k)
  rw [_root_.GD.N0232.N0720.N1166.d017439]
  exact hon



theorem d017702
    (k : ℕ) {f : _root_.GD.N0232.N0720.N1080.d014168 → ℝ} (hf : Continuous f) :
    Integrable f (_root_.GD.N0232.N0720.N1362.d017692 k) := by
  unfold _root_.GD.N0232.N0720.N1362.d017692
  apply (integrable_map_measure hf.aestronglyMeasurable
    (_root_.GD.N0232.N0720.N1486.d015877
      2 2 (by norm_num) (by norm_num)).measurable.aemeasurable).2
  exact _root_.GD.N0232.N0720.N1362.d017701 k
    (hf.comp (_root_.GD.N0232.N0720.N1486.d015877
      2 2 (by norm_num) (by norm_num)))

theorem d017703
    (k : ℕ) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1362.d017692 k) := by
  apply _root_.GD.N0232.N0720.N1362.d017702
  exact _root_.GD.N0232.N0720.N1499.d015007 2 2 omega

theorem d017704
    (k : ℕ) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1362.d017692 k) := by
  apply _root_.GD.N0232.N0720.N1362.d017702
  exact _root_.GD.N0232.N0720.N1499.d014998.mul
    (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)

theorem d017705
    (k : ℕ) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1362.d017692 k) := by
  apply _root_.GD.N0232.N0720.N1362.d017702
  exact _root_.GD.N0232.N0720.N1499.d014998.pow 2 |>.mul
    (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)

theorem d017706
    (k : ℕ) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1276.d016061 theta - _root_.GD.N0232.N0720.N1405.d016086 omega) *
        _root_.GD.N0232.N0720.N1276.d016062 theta omega) (_root_.GD.N0232.N0720.N1362.d017692 k) := by
  apply _root_.GD.N0232.N0720.N1362.d017702
  exact (_root_.GD.N0232.N0720.N1499.d014998.sub continuous_const).mul
    (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)



theorem d017707 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1362.d017692 k)) := by
  exact _root_.GD.N0232.N0720.N1365.d016991 (_root_.GD.N0232.N0720.N1362.d017692 k)

theorem d017708 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1362.d017692 k)
      _root_.GD.N0232.N0720.N1405.d016086) := by
  unfold _root_.GD.N0232.N0720.N1276.d016066
  have hjoint : Measurable (fun z : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1276.d016060 ↦
      (_root_.GD.N0232.N0720.N1276.d016061 z.1 - _root_.GD.N0232.N0720.N1405.d016086 z.2) *
        _root_.GD.N0232.N0720.N1276.d016062 z.1 z.2) := by
    exact ((_root_.GD.N0232.N0720.N1499.d014998.measurable.comp measurable_fst).sub
      (_root_.GD.N0232.N0720.N1365.d016969.comp measurable_snd)).mul
        _root_.GD.N0232.N0720.N1365.d016976
  exact hjoint.stronglyMeasurable.integral_prod_left'.measurable

theorem d017709 (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1166.d017433 k Set.univ := by
  rw [_root_.GD.N0232.N0720.N1166.d017439]
  simpa [Measure.restrict_apply, _root_.GD.N0232.N0720.N1485.d017360] using
    _root_.GD.N0232.N0720.N1166.d017461 k

theorem d017710 (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1362.d017692 k Set.univ := by
  unfold _root_.GD.N0232.N0720.N1362.d017692
  rw [Measure.map_apply
    _root_.GD.N0232.N0720.N1362.d017694 MeasurableSet.univ]
  simpa using _root_.GD.N0232.N0720.N1362.d017709 k

theorem d017711
    (k : ℕ) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    0 < _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1362.d017692 k) omega := by
  have hint := _root_.GD.N0232.N0720.N1362.d017703 k omega
  unfold _root_.GD.N0232.N0720.N1276.d016063 _root_.GD.N0230.N0589.d000088
  apply (integral_pos_iff_support_of_nonneg
    (fun theta ↦ _root_.GD.N0232.N0720.N1499.d015003 2 2 theta omega) hint).2
  have hsupp : Function.support
      (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1499.d015001 2 2 theta omega) =
        Set.univ := by
    ext theta
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (_root_.GD.N0232.N0720.N1499.d015005 2 2 theta omega).ne'
  rw [hsupp]
  exact _root_.GD.N0232.N0720.N1362.d017710 k


theorem d017712 (k : ℕ) :
    ∀ omega : _root_.GD.N0232.N0720.N1276.d016060,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
          (_root_.GD.N0232.N0720.N1362.d017692 k) ∧
      Integrable (fun theta ↦
          _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
          (_root_.GD.N0232.N0720.N1362.d017692 k) ∧
      Integrable (fun theta ↦
          _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
          (_root_.GD.N0232.N0720.N1362.d017692 k) ∧
      _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1362.d017692 k) omega ≠ 0 := by
  intro omega
  exact ⟨_root_.GD.N0232.N0720.N1362.d017703 k omega,
    _root_.GD.N0232.N0720.N1362.d017704 k omega,
    _root_.GD.N0232.N0720.N1362.d017705 k omega,
    (_root_.GD.N0232.N0720.N1362.d017711 k omega).ne'⟩



theorem d017713
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1405.d016086 omega - theta.location =
      _root_.GD.N0107.d012732 2 2 theta.location (1 / 2) omega := by
  unfold _root_.GD.N0232.N0720.N1405.d016086
  rw [_root_.GD.N0232.N0720.N1397.d014817]
  unfold _root_.GD.N0107.d012732 _root_.GD.N0107.d009090
  unfold _root_.GD.N0107.d009084
    _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
    Finset.sum_range_zero, Fintype.card_fin]
  norm_num
  ring



theorem d017714 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1405.d016086 omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
  let e := _root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂
  have hU : MemLp (_root_.GD.N0107.d012732 2 2 theta.location e) 2
      (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
    exact _root_.GD.N0107.d012747 2 2 (by norm_num) (by norm_num)
      theta.location theta.scale₁ theta.scale₂ theta.scale₁_pos theta.scale₂_pos
  have hcarrier := (_root_.GD.N0107.d012748
    2 2 (by norm_num) (by norm_num) theta.location
    theta.scale₁ theta.scale₂ theta.scale₁_pos theta.scale₂_pos
    (fun _ : ℝ × ℝ ↦ 1) measurable_const
    (B := 1) (by norm_num) (by intro p; simp)).2
  have hD : MemLp (_root_.GD.N0107.d009090 2 2) 2 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
    refine (memLp_congr_ae (ae_of_all _ fun omega ↦ ?_)).mp hcarrier
    rw [_root_.GD.N0107.d012724
      2 2 (by norm_num) (by norm_num) theta.location
      theta.scale₁ theta.scale₂ theta.scale₁_pos theta.scale₂_pos omega]
    simp
  have hsum : MemLp (fun omega ↦
      _root_.GD.N0107.d012732 2 2 theta.location e omega +
        (1 / 2 - e) * _root_.GD.N0107.d009090 2 2 omega)
      2 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := hU.add (hD.const_mul (1 / 2 - e))
  refine (memLp_congr_ae (ae_of_all _ fun omega ↦ ?_)).mp hsum
  rw [_root_.GD.N0232.N0720.N1362.d017713]
  unfold _root_.GD.N0107.d012732
  ring


def d017715 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  MemLp.toLp _root_.GD.N0232.N0720.N1405.d016086 (by
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      _root_.GD.N0232.N0720.N1362.d017714 _root_.GD.N0232.N0720.N1080.d014169)

@[simp]
theorem d017716 :
    (fun omega ↦ _root_.GD.N0232.N0720.N1362.d017715 omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1405.d016086 := by
  exact (by
    simpa [_root_.GD.N0232.N0720.N1362.d017715] using
      (show MemLp _root_.GD.N0232.N0720.N1405.d016086 2 (_root_.GD.N0232.N0720.N1080.d014172 2 2) by
        simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
          _root_.GD.N0232.N0720.N1362.d017714 _root_.GD.N0232.N0720.N1080.d014169).coeFn_toLp)

theorem d017717 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715 =
      ENNReal.ofReal (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
        (fun omega ↦ _root_.GD.N0232.N0720.N1405.d016086 omega - theta.location)) := by
  apply _root_.GD.N0232.N0720.N1080.d014183
    2 2 (_root_.GD.N0232.N0720.N1080.d014173 2 2 theta)
  exact _root_.GD.N0232.N0720.N1362.d017714 theta

theorem d017718 :
    _root_.GD.N0232.N0720.N1159.d014637 2 2 _root_.GD.N0232.N0720.N1362.d017715 := by
  intro theta
  rw [_root_.GD.N0232.N0720.N1362.d017717 theta]
  exact ENNReal.ofReal_ne_top

theorem d017719 (k : ℕ) :
    Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715).toReal)
      (_root_.GD.N0232.N0720.N1362.d017692 k) := by
  apply _root_.GD.N0232.N0720.N1362.d017702
  exact _root_.GD.N0232.N0720.N1111.d016606
    2 2 _root_.GD.N0232.N0720.N1362.d017715 _root_.GD.N0232.N0720.N1362.d017718

theorem d017720 (k : ℕ) :
    Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1362.d017715).toReal)
      (_root_.GD.N0232.N0720.N1166.d017433 k) :=
  _root_.GD.N0232.N0720.N1166.d017483
    k _root_.GD.N0232.N0720.N1362.d017715 _root_.GD.N0232.N0720.N1362.d017718



theorem d017721
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715).toReal)
      (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
  have hjoint := _root_.GD.N0232.N0720.N1365.d016990 hN
  have hsections := (integrable_prod_iff
    _root_.GD.N0232.N0720.N1365.d016977.aestronglyMeasurable).1 hjoint
  refine hsections.2.congr (ae_of_all _ fun theta ↦ ?_)
  have hrisk := _root_.GD.N0232.N0720.N1126.d016430
    theta _root_.GD.N0232.N0720.N1362.d017715
      (_root_.GD.N0232.N0720.N1362.d017718 theta)
  change (∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
      ‖_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086 theta omega‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
    (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715).toReal
  rw [hrisk]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1362.d017716] with omega homega
  rw [_root_.GD.N0232.N0720.N1365.d016978, homega]
  rfl



private theorem d017722 :
    _root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1362.d017715 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1405.d016086 :=
  (_root_.GD.N0232.N0720.N1214.d014267 2 2 _root_.GD.N0232.N0720.N1362.d017715).trans
    _root_.GD.N0232.N0720.N1362.d017716

theorem d017723 (k : ℕ) :
    Integrable (fun omega ↦
      _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1405.d016086 (_root_.GD.N0232.N0720.N1166.d017432 k) omega ^ 2 /
        _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1166.d017432 k) omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  have hborel := _root_.GD.N0232.N0720.N1188.d017609
    k _root_.GD.N0232.N0720.N1362.d017715 _root_.GD.N0232.N0720.N1362.d017718
  have hcurrent :
      _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1362.d017715)
            (_root_.GD.N0232.N0720.N1166.d017432 k) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
        _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1405.d016086 (_root_.GD.N0232.N0720.N1166.d017432 k) := by
    filter_upwards [_root_.GD.N0232.N0720.N1362.d017722] with omega homega
    exact _root_.GD.N0232.N0720.N1190.d017539
      _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1166.d017432 k) omega homega
  have hac : _root_.GD.N0232.N0720.N1186.d017597 k ≪ _root_.GD.N0232.N0720.N1080.d014172 2 2 :=
    withDensity_absolutelyContinuous _ _
  have hraw : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1405.d016086 (_root_.GD.N0232.N0720.N1166.d017432 k)) 2
      (_root_.GD.N0232.N0720.N1186.d017597 k) :=
    MemLp.ae_eq (hac.ae_le hcurrent) hborel
  exact _root_.GD.N0232.N0720.N1192.d017641 k _ hraw

theorem d017724
    (k : ℕ) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1362.d017692 k) omega =
      _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1166.d017432 k) omega := by
  unfold _root_.GD.N0232.N0720.N1276.d016063 _root_.GD.N0230.N0589.d000088 _root_.GD.N0232.N0720.N1362.d017692
  change (∫ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1499.d015001 2 2 theta omega ∂
        Measure.map _root_.GD.N0232.N0720.N1173.d015935 (_root_.GD.N0232.N0720.N1166.d017433 k)) = _
  rw [integral_map
    _root_.GD.N0232.N0720.N1362.d017694.aemeasurable
    (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega).aestronglyMeasurable]
  rw [_root_.GD.N0232.N0720.N1166.d017440,
    integral_withDensity_eq_integral_toReal_smul
      ((_root_.GD.N0232.N0720.N1166.d017436 k).pow_const 2).ennreal_ofReal
      (ae_of_all (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104)
        fun _ ↦ ENNReal.ofReal_lt_top)]
  unfold _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088 _root_.GD.N0232.N0720.N1173.d015939 _root_.GD.N0232.N0720.N1173.d015937
  apply integral_congr_ae
  filter_upwards with theta
  rw [ENNReal.toReal_ofReal (sq_nonneg _), _root_.GD.N0232.N0720.N1166.d017435]
  simp only [smul_eq_mul]
  ring

theorem d017725
    (k : ℕ) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1362.d017692 k)
        _root_.GD.N0232.N0720.N1405.d016086 omega =
      _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1405.d016086 (_root_.GD.N0232.N0720.N1166.d017432 k) omega := by
  unfold _root_.GD.N0232.N0720.N1276.d016066 _root_.GD.N0232.N0720.N1362.d017692
  rw [integral_map
    _root_.GD.N0232.N0720.N1362.d017694.aemeasurable
    (by
      exact ((_root_.GD.N0232.N0720.N1499.d014998.sub continuous_const).mul
        (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)).aestronglyMeasurable)]
  rw [_root_.GD.N0232.N0720.N1166.d017440,
    integral_withDensity_eq_integral_toReal_smul
      ((_root_.GD.N0232.N0720.N1166.d017436 k).pow_const 2).ennreal_ofReal
      (ae_of_all (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104)
        fun _ ↦ ENNReal.ofReal_lt_top)]
  unfold _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1173.d015939 _root_.GD.N0232.N0720.N1173.d015937
    _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1173.d015938
  apply integral_congr_ae
  filter_upwards with theta
  rw [ENNReal.toReal_ofReal (sq_nonneg _), _root_.GD.N0232.N0720.N1166.d017435]
  simp only [smul_eq_mul, _root_.GD.N0232.N0720.N1173.d015935,
    _root_.GD.N0232.N0720.N1486.d015874]
  ring

theorem d017726 (k : ℕ) :
    Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1362.d017692 k)
          _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1362.d017692 k) omega)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  refine (_root_.GD.N0232.N0720.N1362.d017723 k).congr
    (ae_of_all _ fun omega ↦ ?_)
  change
    _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1405.d016086 (_root_.GD.N0232.N0720.N1166.d017432 k) omega ^ 2 /
        _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1166.d017432 k) omega =
      _root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1362.d017692 k)
          _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1362.d017692 k) omega
  rw [_root_.GD.N0232.N0720.N1362.d017724,
    _root_.GD.N0232.N0720.N1362.d017725]



noncomputable instance d017727 (k n : ℕ) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n) := by
  letI : IsFiniteMeasure
      (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) :=
    _root_.GD.N0232.N0720.N1367.d016869 (_root_.GD.N0232.N0720.N1275.d016919 n)
  unfold _root_.GD.N0232.N0720.N1361.d016942
  infer_instance

theorem d017728 (k n : ℕ) :
    ∀ omega : _root_.GD.N0232.N0720.N1276.d016060,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
          (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n) ∧
      Integrable (fun theta ↦
          _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
          (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n) ∧
      Integrable (fun theta ↦
          _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
          (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n) ∧
      _root_.GD.N0232.N0720.N1276.d016063
          (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n) omega ≠ 0 := by
  intro omega
  have hc := _root_.GD.N0232.N0720.N1365.d016967 (_root_.GD.N0232.N0720.N1275.d016919 n) omega
  have hr := _root_.GD.N0232.N0720.N1362.d017712 k omega
  have hlike := hc.1.add_measure hr.1
  have hmom := hc.2.1.add_measure hr.2.1
  have hmom2 := hc.2.2.1.add_measure hr.2.2.1
  have hE : _root_.GD.N0232.N0720.N1276.d016063
      (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n) omega =
        _root_.GD.N0232.N0720.N1276.d016063
            (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega +
          _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1362.d017692 k) omega := by
    exact _root_.GD.N0232.N0720.N1361.d016936 _ _ omega hc.1 hr.1
  refine ⟨hlike, hmom, hmom2, ?_⟩
  rw [hE]
  exact (add_pos
    (_root_.GD.N0232.N0720.N1365.d016966 (_root_.GD.N0232.N0720.N1275.d016919 n) omega)
    (_root_.GD.N0232.N0720.N1362.d017711 k omega)).ne'

theorem d017729
    (k n : ℕ) :
    Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715).toReal)
      (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n) := by
  unfold _root_.GD.N0232.N0720.N1361.d016942
  exact (_root_.GD.N0232.N0720.N1362.d017721
    (_root_.GD.N0232.N0720.N1275.d016919 n)).add_measure
      (_root_.GD.N0232.N0720.N1362.d017719 k)

theorem d017730
    (k n : ℕ) :
    Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066
          (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n)
          _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063
          (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n) omega)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  let central := _root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)
  let rho := _root_.GD.N0232.N0720.N1362.d017692 k
  letI : IsFiniteMeasure central :=
    _root_.GD.N0232.N0720.N1367.d016869 (_root_.GD.N0232.N0720.N1275.d016919 n)
  have hE : _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1361.d016942 rho n) =
      fun omega ↦ _root_.GD.N0232.N0720.N1276.d016063 central omega + _root_.GD.N0232.N0720.N1276.d016063 rho omega := by
    funext omega
    exact _root_.GD.N0232.N0720.N1361.d016936 central rho omega
      (_root_.GD.N0232.N0720.N1361.d016934
        (_root_.GD.N0232.N0720.N1275.d016919 n) omega)
      (_root_.GD.N0232.N0720.N1362.d017703 k omega)
  have hJ : _root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1361.d016942 rho n)
      _root_.GD.N0232.N0720.N1405.d016086 = fun omega ↦
        _root_.GD.N0232.N0720.N1276.d016066 central _root_.GD.N0232.N0720.N1405.d016086 omega +
          _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega := by
    funext omega
    exact _root_.GD.N0232.N0720.N1361.d016937 central rho
      _root_.GD.N0232.N0720.N1405.d016086 omega
      (_root_.GD.N0232.N0720.N1361.d016935
        (_root_.GD.N0232.N0720.N1275.d016919 n) omega)
      (_root_.GD.N0232.N0720.N1362.d017706 k omega)
  have hcentral := _root_.GD.N0232.N0720.N1361.d016933
    (_root_.GD.N0232.N0720.N1275.d016919 n)
  have hshield := _root_.GD.N0232.N0720.N1348.d017003 rho n
    (_root_.GD.N0232.N0720.N1362.d017707 k)
    (_root_.GD.N0232.N0720.N1362.d017708 k)
    (ae_of_all _ (_root_.GD.N0232.N0720.N1362.d017711 k))
    (_root_.GD.N0232.N0720.N1362.d017726 k)
  have hupper : Integrable (fun omega ↦
      2 * (_root_.GD.N0232.N0720.N1276.d016066 central
            _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 central omega) +
      2 * (_root_.GD.N0232.N0720.N1276.d016066 rho
            _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
          (_root_.GD.N0232.N0720.N1276.d016063 central omega + _root_.GD.N0232.N0720.N1276.d016063 rho omega)))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
    (hcentral.const_mul 2).add (hshield.const_mul 2)
  rw [hE, hJ]
  apply hupper.mono_nonneg
  · have hmixed : Measurable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
        (_root_.GD.N0232.N0720.N1276.d016066 central _root_.GD.N0232.N0720.N1405.d016086 omega +
            _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega) ^ 2 /
          (_root_.GD.N0232.N0720.N1276.d016063 central omega + _root_.GD.N0232.N0720.N1276.d016063 rho omega)) :=
      (((_root_.GD.N0232.N0720.N1348.d017000 central).add
        (_root_.GD.N0232.N0720.N1362.d017708 k)).pow_const 2).div
          ((_root_.GD.N0232.N0720.N1365.d016991 central).add
            (_root_.GD.N0232.N0720.N1362.d017707 k))
    exact hmixed.aestronglyMeasurable
  · filter_upwards with omega
    exact div_nonneg (sq_nonneg _)
      (add_nonneg (_root_.GD.N0232.N0720.N1361.d016938 central omega)
        (_root_.GD.N0232.N0720.N1361.d016938 rho omega))
  · filter_upwards with omega
    exact _root_.GD.N0232.N0720.N1347.d002848
      ((_root_.GD.N0232.N0720.N1361.d016939
        (_root_.GD.N0232.N0720.N1275.d016919 n) omega).trans_lt' zero_lt_one)
      (_root_.GD.N0232.N0720.N1361.d016938 rho omega)






theorem d017731 :
    ∃ select : ℕ → ℕ,
      (∀ k, k ≤ select k) ∧
      _root_.GD.N0232.N0720.N1111.d016605
        (fun k ↦ _root_.GD.N0232.N0720.N1361.d016942
          (_root_.GD.N0232.N0720.N1362.d017692 k) (select k)) ∧
      Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067
        (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) (select k))
        _root_.GD.N0232.N0720.N1405.d016086) atTop (𝓝 0) := by
  exact _root_.GD.N0232.N0720.N1348.d017005
    _root_.GD.N0232.N0720.N1362.d017692
    (fun k ↦ _root_.GD.N0232.N0720.N1362.d017695 k)
    _root_.GD.N0232.N0720.N1362.d017696
    _root_.GD.N0232.N0720.N1362.d017703
    _root_.GD.N0232.N0720.N1362.d017706
    _root_.GD.N0232.N0720.N1362.d017707
    _root_.GD.N0232.N0720.N1362.d017708
    (fun k ↦ ae_of_all _ (_root_.GD.N0232.N0720.N1362.d017711 k))
    _root_.GD.N0232.N0720.N1362.d017726

theorem d017732 (k n : ℕ) :
    0 < _root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) n Set.univ := by
  exact (_root_.GD.N0232.N0720.N1362.d017710 k).trans_le
    (Measure.le_add_left le_rfl Set.univ)



theorem d017733 :
    ∃ select : ℕ → ℕ,
      (∀ k, k ≤ select k) ∧
      (∀ k, IsFiniteMeasure
        (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) (select k))) ∧
      (∀ k, 0 < _root_.GD.N0232.N0720.N1361.d016942
        (_root_.GD.N0232.N0720.N1362.d017692 k) (select k) Set.univ) ∧
      _root_.GD.N0232.N0720.N1111.d016605
        (fun k ↦ _root_.GD.N0232.N0720.N1361.d016942
          (_root_.GD.N0232.N0720.N1362.d017692 k) (select k)) ∧
      Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067
        (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) (select k))
        _root_.GD.N0232.N0720.N1405.d016086) atTop (𝓝 0) := by
  obtain ⟨select, hcofinal, hretain, hzero⟩ :=
    _root_.GD.N0232.N0720.N1362.d017731
  exact ⟨select, hcofinal,
    fun k ↦ _root_.GD.N0232.N0720.N1362.d017727 k (select k),
    fun k ↦ _root_.GD.N0232.N0720.N1362.d017732 k (select k),
    hretain, hzero⟩

end

end GD.N0232.N0720.N1362

#print axioms _root_.GD.N0232.N0720.N1362.d017696
#print axioms _root_.GD.N0232.N0720.N1362.d017726
#print axioms _root_.GD.N0232.N0720.N1362.d017730
#print axioms _root_.GD.N0232.N0720.N1362.d017731
#print axioms _root_.GD.N0232.N0720.N1362.d017733
