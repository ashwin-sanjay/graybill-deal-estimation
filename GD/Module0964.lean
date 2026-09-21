import GD.Module0735
import GD.Module0744
import GD.Module0963


















open Filter MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace GD
namespace N0232
namespace N0719
namespace N1022

noncomputable section

open _root_.GD.N0232.N0719.N0828
open _root_.GD.N0232.N0719.N0829
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0230.N0594
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0655
open _root_.GD.N0232.N0720.N1482

abbrev d015176 :=
  _root_.GD.N0232.N0719.N0946.d009229

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)

noncomputable local instance d015177 :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813
    _root_.GD.N0232.N0719.d009182
  infer_instance




def d015178 (g : _root_.GD.N0232.N0719.N1022.d015176) : _root_.GD.N0230.N0655.d000349 :=
  (g.shift, ⟨g.d009239, g.d009240⟩)

@[simp] theorem d015179 (g : _root_.GD.N0232.N0719.N1022.d015176) :
    (_root_.GD.N0232.N0719.N1022.d015178 g).1 = g.shift := rfl

@[simp] theorem d015180 (g : _root_.GD.N0232.N0719.N1022.d015176) :
    ((_root_.GD.N0232.N0719.N1022.d015178 g).2 : ℝ) = g.d009239 := rfl




theorem d015181 : Continuous _root_.GD.N0232.N0719.N1022.d015178 := by
  apply Continuous.prodMk
  · exact _root_.GD.N0232.N0720.N1482.d015127
  · apply Continuous.subtype_mk
    exact Real.continuous_exp.comp _root_.GD.N0232.N0720.N1482.d015126



theorem d015182
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) (g : _root_.GD.N0232.N0719.N1022.d015176) :
    MemLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) 2
      ((_root_.GD.N0232.N0719.N0859.d010813 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239)) := by
  let d := _root_.GD.N0232.N0719.N0896.d011088 k sizes p
  have horbit : MemLp
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 d) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    _root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp
  have hcentered : MemLp
      (fun omega ↦
        _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 d omega - g.shift)
      2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    horbit.sub (memLp_const g.shift)
  have hscaled : MemLp
      (fun omega ↦ g.d009239⁻¹ *
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 d omega - g.shift))
      2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    hcentered.const_mul g.d009239⁻¹
  have hcomp : MemLp
      (d ∘ _root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239)
      2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    simpa [d, _root_.GD.N0232.N0719.N0842.d010911, Function.comp_def, g.d009241] using hscaled
  exact (memLp_map_measure_iff
    (_root_.GD.N0232.N0719.N0896.d011089 k sizes p).aestronglyMeasurable
    (_root_.GD.N0232.N0719.N0842.d010908 k sizes g.shift g.d009239).aemeasurable).2 hcomp



theorem d015183
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    ∀ (gSeq : ℕ → _root_.GD.N0232.N0719.N1022.d015176) (g : _root_.GD.N0232.N0719.N1022.d015176),
      Tendsto gSeq atTop (nhds g) →
        TendstoInMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (fun j ↦ _root_.GD.N0232.N0719.N0842.d010911 k sizes (gSeq j).shift (gSeq j).d009239
            (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)) atTop
          (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239
            (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)) := by
  intro gSeq g hg
  have hparameter : Tendsto (fun j ↦ _root_.GD.N0232.N0719.N1022.d015178 (gSeq j)) atTop
      (nhds (_root_.GD.N0232.N0719.N1022.d015178 g)) :=
    _root_.GD.N0232.N0719.N1022.d015181.tendsto g |>.comp hg
  apply _root_.GD.N0232.N0719.N0829.d011030
    k sizes (fun j ↦ _root_.GD.N0232.N0719.N1022.d015178 (gSeq j)) (_root_.GD.N0232.N0719.N1022.d015178 g)
      hparameter (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (_root_.GD.N0232.N0719.N0896.d011089 k sizes p)
      (p := (2 : ENNReal)) (by norm_num) (by norm_num)
  · simpa [_root_.GD.N0232.N0719.N1022.d015178, _root_.GD.N0232.N0719.N0859.d010813] using
      (_root_.GD.N0232.N0719.N1022.d015182 k sizes p hp g)
  · rw [_root_.GD.N0232.N0719.N0828.d010997]
    infer_instance





theorem d015184
    (g h : _root_.GD.N0232.N0719.N1022.d015176)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes (g * h).shift (g * h).d009239 d =
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes h.shift h.d009239 d) := by
  simpa [_root_.GD.N0232.N0719.N0946.d009229.d009239,
    Real.exp_add] using
    (_root_.GD.N0232.N0719.N0842.d010916
      k sizes g.shift g.d009239 h.shift h.d009239
        g.d009241 h.d009241 d).symm



theorem d015185
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hTwo : _root_.GD.N0232.N0719.N0842.d010911 k sizes _root_.GD.N0232.N0720.N1482.d015130.shift _root_.GD.N0232.N0720.N1482.d015130.d009239
        (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0896.d011088 k sizes p)
    (hThree : _root_.GD.N0232.N0719.N0842.d010911 k sizes _root_.GD.N0232.N0720.N1482.d015131.shift
        _root_.GD.N0232.N0720.N1482.d015131.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0896.d011088 k sizes p) :
    ∀ g : _root_.GD.N0232.N0720.N1482.d015132,
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1.shift g.1.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
  let fixedSubgroup : Subgroup _root_.GD.N0232.N0719.N1022.d015176 :=
    { carrier := {g | _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239
          (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
            _root_.GD.N0232.N0719.N0896.d011088 k sizes p}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh
        change _root_.GD.N0232.N0719.N0842.d010911 k sizes (g * h).shift (g * h).d009239
            (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
              _root_.GD.N0232.N0719.N0859.d010813 k sizes]
          _root_.GD.N0232.N0719.N0896.d011088 k sizes p
        rw [_root_.GD.N0232.N0719.N1022.d015184]
        exact (_root_.GD.N0232.N0719.N0896.d011120 k sizes g hh).trans hg
      inv_mem' := by
        intro g hg
        change _root_.GD.N0232.N0719.N0842.d010911 k sizes g⁻¹.shift g⁻¹.d009239
            (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
              _root_.GD.N0232.N0719.N0859.d010813 k sizes]
          _root_.GD.N0232.N0719.N0896.d011088 k sizes p
        have htransport := _root_.GD.N0232.N0719.N0896.d011120 k sizes g⁻¹ hg
        rw [← _root_.GD.N0232.N0719.N1022.d015184, show g⁻¹ * g = 1 from inv_mul_cancel g] at htransport
        simpa using htransport.symm }
  have hle : _root_.GD.N0232.N0720.N1482.d015132 ≤ fixedSubgroup := by
    apply (Subgroup.closure_le fixedSubgroup).2
    intro g hg
    rcases hg with (rfl | rfl)
    · exact hTwo
    · exact hThree
  intro g
  exact hle g.2




theorem d015186
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p)
    (hTwo : _root_.GD.N0232.N0719.N0896.d011109 k sizes _root_.GD.N0232.N0720.N1482.d015130 p hp = p)
    (hThree : _root_.GD.N0232.N0719.N0896.d011109 k sizes _root_.GD.N0232.N0720.N1482.d015131 p hp = p)
    (horbit : ∀ (sequence : ℕ → _root_.GD.N0232.N0720.N1482.d015132) (g : _root_.GD.N0232.N0719.N1022.d015176),
      Tendsto (fun j ↦ (sequence j).1) atTop (nhds g) →
        TendstoInMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (fun j ↦ _root_.GD.N0232.N0719.N0842.d010911 k sizes (sequence j).1.shift
            (sequence j).1.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)) atTop
          (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239
            (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))) :
    ∀ g : _root_.GD.N0232.N0719.N1022.d015176, _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp = p := by
  have toRaw (g : _root_.GD.N0232.N0719.N1022.d015176)
      (hg : _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp = p) :
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
    apply (MemLp.toLp_eq_toLp_iff
      (_root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp)
      (_root_.GD.N0232.N0719.N0896.d011091 k sizes p)).mp
    rw [_root_.GD.N0232.N0719.N0896.d011092]
    exact hg
  have hsubFixed := _root_.GD.N0232.N0719.N1022.d015185
    k sizes p (toRaw _root_.GD.N0232.N0720.N1482.d015130 hTwo)
      (toRaw _root_.GD.N0232.N0720.N1482.d015131 hThree)
  have hallRaw : ∀ g : _root_.GD.N0232.N0719.N1022.d015176,
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
    apply _root_.GD.N0230.N0594.d000115
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (fun g : _root_.GD.N0232.N0720.N1482.d015132 ↦ g.1)
      (Dense.denseRange_val _root_.GD.N0232.N0720.N1482.d015157)
      (fun g ↦ _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239
        (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))
      (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)
      (_root_.GD.N0232.N0719.N0896.d011089 k sizes p).aestronglyMeasurable hsubFixed
    exact horbit
  intro g
  unfold _root_.GD.N0232.N0719.N0896.d011109
  calc
    MemLp.toLp
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))
        (_root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp) =
        MemLp.toLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (_root_.GD.N0232.N0719.N0896.d011091 k sizes p) :=
      MemLp.toLp_congr _ _ (hallRaw g)
    _ = p := _root_.GD.N0232.N0719.N0896.d011092 k sizes p




theorem d015187
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p)
    (hTwo : _root_.GD.N0232.N0719.N0896.d011109 k sizes _root_.GD.N0232.N0720.N1482.d015130 p hp = p)
    (hThree : _root_.GD.N0232.N0719.N0896.d011109 k sizes _root_.GD.N0232.N0720.N1482.d015131 p hp = p) :
    ∀ g : _root_.GD.N0232.N0719.N1022.d015176, _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp = p := by
  apply _root_.GD.N0232.N0719.N1022.d015186
    k sizes p hp hTwo hThree
  intro sequence g hsequence
  exact _root_.GD.N0232.N0719.N1022.d015183
    k sizes p hp (fun j ↦ (sequence j).1) g hsequence





theorem d015188
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) :
    (_root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015130 = 0 ∧
      _root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015131 = 0) ↔
      ∀ g : _root_.GD.N0232.N0719.N1022.d015176, _root_.GD.N0232.N0719.N0896.d011114 k sizes s g = 0 := by
  let p := _root_.GD.N0232.N0719.N0896.d011099 k sizes s.value
  let hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p :=
    _root_.GD.N0232.N0719.N0896.d011111 k sizes s p
      (_root_.GD.N0232.N0719.N0896.d011100 k sizes s.value).1
  constructor
  · rintro ⟨hTwoDefect, hThreeDefect⟩
    have hTwoPoint :=
      (_root_.GD.N0232.N0719.N0896.d011118 k sizes s _root_.GD.N0232.N0720.N1482.d015130).1 hTwoDefect
    have hThreePoint :=
      (_root_.GD.N0232.N0719.N0896.d011118
        k sizes s _root_.GD.N0232.N0720.N1482.d015131).1 hThreeDefect
    have hTwo : _root_.GD.N0232.N0719.N0896.d011109 k sizes _root_.GD.N0232.N0720.N1482.d015130 p hp = p := by
      have hvalue := congrArg Subtype.val hTwoPoint
      change _root_.GD.N0232.N0719.N0896.d011109 k sizes _root_.GD.N0232.N0720.N1482.d015130 p hp = p
      exact hvalue
    have hThree : _root_.GD.N0232.N0719.N0896.d011109 k sizes _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
      have hvalue := congrArg Subtype.val hThreePoint
      change _root_.GD.N0232.N0719.N0896.d011109 k sizes _root_.GD.N0232.N0720.N1482.d015131 p hp = p
      exact hvalue
    have hall := _root_.GD.N0232.N0719.N1022.d015187 k sizes p hp hTwo hThree
    intro g
    apply (_root_.GD.N0232.N0719.N0896.d011118 k sizes s g).2
    apply Subtype.ext
    change _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp = p
    exact hall g
  · intro hall
    exact ⟨hall _root_.GD.N0232.N0720.N1482.d015130, hall _root_.GD.N0232.N0720.N1482.d015131⟩



noncomputable def d015189
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015130 +
    _root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015131

theorem d015190
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N1022.d015189 (k := k) (sizes := sizes) s := by
  exact add_nonneg
    (_root_.GD.N0232.N0719.N0896.d011117 k sizes s _root_.GD.N0232.N0720.N1482.d015130)
    (_root_.GD.N0232.N0719.N0896.d011117 k sizes s _root_.GD.N0232.N0720.N1482.d015131)



theorem d015191
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) :
    _root_.GD.N0232.N0719.N1022.d015189 (k := k) (sizes := sizes) s = 0 ↔
      ∀ g : _root_.GD.N0232.N0719.N1022.d015176, _root_.GD.N0232.N0719.N0896.d011114 k sizes s g = 0 := by
  rw [_root_.GD.N0232.N0719.N1022.d015189, add_eq_zero_iff_of_nonneg
    (_root_.GD.N0232.N0719.N0896.d011117 k sizes s _root_.GD.N0232.N0720.N1482.d015130)
    (_root_.GD.N0232.N0719.N0896.d011117 k sizes s _root_.GD.N0232.N0720.N1482.d015131)]
  exact _root_.GD.N0232.N0719.N1022.d015188 k sizes s



theorem d015192 :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes ↔
      ∃ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
        _root_.GD.N0230.N0608.d000675
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
          (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) ∧
        _root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015130 = 0 ∧
        _root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015131 = 0 := by
  rw [_root_.GD.N0232.N0719.N0896.d011136
    k sizes hk hsizes]
  constructor
  · rintro ⟨s, hstrict, hall⟩
    exact ⟨s, hstrict, hall _root_.GD.N0232.N0720.N1482.d015130, hall _root_.GD.N0232.N0720.N1482.d015131⟩
  · rintro ⟨s, hstrict, hTwo, hThree⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0719.N1022.d015188 k sizes s).1
        ⟨hTwo, hThree⟩⟩


theorem d015193 :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes ↔
      ∃ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
        _root_.GD.N0230.N0608.d000675
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
          (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) ∧
        _root_.GD.N0232.N0719.N1022.d015189 (k := k) (sizes := sizes) s = 0 := by
  rw [_root_.GD.N0232.N0719.N0896.d011136
    k sizes hk hsizes]
  constructor
  · rintro ⟨s, hstrict, hall⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0719.N1022.d015191
        k sizes s).2 hall⟩
  · rintro ⟨s, hstrict, hmaster⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0719.N1022.d015191
        k sizes s).1 hmaster⟩




theorem d015194 :
    ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes ↔
      ∀ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
        _root_.GD.N0230.N0608.d000675
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
          (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) →
        0 < _root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015130 ∨
        0 < _root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015131 := by
  constructor
  · intro hnot s hstrict
    have hnotBoth : ¬
        (_root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015130 = 0 ∧
          _root_.GD.N0232.N0719.N0896.d011114 k sizes s _root_.GD.N0232.N0720.N1482.d015131 = 0) := by
      intro hzero
      apply hnot
      exact (_root_.GD.N0232.N0719.N1022.d015192
        k sizes hk hsizes).2 ⟨s, hstrict, hzero⟩
    rcases not_and_or.mp hnotBoth with hTwo | hThree
    · left
      exact lt_of_le_of_ne
        (_root_.GD.N0232.N0719.N0896.d011117 k sizes s _root_.GD.N0232.N0720.N1482.d015130) (Ne.symm hTwo)
    · right
      exact lt_of_le_of_ne
        (_root_.GD.N0232.N0719.N0896.d011117 k sizes s _root_.GD.N0232.N0720.N1482.d015131)
        (Ne.symm hThree)
  · intro hobstruction hexists
    obtain ⟨s, hstrict, hTwo, hThree⟩ :=
      (_root_.GD.N0232.N0719.N1022.d015192
        k sizes hk hsizes).1 hexists
    rcases hobstruction s hstrict with hpositive | hpositive
    · exact (ne_of_gt hpositive) hTwo
    · exact (ne_of_gt hpositive) hThree



theorem d015195 :
    ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes ↔
      ∀ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
        _root_.GD.N0230.N0608.d000675
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
          (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) →
        0 < _root_.GD.N0232.N0719.N1022.d015189 (k := k) (sizes := sizes) s := by
  constructor
  · intro hnot s hstrict
    have hnonneg := _root_.GD.N0232.N0719.N1022.d015190 k sizes s
    exact lt_of_le_of_ne hnonneg fun hzero ↦ hnot
      ((_root_.GD.N0232.N0719.N1022.d015193
        k sizes hk hsizes).2 ⟨s, hstrict, hzero.symm⟩)
  · intro hpositive hexists
    obtain ⟨s, hstrict, hzero⟩ :=
      (_root_.GD.N0232.N0719.N1022.d015193
        k sizes hk hsizes).1 hexists
    exact (ne_of_gt (hpositive s hstrict)) hzero

end

end N1022
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N1022.d015183
#print axioms _root_.GD.N0232.N0719.N1022.d015187
#print axioms _root_.GD.N0232.N0719.N1022.d015188
#print axioms _root_.GD.N0232.N0719.N1022.d015192
#print axioms _root_.GD.N0232.N0719.N1022.d015194
#print axioms _root_.GD.N0232.N0719.N1022.d015191
#print axioms _root_.GD.N0232.N0719.N1022.d015193
#print axioms _root_.GD.N0232.N0719.N1022.d015195
