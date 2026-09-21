import GD.Module0013
import GD.Module0932
import GD.Module0961
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup



























open Filter MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace GD
namespace N0232
namespace N0720
namespace N1482

noncomputable section

open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0230.N0594
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

abbrev d015118 :=
  _root_.GD.N0232.N0719.N0946.d009229

noncomputable local instance d015119 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

noncomputable local instance d015120 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172
  infer_instance




def d015121 : _root_.GD.N0232.N0720.N1482.d015118 → ℝ × ℝ :=
  _root_.GD.N0232.N0719.N0946.d009229.d009230

theorem d015122 : Function.Injective _root_.GD.N0232.N0720.N1482.d015121 :=
  _root_.GD.N0232.N0719.N0946.d009229.d009230.injective


noncomputable instance d015123 : MetricSpace _root_.GD.N0232.N0720.N1482.d015118 :=
  MetricSpace.induced _root_.GD.N0232.N0720.N1482.d015121 _root_.GD.N0232.N0720.N1482.d015122 inferInstance

theorem d015124 : Isometry _root_.GD.N0232.N0720.N1482.d015121 :=
  MetricSpace.isometry_induced _root_.GD.N0232.N0720.N1482.d015121 _root_.GD.N0232.N0720.N1482.d015122

@[fun_prop]
theorem d015125 : Continuous _root_.GD.N0232.N0720.N1482.d015121 :=
  _root_.GD.N0232.N0720.N1482.d015124.continuous

@[fun_prop]
theorem d015126 :
    Continuous (fun g : _root_.GD.N0232.N0720.N1482.d015118 ↦ g.logScale) := by
  exact continuous_fst.comp _root_.GD.N0232.N0720.N1482.d015125

@[fun_prop]
theorem d015127 :
    Continuous (fun g : _root_.GD.N0232.N0720.N1482.d015118 ↦ g.shift) := by
  exact continuous_snd.comp _root_.GD.N0232.N0720.N1482.d015125




def d015128 (t : ℝ) : _root_.GD.N0232.N0720.N1482.d015118 := ⟨t, 0⟩


def d015129 (r : ℝ) : _root_.GD.N0232.N0720.N1482.d015118 := ⟨0, r⟩


def d015130 : _root_.GD.N0232.N0720.N1482.d015118 := _root_.GD.N0232.N0720.N1482.d015129 (Real.log 2)


def d015131 : _root_.GD.N0232.N0720.N1482.d015118 :=
  ⟨1, Real.log 3⟩


def d015132 : Subgroup _root_.GD.N0232.N0720.N1482.d015118 :=
  Subgroup.closure {_root_.GD.N0232.N0720.N1482.d015130, _root_.GD.N0232.N0720.N1482.d015131}

@[simp] theorem d015133 (t : ℝ) :
    (_root_.GD.N0232.N0720.N1482.d015128 t).shift = t := rfl

@[simp] theorem d015134 (t : ℝ) :
    (_root_.GD.N0232.N0720.N1482.d015128 t).logScale = 0 := rfl

@[simp] theorem d015135 (r : ℝ) :
    (_root_.GD.N0232.N0720.N1482.d015129 r).shift = 0 := rfl

@[simp] theorem d015136 (r : ℝ) :
    (_root_.GD.N0232.N0720.N1482.d015129 r).logScale = r := rfl

@[simp] theorem d015137 : _root_.GD.N0232.N0720.N1482.d015128 0 = 1 := rfl

@[simp] theorem d015138 : _root_.GD.N0232.N0720.N1482.d015129 0 = 1 := rfl

@[simp] theorem d015139 (s t : ℝ) :
    _root_.GD.N0232.N0720.N1482.d015128 s * _root_.GD.N0232.N0720.N1482.d015128 t = _root_.GD.N0232.N0720.N1482.d015128 (s + t) := by
  ext <;> simp [_root_.GD.N0232.N0720.N1482.d015128]

@[simp] theorem d015140 (r s : ℝ) :
    _root_.GD.N0232.N0720.N1482.d015129 r * _root_.GD.N0232.N0720.N1482.d015129 s = _root_.GD.N0232.N0720.N1482.d015129 (r + s) := by
  ext <;> simp [_root_.GD.N0232.N0720.N1482.d015129]

@[simp] theorem d015141 (t : ℝ) :
    (_root_.GD.N0232.N0720.N1482.d015128 t)⁻¹ = _root_.GD.N0232.N0720.N1482.d015128 (-t) := by
  ext <;> simp [_root_.GD.N0232.N0720.N1482.d015128]

@[simp] theorem d015142 (r : ℝ) :
    (_root_.GD.N0232.N0720.N1482.d015129 r)⁻¹ = _root_.GD.N0232.N0720.N1482.d015129 (-r) := by
  ext <;> simp [_root_.GD.N0232.N0720.N1482.d015129]


theorem d015143 (r t : ℝ) :
    _root_.GD.N0232.N0720.N1482.d015129 r * _root_.GD.N0232.N0720.N1482.d015128 t * (_root_.GD.N0232.N0720.N1482.d015129 r)⁻¹ =
      _root_.GD.N0232.N0720.N1482.d015128 (Real.exp r * t) := by
  ext <;> simp [_root_.GD.N0232.N0720.N1482.d015128, _root_.GD.N0232.N0720.N1482.d015129]

theorem d015144 :
    _root_.GD.N0232.N0720.N1482.d015130 ∈ _root_.GD.N0232.N0720.N1482.d015132 := by
  exact Subgroup.subset_closure (by simp)

theorem d015145 :
    _root_.GD.N0232.N0720.N1482.d015131 ∈ _root_.GD.N0232.N0720.N1482.d015132 := by
  exact Subgroup.subset_closure (by simp)


theorem d015146 :
    _root_.GD.N0232.N0720.N1482.d015130 * _root_.GD.N0232.N0720.N1482.d015131 * _root_.GD.N0232.N0720.N1482.d015130⁻¹ *
        _root_.GD.N0232.N0720.N1482.d015131⁻¹ = _root_.GD.N0232.N0720.N1482.d015128 1 := by
  ext <;>
    simp [_root_.GD.N0232.N0720.N1482.d015130, _root_.GD.N0232.N0720.N1482.d015131, _root_.GD.N0232.N0720.N1482.d015128,
      _root_.GD.N0232.N0720.N1482.d015129, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  all_goals ring

theorem d015147 :
    _root_.GD.N0232.N0720.N1482.d015128 1 ∈ _root_.GD.N0232.N0720.N1482.d015132 := by
  rw [← _root_.GD.N0232.N0720.N1482.d015146]
  exact Subgroup.mul_mem _root_.GD.N0232.N0720.N1482.d015132
    (Subgroup.mul_mem _root_.GD.N0232.N0720.N1482.d015132
      (Subgroup.mul_mem _root_.GD.N0232.N0720.N1482.d015132
        _root_.GD.N0232.N0720.N1482.d015144
        _root_.GD.N0232.N0720.N1482.d015145)
      (Subgroup.inv_mem _root_.GD.N0232.N0720.N1482.d015132
        _root_.GD.N0232.N0720.N1482.d015144))
    (Subgroup.inv_mem _root_.GD.N0232.N0720.N1482.d015132
      _root_.GD.N0232.N0720.N1482.d015145)



theorem d015148 :
    _root_.GD.N0232.N0720.N1482.d015129 (Real.log 3) ∈ _root_.GD.N0232.N0720.N1482.d015132 := by
  have h := Subgroup.mul_mem _root_.GD.N0232.N0720.N1482.d015132
    (Subgroup.inv_mem _root_.GD.N0232.N0720.N1482.d015132
      _root_.GD.N0232.N0720.N1482.d015147)
    _root_.GD.N0232.N0720.N1482.d015145
  convert h using 1
  ext <;> simp [_root_.GD.N0232.N0720.N1482.d015128, _root_.GD.N0232.N0720.N1482.d015129,
    _root_.GD.N0232.N0720.N1482.d015131]

theorem d015149 :
    _root_.GD.N0232.N0720.N1482.d015129 (Real.log 2) ∈ _root_.GD.N0232.N0720.N1482.d015132 :=
  _root_.GD.N0232.N0720.N1482.d015144



private theorem d015150
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : (b : ℝ) * Real.log 2 = (a : ℝ) * Real.log 3) : False := by
  have hlog : Real.log ((2 : ℝ) ^ b) = Real.log ((3 : ℝ) ^ a) := by
    simpa [Real.log_pow] using h
  have hpowReal : (2 : ℝ) ^ b = (3 : ℝ) ^ a := by
    calc
      (2 : ℝ) ^ b = Real.exp (Real.log ((2 : ℝ) ^ b)) := by
        rw [Real.exp_log (pow_pos (by norm_num) _)]
      _ = Real.exp (Real.log ((3 : ℝ) ^ a)) := by rw [hlog]
      _ = (3 : ℝ) ^ a := Real.exp_log (pow_pos (by norm_num) _)
  have hpow : 2 ^ b = 3 ^ a := by
    exact_mod_cast hpowReal
  have hprime := Nat.prime_two.pow_inj' (by norm_num : Nat.Prime 3)
    (Nat.ne_of_gt hb) (Nat.ne_of_gt ha) hpow
  norm_num at hprime


theorem d015151 :
    Irrational (Real.log 2 / Real.log 3) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hratio
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogThree : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hlogThreeNe : Real.log (3 : ℝ) ≠ 0 := ne_of_gt hlogThree
  have hratioPos : 0 < (a : ℝ) / (b : ℝ) := by
    rw [← hratio]
    exact div_pos hlogTwo hlogThree
  have hlinear : (b : ℝ) * Real.log 2 = (a : ℝ) * Real.log 3 := by
    have hratio' : Real.log 2 = ((a : ℝ) / (b : ℝ)) * Real.log 3 :=
      (div_eq_iff hlogThreeNe).mp hratio
    rw [hratio']
    field_simp
  rcases div_pos_iff.mp hratioPos with hab | hab
  · have haInt : 0 < a := by exact_mod_cast hab.1
    have hbInt : 0 < b := by exact_mod_cast hab.2
    apply _root_.GD.N0232.N0720.N1482.d015150 a.toNat b.toNat
    · omega
    · omega
    · have haCast : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (le_of_lt haInt)
      have hbCast : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (le_of_lt hbInt)
      simpa only [haCast, hbCast] using hlinear
  · have haInt : a < 0 := by exact_mod_cast hab.1
    have hbInt : b < 0 := by exact_mod_cast hab.2
    apply _root_.GD.N0232.N0720.N1482.d015150 (-a).toNat (-b).toNat
    · omega
    · omega
    · have hneg : ((-b : ℤ) : ℝ) * Real.log 2 =
          ((-a : ℤ) : ℝ) * Real.log 3 := by
        push_cast
        linarith
      have haCast : (((-a).toNat : ℕ) : ℝ) = ((-a : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr haInt))
      have hbCast : (((-b).toNat : ℕ) : ℝ) = ((-b : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hbInt))
      simpa only [haCast, hbCast] using hneg


def d015152 : AddSubgroup ℝ where
  carrier := {r | _root_.GD.N0232.N0720.N1482.d015129 r ∈ _root_.GD.N0232.N0720.N1482.d015132}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs
    change _root_.GD.N0232.N0720.N1482.d015129 (r + s) ∈ _root_.GD.N0232.N0720.N1482.d015132
    rw [← _root_.GD.N0232.N0720.N1482.d015140]
    exact Subgroup.mul_mem _root_.GD.N0232.N0720.N1482.d015132 hr hs
  neg_mem' := by
    intro r hr
    change _root_.GD.N0232.N0720.N1482.d015129 (-r) ∈ _root_.GD.N0232.N0720.N1482.d015132
    rw [← _root_.GD.N0232.N0720.N1482.d015142]
    exact Subgroup.inv_mem _root_.GD.N0232.N0720.N1482.d015132 hr

theorem d015153 : Dense (_root_.GD.N0232.N0720.N1482.d015152 : Set ℝ) := by
  have hclosure : AddSubgroup.closure {Real.log 2, Real.log 3} ≤
      _root_.GD.N0232.N0720.N1482.d015152 := by
    apply (AddSubgroup.closure_le _root_.GD.N0232.N0720.N1482.d015152).2
    intro r hr
    rcases hr with (rfl | rfl)
    · exact _root_.GD.N0232.N0720.N1482.d015149
    · exact _root_.GD.N0232.N0720.N1482.d015148
  exact (dense_addSubgroupClosure_pair_iff.2
    _root_.GD.N0232.N0720.N1482.d015151).mono hclosure





def d015154 : AddSubgroup ℝ where
  carrier := {t | _root_.GD.N0232.N0720.N1482.d015128 t ∈ _root_.GD.N0232.N0720.N1482.d015132}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht
    change _root_.GD.N0232.N0720.N1482.d015128 (s + t) ∈ _root_.GD.N0232.N0720.N1482.d015132
    rw [← _root_.GD.N0232.N0720.N1482.d015139]
    exact Subgroup.mul_mem _root_.GD.N0232.N0720.N1482.d015132 hs ht
  neg_mem' := by
    intro t ht
    change _root_.GD.N0232.N0720.N1482.d015128 (-t) ∈ _root_.GD.N0232.N0720.N1482.d015132
    rw [← _root_.GD.N0232.N0720.N1482.d015141]
    exact Subgroup.inv_mem _root_.GD.N0232.N0720.N1482.d015132 ht

theorem d015155
    {r : ℝ} (hr : r ∈ _root_.GD.N0232.N0720.N1482.d015152) :
    Real.exp r ∈ _root_.GD.N0232.N0720.N1482.d015154 := by
  change _root_.GD.N0232.N0720.N1482.d015128 (Real.exp r) ∈ _root_.GD.N0232.N0720.N1482.d015132
  rw [← mul_one (Real.exp r), ← _root_.GD.N0232.N0720.N1482.d015143]
  exact Subgroup.mul_mem _root_.GD.N0232.N0720.N1482.d015132
    (Subgroup.mul_mem _root_.GD.N0232.N0720.N1482.d015132 hr
      _root_.GD.N0232.N0720.N1482.d015147)
    (Subgroup.inv_mem _root_.GD.N0232.N0720.N1482.d015132 hr)

theorem d015156 : Dense (_root_.GD.N0232.N0720.N1482.d015154 : Set ℝ) := by
  apply AddSubgroup.dense_of_not_isolated_zero
  intro ε hε
  have hopen : IsOpen (Set.Iio (Real.log ε)) := isOpen_Iio
  have hnonempty : (Set.Iio (Real.log ε)).Nonempty :=
    ⟨Real.log ε - 1, by
      change Real.log ε - 1 < Real.log ε
      exact sub_lt_self _ zero_lt_one⟩
  obtain ⟨r, hrGenerated, hrLog⟩ :=
    _root_.GD.N0232.N0720.N1482.d015153.exists_mem_open hopen hnonempty
  refine ⟨Real.exp r,
    _root_.GD.N0232.N0720.N1482.d015155 hrGenerated,
    Real.exp_pos r, ?_⟩
  rw [← Real.exp_log hε]
  exact Real.exp_lt_exp.mpr hrLog



theorem d015157 :
    Dense (_root_.GD.N0232.N0720.N1482.d015132 : Set _root_.GD.N0232.N0720.N1482.d015118) := by
  intro g
  obtain ⟨rSeq, hrSeqMem, hrSeqTendsto⟩ :=
    mem_closure_iff_seq_limit.mp (_root_.GD.N0232.N0720.N1482.d015153 g.logScale)
  obtain ⟨tSeq, htSeqMem, htSeqTendsto⟩ :=
    mem_closure_iff_seq_limit.mp (_root_.GD.N0232.N0720.N1482.d015156 g.shift)
  let sequence : ℕ → _root_.GD.N0232.N0720.N1482.d015118 := fun j ↦
    _root_.GD.N0232.N0720.N1482.d015128 (tSeq j) * _root_.GD.N0232.N0720.N1482.d015129 (rSeq j)
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨sequence, ?_, ?_⟩
  · intro j
    exact Subgroup.mul_mem _root_.GD.N0232.N0720.N1482.d015132 (htSeqMem j) (hrSeqMem j)
  · rw [_root_.GD.N0232.N0720.N1482.d015124.tendsto_nhds_iff]
    have hsequence : _root_.GD.N0232.N0720.N1482.d015121 ∘ sequence =
        (fun j ↦ (rSeq j, tSeq j)) := by
      funext j
      apply Prod.ext
      · change 0 + rSeq j = rSeq j
        ring
      · change tSeq j + Real.exp 0 * 0 = tSeq j
        simp
    rw [hsequence]
    change Tendsto (fun j ↦ (rSeq j, tSeq j)) atTop
      (nhds (g.logScale, g.shift))
    exact hrSeqTendsto.prodMk_nhds htSeqTendsto




theorem d015158
    (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp) := by
  intro eta
  let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by simp [theta]
  rw [← heta, _root_.GD.N0232.N0720.N1159.d014643]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp theta)


@[simp] theorem d015159
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1159.d014642 m n 1 p hp = p := by
  unfold _root_.GD.N0232.N0720.N1159.d014642
  simpa only [_root_.GD.N0232.N0720.N1214.d014263] using _root_.GD.N0232.N0720.N1214.d014269 m n p



theorem d015160
    (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
  let f := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)
  let hf : MemLp f 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1159.d014641 m n g p hp
  have hcanonical :
      _root_.GD.N0232.N0720.N1214.d014265 m n (MemLp.toLp f hf) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ MemLp.toLp f hf omega :=
    _root_.GD.N0232.N0720.N1214.d014267 m n (MemLp.toLp f hf)
  have htoLp : (fun omega ↦ MemLp.toLp f hf omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] f := by
    simpa [f] using hf.coeFn_toLp
  simpa [_root_.GD.N0232.N0720.N1159.d014642, f, hf] using hcanonical.trans htoLp


theorem d015161
    (g h : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g
        (_root_.GD.N0232.N0720.N1159.d014642 m n h p hp)
        (_root_.GD.N0232.N0720.N1482.d015158 (m := m) (n := n) h p hp) =
      _root_.GD.N0232.N0720.N1159.d014642 m n (g * h) p hp := by
  let ph := _root_.GD.N0232.N0720.N1159.d014642 m n h p hp
  let hph : _root_.GD.N0232.N0720.N1159.d014637 m n ph :=
    _root_.GD.N0232.N0720.N1482.d015158 (m := m) (n := n) h p hp
  let lhsRaw := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n ph)
  let rhsRaw := _root_.GD.N0232.N0720.N1214.d014261 m n (g * h) (_root_.GD.N0232.N0720.N1214.d014265 m n p)
  let hlhs : MemLp lhsRaw 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1159.d014641 m n g ph hph
  let hrhs : MemLp rhsRaw 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1159.d014641 m n (g * h) p hp
  have hfirst : lhsRaw =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014261 m n h (_root_.GD.N0232.N0720.N1214.d014265 m n p)) := by
    exact _root_.GD.N0232.N0720.N1081.d014625
      m n g (_root_.GD.N0232.N0720.N1482.d015160
        (m := m) (n := n) h p hp)
  have hraw : lhsRaw =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] rhsRaw := by
    filter_upwards [hfirst] with omega homega
    rw [homega]
    exact congrFun (_root_.GD.N0232.N0720.N1214.d014264 m n g h (_root_.GD.N0232.N0720.N1214.d014265 m n p)) omega
  change MemLp.toLp lhsRaw hlhs = MemLp.toLp rhsRaw hrhs
  exact MemLp.toLp_congr hlhs hrhs hraw





theorem d015162
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) 2
      ((_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  let d := _root_.GD.N0232.N0720.N1214.d014265 m n p
  have horbit : MemLp (_root_.GD.N0232.N0720.N1214.d014261 m n g d) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1159.d014641 m n g p hp
  have hcentered : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1214.d014261 m n g d omega - g.shift)
      2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := horbit.sub (memLp_const g.shift)
  have hscaled : MemLp
      (fun omega ↦ g.d009239⁻¹ *
        (_root_.GD.N0232.N0720.N1214.d014261 m n g d omega - g.shift))
      2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := hcentered.const_mul g.d009239⁻¹
  have hcomp : MemLp (d ∘ _root_.GD.N0232.N0720.N1484.d015094 m n g)
      2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    simpa [d, _root_.GD.N0232.N0720.N1484.d015094, _root_.GD.N0232.N0720.N1214.d014261, Function.comp_def,
      _root_.GD.N0232.N0719.N0946.d009229.d009244, g.d009241] using hscaled
  exact (memLp_map_measure_iff
    (_root_.GD.N0232.N0720.N1214.d014266 m n p).aestronglyMeasurable
    (_root_.GD.N0232.N0720.N1484.d015095 m n g).aemeasurable).2 hcomp



theorem d015163
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    ∀ (gSeq : ℕ → _root_.GD.N0232.N0720.N1482.d015118) (g : _root_.GD.N0232.N0720.N1482.d015118),
      Tendsto gSeq atTop (nhds g) →
        TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
          (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) (_root_.GD.N0232.N0720.N1214.d014265 m n p)) atTop
          (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) := by
  intro gSeq g hg
  have hcoordinate : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale)) atTop
      (nhds (g.shift, g.logScale)) := by
    exact (_root_.GD.N0232.N0720.N1482.d015127.tendsto g |>.comp hg).prodMk_nhds
      (_root_.GD.N0232.N0720.N1482.d015126.tendsto g |>.comp hg)
  apply _root_.GD.N0232.N0720.N1484.d015109
    (p := (2 : ENNReal)) m n gSeq (g.shift, g.logScale) hcoordinate
    (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014266 m n p)
    (by norm_num) (by norm_num)
    (by
      simpa using (_root_.GD.N0232.N0720.N1482.d015162
        (m := m) (n := n) p hp g))
    (by
      rw [_root_.GD.N0232.N0720.N1484.d015101 m n g]
      infer_instance)
  intro s hs δ hδ
  exact _root_.GD.N0232.N0720.N1484.d015105
    m n gSeq (g.shift, g.logScale) hcoordinate s hs δ hδ





theorem d015164
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (_hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hTwo : _root_.GD.N0232.N0720.N1214.d014261 m n _root_.GD.N0232.N0720.N1482.d015130 (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014265 m n p)
    (hThree : _root_.GD.N0232.N0720.N1214.d014261 m n _root_.GD.N0232.N0720.N1482.d015131 (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014265 m n p) :
    ∀ g : _root_.GD.N0232.N0720.N1482.d015132,
      _root_.GD.N0232.N0720.N1214.d014261 m n g.1 (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p := by
  let fixedSubgroup : Subgroup _root_.GD.N0232.N0720.N1482.d015118 :=
    { carrier := {g | _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          _root_.GD.N0232.N0720.N1214.d014265 m n p}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh
        change _root_.GD.N0232.N0720.N1214.d014261 m n (g * h) (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          _root_.GD.N0232.N0720.N1214.d014265 m n p
        rw [← _root_.GD.N0232.N0720.N1214.d014264]
        exact (_root_.GD.N0232.N0720.N1081.d014625
          m n g hh).trans hg
      inv_mem' := by
        intro g hg
        change _root_.GD.N0232.N0720.N1214.d014261 m n g⁻¹ (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          _root_.GD.N0232.N0720.N1214.d014265 m n p
        have htransport := _root_.GD.N0232.N0720.N1081.d014625
          m n g⁻¹ hg
        rw [_root_.GD.N0232.N0720.N1214.d014264, show g⁻¹ * g = 1 from inv_mul_cancel g,
          _root_.GD.N0232.N0720.N1214.d014263] at htransport
        exact htransport.symm }
  have hle : _root_.GD.N0232.N0720.N1482.d015132 ≤ fixedSubgroup := by
    apply (Subgroup.closure_le fixedSubgroup).2
    intro g hg
    rcases hg with (rfl | rfl)
    · exact hTwo
    · exact hThree
  intro g
  exact hle g.2


theorem d015165
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p) :
    ∀ g : _root_.GD.N0232.N0720.N1482.d015132,
      _root_.GD.N0232.N0720.N1159.d014642 m n g.1 p hp = p := by
  have toRaw (g : _root_.GD.N0232.N0720.N1482.d015118)
      (hg : _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p) :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p := by
    apply (MemLp.toLp_eq_toLp_iff
      (_root_.GD.N0232.N0720.N1159.d014641 m n g p hp)
      (_root_.GD.N0232.N0720.N1214.d014268 m n p)).mp
    rw [_root_.GD.N0232.N0720.N1214.d014269]
    exact hg
  have hraw := _root_.GD.N0232.N0720.N1482.d015164 (m := m) (n := n) p hp
    (toRaw _root_.GD.N0232.N0720.N1482.d015130 hTwo) (toRaw _root_.GD.N0232.N0720.N1482.d015131 hThree)
  intro g
  unfold _root_.GD.N0232.N0720.N1159.d014642
  calc
    MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n g.1 (_root_.GD.N0232.N0720.N1214.d014265 m n p))
        (_root_.GD.N0232.N0720.N1159.d014641 m n g.1 p hp) =
        MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014268 m n p) :=
      MemLp.toLp_congr _ _ (hraw g)
    _ = p := _root_.GD.N0232.N0720.N1214.d014269 m n p




theorem d015166
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p)
    (horbit : ∀ (sequence : ℕ → _root_.GD.N0232.N0720.N1482.d015132) (g : _root_.GD.N0232.N0720.N1482.d015118),
      Tendsto (fun j ↦ (sequence j).1) atTop (nhds g) →
        TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
          (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n (sequence j).1 (_root_.GD.N0232.N0720.N1214.d014265 m n p)) atTop
          (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))) :
    ∀ g : _root_.GD.N0232.N0720.N1482.d015118, _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have hsubFixed := _root_.GD.N0232.N0720.N1482.d015165
    (m := m) (n := n) p hp hTwo hThree
  have hrawFixed : ∀ g : _root_.GD.N0232.N0720.N1482.d015132,
      _root_.GD.N0232.N0720.N1214.d014261 m n g.1 (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p := by
    intro g
    apply (MemLp.toLp_eq_toLp_iff
      (_root_.GD.N0232.N0720.N1159.d014641 m n g.1 p hp)
      (_root_.GD.N0232.N0720.N1214.d014268 m n p)).mp
    rw [_root_.GD.N0232.N0720.N1214.d014269]
    exact hsubFixed g
  have hallRaw : ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p := by
    apply _root_.GD.N0230.N0594.d000115
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (fun g : _root_.GD.N0232.N0720.N1482.d015132 ↦ g.1)
      (Dense.denseRange_val _root_.GD.N0232.N0720.N1482.d015157)
      (fun g ↦ _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
      (_root_.GD.N0232.N0720.N1214.d014265 m n p)
      (_root_.GD.N0232.N0720.N1214.d014266 m n p).aestronglyMeasurable hrawFixed
    exact horbit
  intro g
  unfold _root_.GD.N0232.N0720.N1159.d014642
  calc
    MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
        (_root_.GD.N0232.N0720.N1159.d014641 m n g p hp) =
        MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014268 m n p) :=
      MemLp.toLp_congr _ _ (hallRaw g)
    _ = p := _root_.GD.N0232.N0720.N1214.d014269 m n p




theorem d015167
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p) :
    ∀ g : _root_.GD.N0232.N0720.N1482.d015118, _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p := by
  apply _root_.GD.N0232.N0720.N1482.d015166
    (m := m) (n := n) p hp hTwo hThree
  intro sequence g hsequence
  exact _root_.GD.N0232.N0720.N1482.d015163
    (m := m) (n := n) p hp (fun j ↦ (sequence j).1) g hsequence





theorem d015168
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (_root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 ∧
      _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0) ↔
      ∀ g : _root_.GD.N0232.N0720.N1482.d015118, _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s p
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  constructor
  · rintro ⟨hTwoDefect, hThreeDefect⟩
    have hTwoPoint :=
      (_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015130).1 hTwoDefect
    have hThreePoint :=
      (_root_.GD.N0232.N0720.N1159.d014651
        m n s _root_.GD.N0232.N0720.N1482.d015131).1 hThreeDefect
    have hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p := by
      have hvalue := congrArg Subtype.val hTwoPoint
      change _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p
      exact hvalue
    have hThree : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
      have hvalue := congrArg Subtype.val hThreePoint
      change _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p
      exact hvalue
    have hall := _root_.GD.N0232.N0720.N1482.d015167
      (m := m) (n := n) p hp hTwo hThree
    intro g
    apply (_root_.GD.N0232.N0720.N1159.d014651 m n s g).2
    apply Subtype.ext
    change _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p
    exact hall g
  · intro hall
    exact ⟨hall _root_.GD.N0232.N0720.N1482.d015130, hall _root_.GD.N0232.N0720.N1482.d015131⟩



noncomputable def d015169
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 +
    _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131

theorem d015170
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s := by
  exact add_nonneg
    (_root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015130)
    (_root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015131)



theorem d015171
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 ↔
      ∀ g : _root_.GD.N0232.N0720.N1482.d015118, _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  rw [_root_.GD.N0232.N0720.N1482.d015169, add_eq_zero_iff_of_nonneg
    (_root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015130)
    (_root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015131)]
  exact _root_.GD.N0232.N0720.N1482.d015168
    (m := m) (n := n) s



theorem d015172
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 ∧
        _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0 := by
  rw [_root_.GD.N0232.N0720.N1159.d014666 m n hm hn]
  constructor
  · rintro ⟨s, hs, hall⟩
    exact ⟨s, hs, hall _root_.GD.N0232.N0720.N1482.d015130, hall _root_.GD.N0232.N0720.N1482.d015131⟩
  · rintro ⟨s, hs, hTwo, hThree⟩
    exact ⟨s, hs,
      (_root_.GD.N0232.N0720.N1482.d015168
        (m := m) (n := n) s).1
        ⟨hTwo, hThree⟩⟩


theorem d015173
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  rw [_root_.GD.N0232.N0720.N1159.d014666 m n hm hn]
  constructor
  · rintro ⟨s, hstrict, hall⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1482.d015171
        (m := m) (n := n) s).2 hall⟩
  · rintro ⟨s, hstrict, hmaster⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1482.d015171
        (m := m) (n := n) s).1 hmaster⟩




theorem d015174
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) →
        0 < _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 ∨
        0 < _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 := by
  constructor
  · intro hnot s hstrict
    have hnotBoth : ¬
        (_root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 ∧
          _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0) := by
      intro hzero
      apply hnot
      exact (_root_.GD.N0232.N0720.N1482.d015172
        (m := m) (n := n) hm hn).2 ⟨s, hstrict, hzero⟩
    rcases not_and_or.mp hnotBoth with hTwo | hThree
    · left
      exact lt_of_le_of_ne (_root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015130)
        (Ne.symm hTwo)
    · right
      exact lt_of_le_of_ne
        (_root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015131)
        (Ne.symm hThree)
  · intro hobstruction hexists
    obtain ⟨s, hstrict, hTwo, hThree⟩ :=
      (_root_.GD.N0232.N0720.N1482.d015172
        (m := m) (n := n) hm hn).1 hexists
    rcases hobstruction s hstrict with hpositive | hpositive
    · exact (ne_of_gt hpositive) hTwo
    · exact (ne_of_gt hpositive) hThree



theorem d015175
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) →
        0 < _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s := by
  constructor
  · intro hnot s hstrict
    have hnonneg := _root_.GD.N0232.N0720.N1482.d015170 (m := m) (n := n) s
    exact lt_of_le_of_ne hnonneg fun hzero ↦ hnot
      ((_root_.GD.N0232.N0720.N1482.d015173
        (m := m) (n := n) hm hn).2 ⟨s, hstrict, hzero.symm⟩)
  · intro hpositive hexists
    obtain ⟨s, hstrict, hzero⟩ :=
      (_root_.GD.N0232.N0720.N1482.d015173
        (m := m) (n := n) hm hn).1 hexists
    exact (ne_of_gt (hpositive s hstrict)) hzero

end

end N1482
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1482.d015157
#print axioms _root_.GD.N0232.N0720.N1482.d015163
#print axioms _root_.GD.N0232.N0720.N1482.d015167
#print axioms _root_.GD.N0232.N0720.N1482.d015168
#print axioms _root_.GD.N0232.N0720.N1482.d015172
#print axioms _root_.GD.N0232.N0720.N1482.d015174
#print axioms _root_.GD.N0232.N0720.N1482.d015171
#print axioms _root_.GD.N0232.N0720.N1482.d015173
#print axioms _root_.GD.N0232.N0720.N1482.d015175
