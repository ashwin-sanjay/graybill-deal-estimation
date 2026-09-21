import GD.Module1269
import GD.Module0755
import GD.Module1232

set_option autoImplicit false
set_option warningAsError true
















open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0213.N0496

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0990
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0989
open _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1324
open _root_.GD.N0232.N0720.N1321
  (d020069)

abbrev d021972 (d : ℕ) := _root_.GD.N0232.N0720.N1341.d004414 d

variable {k d : ℕ}

def d021973 (p : _root_.GD.N0232.N0719.N0983.d009709 k) : Fin k → ℝ := fun i => _root_.GD.N0232.N0719.N0983.d009710 i p

theorem d021974 (p : _root_.GD.N0232.N0719.N0983.d009709 k) (i : Fin k) :
    0 ≤ _root_.GD.N0213.N0496.d021973 p i := (_root_.GD.N0232.N0719.N0983.d009710 i p).property.1

theorem d021975 (p : _root_.GD.N0232.N0719.N0983.d009709 k) : ∑ i, _root_.GD.N0213.N0496.d021973 p i = 1 :=
  _root_.GD.N0232.N0719.N0983.d009712 p

def d021976 (lo hi : ℝ) : Set (_root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :=
  {x | (∀ i, x.1 i ∈ Ioo lo hi) ∧ ∀ i, x.2 i ∈ Ioo (1 / 2 : ℝ) 2}

theorem d021977 (p : _root_.GD.N0232.N0719.N0983.d009709 k) (a : Fin k → ℝ) (lo hi : ℝ)
    (ha : ∀ i, a i ∈ Icc lo hi) :
    (∑ i, _root_.GD.N0213.N0496.d021973 p i * a i) ∈ Icc lo hi := by
  constructor
  · calc
      lo = ∑ i, _root_.GD.N0213.N0496.d021973 p i * lo := by rw [← Finset.sum_mul, _root_.GD.N0213.N0496.d021975, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (ha i).1 (_root_.GD.N0213.N0496.d021974 p i)
  · calc
      _ ≤ ∑ i, _root_.GD.N0213.N0496.d021973 p i * hi := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (ha i).2 (_root_.GD.N0213.N0496.d021974 p i)
      _ = hi := by rw [← Finset.sum_mul, _root_.GD.N0213.N0496.d021975, one_mul]

theorem d021978 (p : _root_.GD.N0232.N0719.N0983.d009709 k) {lo hi : ℝ}
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)}
    (hlo : 0 ≤ lo) (hx : x ∈ _root_.GD.N0213.N0496.d021976 lo hi) :
    _root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0213.N0496.d021973 p) x ∈ Icc lo hi ∧
      _root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0213.N0496.d021973 p) x ∈ Icc (lo ^ 2 + 1) (hi ^ 2 + 4) := by
  refine ⟨_root_.GD.N0213.N0496.d021977 p x.1 lo hi (fun i => ⟨(hx.1 i).1.le, (hx.1 i).2.le⟩), ?_⟩
  apply _root_.GD.N0213.N0496.d021977
  intro i
  have hy0 : 0 ≤ x.1 i := hlo.trans (hx.1 i).1.le
  have hhi : 0 ≤ hi := hy0.trans (hx.1 i).2.le
  have hl := (sq_le_sq₀ hlo hy0).2 (hx.1 i).1.le
  have hu := (sq_le_sq₀ hy0 hhi).2 (hx.1 i).2.le
  constructor <;> linarith [(hx.2 i).1, (hx.2 i).2]

theorem d021979 (p : _root_.GD.N0232.N0719.N0983.d009709 k) {lo hi level delta : ℝ}
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)}
    (hlo : 0 < lo) (hx : x ∈ _root_.GD.N0213.N0496.d021976 lo hi)
    (hlevel : hi ≤ level + delta) (hmargin : (level + delta - lo) * hi ≤ 1) :
    level + delta ≤ _root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0213.N0496.d021973 p) x / _root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0213.N0496.d021973 p) x := by
  have hB : 0 < _root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0213.N0496.d021973 p) x :=
    hlo.trans_le (_root_.GD.N0213.N0496.d021978 p hlo.le hx).1.1
  apply (le_div_iff₀ hB).2
  unfold _root_.GD.N0232.N0719.N0989.d011340 _root_.GD.N0232.N0719.N0989.d011339
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hy0 : 0 ≤ x.1 i := (hlo.trans (hx.1 i).1).le
  have hg : 0 ≤ level + delta - lo := by linarith [(hx.1 i).1, (hx.1 i).2]
  have hm := mul_le_mul_of_nonneg_left (hx.1 i).2.le hg
  have hl := mul_le_mul_of_nonneg_right (hx.1 i).1.le hy0
  have hs : (level + delta) * x.1 i ≤ (x.1 i) ^ 2 + 2 * x.2 i := by
    nlinarith [(hx.2 i).1]
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hs (_root_.GD.N0213.N0496.d021974 p i)

theorem d021980 (p : _root_.GD.N0232.N0719.N0983.d009709 k) {lo hi beta : ℝ}
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)}
    (hlo : 0 < lo) (hx : x ∈ _root_.GD.N0213.N0496.d021976 lo hi)
    (hbeta : 0 ≤ beta) (hrate : 2 * beta * (hi ^ 2 + 4) ≤ lo ^ 2) :
    beta ≤ _root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0213.N0496.d021973 p) x ^ 2 / (2 * _root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0213.N0496.d021973 p) x) := by
  obtain ⟨hB, hA⟩ := _root_.GD.N0213.N0496.d021978 p hlo.le hx
  have hApos : 0 < _root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0213.N0496.d021973 p) x := by nlinarith [hA.1, sq_nonneg lo]
  apply (le_div_iff₀ (mul_pos (by norm_num) hApos)).2
  have hs := (sq_le_sq₀ hlo.le (hlo.trans_le hB.1).le).2 hB.1
  have hu := mul_le_mul_of_nonneg_left hA.2 (by positivity : 0 ≤ 2 * beta)
  nlinarith

theorem d021981 (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1) :
    Continuous (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim) := by
  apply (_root_.GD.N0232.N0719.N0986.d020365 sizes).comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun x : _root_.GD.N0213.N0496.d021972 d => x (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i, j⟩))
  fun_prop

theorem d021982 (lo hi : ℝ) : IsOpen (_root_.GD.N0213.N0496.d021976 (k := k) lo hi) := by
  simp only [_root_.GD.N0213.N0496.d021976, setOf_and, setOf_forall]
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage
      (show Continuous (fun x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) => x.1 i) by
        fun_prop)
  · exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage
      (show Continuous (fun x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) => x.2 i) by
        fun_prop)

theorem d021983 (sizes : Fin k → ℕ)
    (hdim : (∑ i, sizes i) = d + 1) (hn : ∀ i, 2 ≤ sizes i)
    {lo hi : ℝ} (hwidth : lo < hi) {P : _root_.GD.N0213.N0496.d021972 d → Prop}
    (hP : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), P x) :
    ∃ x : _root_.GD.N0213.N0496.d021972 d, _root_.GD.N0232.N0719.N0990.d020512 sizes hdim x ∈ _root_.GD.N0213.N0496.d021976 lo hi ∧ P x := by
  let U := _root_.GD.N0232.N0719.N0990.d020512 sizes hdim ⁻¹' _root_.GD.N0213.N0496.d021976 lo hi
  have hopen : IsOpen U := (_root_.GD.N0213.N0496.d021982 lo hi).preimage (_root_.GD.N0213.N0496.d021981 sizes hdim)
  have hne : U.Nonempty := by
    let y : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) := (fun _ => (lo + hi) / 2, fun _ => 1)
    have hy : y ∈ _root_.GD.N0232.N0719.N0982.d020342 := fun _ => zero_lt_one
    refine ⟨_root_.GD.N0232.N0719.N0997.d019807 sizes hdim (_root_.GD.N0232.N0719.N0986.d020372 sizes hn y), ?_⟩
    change _root_.GD.N0232.N0719.N0986.d020362 sizes ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm
      (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim (_root_.GD.N0232.N0719.N0986.d020372 sizes hn y))) ∈ _root_.GD.N0213.N0496.d021976 lo hi
    rw [MeasurableEquiv.symm_apply_apply, _root_.GD.N0232.N0719.N0986.d020375 sizes hn hy]
    constructor
    · intro i; constructor <;> dsimp [y] <;> linarith
    · intro i; constructor <;> norm_num [y]
  have hpos := hopen.measure_pos volume hne
  by_contra hnot
  have hempty : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), x ∉ U := by
    filter_upwards [hP] with x hx hu
    exact hnot ⟨x, hu, hx⟩
  have hzero : (volume : Measure (_root_.GD.N0213.N0496.d021972 d)) U = 0 := by
    simpa only [ae_iff, not_not, setOf_mem_eq] using hempty
  exact hpos.ne' hzero

variable {I : Type*} [Fintype I]

def d021984 (d : ℕ) (p : I → _root_.GD.N0232.N0719.N0990.d020496 k) (weight : I → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) : ℝ :=
  (∑ i, weight i * _root_.GD.N0232.N0719.N0990.d020511 (d := d) (p i) x) /
    (∑ i, weight i * _root_.GD.N0232.N0719.N0990.d020510 (d := d) (p i) x)

theorem d021985 (p : I → _root_.GD.N0232.N0719.N0990.d020496 k) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hprob : ∑ i, weight i = 1)
    {lo hi : ℝ} {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)}
    (hlo : 0 ≤ lo) (hx : x ∈ _root_.GD.N0213.N0496.d021976 lo hi) :
    0 < ∑ i, weight i * _root_.GD.N0232.N0719.N0990.d020510 (d := d) (p i) x := by
  have hp (i : I) : 0 < _root_.GD.N0232.N0719.N0990.d020510 (d := d) (p i) x := by
    apply _root_.GD.N0232.N0720.N1377.d002861
    have h := (_root_.GD.N0213.N0496.d021978 (p i).2 hlo hx).2.1
    simp only [_root_.GD.N0232.N0719.N0989.d011339, _root_.GD.N0213.N0496.d021973] at h ⊢
    nlinarith [sq_nonneg lo]
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)).1
    (show 0 < ∑ i, weight i by rw [hprob]; norm_num)
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (hp i).le)
    ⟨j, Finset.mem_univ j, mul_pos hj (hp j)⟩

theorem d021986 (hd : 1 ≤ d)
    (p : I → _root_.GD.N0232.N0719.N0990.d020496 k) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hprob : ∑ i, weight i = 1)
    {lo hi level delta beta cutoff : ℝ}
    (hlo : 0 < lo) (hbeta : 0 ≤ beta) (hdelta : 0 ≤ delta)
    (hlevel : hi ≤ level + delta) (hmargin : (level + delta - lo) * hi ≤ 1)
    (hrate : 2 * beta * (hi ^ 2 + 4) ≤ lo ^ 2) (hcutoff : 1 ≤ cutoff)
    (hthreshold : 2 * ((d + 1 : ℕ) : ℝ) * (hi ^ 2 + 4) ^ 2 ≤ delta * lo ^ 3 * cutoff ^ 2)
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0213.N0496.d021976 lo hi)
    (hposterior : _root_.GD.N0213.N0496.d021984 d p weight x ≤ level) :
    (∑ i, weight i * (if cutoff ≤ (p i).1 then
      (delta / 2 * _root_.GD.N0232.N0720.N1324.d002946 (d + 1) (hi ^ 2 + 4) lo) *
        Real.exp (beta * (p i).1 ^ 2) else 0)) ≤
      ((d + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 d (lo ^ 2 + 1) (hi * cutoff) / lo := by
  have hparameters (i : I) := _root_.GD.N0213.N0496.d021978 (p i).2 hlo.le hx
  have h := _root_.GD.N0232.N0720.N1324.d002956 (d + 1) (by omega) weight
    (fun i => _root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0213.N0496.d021973 (p i).2) x)
    (fun i => _root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0213.N0496.d021973 (p i).2) x) (fun i => (p i).1)
    (by positivity) (fun i => (hparameters i).2.1) (fun i => (hparameters i).2.2)
    hlo (fun i => (hparameters i).1.1) (fun i => (hparameters i).1.2)
    hdelta hcutoff (fun i => _root_.GD.N0213.N0496.d021979 (p i).2 hlo hx hlevel hmargin)
    (fun i => _root_.GD.N0213.N0496.d021980 (p i).2 hlo hx hbeta hrate) hthreshold hw hprob
    (by simpa [_root_.GD.N0232.N0719.N0990.d020510, _root_.GD.N0232.N0719.N0989.d011346, _root_.GD.N0232.N0719.N0989.d011339, _root_.GD.N0232.N0719.N0989.d011340, Nat.add_assoc, _root_.GD.N0213.N0496.d021973] using
      _root_.GD.N0213.N0496.d021985 (d := d) p weight hw hprob hlo.le hx)
    (by simpa [_root_.GD.N0213.N0496.d021984, _root_.GD.N0232.N0719.N0990.d020510, _root_.GD.N0232.N0719.N0990.d020511, _root_.GD.N0232.N0719.N0989.d011346, _root_.GD.N0232.N0719.N0989.d011339, _root_.GD.N0232.N0719.N0989.d011340, Nat.add_assoc,
      _root_.GD.N0213.N0496.d021973] using hposterior)
  simpa only [Nat.add_sub_cancel] using h

variable {Index : ℕ → Type*} [∀ j, Fintype (Index j)]

theorem d021987
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (hn : ∀ i, 2 ≤ sizes i) (hd : 1 ≤ d)
    (p : ∀ j, Index j → _root_.GD.N0232.N0719.N0990.d020496 k) (weight : ∀ j, Index j → ℝ)
    (hw : ∀ j i, 0 ≤ weight j i) (hprob : ∀ j, ∑ i, weight j i = 1)
    (f : _root_.GD.N0213.N0496.d021972 d → ℝ)
    (hlim : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), Tendsto
      (fun j => _root_.GD.N0213.N0496.d021984 d (p j) (weight j) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x)) atTop (𝓝 (f x)))
    (hupper : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
      ∀ c : ℝ, (∀ i, (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x).1 i ≤ c) → f x ≤ c)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ c C cutoff : ℝ, 0 < c ∧ 1 ≤ cutoff ∧ ∀ᶠ j in atTop,
      (∑ i, weight j i * (if cutoff ≤ (p j i).1 then
        c * Real.exp (beta * (p j i).1 ^ 2) else 0)) ≤ C := by
  obtain ⟨lo, hi, level, delta, hlo, hwidth, hlevel, hdelta, hgap, hmargin, hrate⟩ :=
    _root_.GD.N0232.N0720.N1383.d004678 hbeta hhalf
  obtain ⟨cutoff, hcutoff, hthreshold⟩ :=
    _root_.GD.N0232.N0720.N1321.d020069 (d + 1) (Amax := hi ^ 2 + 4) hlo hdelta
  obtain ⟨x, hx, hxlim, hxupper⟩ := _root_.GD.N0213.N0496.d021983 sizes hdim hn hwidth
    (hlim.and hupper)
  have hf : f x < level :=
    (hxupper hi (fun i => (hx.1 i).2.le)).trans_lt hlevel
  refine ⟨delta / 2 * _root_.GD.N0232.N0720.N1324.d002946 (d + 1) (hi ^ 2 + 4) lo,
    ((d + 1 : ℕ) : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 d (lo ^ 2 + 1) (hi * cutoff) / lo,
    cutoff, mul_pos (by positivity) (_root_.GD.N0232.N0720.N1324.d002947 _ (by positivity) hlo),
    hcutoff, ?_⟩
  filter_upwards [hxlim.eventually (gt_mem_nhds hf)] with j hj
  exact _root_.GD.N0213.N0496.d021986 hd (p j) (weight j) (hw j) (hprob j)
    hlo hbeta hdelta.le hgap hmargin hrate hcutoff hthreshold hx hj.le


def d021988 (p : _root_.GD.N0232.N0719.N0990.d020496 k) : _root_.GD.N0232.N0719.N0990.d020496 k := (-p.1, p.2)

def d021989 (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :
    _root_.GD.N0232.N0719.N0873.d011295 (Fin k) := (-x.1, x.2)

theorem d021990 (p : Fin k → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :
    _root_.GD.N0232.N0719.N0989.d011339 p (_root_.GD.N0213.N0496.d021989 x) = _root_.GD.N0232.N0719.N0989.d011339 p x := by
  simp [_root_.GD.N0232.N0719.N0989.d011339, _root_.GD.N0213.N0496.d021989]

theorem d021991 (p : Fin k → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :
    _root_.GD.N0232.N0719.N0989.d011340 p (_root_.GD.N0213.N0496.d021989 x) = -_root_.GD.N0232.N0719.N0989.d011340 p x := by
  simp [_root_.GD.N0232.N0719.N0989.d011340, _root_.GD.N0213.N0496.d021989, Finset.sum_neg_distrib]

theorem d021992 (p : _root_.GD.N0232.N0719.N0990.d020496 k)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :
    _root_.GD.N0232.N0719.N0990.d020510 (d := d) (_root_.GD.N0213.N0496.d021988 p) x = _root_.GD.N0232.N0719.N0990.d020510 (d := d) p (_root_.GD.N0213.N0496.d021989 x) := by
  simp [_root_.GD.N0232.N0719.N0990.d020510, _root_.GD.N0232.N0719.N0989.d011346, _root_.GD.N0213.N0496.d021988, _root_.GD.N0213.N0496.d021990, _root_.GD.N0213.N0496.d021991]

theorem d021993 (p : _root_.GD.N0232.N0719.N0990.d020496 k)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :
    _root_.GD.N0232.N0719.N0990.d020511 (d := d) (_root_.GD.N0213.N0496.d021988 p) x = -_root_.GD.N0232.N0719.N0990.d020511 (d := d) p (_root_.GD.N0213.N0496.d021989 x) := by
  simp [_root_.GD.N0232.N0719.N0990.d020511, _root_.GD.N0232.N0719.N0989.d011346, _root_.GD.N0213.N0496.d021988, _root_.GD.N0213.N0496.d021990, _root_.GD.N0213.N0496.d021991]

theorem d021994 (p : I → _root_.GD.N0232.N0719.N0990.d020496 k) (weight : I → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :
    _root_.GD.N0213.N0496.d021984 d (fun i => _root_.GD.N0213.N0496.d021988 (p i)) weight x = -_root_.GD.N0213.N0496.d021984 d p weight (_root_.GD.N0213.N0496.d021989 x) := by
  simp only [_root_.GD.N0213.N0496.d021984, _root_.GD.N0213.N0496.d021992, _root_.GD.N0213.N0496.d021993,
    mul_neg, Finset.sum_neg_distrib, neg_div]

theorem d021995 (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (x : _root_.GD.N0213.N0496.d021972 d) :
    _root_.GD.N0232.N0719.N0990.d020512 sizes hdim (-x) = _root_.GD.N0213.N0496.d021989 (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) := by
  have hflat : (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm (-x) = -(_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x := by
    funext i j
    rfl
  unfold _root_.GD.N0232.N0719.N0990.d020512
  rw [hflat]
  let z := (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x
  have hmean (i : Fin k) : _root_.GD.N0232.N0719.N0986.d020360 sizes (-z) i = -_root_.GD.N0232.N0719.N0986.d020360 sizes z i := by
    simp [_root_.GD.N0232.N0719.N0986.d020360, Finset.sum_neg_distrib, neg_div]
  apply Prod.ext
  · funext i
    exact hmean i
  · funext i
    change _root_.GD.N0232.N0719.N0986.d020361 sizes (-z) i = _root_.GD.N0232.N0719.N0986.d020361 sizes z i
    simp only [_root_.GD.N0232.N0719.N0986.d020361, hmean, Pi.neg_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem d021996
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (hn : ∀ i, 2 ≤ sizes i) (hd : 1 ≤ d)
    (p : ∀ j, Index j → _root_.GD.N0232.N0719.N0990.d020496 k) (weight : ∀ j, Index j → ℝ)
    (hw : ∀ j i, 0 ≤ weight j i) (hprob : ∀ j, ∑ i, weight j i = 1)
    (f : _root_.GD.N0213.N0496.d021972 d → ℝ)
    (hlim : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), Tendsto
      (fun j => _root_.GD.N0213.N0496.d021984 d (p j) (weight j) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x)) atTop (𝓝 (f x)))
    (hlower : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
      ∀ c : ℝ, (∀ i, c ≤ (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x).1 i) → c ≤ f x)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ c C cutoff : ℝ, 0 < c ∧ 1 ≤ cutoff ∧ ∀ᶠ j in atTop,
      (∑ i, weight j i * (if cutoff ≤ -(p j i).1 then
        c * Real.exp (beta * (p j i).1 ^ 2) else 0)) ≤ C := by
  have hreflect := (Measure.measurePreserving_neg (volume : Measure (_root_.GD.N0213.N0496.d021972 d))).quasiMeasurePreserving.ae
    (hlim.and hlower)
  have hlim' : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), Tendsto
      (fun j => _root_.GD.N0213.N0496.d021984 d (fun i => _root_.GD.N0213.N0496.d021988 (p j i)) (weight j)
        (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x)) atTop (𝓝 (-f (-x))) := by
    filter_upwards [hreflect] with x hx
    simpa only [_root_.GD.N0213.N0496.d021994, ← _root_.GD.N0213.N0496.d021995 sizes hdim] using hx.1.neg
  have hupper : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
      ∀ c : ℝ, (∀ i, (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x).1 i ≤ c) → -f (-x) ≤ c := by
    filter_upwards [hreflect] with x hx
    intro c hc
    have hf := hx.2 (-c) (fun i => by
      rw [_root_.GD.N0213.N0496.d021995]
      exact neg_le_neg (hc i))
    simpa using neg_le_neg hf
  obtain ⟨c, C, cutoff, hc, hcutoff, hbudget⟩ := _root_.GD.N0213.N0496.d021987
    sizes hdim hn hd (fun j i => _root_.GD.N0213.N0496.d021988 (p j i)) weight hw hprob
    (fun x => -f (-x)) hlim' hupper hbeta hhalf
  exact ⟨c, C, cutoff, hc, hcutoff, by simpa only [_root_.GD.N0213.N0496.d021988, neg_sq] using hbudget⟩

theorem d021997 (a weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hprob : ∑ i, weight i = 1)
    {beta cp cn Cp Cn Rp Rn : ℝ} (hbeta : 0 ≤ beta)
    (hcp : 0 < cp) (hcn : 0 < cn) (hRp : 1 ≤ Rp)
    (hp : (∑ i, weight i * (if Rp ≤ a i then cp * Real.exp (beta * a i ^ 2) else 0)) ≤ Cp)
    (hn : (∑ i, weight i * (if Rn ≤ -a i then cn * Real.exp (beta * a i ^ 2) else 0)) ≤ Cn) :
    (∑ i, weight i * Real.exp (beta * a i ^ 2)) ≤
      Cp / cp + Cn / cn + Real.exp (beta * (max Rp Rn) ^ 2) := by
  classical
  let P (i : I) : ℝ := if Rp ≤ a i then cp * Real.exp (beta * a i ^ 2) else 0
  let M (i : I) : ℝ := if Rn ≤ -a i then cn * Real.exp (beta * a i ^ 2) else 0
  let E : ℝ := Real.exp (beta * (max Rp Rn) ^ 2)
  have hP (i : I) : 0 ≤ P i := by dsimp [P]; split_ifs <;> positivity
  have hM (i : I) : 0 ≤ M i := by dsimp [M]; split_ifs <;> positivity
  have hpoint (i : I) : Real.exp (beta * a i ^ 2) ≤ P i / cp + M i / cn + E := by
    by_cases hpi : Rp ≤ a i
    · have heq : P i / cp = Real.exp (beta * a i ^ 2) := by
        simp only [P, if_pos hpi, mul_div_cancel_left₀ _ hcp.ne']
      rw [heq]
      have hmn := div_nonneg (hM i) hcn.le
      have he : 0 ≤ E := (Real.exp_pos _).le
      linarith
    by_cases hni : Rn ≤ -a i
    · have heq : M i / cn = Real.exp (beta * a i ^ 2) := by
        simp only [M, if_pos hni, mul_div_cancel_left₀ _ hcn.ne']
      rw [heq]
      have hpn := div_nonneg (hP i) hcp.le
      have he : 0 ≤ E := (Real.exp_pos _).le
      linarith
    have habs : |a i| ≤ max Rp Rn := by
      apply abs_le.mpr
      constructor
      · have hl := le_max_right Rp Rn
        linarith [lt_of_not_ge hni]
      · exact (le_of_not_ge hpi).trans (le_max_left _ _)
    have hR : 0 ≤ max Rp Rn := (zero_le_one.trans hRp).trans (le_max_left _ _)
    have hs : a i ^ 2 ≤ max Rp Rn ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 habs
    have he : Real.exp (beta * a i ^ 2) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs hbeta)
    exact he.trans (by linarith [div_nonneg (hP i) hcp.le, div_nonneg (hM i) hcn.le])
  calc
    _ ≤ ∑ i, weight i * (P i / cp + M i / cn + E) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hw i)
    _ = (∑ i, weight i * P i) / cp + (∑ i, weight i * M i) / cn + E := by
      simp only [mul_add, ← mul_div_assoc, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.sum_mul, hprob, one_mul]
    _ ≤ _ := add_le_add (add_le_add
      (div_le_div_of_nonneg_right hp hcp.le) (div_le_div_of_nonneg_right hn hcn.le)) le_rfl

theorem d021998 (f : ℕ → ℝ) {C : ℝ}
    (h : ∀ᶠ n in atTop, f n ≤ C) : ∃ B : ℝ, ∀ n, f n ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max C (∑ j ∈ Finset.range N, |f j|), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_max_left _ _)
  · have hs : |f n| ≤ ∑ j ∈ Finset.range N, |f j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_range.mpr (lt_of_not_ge hn))
    exact ((le_abs_self _).trans hs).trans (le_max_right _ _)

theorem d021999
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (hn : ∀ i, 2 ≤ sizes i) (hd : 1 ≤ d)
    (p : ∀ j, Index j → _root_.GD.N0232.N0719.N0990.d020496 k) (weight : ∀ j, Index j → ℝ)
    (hw : ∀ j i, 0 ≤ weight j i) (hprob : ∀ j, ∑ i, weight j i = 1)
    (f : _root_.GD.N0213.N0496.d021972 d → ℝ)
    (hlim : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), Tendsto
      (fun j => _root_.GD.N0213.N0496.d021984 d (p j) (weight j) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x)) atTop (𝓝 (f x)))
    (hupper : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
      ∀ c : ℝ, (∀ i, (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x).1 i ≤ c) → f x ≤ c)
    (hlower : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
      ∀ c : ℝ, (∀ i, c ≤ (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x).1 i) → c ≤ f x)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ B : ℝ, ∀ j, (∑ i, weight j i * Real.exp (beta * (p j i).1 ^ 2)) ≤ B := by
  obtain ⟨cp, Cp, Rp, hcp, hRp, hp⟩ := _root_.GD.N0213.N0496.d021987
    sizes hdim hn hd p weight hw hprob f hlim hupper hbeta hhalf
  obtain ⟨cn, Cn, Rn, hcn, _hRn, hn'⟩ := _root_.GD.N0213.N0496.d021996
    sizes hdim hn hd p weight hw hprob f hlim hlower hbeta hhalf
  apply _root_.GD.N0213.N0496.d021998
  filter_upwards [hp, hn'] with j hpj hnj
  exact _root_.GD.N0213.N0496.d021997 (fun i => (p j i).1) (weight j) (hw j) (hprob j)
    hbeta hcp hcn hRp hpj hnj

end
end GD.N0213.N0496

#print axioms _root_.GD.N0213.N0496.d021987

#print axioms _root_.GD.N0213.N0496.d021996
#print axioms _root_.GD.N0213.N0496.d021999
