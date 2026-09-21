import GD.Module1170
import GD.Module1039
import Mathlib.NumberTheory.Real.Irrational



















open Filter Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1369

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1219
open _root_.GD.N0232.N0720.N1355
open _root_.GD.N0232.N0720.N1370
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1133

variable {m n : ℕ}



abbrev d018798 := Set.Ioo (0 : ℝ) 1


def d018799 (k : ℕ) : Set _root_.GD.N0232.N0720.N1369.d018798 :=
  {z | 1 / ((k : ℝ) + 2) ≤ (z : ℝ) ∧
    (z : ℝ) ≤ 1 - 1 / ((k : ℝ) + 2)}



theorem d018800 (k : ℕ) :
    _root_.GD.N0232.N0720.N1369.d018799 k ⊆ (Set.univ : Set _root_.GD.N0232.N0720.N1369.d018798) := by
  intro z hz
  trivial



def d018801
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1369.d018798 → _root_.GD.N0232.N0720.N1080.d014168 :=
  fun z ↦ _root_.GD.N0232.N0720.N1219.d017942 m n hm hn z.1 z.2

@[fun_prop]
theorem d018802
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Continuous (_root_.GD.N0232.N0720.N1369.d018801 m n hm hn) := by
  apply (_root_.GD.N0232.N0720.N1499.d014996.comp_continuous_iff).mp
  change Continuous (fun z : _root_.GD.N0232.N0720.N1369.d018798 ↦
    ((0 : ℝ),
      (Real.sqrt ((m : ℝ) * (1 - (z : ℝ))),
        Real.sqrt ((n : ℝ) * (z : ℝ)))))
  fun_prop


theorem d018803
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  intro theta
  rw [_root_.GD.N0232.N0720.N1080.d014184 m n hm hn theta]
  exact ENNReal.ofReal_ne_top



theorem d018804
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
  _root_.GD.N0232.N0720.N1159.d014644 m n s
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1


theorem d018805
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    Continuous (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n theta q).toReal) := by
  apply continuous_iff_continuousAt.2
  intro theta
  exact
    (ENNReal.continuousAt_toReal
      (x := _root_.GD.N0232.N0720.N1080.d014182 m n theta q) (hq theta)).tendsto.comp
        (_root_.GD.N0232.N0720.N1133.d016587 m n q hq).continuousAt



def d018806
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (z : _root_.GD.N0232.N0720.N1369.d018798) : ℝ :=
  (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1369.d018801 m n hm hn z)
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).toReal -
    (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1369.d018801 m n hm hn z)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal



theorem d018807
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Continuous (_root_.GD.N0232.N0720.N1369.d018806 hm hn s) := by
  unfold _root_.GD.N0232.N0720.N1369.d018806
  exact
    (_root_.GD.N0232.N0720.N1369.d018805
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) (_root_.GD.N0232.N0720.N1369.d018803 m n hm hn)).comp
        (_root_.GD.N0232.N0720.N1369.d018802 m n hm hn) |>.sub
      ((_root_.GD.N0232.N0720.N1369.d018805
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1369.d018804 s)).comp
          (_root_.GD.N0232.N0720.N1369.d018802 m n hm hn))


theorem d018808
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1370.d018790 hm hn s ↔
      ∀ z : _root_.GD.N0232.N0720.N1369.d018798,
        0 < _root_.GD.N0232.N0720.N1369.d018806 hm hn s z := by
  constructor
  · intro h z
    have hlt := h z.1 z.2
    have hreal :
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1369.d018801 m n hm hn z)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal <
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1369.d018801 m n hm hn z)
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).toReal :=
      (ENNReal.toReal_lt_toReal
        (_root_.GD.N0232.N0720.N1369.d018804 s _)
        (_root_.GD.N0232.N0720.N1369.d018803 m n hm hn _)).2 hlt
    unfold _root_.GD.N0232.N0720.N1369.d018806
    linarith
  · intro h z hz
    let z' : _root_.GD.N0232.N0720.N1369.d018798 := ⟨z, hz⟩
    have hgap := h z'
    have hreal :
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1369.d018801 m n hm hn z')
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal <
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1369.d018801 m n hm hn z')
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).toReal := by
      unfold _root_.GD.N0232.N0720.N1369.d018806 at hgap
      linarith
    exact (ENNReal.toReal_lt_toReal
      (_root_.GD.N0232.N0720.N1369.d018804 s _)
      (_root_.GD.N0232.N0720.N1369.d018803 m n hm hn _)).1 hreal




def d018809 (f : _root_.GD.N0232.N0720.N1369.d018798 → ℝ) : Prop :=
  ∀ k : ℕ, ∃ epsilon : ℝ, 0 < epsilon ∧
    ∀ z : _root_.GD.N0232.N0720.N1369.d018798, z ∈ _root_.GD.N0232.N0720.N1369.d018799 k → epsilon ≤ f z

private theorem d018810 (k : ℕ) :
    0 < 1 / ((k : ℝ) + 2) := by positivity

private theorem d018811 (k : ℕ) :
    1 / ((k : ℝ) + 2) ≤ (1 / 2 : ℝ) := by
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
  norm_num

private theorem d018812 (k : ℕ) :
    (1 / 2 : ℝ) ≤ 1 - 1 / ((k : ℝ) + 2) := by
  have h := _root_.GD.N0232.N0720.N1369.d018811 k
  linarith

private theorem d018813 (k : ℕ) :
    (_root_.GD.N0232.N0720.N1369.d018799 k).Nonempty := by
  let half : _root_.GD.N0232.N0720.N1369.d018798 := ⟨1 / 2, by norm_num⟩
  exact ⟨half, _root_.GD.N0232.N0720.N1369.d018811 k, _root_.GD.N0232.N0720.N1369.d018812 k⟩

private theorem d018814 (k : ℕ) :
    IsCompact (_root_.GD.N0232.N0720.N1369.d018799 k) := by
  rw [Subtype.isCompact_iff]
  have himage :
      ((↑) '' _root_.GD.N0232.N0720.N1369.d018799 k : Set ℝ) =
        Set.Icc (1 / ((k : ℝ) + 2))
          (1 - 1 / ((k : ℝ) + 2)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      have hxOpen : x ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor
        · exact lt_of_lt_of_le (_root_.GD.N0232.N0720.N1369.d018810 k) hx.1
        · have hleft := _root_.GD.N0232.N0720.N1369.d018810 k
          exact lt_of_le_of_lt hx.2 (by linarith)
      exact ⟨⟨x, hxOpen⟩, hx, rfl⟩
  rw [himage]
  exact isCompact_Icc

private theorem d018815 (z : _root_.GD.N0232.N0720.N1369.d018798) :
    ∃ k : ℕ, z ∈ _root_.GD.N0232.N0720.N1369.d018799 k := by
  have hmin : 0 < min (z : ℝ) (1 - (z : ℝ)) :=
    lt_min z.2.1 (sub_pos.mpr z.2.2)
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / min (z : ℝ) (1 - (z : ℝ)))
  refine ⟨k, ?_, ?_⟩
  · have hkR : 1 / min (z : ℝ) (1 - (z : ℝ)) < (k : ℝ) := by
      exact_mod_cast hk
    have hkpos : 0 < (k : ℝ) + 2 := by positivity
    have hrecip : 1 / ((k : ℝ) + 2) < min (z : ℝ) (1 - (z : ℝ)) := by
      apply (one_div_lt hkpos hmin).2
      exact lt_trans hkR (by linarith)
    exact (lt_min_iff.mp hrecip).1.le
  · have hkR : 1 / min (z : ℝ) (1 - (z : ℝ)) < (k : ℝ) := by
      exact_mod_cast hk
    have hkpos : 0 < (k : ℝ) + 2 := by positivity
    have hrecip : 1 / ((k : ℝ) + 2) < min (z : ℝ) (1 - (z : ℝ)) := by
      apply (one_div_lt hkpos hmin).2
      exact lt_trans hkR (by linarith)
    have hright := (lt_min_iff.mp hrecip).2
    linarith




theorem d018816
    (f : _root_.GD.N0232.N0720.N1369.d018798 → ℝ) (hf : Continuous f) :
    (∀ z : _root_.GD.N0232.N0720.N1369.d018798, 0 < f z) ↔ _root_.GD.N0232.N0720.N1369.d018809 f := by
  constructor
  · intro hpos k
    obtain ⟨z, hz, hmin⟩ :=
      (_root_.GD.N0232.N0720.N1369.d018814 k).exists_isMinOn
        (_root_.GD.N0232.N0720.N1369.d018813 k) hf.continuousOn
    exact ⟨f z, hpos z, fun y hy ↦ hmin hy⟩
  · intro hmargins z
    obtain ⟨k, hzk⟩ := _root_.GD.N0232.N0720.N1369.d018815 z
    obtain ⟨epsilon, hepsilon, hbound⟩ := hmargins k
    exact lt_of_lt_of_le hepsilon (hbound z hzk)



theorem d018817
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1370.d018790 hm hn s ↔
      _root_.GD.N0232.N0720.N1369.d018809 (_root_.GD.N0232.N0720.N1369.d018806 hm hn s) := by
  rw [_root_.GD.N0232.N0720.N1369.d018808]
  exact _root_.GD.N0232.N0720.N1369.d018816 _
    (_root_.GD.N0232.N0720.N1369.d018807 hm hn s)



theorem d018818
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1355.d018776 weight s ≤
            _root_.GD.N0232.N0720.N1355.d018777 s ∧
          _root_.GD.N0232.N0720.N1369.d018809
            (_root_.GD.N0232.N0720.N1369.d018806 hm hn s) := by
  rw [_root_.GD.N0232.N0720.N1370.d018797
    hm hn weight hweight0 hweight1]
  apply exists_congr
  intro s
  rw [_root_.GD.N0232.N0720.N1369.d018817]




def d018819 (z : _root_.GD.N0232.N0720.N1369.d018798) : ℝ :=
  (z : ℝ) * (1 - (z : ℝ))

theorem d018820 :
    Continuous _root_.GD.N0232.N0720.N1369.d018819 := by
  unfold _root_.GD.N0232.N0720.N1369.d018819
  fun_prop

theorem d018821 (z : _root_.GD.N0232.N0720.N1369.d018798) :
    0 < _root_.GD.N0232.N0720.N1369.d018819 z := by
  exact mul_pos z.2.1 (sub_pos.mpr z.2.2)



theorem d018822 :
    ¬ ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ z : _root_.GD.N0232.N0720.N1369.d018798, epsilon ≤ _root_.GD.N0232.N0720.N1369.d018819 z := by
  rintro ⟨epsilon, hepsilon, hbound⟩
  by_cases he : epsilon ≤ 1
  · let z : _root_.GD.N0232.N0720.N1369.d018798 := ⟨epsilon / 2, by constructor <;> linarith⟩
    have hz := hbound z
    unfold _root_.GD.N0232.N0720.N1369.d018819 at hz
    change epsilon ≤ (epsilon / 2) * (1 - epsilon / 2) at hz
    nlinarith [mul_pos hepsilon (sub_pos.mpr (by linarith : epsilon / 2 < 1))]
  · let z : _root_.GD.N0232.N0720.N1369.d018798 := ⟨1 / 2, by norm_num⟩
    have hz := hbound z
    unfold _root_.GD.N0232.N0720.N1369.d018819 at hz
    norm_num at hz
    linarith

theorem d018823 :
    _root_.GD.N0232.N0720.N1369.d018809 _root_.GD.N0232.N0720.N1369.d018819 :=
  (_root_.GD.N0232.N0720.N1369.d018816
    _root_.GD.N0232.N0720.N1369.d018819 _root_.GD.N0232.N0720.N1369.d018820).1
      _root_.GD.N0232.N0720.N1369.d018821


def d018824 : Set _root_.GD.N0232.N0720.N1369.d018798 :=
  {z | (z : ℝ) ∈ Set.range ((↑) : ℚ → ℝ)}


theorem d018825 :
    Dense _root_.GD.N0232.N0720.N1369.d018824 := by
  rw [Subtype.dense_iff]
  intro x hx
  have hopen : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hdense : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  have hclosure :
      x ∈ closure (Set.Ioo (0 : ℝ) 1 ∩
        Set.range ((↑) : ℚ → ℝ)) :=
    hdense.open_subset_closure_inter hopen hx
  apply (closure_mono ?_) hclosure
  rintro y ⟨hy, q, rfl⟩
  exact ⟨⟨(q : ℝ), hy⟩, ⟨q, rfl⟩, rfl⟩


def d018826 : _root_.GD.N0232.N0720.N1369.d018798 :=
  ⟨Real.sqrt 2 / 2, by
    have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    constructor
    · positivity
    · nlinarith⟩

theorem d018827 :
    Irrational (_root_.GD.N0232.N0720.N1369.d018826 : ℝ) := by
  change Irrational (Real.sqrt 2 / 2)
  exact irrational_sqrt_two.div_ratCast (q := (2 : ℚ)) (by norm_num)


def d018828 (z : _root_.GD.N0232.N0720.N1369.d018798) : ℝ :=
  if z = _root_.GD.N0232.N0720.N1369.d018826 then 0 else 1



theorem d018829
    (z : _root_.GD.N0232.N0720.N1369.d018798) (hz : z ∈ _root_.GD.N0232.N0720.N1369.d018824) :
    0 < _root_.GD.N0232.N0720.N1369.d018828 z := by
  obtain ⟨q, hq⟩ := hz
  have hne : z ≠ _root_.GD.N0232.N0720.N1369.d018826 := by
    intro h
    have hcast : (_root_.GD.N0232.N0720.N1369.d018826 : ℝ) = (q : ℝ) := by
      rw [← h]
      exact hq.symm
    exact (_root_.GD.N0232.N0720.N1369.d018827.ne_rat q) hcast
  simp [_root_.GD.N0232.N0720.N1369.d018828, hne]


theorem d018830 :
    ¬ ∀ z : _root_.GD.N0232.N0720.N1369.d018798, 0 < _root_.GD.N0232.N0720.N1369.d018828 z := by
  intro h
  simpa [_root_.GD.N0232.N0720.N1369.d018828] using h _root_.GD.N0232.N0720.N1369.d018826

end

end N1369
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1369.d018807
#print axioms _root_.GD.N0232.N0720.N1369.d018816
#print axioms _root_.GD.N0232.N0720.N1369.d018817
#print axioms _root_.GD.N0232.N0720.N1369.d018818
#print axioms _root_.GD.N0232.N0720.N1369.d018822
#print axioms _root_.GD.N0232.N0720.N1369.d018825
#print axioms _root_.GD.N0232.N0720.N1369.d018830
