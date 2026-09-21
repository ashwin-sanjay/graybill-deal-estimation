import GD.Module0728
import GD.Module0764
import GD.Module0219





















open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD
namespace N0232
namespace N0719
namespace N0870

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0720.N1463
open _root_.GD.N0232.N0719.N0871



def d011575
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := theta.location
  scale := fun i ↦ if i ∈ active then theta.scale i
    else growth * theta.scale i
  scale_pos := fun i ↦ by
    by_cases hi : i ∈ active
    · simp [hi, theta.scale_pos i]
    · simp [hi, mul_pos hgrowth (theta.scale_pos i)]

@[simp] theorem d011576
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta).location =
      theta.location := rfl

@[simp] theorem d011577
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) (hi : i ∈ active) :
    (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta).scale i =
      theta.scale i := by
  simp [_root_.GD.N0232.N0719.N0870.d011575, hi]

@[simp] theorem d011578
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) (hi : i ∉ active) :
    (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta).scale i =
      growth * theta.scale i := by
  simp [_root_.GD.N0232.N0719.N0870.d011575, hi]


theorem d011579
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) (hi : i ∈ active) :
    _root_.GD.N0232.N0719.N0815.d010924
        (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) i =
      _root_.GD.N0232.N0719.N0815.d010924 theta i := by
  unfold _root_.GD.N0232.N0719.N0815.d010924
  rw [_root_.GD.N0232.N0719.N0870.d011577 active growth hgrowth theta i hi]


theorem d011580
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) (hi : i ∉ active) :
    _root_.GD.N0232.N0719.N0815.d010924
        (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) i =
      (1 / growth ^ 2) * _root_.GD.N0232.N0719.N0815.d010924 theta i := by
  unfold _root_.GD.N0232.N0719.N0815.d010924
  rw [_root_.GD.N0232.N0719.N0870.d011578
    active growth hgrowth theta i hi]
  field_simp [hgrowth.ne', (theta.scale_pos i).ne']


def d011581
    {k : ℕ} (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  ∑ i ∈ activeᶜ, _root_.GD.N0232.N0719.N0815.d010924 theta i


def d011582
    {k : ℕ} (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  ∑ i ∈ active, _root_.GD.N0232.N0719.N0815.d010924 theta i

theorem d011583
    {k : ℕ} (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 ≤ _root_.GD.N0232.N0719.N0870.d011581 active theta := by
  unfold _root_.GD.N0232.N0719.N0870.d011581
  exact Finset.sum_nonneg fun i _ ↦ (_root_.GD.N0232.N0719.N0815.d010925 theta i).le

theorem d011584
    {k : ℕ} {active : Finset (Fin k)} (hactive : active.Nonempty)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0870.d011582 active theta := by
  obtain ⟨i, hi⟩ := hactive
  unfold _root_.GD.N0232.N0719.N0870.d011582
  exact Finset.sum_pos'
    (fun j _ ↦ (_root_.GD.N0232.N0719.N0815.d010925 theta j).le)
    ⟨i, hi, _root_.GD.N0232.N0719.N0815.d010925 theta i⟩



theorem d011585
    {k : ℕ} (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010926 theta =
      _root_.GD.N0232.N0719.N0870.d011582 active theta + _root_.GD.N0232.N0719.N0870.d011581 active theta := by
  unfold _root_.GD.N0232.N0719.N0815.d010926 _root_.GD.N0232.N0719.N0870.d011582 _root_.GD.N0232.N0719.N0870.d011581
  rw [← Finset.sum_union]
  · simp
  · exact Finset.disjoint_left.mpr fun i hi hic ↦
      (Finset.mem_compl.mp hic) hi



theorem d011586
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0870.d011581 active
        (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) =
      (1 / growth ^ 2) * _root_.GD.N0232.N0719.N0870.d011581 active theta := by
  unfold _root_.GD.N0232.N0719.N0870.d011581
  calc
    ∑ i ∈ activeᶜ,
        _root_.GD.N0232.N0719.N0815.d010924
          (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) i =
        ∑ i ∈ activeᶜ,
          (1 / growth ^ 2) * _root_.GD.N0232.N0719.N0815.d010924 theta i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact _root_.GD.N0232.N0719.N0870.d011580
        active growth hgrowth theta i (by simpa using hi)
    _ = (1 / growth ^ 2) *
        ∑ i ∈ activeᶜ, _root_.GD.N0232.N0719.N0815.d010924 theta i := by
      rw [Finset.mul_sum]


theorem d011587
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0870.d011582 active
        (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) =
      _root_.GD.N0232.N0719.N0870.d011582 active theta := by
  unfold _root_.GD.N0232.N0719.N0870.d011582
  apply Finset.sum_congr rfl
  intro i hi
  exact _root_.GD.N0232.N0719.N0870.d011579
    active growth hgrowth theta i hi




theorem d011588
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010928 active
        (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) =
      ((1 / growth ^ 2) * _root_.GD.N0232.N0719.N0870.d011581 active theta) /
        (_root_.GD.N0232.N0719.N0870.d011582 active theta +
          (1 / growth ^ 2) * _root_.GD.N0232.N0719.N0870.d011581 active theta) := by
  unfold _root_.GD.N0232.N0719.N0815.d010928
  change
    _root_.GD.N0232.N0719.N0870.d011581 active
        (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) /
        _root_.GD.N0232.N0719.N0815.d010926
          (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) = _
  rw [_root_.GD.N0232.N0719.N0870.d011585,
    _root_.GD.N0232.N0719.N0870.d011587, _root_.GD.N0232.N0719.N0870.d011586]


theorem d011589
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010928 active
        (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) =
      _root_.GD.N0232.N0719.N0870.d011581 active theta /
        (growth ^ 2 * _root_.GD.N0232.N0719.N0870.d011582 active theta +
          _root_.GD.N0232.N0719.N0870.d011581 active theta) := by
  rw [_root_.GD.N0232.N0719.N0870.d011588]
  field_simp [hgrowth.ne']


def d011590
    {k : ℕ} (active : Finset (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (n : ℕ) : _root_.GD.N0232.N0719.N0859.d010809 k :=
  _root_.GD.N0232.N0719.N0870.d011575 active (n + 1 : ℝ) (by positivity) theta





def d011591
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (active : Finset (Fin k)) : Finset (Fin k) :=
  Finset.univ.filter (fun i ↦ sigma i ∈ active)

@[simp] theorem d011592
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (active : Finset (Fin k)) (i : Fin k) :
    i ∈ _root_.GD.N0232.N0719.N0870.d011591 sigma active ↔ sigma i ∈ active := by
  simp [_root_.GD.N0232.N0719.N0870.d011591]

theorem d011593
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (active : Finset (Fin k)) :
    _root_.GD.N0232.N0719.N0870.d011591 sigma active = active.map sigma.symm.toEmbedding := by
  ext i
  simp [_root_.GD.N0232.N0719.N0870.d011591]

@[simp] theorem d011594
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (active : Finset (Fin k)) :
    (_root_.GD.N0232.N0719.N0870.d011591 sigma active).card = active.card := by
  rw [_root_.GD.N0232.N0719.N0870.d011593]
  exact Finset.card_map _

theorem d011595
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    {active : Finset (Fin k)} (hactive : active.Nonempty) :
    (_root_.GD.N0232.N0719.N0870.d011591 sigma active).Nonempty := by
  obtain ⟨j, hj⟩ := hactive
  refine ⟨sigma.symm j, ?_⟩
  simp [hj]


theorem d011596
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0815.d010924 (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) i =
      _root_.GD.N0232.N0719.N0815.d010924 theta (sigma i) := by
  rfl


theorem d011597
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010926 (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) =
      _root_.GD.N0232.N0719.N0815.d010926 theta := by
  unfold _root_.GD.N0232.N0719.N0815.d010926
  simpa [_root_.GD.N0232.N0719.N0870.d011596] using
    (Equiv.sum_comp sigma (fun i ↦ _root_.GD.N0232.N0719.N0815.d010924 theta i))



theorem d011598
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0870.d011582 (_root_.GD.N0232.N0719.N0870.d011591 sigma active)
        (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) =
      _root_.GD.N0232.N0719.N0870.d011582 active theta := by
  rw [_root_.GD.N0232.N0719.N0870.d011593]
  unfold _root_.GD.N0232.N0719.N0870.d011582
  simp [_root_.GD.N0232.N0719.N0870.d011596]


theorem d011599
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0870.d011581 (_root_.GD.N0232.N0719.N0870.d011591 sigma active)
        (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) =
      _root_.GD.N0232.N0719.N0870.d011581 active theta := by
  have hsource := _root_.GD.N0232.N0719.N0870.d011585 active theta
  have htarget := _root_.GD.N0232.N0719.N0870.d011585
    (_root_.GD.N0232.N0719.N0870.d011591 sigma active) (_root_.GD.N0232.N0719.N0871.d011549 sigma theta)
  rw [_root_.GD.N0232.N0719.N0870.d011597,
    _root_.GD.N0232.N0719.N0870.d011598] at htarget
  linarith



theorem d011600
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010928 (_root_.GD.N0232.N0719.N0870.d011591 sigma active)
        (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) =
      _root_.GD.N0232.N0719.N0815.d010928 active theta := by
  unfold _root_.GD.N0232.N0719.N0815.d010928
  change _root_.GD.N0232.N0719.N0870.d011581 (_root_.GD.N0232.N0719.N0870.d011591 sigma active)
      (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) /
      _root_.GD.N0232.N0719.N0815.d010926 (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) =
    _root_.GD.N0232.N0719.N0870.d011581 active theta / _root_.GD.N0232.N0719.N0815.d010926 theta
  rw [_root_.GD.N0232.N0719.N0870.d011599,
    _root_.GD.N0232.N0719.N0870.d011597]




theorem d011601
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0871.d011549 sigma
        (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) =
      _root_.GD.N0232.N0719.N0870.d011575 (_root_.GD.N0232.N0719.N0870.d011591 sigma active)
        growth hgrowth (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) := by
  apply _root_.GD.N0232.N0719.N0845.d010880
  · rfl
  · intro i
    by_cases hi : sigma i ∈ active
    · simp [_root_.GD.N0232.N0719.N0871.d011549, _root_.GD.N0232.N0719.N0870.d011575,
        _root_.GD.N0232.N0719.N0870.d011591, hi]
    · simp [_root_.GD.N0232.N0719.N0871.d011549, _root_.GD.N0232.N0719.N0870.d011575,
        _root_.GD.N0232.N0719.N0870.d011591, hi]




theorem d011602
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (n : ℕ) :
    _root_.GD.N0232.N0719.N0871.d011549 sigma (_root_.GD.N0232.N0719.N0870.d011590 active theta n) =
      _root_.GD.N0232.N0719.N0870.d011590 (_root_.GD.N0232.N0719.N0870.d011591 sigma active)
        (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) n := by
  exact _root_.GD.N0232.N0719.N0870.d011601
    sigma active (n + 1 : ℝ) (by positivity) theta





theorem d011603
    {k : ℕ} (active : Finset (Fin k))
    (growth : ℝ) (hgrowth : 0 < growth)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation
        (_root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth theta) =
      _root_.GD.N0232.N0719.N0870.d011575 active growth hgrowth
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) := by
  apply _root_.GD.N0232.N0719.N0845.d010880
  · rfl
  · intro i
    by_cases hi : i ∈ active
    · simp [_root_.GD.N0232.N0719.N0845.d010881, _root_.GD.N0232.N0719.N0870.d011575, hi]
    · simp [_root_.GD.N0232.N0719.N0845.d010881, _root_.GD.N0232.N0719.N0870.d011575, hi,
        mul_assoc, mul_left_comm]


theorem d011604
    {k : ℕ} (active : Finset (Fin k))
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (n : ℕ) :
    _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation
        (_root_.GD.N0232.N0719.N0870.d011590 active theta n) =
      _root_.GD.N0232.N0719.N0870.d011590 active
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) n := by
  exact _root_.GD.N0232.N0719.N0870.d011603
    active (n + 1 : ℝ) (by positivity)
      shift dilation hdilation theta



theorem d011605
    {k : ℕ} (active : Finset (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (n : ℕ) :
    _root_.GD.N0232.N0719.N0870.d011581 active (_root_.GD.N0232.N0719.N0870.d011590 active theta n) =
      (1 / (n + 1 : ℝ) ^ 2) * _root_.GD.N0232.N0719.N0870.d011581 active theta := by
  exact _root_.GD.N0232.N0719.N0870.d011586
    active (n + 1 : ℝ) (by positivity) theta


theorem d011606
    {k : ℕ} (active : Finset (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (n : ℕ) :
    _root_.GD.N0232.N0719.N0815.d010928 active (_root_.GD.N0232.N0719.N0870.d011590 active theta n) =
      _root_.GD.N0232.N0719.N0870.d011581 active theta /
        ((n + 1 : ℝ) ^ 2 * _root_.GD.N0232.N0719.N0870.d011582 active theta +
          _root_.GD.N0232.N0719.N0870.d011581 active theta) := by
  exact _root_.GD.N0232.N0719.N0870.d011589
    active (n + 1 : ℝ) (by positivity) theta



theorem d011607
    {k : ℕ} {active : Finset (Fin k)} (hactive : active.Nonempty)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010928 active
        (_root_.GD.N0232.N0719.N0870.d011590 active theta n))
      atTop (nhds 0) := by
  have hgrowth :
      Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    change Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop
    exact tendsto_atTop_add_const_right
      atTop 1 tendsto_natCast_atTop_atTop
  have hgrowthSq :
      Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) ^ 2) atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hgrowth
  have hactivePos : 0 < _root_.GD.N0232.N0719.N0870.d011582 active theta :=
    _root_.GD.N0232.N0719.N0870.d011584 hactive theta
  have hden : Tendsto
      (fun n : ℕ ↦
        (n + 1 : ℝ) ^ 2 * _root_.GD.N0232.N0719.N0870.d011582 active theta +
          _root_.GD.N0232.N0719.N0870.d011581 active theta)
      atTop atTop := by
    have hmul : Tendsto
        (fun n : ℕ ↦
          _root_.GD.N0232.N0719.N0870.d011582 active theta * (n + 1 : ℝ) ^ 2)
        atTop atTop :=
      Tendsto.const_mul_atTop hactivePos hgrowthSq
    have hadd := tendsto_atTop_add_const_right
      atTop (_root_.GD.N0232.N0719.N0870.d011581 active theta) hmul
    simpa [mul_comm] using hadd
  rw [show
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010928 active
        (_root_.GD.N0232.N0719.N0870.d011590 active theta n)) =
        (fun n : ℕ ↦ _root_.GD.N0232.N0719.N0870.d011581 active theta /
          ((n + 1 : ℝ) ^ 2 * _root_.GD.N0232.N0719.N0870.d011582 active theta +
            _root_.GD.N0232.N0719.N0870.d011581 active theta)) by
      funext n
      exact _root_.GD.N0232.N0719.N0870.d011606 active theta n]
  exact tendsto_const_nhds.div_atTop hden





theorem d011608
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    {epsilon delta : ℝ} (h : epsilon ≤ delta) :
    _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active epsilon d ≤
      _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active delta d := by
  unfold _root_.GD.N0232.N0719.N0815.d010935
  apply iSup_le
  intro theta
  exact le_iSup
    (fun eta : {eta : _root_.GD.N0232.N0719.N0859.d010809 k //
        _root_.GD.N0232.N0719.N0815.d010928 active eta ≤ delta} ↦
      _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes eta.1 d)
    ⟨theta.1, theta.2.trans h⟩


theorem d011609 : Antitone _root_.GD.N0232.N0719.N0815.d010938 := by
  intro n m hnm
  unfold _root_.GD.N0232.N0719.N0815.d010938
  gcongr


theorem d011610
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    Antitone (fun n ↦ _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active
      (_root_.GD.N0232.N0719.N0815.d010938 n) d) := by
  intro n m hnm
  exact _root_.GD.N0232.N0719.N0870.d011608
    k sizes hk hsizes active d (_root_.GD.N0232.N0719.N0870.d011609 hnm)



theorem d011611
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active
        (_root_.GD.N0232.N0719.N0815.d010938 n) d)
      atTop
      (nhds (_root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d)) := by
  exact tendsto_atTop_iInf
    (_root_.GD.N0232.N0719.N0870.d011610
      k sizes hk hsizes active d)





theorem d011612
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k))
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    {boundaryRisk : ENNReal}
    (hface : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010928 active (theta n))
      atTop (nhds 0))
    (hlimit : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes (theta n) d)
      atTop (nhds boundaryRisk)) :
    boundaryRisk ≤
      _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d := by
  unfold _root_.GD.N0232.N0719.N0815.d010940
  apply le_iInf
  intro collar
  have hradius : 0 < _root_.GD.N0232.N0719.N0815.d010938 collar := by
    unfold _root_.GD.N0232.N0719.N0815.d010938
    positivity
  have heventually :
      ∀ᶠ n in atTop,
        _root_.GD.N0232.N0719.N0815.d010928 active (theta n) ≤ _root_.GD.N0232.N0719.N0815.d010938 collar :=
    ((tendsto_order.1 hface).2 (_root_.GD.N0232.N0719.N0815.d010938 collar) hradius).mono
      fun _ hn ↦ hn.le
  apply le_of_tendsto hlimit
  filter_upwards [heventually] with n hn
  exact le_iSup
    (fun eta : {eta : _root_.GD.N0232.N0719.N0859.d010809 k //
        _root_.GD.N0232.N0719.N0815.d010928 active eta ≤ _root_.GD.N0232.N0719.N0815.d010938 collar} ↦
      _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes eta.1 d)
    ⟨theta n, hn⟩







theorem d011613
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {active : Finset (Fin k)} (hactive : active.Nonempty)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    {boundaryRisk : ENNReal}
    (hlimit : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0870.d011590 active theta n) d)
      atTop (nhds boundaryRisk)) :
    boundaryRisk ≤
      _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d := by
  exact _root_.GD.N0232.N0719.N0870.d011612
    k sizes hk hsizes active
      (_root_.GD.N0232.N0719.N0870.d011590 active theta) d
      (_root_.GD.N0232.N0719.N0870.d011607
        hactive theta)
      hlimit





theorem d011614
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {active : Finset (Fin k)} (hactive : active.Nonempty)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    {boundaryRisk : ENNReal}
    (hpath : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0870.d011590 active theta n) d)
      atTop (nhds boundaryRisk))
    (hcollars : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active
        (_root_.GD.N0232.N0719.N0815.d010938 n) d)
      atTop (nhds boundaryRisk)) :
    _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d = boundaryRisk := by
  apply le_antisymm
  · apply ge_of_tendsto' hcollars
    exact fun n ↦
      iInf_le
        (fun m ↦ _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active
          (_root_.GD.N0232.N0719.N0815.d010938 m) d) n
  · exact _root_.GD.N0232.N0719.N0870.d011613
      k sizes hk hsizes hactive theta d hpath







theorem d011615
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {active : Finset (Fin k)} (hactive : active.Nonempty)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (singularBoundaryRisk : ENNReal)
    (htransport : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0870.d011590 active theta n) d)
      atTop (nhds singularBoundaryRisk)) :
    singularBoundaryRisk ≤
      _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d :=
  _root_.GD.N0232.N0719.N0870.d011613
    k sizes hk hsizes hactive theta d htransport





noncomputable def d011616
    (alpha beta l action : ℝ) : ENNReal :=
  ENNReal.ofReal (_root_.GD.N0232.N0720.N1463.d003065 alpha beta l action)




theorem d011617
    {alpha beta l : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (action : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1463.d003065 alpha beta l action := by
  unfold _root_.GD.N0232.N0720.N1463.d003065 _root_.GD.N0232.N0720.N1463.d003052
  have hleft : 0 < _root_.GD.N0232.N0720.N1463.d003059 alpha beta :=
    _root_.GD.N0232.N0720.N1463.d003061 halpha hbeta
  have hright : 0 < _root_.GD.N0232.N0720.N1463.d003060 alpha beta :=
    _root_.GD.N0232.N0720.N1463.d003062 halpha hbeta
  have hlpow : 0 < l ^ (alpha + beta) :=
    Real.rpow_pos_of_pos hl.1 _
  have hrlpow : 0 < (1 - l) ^ (alpha + beta) :=
    Real.rpow_pos_of_pos (sub_pos.mpr hl.2) _
  positivity

theorem d011618
    {alpha beta l : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (action : ℝ) :
    (_root_.GD.N0232.N0719.N0870.d011616 alpha beta l action).toReal =
      _root_.GD.N0232.N0720.N1463.d003065 alpha beta l action := by
  exact ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0719.N0870.d011617 halpha hbeta hl action)




theorem d011619
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {active : Finset (Fin k)} (hcard : active.card = 2)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (alpha beta l action : ℝ)
    (htransport : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0870.d011590 active theta n) d)
      atTop (nhds (_root_.GD.N0232.N0719.N0870.d011616 alpha beta l action))) :
    _root_.GD.N0232.N0719.N0870.d011616 alpha beta l action ≤
      _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d := by
  exact _root_.GD.N0232.N0719.N0870.d011615
    k sizes hk hsizes (active := active)
      (Finset.card_pos.mp (by omega)) theta d
      (_root_.GD.N0232.N0719.N0870.d011616 alpha beta l action) htransport



noncomputable def d011620
    (alpha beta : ℝ)
    (action : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → ℝ) : ENNReal :=
  ⨆ l : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1},
    _root_.GD.N0232.N0719.N0870.d011616 alpha beta l.1 (action l)



def d011621 :
    {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} ≃
      {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} where
  toFun l := ⟨1 - l.1, by
    constructor <;> linarith [l.2.1, l.2.2]⟩
  invFun l := ⟨1 - l.1, by
    constructor <;> linarith [l.2.1, l.2.2]⟩
  left_inv l := by
    ext
    simp
  right_inv l := by
    ext
    simp

@[simp] theorem d011622
    (l : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1}) :
    _root_.GD.N0232.N0719.N0870.d011621 (_root_.GD.N0232.N0719.N0870.d011621 l) = l := by
  apply Subtype.ext
  simp [_root_.GD.N0232.N0719.N0870.d011621]


def d011623
    (action : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → ℝ) :
    {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → ℝ :=
  fun l ↦ 1 - action (_root_.GD.N0232.N0719.N0870.d011621 l)



theorem d011624
    (alpha beta : ℝ)
    (action : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → ℝ)
    (l : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1}) :
    _root_.GD.N0232.N0719.N0870.d011616 beta alpha l.1
        (_root_.GD.N0232.N0719.N0870.d011623 action l) =
      _root_.GD.N0232.N0719.N0870.d011616 alpha beta
        (_root_.GD.N0232.N0719.N0870.d011621 l).1
        (action (_root_.GD.N0232.N0719.N0870.d011621 l)) := by
  unfold _root_.GD.N0232.N0719.N0870.d011616 _root_.GD.N0232.N0719.N0870.d011623 _root_.GD.N0232.N0719.N0870.d011621
  congr 1
  simpa using _root_.GD.N0232.N0720.N1463.d003068
    alpha beta (1 - l.1) (action ⟨1 - l.1, by
      constructor <;> linarith [l.2.1, l.2.2]⟩)



theorem d011625
    (alpha beta : ℝ)
    (action : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → ℝ) :
    _root_.GD.N0232.N0719.N0870.d011620 beta alpha (_root_.GD.N0232.N0719.N0870.d011623 action) =
      _root_.GD.N0232.N0719.N0870.d011620 alpha beta action := by
  apply le_antisymm
  · unfold _root_.GD.N0232.N0719.N0870.d011620
    apply iSup_le
    intro l
    rw [_root_.GD.N0232.N0719.N0870.d011624]
    exact le_iSup
      (fun z : {z : ℝ // z ∈ Set.Ioo (0 : ℝ) 1} ↦
        _root_.GD.N0232.N0719.N0870.d011616 alpha beta z.1 (action z))
      (_root_.GD.N0232.N0719.N0870.d011621 l)
  · unfold _root_.GD.N0232.N0719.N0870.d011620
    apply iSup_le
    intro l
    have hreflect := _root_.GD.N0232.N0719.N0870.d011624
      alpha beta action (_root_.GD.N0232.N0719.N0870.d011621 l)
    have hpoint :
        _root_.GD.N0232.N0719.N0870.d011616 alpha beta l.1 (action l) =
          _root_.GD.N0232.N0719.N0870.d011616 beta alpha
            (_root_.GD.N0232.N0719.N0870.d011621 l).1
            (_root_.GD.N0232.N0719.N0870.d011623 action (_root_.GD.N0232.N0719.N0870.d011621 l)) := by
      simpa using hreflect.symm
    rw [hpoint]
    exact le_iSup
      (fun z : {z : ℝ // z ∈ Set.Ioo (0 : ℝ) 1} ↦
        _root_.GD.N0232.N0719.N0870.d011616 beta alpha z.1
          (_root_.GD.N0232.N0719.N0870.d011623 action z))
      (_root_.GD.N0232.N0719.N0870.d011621 l)




theorem d011626
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {active : Finset (Fin k)} (hcard : active.card = 2)
    (theta :
      {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (alpha beta : ℝ)
    (action : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → ℝ)
    (htransport : ∀ l,
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0870.d011590 active (theta l) n) d)
        atTop
        (nhds (_root_.GD.N0232.N0719.N0870.d011616
          alpha beta l.1 (action l)))) :
    _root_.GD.N0232.N0719.N0870.d011620 alpha beta action ≤
      _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d := by
  unfold _root_.GD.N0232.N0719.N0870.d011620
  apply iSup_le
  intro l
  exact _root_.GD.N0232.N0719.N0870.d011619
    k sizes hk hsizes hcard (theta l) d alpha beta l.1 (action l)
      (htransport l)




theorem d011627
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {active : Finset (Fin k)} (hcard : active.card = 2)
    (theta :
      {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (alpha beta : ℝ)
    (action : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → ℝ)
    (htransport : ∀ l,
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0870.d011590 active (theta l) n) d)
        atTop
        (nhds (_root_.GD.N0232.N0719.N0870.d011616
          alpha beta l.1 (action l))))
    (hrecovery :
      _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d ≤
        _root_.GD.N0232.N0719.N0870.d011620 alpha beta action) :
    _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d =
      _root_.GD.N0232.N0719.N0870.d011620 alpha beta action := by
  apply le_antisymm hrecovery
  exact _root_.GD.N0232.N0719.N0870.d011626
    k sizes hk hsizes hcard theta d alpha beta action htransport




theorem d011628
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {active : Finset (Fin k)} (hcard : active.card = 2)
    (theta :
      {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (alpha beta : ℝ)
    (action : {l : ℝ // l ∈ Set.Ioo (0 : ℝ) 1} → ℝ)
    (hpointwise : ∀ l,
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0870.d011590 active (theta l) n) d)
        atTop
        (nhds (_root_.GD.N0232.N0719.N0870.d011616
          alpha beta l.1 (action l))))
    (huniform : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active
        (_root_.GD.N0232.N0719.N0815.d010938 n) d)
      atTop (nhds (_root_.GD.N0232.N0719.N0870.d011620 alpha beta action))) :
    _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d =
      _root_.GD.N0232.N0719.N0870.d011620 alpha beta action := by
  apply le_antisymm
  · apply ge_of_tendsto' huniform
    exact fun n ↦
      iInf_le
        (fun m ↦ _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active
          (_root_.GD.N0232.N0719.N0815.d010938 m) d) n
  · exact _root_.GD.N0232.N0719.N0870.d011626
      k sizes hk hsizes hcard theta d alpha beta action hpointwise

end

end N0870
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0870.d011580
#print axioms _root_.GD.N0232.N0719.N0870.d011586
#print axioms _root_.GD.N0232.N0719.N0870.d011587
#print axioms _root_.GD.N0232.N0719.N0870.d011589
#print axioms _root_.GD.N0232.N0719.N0870.d011607
#print axioms _root_.GD.N0232.N0719.N0870.d011602
#print axioms _root_.GD.N0232.N0719.N0870.d011600
#print axioms _root_.GD.N0232.N0719.N0870.d011611
#print axioms _root_.GD.N0232.N0719.N0870.d011612
#print axioms _root_.GD.N0232.N0719.N0870.d011613
#print axioms _root_.GD.N0232.N0719.N0870.d011614
#print axioms _root_.GD.N0232.N0719.N0870.d011615
#print axioms _root_.GD.N0232.N0719.N0870.d011619
#print axioms _root_.GD.N0232.N0719.N0870.d011625
#print axioms _root_.GD.N0232.N0719.N0870.d011626
#print axioms _root_.GD.N0232.N0719.N0870.d011627
#print axioms _root_.GD.N0232.N0719.N0870.d011628
