import GD.Module0794
import GD.Module0792
import GD.Module0780
import GD.Module0746
import GD.Module0782
set_option maxHeartbeats 1200000































open Filter Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0952

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0820
open _root_.GD.N0232.N0719.N0817
open _root_.GD.N0232.N0719.N0957
open _root_.GD.N0232.N0719.N0934
open _root_.GD.N0232.N0719.N0898
open _root_.GD.N0232.N0719.N0847
open _root_.GD.N0232.N0719.N0846
open _root_.GD.N0232.N0719.N0848
open _root_.GD.N0232.N0719.N0822






theorem d012062
    {k : ℕ} (first second : Finset (Fin k))
    (x y : Fin k → ℝ)
    (hxFirst : _root_.GD.N0232.N0719.N0957.d012044 first x ≠ 0)
    (hyFirst : _root_.GD.N0232.N0719.N0957.d012044 first y ≠ 0)
    (hxSecond : _root_.GD.N0232.N0719.N0957.d012044 second x ≠ 0)
    (hySecond : _root_.GD.N0232.N0719.N0957.d012044 second y ≠ 0) :
    _root_.GD.N0232.N0719.N0957.d012045 first x = _root_.GD.N0232.N0719.N0957.d012045 first y ↔
      _root_.GD.N0232.N0719.N0957.d012045 second x = _root_.GD.N0232.N0719.N0957.d012045 second y := by
  constructor
  · intro h
    have h' := congrArg (_root_.GD.N0232.N0719.N0957.d012045 second) h
    rw [_root_.GD.N0232.N0719.N0957.d012048 first second x hxFirst hxSecond,
      _root_.GD.N0232.N0719.N0957.d012048 first second y hyFirst hySecond] at h'
    exact h'
  · intro h
    have h' := congrArg (_root_.GD.N0232.N0719.N0957.d012045 first) h
    rw [_root_.GD.N0232.N0719.N0957.d012048 second first x hxSecond hxFirst,
      _root_.GD.N0232.N0719.N0957.d012048 second first y hySecond hyFirst] at h'
    exact h'



theorem d012063
    {k : ℕ} (active : Finset (Fin k)) (x : Fin k → ℝ)
    (hmass : _root_.GD.N0232.N0719.N0957.d012044 active x ≠ 0) :
    _root_.GD.N0232.N0719.N0957.d012045 active x = x ↔ _root_.GD.N0232.N0719.N0957.d012044 active x = 1 := by
  constructor
  · intro hfix
    have hmassEq := congrArg (_root_.GD.N0232.N0719.N0957.d012044 active) hfix
    rw [_root_.GD.N0232.N0719.N0957.d012047, div_self hmass] at hmassEq
    exact hmassEq.symm
  · intro hone
    funext i
    simp [_root_.GD.N0232.N0719.N0957.d012045, hone]




theorem d012064
    {k : ℕ} (first second : Finset (Fin k))
    (x : Fin k → ℝ)
    (hfirst : _root_.GD.N0232.N0719.N0957.d012044 first x ≠ 0)
    (hsecond : _root_.GD.N0232.N0719.N0957.d012044 second x ≠ 0)
    (hx : _root_.GD.N0232.N0719.N0957.d012045 first x = x) :
    _root_.GD.N0232.N0719.N0957.d012045 first (_root_.GD.N0232.N0719.N0957.d012045 second x) = x ∧
      _root_.GD.N0232.N0719.N0957.d012045 second (_root_.GD.N0232.N0719.N0957.d012045 first x) = _root_.GD.N0232.N0719.N0957.d012045 second x := by
  constructor
  · rw [_root_.GD.N0232.N0719.N0957.d012048 second first x hsecond hfirst, hx]
  · exact _root_.GD.N0232.N0719.N0957.d012048 first second x hfirst hsecond





theorem d012065
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010881 theta.location (_root_.GD.N0232.N0719.N0845.d010886 theta)
        (_root_.GD.N0232.N0719.N0845.d010887 hk theta) (_root_.GD.N0232.N0719.N0845.d010890 hk theta) = theta := by
  apply _root_.GD.N0232.N0719.N0845.d010880
  · simp
  · intro i
    simp only [_root_.GD.N0232.N0719.N0845.d010883, _root_.GD.N0232.N0719.N0845.d010892]
    field_simp [(_root_.GD.N0232.N0719.N0845.d010887 hk theta).ne']



theorem d012066
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta =
      _root_.GD.N0232.N0719.N0845.d010886 theta ^ 2 *
        _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta) := by
  calc
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta =
        _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0845.d010881 theta.location (_root_.GD.N0232.N0719.N0845.d010886 theta)
            (_root_.GD.N0232.N0719.N0845.d010887 (by omega : 0 < k) theta)
            (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta)) := by
      rw [_root_.GD.N0232.N0719.N0952.d012065
        (by omega : 0 < k) theta]
    _ = _root_.GD.N0232.N0719.N0845.d010886 theta ^ 2 *
        _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta) :=
      _root_.GD.N0232.N0719.N0845.d010897 k sizes hk hsizes
        theta.location (_root_.GD.N0232.N0719.N0845.d010886 theta)
        (_root_.GD.N0232.N0719.N0845.d010887 (by omega : 0 < k) theta)
        (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta)




theorem d012067
    {k : ℕ} (hk : 0 < k)
    (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k) (shape : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hshapeLocation : shape.location = 0)
    (locationLimit scaleLimit : ℝ) (hscaleLimit : 0 < scaleLimit)
    (hnormalized : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0845.d010890 hk (thetaSeq n))
      atTop (nhds shape))
    (hlocation : Tendsto (fun n ↦ (thetaSeq n).location)
      atTop (nhds locationLimit))
    (htotalScale : Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq n))
      atTop (nhds scaleLimit)) :
    Tendsto thetaSeq atTop
      (nhds (_root_.GD.N0232.N0719.N0845.d010881 locationLimit scaleLimit hscaleLimit shape)) := by
  rw [(_root_.GD.N0232.N0719.N0859.d011199 k).tendsto_nhds_iff]
  change Tendsto
    (fun n ↦ ((thetaSeq n).location, (thetaSeq n).scale)) atTop
    (nhds
      ((_root_.GD.N0232.N0719.N0845.d010881 locationLimit scaleLimit hscaleLimit shape).location,
        (_root_.GD.N0232.N0719.N0845.d010881 locationLimit scaleLimit hscaleLimit shape).scale))
  simp only [_root_.GD.N0232.N0719.N0845.d010882,
    hshapeLocation, mul_zero, add_zero]
  apply hlocation.prodMk_nhds
  apply tendsto_pi_nhds.mpr
  intro i
  have hshapeCoordinate : Tendsto
      (fun n ↦ (_root_.GD.N0232.N0719.N0845.d010890 hk (thetaSeq n)).scale i)
      atTop (nhds (shape.scale i)) :=
    ((_root_.GD.N0232.N0719.N0859.d011203 k i).tendsto shape).comp hnormalized
  have hproduct := htotalScale.mul hshapeCoordinate
  convert hproduct using 1
  · funext n
    simp only [_root_.GD.N0232.N0719.N0845.d010892]
    field_simp [(_root_.GD.N0232.N0719.N0845.d010887 hk (thetaSeq n)).ne']
  · simp only [_root_.GD.N0232.N0719.N0845.d010883]






def d012068 {k : ℕ}
    (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k) : Prop :=
  ∃ extraction : ℕ → ℕ,
    Tendsto extraction atTop atTop ∧
    ∃ locationLimit scaleLimit : ℝ,
      0 < scaleLimit ∧
      Tendsto (fun n ↦ (thetaSeq (extraction n)).location)
        atTop (nhds locationLimit) ∧
      Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n)))
        atTop (nhds scaleLimit)












theorem d012069
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    ¬ _root_.GD.N0232.N0719.N0952.d012068 z.1.thetaSeq := by
  rintro ⟨extraction, hextraction, locationLimit, scaleLimit,
    hscaleLimit, hlocation, htotalScale⟩
  have hnormalized : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k)
        (z.1.thetaSeq (extraction n))) atTop
      (nhds (_root_.GD.N0232.N0719.N0817.d011944 z hfull)) :=
    (_root_.GD.N0232.N0719.N0817.d011950 z hfull).comp hextraction
  have hparameter : Tendsto (fun n ↦ z.1.thetaSeq (extraction n)) atTop
      (nhds (_root_.GD.N0232.N0719.N0845.d010881 locationLimit scaleLimit hscaleLimit
        (_root_.GD.N0232.N0719.N0817.d011944 z hfull))) :=
    _root_.GD.N0232.N0719.N0952.d012067
      (by omega : 0 < k) (fun n ↦ z.1.thetaSeq (extraction n))
      (_root_.GD.N0232.N0719.N0817.d011944 z hfull)
      (_root_.GD.N0232.N0719.N0817.d011945 z hfull)
      locationLimit scaleLimit hscaleLimit hnormalized
      hlocation htotalScale
  let B : ℝ := scaleLimit + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hscaleBound : ∀ᶠ n in atTop,
      _root_.GD.N0232.N0719.N0845.d010886 (z.1.thetaSeq (extraction n)) < B :=
    htotalScale.eventually (Iio_mem_nhds (by dsimp [B]; linarith))
  let C : ℝ := B ^ 2 * (k : ℝ)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hcap : ∀ᶠ n in atTop,
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (z.1.thetaSeq (extraction n)) ≤ C := by
    filter_upwards [hscaleBound] with n hn
    rw [_root_.GD.N0232.N0719.N0952.d012066
      k sizes hk hsizes (z.1.thetaSeq (extraction n))]
    have hscalePos : 0 < _root_.GD.N0232.N0719.N0845.d010886 (z.1.thetaSeq (extraction n)) :=
      _root_.GD.N0232.N0719.N0845.d010887 (by omega : 0 < k) (z.1.thetaSeq (extraction n))
    have hscaleSq : _root_.GD.N0232.N0719.N0845.d010886 (z.1.thetaSeq (extraction n)) ^ 2 ≤ B ^ 2 := by
      nlinarith
    have hnormalizedCap :
        _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k)
            (z.1.thetaSeq (extraction n))) ≤ (k : ℝ) :=
      (_root_.GD.N0232.N0719.N0934.d011163
        k sizes hk hsizes (z.1.thetaSeq (extraction n))).le
    exact (mul_le_mul_of_nonneg_right hscaleSq
      (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k)
          (z.1.thetaSeq (extraction n)))).le).trans
      (mul_le_mul_of_nonneg_left hnormalizedCap (sq_nonneg B))
  rcases z.2 with
    ⟨hp, hq, hpq, _hw, _hsupport, _hactive, _hdepth,
      _hweights, _hinactive, _hlower, htax, _hpGap, _hqGap⟩
  have htaxSub : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes
        (z.1.thetaSeq (extraction n)) z.1.p z.1.q)
      atTop (nhds 0) := htax.comp hextraction
  exact (_root_.GD.N0232.N0719.N0898.d011915
    k sizes hk hsizes
    (fun n ↦ z.1.thetaSeq (extraction n))
    (_root_.GD.N0232.N0719.N0845.d010881 locationLimit scaleLimit hscaleLimit
      (_root_.GD.N0232.N0719.N0817.d011944 z hfull))
    hp hq hpq hparameter C hC hcap) htaxSub





structure d012070
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) where
  witness : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes
  fullSupport : witness.1.active = Finset.univ
  normalizedBaseConverges :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k)
        (witness.1.thetaSeq n)) atTop
      (nhds (_root_.GD.N0232.N0719.N0817.d011944 witness fullSupport))
  noLiveAffineGaugeCluster :
    ¬ _root_.GD.N0232.N0719.N0952.d012068 witness.1.thetaSeq


def d012071
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  Nonempty (_root_.GD.N0232.N0719.N0952.d012070 k sizes hk hsizes)



theorem d012072
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    _root_.GD.N0232.N0719.N0952.d012071 k sizes hk hsizes := by
  exact ⟨⟨z, hfull,
    _root_.GD.N0232.N0719.N0817.d011950 z hfull,
    _root_.GD.N0232.N0719.N0952.d012069 z hfull⟩⟩




theorem d012073
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0848.d012024 k sizes hk hsizes ↔
      _root_.GD.N0232.N0719.N0952.d012071 k sizes hk hsizes := by
  constructor
  · rintro ⟨z⟩
    exact _root_.GD.N0232.N0719.N0952.d012072
      z.witness z.fullSupport
  · rintro ⟨z⟩
    exact ⟨⟨z.witness, z.fullSupport, z.normalizedBaseConverges⟩⟩









theorem d012074
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      _root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
      _root_.GD.N0232.N0719.N0848.d012022
        k sizes hk hsizes ∨
      _root_.GD.N0232.N0719.N0952.d012071
        k sizes hk hsizes := by
  rcases _root_.GD.N0232.N0719.N0848.d012027
      k sizes hk hsizes with hterminal | hlow | hproper | hfull
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hlow)
  · exact Or.inr (Or.inr (Or.inl hproper))
  · exact Or.inr (Or.inr (Or.inr
      ((_root_.GD.N0232.N0719.N0952.d012073
        k sizes hk hsizes).1 hfull)))




theorem d012075
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      (_root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes ∧
        (_root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
          _root_.GD.N0232.N0719.N0848.d012022
            k sizes hk hsizes ∨
          _root_.GD.N0232.N0719.N0952.d012071
            k sizes hk hsizes)) := by
  rcases _root_.GD.N0232.N0719.N0848.d012028
      k sizes hk hsizes with hterminal | ⟨hphysical, hsupport⟩
  · exact Or.inl hterminal
  · refine Or.inr ⟨hphysical, ?_⟩
    rcases hsupport with hlow | hproper | hfull
    · exact Or.inl hlow
    · exact Or.inr (Or.inl hproper)
    · exact Or.inr (Or.inr
        ((_root_.GD.N0232.N0719.N0952.d012073
          k sizes hk hsizes).1 hfull))















theorem d012076
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      ∃ z : _root_.GD.N0232.N0719.N0822.d011886
          k sizes hk hsizes,
        z.localized.1.1.active.card ≤ 2 ∨
        (3 ≤ z.localized.1.1.active.card ∧
          z.localized.1.1.active.card < k) ∨
        (z.localized.1.1.active = Finset.univ ∧
          ¬ _root_.GD.N0232.N0719.N0952.d012068 z.localized.1.1.thetaSeq) := by
  rcases _root_.GD.N0232.N0719.N0822.d011891
      k sizes hk hsizes with hterminal | hsync
  · exact Or.inl hterminal
  · obtain ⟨z⟩ := hsync
    right
    refine ⟨z, ?_⟩
    rcases _root_.GD.N0232.N0719.N0822.d011890 z with hlow | hthree
    · exact Or.inl hlow
    · by_cases hproper : z.localized.1.1.active.card < k
      · exact Or.inr (Or.inl ⟨hthree, hproper⟩)
      · right
        right
        have hle : z.localized.1.1.active.card ≤ k := by
          simpa using Finset.card_le_univ z.localized.1.1.active
        have hcard : z.localized.1.1.active.card = k := by omega
        have hfull : z.localized.1.1.active = Finset.univ :=
          Finset.eq_univ_of_card z.localized.1.1.active (by simpa using hcard)
        exact ⟨hfull,
          _root_.GD.N0232.N0719.N0952.d012069
            z.localized.1 hfull⟩

end

end N0952
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0952.d012062
#print axioms _root_.GD.N0232.N0719.N0952.d012064
#print axioms _root_.GD.N0232.N0719.N0952.d012066
#print axioms _root_.GD.N0232.N0719.N0952.d012067
#print axioms _root_.GD.N0232.N0719.N0952.d012069
#print axioms _root_.GD.N0232.N0719.N0952.d012073
#print axioms _root_.GD.N0232.N0719.N0952.d012074
#print axioms _root_.GD.N0232.N0719.N0952.d012075
#print axioms _root_.GD.N0232.N0719.N0952.d012076
