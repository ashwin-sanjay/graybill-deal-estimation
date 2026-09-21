import GD.Module0977
import GD.Module0965
import GD.Module0995
import GD.Module0996








































open Filter Set Topology

namespace GD
namespace N0232
namespace N0720
namespace N1204

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1205
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1099
open _root_.GD.N0232.N0720.N1160
open _root_.GD.N0232.N0720.N1161
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)

abbrev d015773 := _root_.GD.N0232.N0720.N1482.d015118





noncomputable def d015774
    {g : _root_.GD.N0232.N0720.N1204.d015773}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (q r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  (_root_.GD.N0232.N0720.N1146.d015213 m n certificate + 1) * ‖q - r‖ +
    ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate r - r‖


theorem d015775
    {g : _root_.GD.N0232.N0720.N1204.d015773}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (q r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    0 ≤ _root_.GD.N0232.N0720.N1204.d015774 m n certificate q r := by
  unfold _root_.GD.N0232.N0720.N1204.d015774
  exact add_nonneg
    (mul_nonneg
      (add_nonneg
        (_root_.GD.N0232.N0720.N1146.d015214 m n certificate)
        zero_le_one)
      (norm_nonneg _))
    (norm_nonneg _)




theorem d015776
    {g : _root_.GD.N0232.N0720.N1204.d015773}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (q r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate q - q‖ ≤
      _root_.GD.N0232.N0720.N1204.d015774 m n certificate q r := by
  have hdecomp :
      _root_.GD.N0232.N0720.N1146.d015212 m n certificate q - q =
        (_root_.GD.N0232.N0720.N1146.d015212 m n certificate q -
            _root_.GD.N0232.N0720.N1146.d015212 m n certificate r) +
          ((_root_.GD.N0232.N0720.N1146.d015212 m n certificate r - r) +
            (r - q)) := by
    abel
  rw [hdecomp]
  calc
    ‖(_root_.GD.N0232.N0720.N1146.d015212 m n certificate q -
          _root_.GD.N0232.N0720.N1146.d015212 m n certificate r) +
        ((_root_.GD.N0232.N0720.N1146.d015212 m n certificate r - r) +
          (r - q))‖ ≤
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate q -
          _root_.GD.N0232.N0720.N1146.d015212 m n certificate r‖ +
          ‖(_root_.GD.N0232.N0720.N1146.d015212 m n certificate r - r) +
            (r - q)‖ := norm_add_le _ _
    _ ≤
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate q -
          _root_.GD.N0232.N0720.N1146.d015212 m n certificate r‖ +
          (‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate r - r‖ +
            ‖r - q‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤
        _root_.GD.N0232.N0720.N1146.d015213 m n certificate * ‖q - r‖ +
          (‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate r - r‖ +
            ‖r - q‖) := by
      gcongr
      exact _root_.GD.N0232.N0720.N1146.d015215
        m n certificate q r
    _ = _root_.GD.N0232.N0720.N1204.d015774 m n certificate q r := by
      unfold _root_.GD.N0232.N0720.N1204.d015774
      rw [norm_sub_rev]
      ring



theorem d015777
    {g : _root_.GD.N0232.N0720.N1204.d015773}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1477.d015744 m n s g =
      _root_.GD.N0232.N0720.N1146.d015212 m n certificate
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  let q := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have hqmem : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hqfinite : _root_.GD.N0232.N0720.N1159.d014637 m n q :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s q hqmem
  unfold _root_.GD.N0232.N0720.N1477.d015744
  change _root_.GD.N0232.N0720.N1159.d014642 m n g q hqfinite - q =
    _root_.GD.N0232.N0720.N1146.d015212 m n certificate q - q
  rw [_root_.GD.N0232.N0720.N1146.d015218
    m n certificate q hqfinite]



theorem d015778
    {g : _root_.GD.N0232.N0720.N1204.d015773}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖_root_.GD.N0232.N0720.N1477.d015744 m n s g‖ ≤
      _root_.GD.N0232.N0720.N1204.d015774 m n certificate
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r := by
  rw [_root_.GD.N0232.N0720.N1204.d015777
    m n certificate s]
  exact _root_.GD.N0232.N0720.N1204.d015776
    m n certificate (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r



noncomputable def d015779
    (q r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  _root_.GD.N0232.N0720.N1204.d015774 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) q r ^ 2 +
    _root_.GD.N0232.N0720.N1204.d015774 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n) q r ^ 2


theorem d015780
    (q r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    0 ≤ _root_.GD.N0232.N0720.N1204.d015779 m n q r := by
  unfold _root_.GD.N0232.N0720.N1204.d015779
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)



theorem d015781
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s ≤
      _root_.GD.N0232.N0720.N1204.d015779 m n
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r := by
  have htwo := _root_.GD.N0232.N0720.N1204.d015778
    m n (_root_.GD.N0232.N0720.N1146.d015221 m n) s r
  have hthree := _root_.GD.N0232.N0720.N1204.d015778
    m n (_root_.GD.N0232.N0720.N1146.d015222 m n) s r
  have htwoSq :
      ‖_root_.GD.N0232.N0720.N1477.d015744 m n s _root_.GD.N0232.N0720.N1482.d015130‖ ^ 2 ≤
        _root_.GD.N0232.N0720.N1204.d015774 m n
          (_root_.GD.N0232.N0720.N1146.d015221 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (_root_.GD.N0232.N0720.N1204.d015775 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) _ _)).2 htwo
  have hthreeSq :
      ‖_root_.GD.N0232.N0720.N1477.d015744 m n s _root_.GD.N0232.N0720.N1482.d015131‖ ^ 2 ≤
        _root_.GD.N0232.N0720.N1204.d015774 m n
          (_root_.GD.N0232.N0720.N1146.d015222 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (_root_.GD.N0232.N0720.N1204.d015775 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) _ _)).2 hthree
  exact add_le_add htwoSq hthreeSq





theorem d015782
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s =
      _root_.GD.N0232.N0720.N1204.d015779 m n
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
  unfold _root_.GD.N0232.N0720.N1204.d015779 _root_.GD.N0232.N0720.N1204.d015774
    _root_.GD.N0232.N0720.N1477.d015749
  simp only [sub_self, norm_zero, mul_zero, zero_add]
  rw [_root_.GD.N0232.N0720.N1204.d015777
      m n (_root_.GD.N0232.N0720.N1146.d015221 m n) s,
    _root_.GD.N0232.N0720.N1204.d015777
      m n (_root_.GD.N0232.N0720.N1146.d015222 m n) s]




theorem d015783
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1204.d015779 m n
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ≤
      _root_.GD.N0232.N0720.N1204.d015779 m n
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r := by
  rw [← _root_.GD.N0232.N0720.N1204.d015782 m n s]
  exact _root_.GD.N0232.N0720.N1204.d015781 m n s r



theorem d015784
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    IsLeast
      (Set.range (fun r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦
        _root_.GD.N0232.N0720.N1204.d015779 m n
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r))
      (_root_.GD.N0232.N0720.N1477.d015749 m n s) := by
  constructor
  · refine ⟨_root_.GD.N0232.N0720.N1159.d014633 m n s.value, ?_⟩
    exact (_root_.GD.N0232.N0720.N1204.d015782 m n s).symm
  · rintro _ ⟨r, rfl⟩
    exact _root_.GD.N0232.N0720.N1204.d015781 m n s r



theorem d015785
    {s : _root_.GD.N0232.N0720.N1159.d014639 m n} {eta : ℝ}
    (hfloor : eta ≤ _root_.GD.N0232.N0720.N1477.d015749 m n s)
    (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    eta ≤ _root_.GD.N0232.N0720.N1204.d015779 m n
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r :=
  hfloor.trans (_root_.GD.N0232.N0720.N1204.d015781 m n s r)




theorem d015786
    {s : _root_.GD.N0232.N0720.N1159.d014639 m n} {eta : ℝ}
    (heta : 0 ≤ eta)
    (hfloor : eta ≤ _root_.GD.N0232.N0720.N1477.d015749 m n s)
    (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    Real.sqrt (eta / 2) ≤
        _root_.GD.N0232.N0720.N1204.d015774 m n
          (_root_.GD.N0232.N0720.N1146.d015221 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r ∨
      Real.sqrt (eta / 2) ≤
        _root_.GD.N0232.N0720.N1204.d015774 m n
          (_root_.GD.N0232.N0720.N1146.d015222 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r := by
  let a := _root_.GD.N0232.N0720.N1204.d015774 m n
    (_root_.GD.N0232.N0720.N1146.d015221 m n)
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r
  let b := _root_.GD.N0232.N0720.N1204.d015774 m n
    (_root_.GD.N0232.N0720.N1146.d015222 m n)
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) r
  have ha : 0 ≤ a := _root_.GD.N0232.N0720.N1204.d015775 m n _ _ _
  have hb : 0 ≤ b := _root_.GD.N0232.N0720.N1204.d015775 m n _ _ _
  have hetaHalf : 0 ≤ eta / 2 := by positivity
  have hsqrtSq : (Real.sqrt (eta / 2)) ^ 2 = eta / 2 :=
    Real.sq_sqrt hetaHalf
  have hsum : eta ≤ a ^ 2 + b ^ 2 := by
    simpa [a, b, _root_.GD.N0232.N0720.N1204.d015779] using
      _root_.GD.N0232.N0720.N1204.d015785 m n hfloor r
  by_contra hnot
  push Not at hnot
  have haSq : a ^ 2 < eta / 2 := by
    nlinarith [Real.sqrt_nonneg (eta / 2)]
  have hbSq : b ^ 2 < eta / 2 := by
    nlinarith [Real.sqrt_nonneg (eta / 2)]
  nlinarith






theorem d015787
    (q r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hclose : Tendsto (fun j ↦ ‖q j - r j‖) atTop (nhds 0))
    (hfixedTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hfixedThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1204.d015779 m n (q j) (r j))
      atTop (nhds 0) := by
  have htwo : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1204.d015774 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) (q j) (r j))
      atTop (nhds 0) := by
    simpa [_root_.GD.N0232.N0720.N1204.d015774, _root_.GD.N0232.N0720.N1146.d015228]
      using
        (hclose.const_mul
          (_root_.GD.N0232.N0720.N1146.d015213 m n
            (_root_.GD.N0232.N0720.N1146.d015221 m n) + 1)).add hfixedTwo
  have hthree : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1204.d015774 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) (q j) (r j))
      atTop (nhds 0) := by
    simpa [_root_.GD.N0232.N0720.N1204.d015774,
      _root_.GD.N0232.N0720.N1146.d015229] using
        (hclose.const_mul
          (_root_.GD.N0232.N0720.N1146.d015213 m n
            (_root_.GD.N0232.N0720.N1146.d015222 m n) + 1)).add
          hfixedThree
  convert (htwo.pow 2).add (hthree.pow 2) using 1 <;>
    simp [_root_.GD.N0232.N0720.N1204.d015779]




theorem d015788
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hclose : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value - r j‖)
      atTop (nhds 0))
    (hfixedTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hfixedThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have htax := _root_.GD.N0232.N0720.N1204.d015787 m n
    (fun j ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value) r
    hclose hfixedTwo hfixedThree
  have henergy : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (seed j))
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦
        _root_.GD.N0232.N0720.N1099.d015757
          m n (seed j))
      (fun j ↦ _root_.GD.N0232.N0720.N1204.d015781
        m n (seed j) (r j)) htax
  exact _root_.GD.N0232.N0720.N1099.d015762
    m n hm hn seed hdesc henergy hstrict




noncomputable def d015789
    (B epsilon delta : ℝ) : ℝ :=
  delta + Real.sqrt
    (epsilon + 2 * Real.sqrt (B ^ 2 + epsilon) * delta + delta ^ 2)



theorem d015790
    (B : ℝ) (epsilon delta : ℕ → ℝ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hdelta : Tendsto delta atTop (nhds 0)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1204.d015789 B (epsilon j) (delta j))
      atTop (nhds 0) := by
  let F : ℝ × ℝ → ℝ := fun z ↦
    z.2 + Real.sqrt
      (z.1 + 2 * Real.sqrt (B ^ 2 + z.1) * z.2 + z.2 ^ 2)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hpair : Tendsto (fun j ↦ (epsilon j, delta j)) atTop
      (nhds ((0, 0) : ℝ × ℝ)) :=
    hepsilon.prodMk_nhds hdelta
  have hcomp := (hF.tendsto (0, 0)).comp hpair
  simpa [_root_.GD.N0232.N0720.N1204.d015789, F, Function.comp_def] using hcomp











theorem d015791
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (epsilon delta : ℕ → ℝ)
    (hdeltaNonneg : ∀ j, 0 ≤ delta j)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hdelta : Tendsto delta atTop (nhds 0))
    (hnear : ∀ j,
      Metric.infDist (r j) (_root_.GD.N0232.N0720.N1159.d014630 m n (seed (j + 1)).value) ≤
        delta j)
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ^ 2 + epsilon j)
    (hfixedTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hfixedThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let B : ℝ := ‖(seed 0).value‖
  let shiftedSeed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n := fun j ↦ seed (j + 1)
  have hcloseUpper : ∀ j,
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n (shiftedSeed j).value - r j‖ ≤
        _root_.GD.N0232.N0720.N1204.d015789 B (epsilon j) (delta j) := by
    intro j
    exact _root_.GD.N0232.N0720.N1205.d015507 m n
      (seed j) (seed (j + 1)) (hdesc j) (r j)
      (hnear j) (hdeltaNonneg j)
      (_root_.GD.N0232.N0720.N1099.d015758 m n seed hdesc j)
      (hradial j)
  have hrepairTax : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1204.d015789 B (epsilon j) (delta j))
      atTop (nhds 0) :=
    _root_.GD.N0232.N0720.N1204.d015790 B epsilon delta hepsilon hdelta
  have hclose : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n (shiftedSeed j).value - r j‖)
      atTop (nhds 0) := by
    exact squeeze_zero (fun j ↦ norm_nonneg _) hcloseUpper hrepairTax
  have hshiftDesc : ∀ j,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (shiftedSeed j).value
        (shiftedSeed (j + 1)).value := by
    intro j
    exact hdesc (j + 1)
  have hshiftStrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (shiftedSeed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
    intro theta
    exact lt_of_le_of_lt (hdesc 0 theta) (hstrict theta)
  exact _root_.GD.N0232.N0720.N1204.d015788
    m n hm hn shiftedSeed hshiftDesc hshiftStrict r hclose
      hfixedTwo hfixedThree






theorem d015792
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {s : _root_.GD.N0232.N0720.N1159.d014639 m n}
    (hs : _root_.GD.N0232.N0720.N1160.d015765 m n hm hn s) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t →
          ∀ r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
            eta ≤ _root_.GD.N0232.N0720.N1204.d015779 m n
              (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) r := by
  obtain ⟨_, eta, heta, hfloor⟩ := hs
  refine ⟨eta, heta, ?_⟩
  intro t ht r
  exact _root_.GD.N0232.N0720.N1204.d015785 m n
    (hfloor t ht) r







theorem d015793
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1160.d015765 m n hm hn s ↔
      _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s ∧
        ∃ eta : ℝ, 0 < eta ∧
          ∀ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
            _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t →
              ∀ r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
                eta ≤ _root_.GD.N0232.N0720.N1204.d015779 m n
                  (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) r := by
  constructor
  · intro hs
    obtain ⟨hsStrict, eta, heta, hfloor⟩ := hs
    refine ⟨hsStrict, eta, heta, ?_⟩
    intro t ht r
    exact _root_.GD.N0232.N0720.N1204.d015785 m n
      (hfloor t ht) r
  · rintro ⟨hsStrict, eta, heta, hfloor⟩
    refine ⟨hsStrict, eta, heta, ?_⟩
    intro t ht
    have hdiag := hfloor t ht (_root_.GD.N0232.N0720.N1159.d014633 m n t.value)
    rwa [← _root_.GD.N0232.N0720.N1204.d015782 m n t]
      at hdiag




theorem d015794
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {s : _root_.GD.N0232.N0720.N1159.d014639 m n}
    (hs : _root_.GD.N0232.N0720.N1160.d015765 m n hm hn s) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t →
          ∀ r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
            Real.sqrt (eta / 2) ≤
                _root_.GD.N0232.N0720.N1204.d015774 m n
                  (_root_.GD.N0232.N0720.N1146.d015221 m n)
                  (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) r ∨
              Real.sqrt (eta / 2) ≤
                _root_.GD.N0232.N0720.N1204.d015774 m n
                  (_root_.GD.N0232.N0720.N1146.d015222 m n)
                  (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) r := by
  obtain ⟨_, eta, heta, hfloor⟩ := hs
  refine ⟨eta, heta, ?_⟩
  intro t ht r
  exact _root_.GD.N0232.N0720.N1204.d015786
    m n heta.le (hfloor t ht) r

end
end N1204
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1204.d015776
#print axioms _root_.GD.N0232.N0720.N1204.d015781
#print axioms _root_.GD.N0232.N0720.N1204.d015782
#print axioms _root_.GD.N0232.N0720.N1204.d015783
#print axioms _root_.GD.N0232.N0720.N1204.d015784
#print axioms _root_.GD.N0232.N0720.N1204.d015788
#print axioms _root_.GD.N0232.N0720.N1204.d015790
#print axioms _root_.GD.N0232.N0720.N1204.d015791
#print axioms _root_.GD.N0232.N0720.N1204.d015792
#print axioms _root_.GD.N0232.N0720.N1204.d015793
#print axioms _root_.GD.N0232.N0720.N1204.d015794
