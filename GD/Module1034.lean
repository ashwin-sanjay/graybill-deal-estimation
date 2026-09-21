import GD.Module0752
import GD.Module1030


















open MeasureTheory
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1124

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false





theorem d016497
    (location scale x : ℝ) (hscale : 0 < scale) :
    _root_.GD.N0232.N0719.N0932.d009204 location scale x =
      scale⁻¹ * Real.exp
        (x ^ 2 / 2 - (x - location) ^ 2 / (2 * scale ^ 2)) := by
  rw [_root_.GD.N0232.N0719.N1011.d011282 location scale x hscale.ne']
  have hsqrt :
      Real.sqrt (2 * Real.pi * scale ^ 2) =
        scale * Real.sqrt (2 * Real.pi) := by
    calc
      Real.sqrt (2 * Real.pi * scale ^ 2) =
          Real.sqrt (scale ^ 2 * (2 * Real.pi)) := by ring_nf
      _ = Real.sqrt (scale ^ 2) * Real.sqrt (2 * Real.pi) := by
        rw [Real.sqrt_mul (sq_nonneg scale)]
      _ = scale * Real.sqrt (2 * Real.pi) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  rw [hsqrt]
  have hroot : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp [hscale.ne', hroot]



theorem d016498
    (g : _root_.GD.N0232.N0719.N0946.d009229) (location scale x : ℝ)
    (hscale : 0 < scale) :
    _root_.GD.N0232.N0719.N0932.d009204
        (g.shift + g.d009239 * location) (g.d009239 * scale)
        (g.shift + g.d009239 * x) =
      _root_.GD.N0232.N0719.N0932.d009204 g.shift g.d009239
          (g.shift + g.d009239 * x) *
        _root_.GD.N0232.N0719.N0932.d009204 location scale x := by
  rw [_root_.GD.N0232.N0720.N1124.d016497 _ _ _
        (mul_pos g.d009240 hscale),
    _root_.GD.N0232.N0720.N1124.d016497 _ _ _ g.d009240,
    _root_.GD.N0232.N0720.N1124.d016497 _ _ _ hscale]
  have hg : g.d009239 ≠ 0 := g.d009241
  have hs : scale ≠ 0 := hscale.ne'
  have hfront : (g.d009239 * scale)⁻¹ =
      g.d009239⁻¹ * scale⁻¹ := by
    rw [mul_inv_rev]
    ring
  have hexponent :
      (g.shift + g.d009239 * x) ^ 2 / 2 -
          (g.shift + g.d009239 * x -
              (g.shift + g.d009239 * location)) ^ 2 /
            (2 * (g.d009239 * scale) ^ 2) =
        ((g.shift + g.d009239 * x) ^ 2 / 2 -
            (g.shift + g.d009239 * x - g.shift) ^ 2 /
              (2 * g.d009239 ^ 2)) +
          (x ^ 2 / 2 - (x - location) ^ 2 / (2 * scale ^ 2)) := by
    field_simp [hg, hs]
    ring_nf
  rw [hfront, hexponent, Real.exp_add]
  ring


theorem d016499
    (sampleSize : ℕ) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (location scale : ℝ) (hscale : 0 < scale)
    (x : _root_.GD.N0137.d008894 sampleSize) :
    _root_.GD.N0232.N0719.N0932.d009213 sampleSize
        (g.shift + g.d009239 * location) (g.d009239 * scale)
        (_root_.GD.N0107.d009018
          sampleSize g.shift g.d009239 x) =
      _root_.GD.N0232.N0719.N0932.d009213 sampleSize g.shift g.d009239
          (_root_.GD.N0107.d009018
            sampleSize g.shift g.d009239 x) *
        _root_.GD.N0232.N0719.N0932.d009213 sampleSize location scale x := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  simp_rw [_root_.GD.N0107.d009018,
    _root_.GD.N0232.N0720.N1124.d016498 g location scale _ hscale]
  exact Finset.prod_mul_distrib



theorem d016500
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) (g • omega) =
      _root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
        _root_.GD.N0232.N0720.N1499.d015001 m n theta omega := by
  rw [_root_.GD.N0232.N0720.N1214.d014259]
  unfold _root_.GD.N0232.N0720.N1499.d015001 _root_.GD.N0107.d009024
  simp only [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1215.d014274,
    _root_.GD.N0232.N0720.N1215.d014275, Prod.fst, Prod.snd]
  rw [_root_.GD.N0232.N0720.N1124.d016499
        m g theta.location theta.scale₁ theta.scale₁_pos omega.1,
    _root_.GD.N0232.N0720.N1124.d016499
        n g theta.location theta.scale₂ theta.scale₂_pos omega.2]
  simp only [_root_.GD.N0232.N0720.N1080.d014169]
  change (_ * _) * (_ * _) = (_ * _) * (_ * _)
  ring





def d016501
    (anchor : _root_.GD.N0232.N0720.N1080.d014168) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦
    _root_.GD.N0232.N0720.N1499.d015001 m n anchor omega +
      ∑ i, weight i * _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega


def d016502
    (anchor : _root_.GD.N0232.N0720.N1080.d014168) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦
    _root_.GD.N0232.N0720.N1499.d015001 m n anchor omega * anchor.location +
      ∑ i, weight i * _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega *
        (packet i).location



def d016503
    (anchor : _root_.GD.N0232.N0720.N1080.d014168) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦
    _root_.GD.N0232.N0720.N1124.d016502 anchor packet weight omega /
      _root_.GD.N0232.N0720.N1124.d016501 anchor packet weight omega

theorem d016504
    (anchor : _root_.GD.N0232.N0720.N1080.d014168) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 < _root_.GD.N0232.N0720.N1124.d016501 anchor packet weight omega := by
  unfold _root_.GD.N0232.N0720.N1124.d016501
  have hsum : 0 ≤ ∑ i,
      weight i * _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega :=
    Finset.sum_nonneg fun i _ ↦
      mul_nonneg (hweight i)
        (_root_.GD.N0232.N0720.N1499.d015003 m n (packet i) omega)
  exact add_pos_of_pos_of_nonneg
    (_root_.GD.N0232.N0720.N1499.d015005 m n anchor omega) hsum



theorem d016505
    (g : _root_.GD.N0232.N0719.N0946.d009229) (anchor : _root_.GD.N0232.N0720.N1080.d014168)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1124.d016501 (_root_.GD.N0232.N0720.N1215.d014272 g anchor)
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight (g • omega) =
      _root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
        _root_.GD.N0232.N0720.N1124.d016501 anchor packet weight omega := by
  unfold _root_.GD.N0232.N0720.N1124.d016501
  rw [_root_.GD.N0232.N0720.N1124.d016500]
  have hsum :
      (∑ i, weight i *
          _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g (packet i))
            (g • omega)) =
        _root_.GD.N0232.N0720.N1499.d015001 m n
            (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
          ∑ i, weight i * _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [_root_.GD.N0232.N0720.N1124.d016500]
    ring
  rw [hsum]
  ring



theorem d016506
    (g : _root_.GD.N0232.N0719.N0946.d009229) (anchor : _root_.GD.N0232.N0720.N1080.d014168)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1124.d016502 (_root_.GD.N0232.N0720.N1215.d014272 g anchor)
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight (g • omega) =
      _root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
        (g.shift * _root_.GD.N0232.N0720.N1124.d016501 anchor packet weight omega +
          g.d009239 *
            _root_.GD.N0232.N0720.N1124.d016502 anchor packet weight omega) := by
  unfold _root_.GD.N0232.N0720.N1124.d016502 _root_.GD.N0232.N0720.N1124.d016501
  rw [_root_.GD.N0232.N0720.N1124.d016500]
  simp only [_root_.GD.N0232.N0720.N1215.d014273]
  let c := _root_.GD.N0232.N0720.N1499.d015001 m n
    (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)
  let la := _root_.GD.N0232.N0720.N1499.d015001 m n anchor omega
  let li : ι → ℝ := fun i ↦ _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega
  let wa : ι → ℝ := fun i ↦ weight i
  let mu : ι → ℝ := fun i ↦ (packet i).location
  change
    c * la * (g.shift + g.d009239 * anchor.location) +
        ∑ i, wa i *
          _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g (packet i))
            (g • omega) * (g.shift + g.d009239 * mu i) =
      c *
        (g.shift * (la + ∑ i, wa i * li i) +
          g.d009239 *
            (la * anchor.location + ∑ i, wa i * li i * mu i))
  calc
    c * la * (g.shift + g.d009239 * anchor.location) +
          ∑ i, wa i *
            _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g (packet i))
              (g • omega) * (g.shift + g.d009239 * mu i) =
        c * la * (g.shift + g.d009239 * anchor.location) +
          ∑ i, wa i * (c * li i) *
            (g.shift + g.d009239 * mu i) := by
        apply congrArg₂ (· + ·) rfl
        apply Finset.sum_congr rfl
        intro i hi
        rw [_root_.GD.N0232.N0720.N1124.d016500]
    _ =
        c * la * (g.shift + g.d009239 * anchor.location) +
          ∑ i,
            (c * g.shift * (wa i * li i) +
              c * g.d009239 * (wa i * li i * mu i)) := by
        apply congrArg₂ (· + ·) rfl
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = c * la * (g.shift + g.d009239 * anchor.location) +
          (c * g.shift * ∑ i, wa i * li i +
            c * g.d009239 * ∑ i, wa i * li i * mu i) := by
        rw [Finset.sum_add_distrib]
        congr 2
        · exact (Finset.mul_sum Finset.univ (fun i ↦ wa i * li i)
            (c * g.shift)).symm
        · exact (Finset.mul_sum Finset.univ
            (fun i ↦ wa i * li i * mu i)
            (c * g.d009239)).symm
    _ = _ := by ring




theorem d016507
    (g : _root_.GD.N0232.N0719.N0946.d009229) (anchor : _root_.GD.N0232.N0720.N1080.d014168)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1124.d016503 (_root_.GD.N0232.N0720.N1215.d014272 g anchor)
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight (g • omega) =
      g • _root_.GD.N0232.N0720.N1124.d016503 anchor packet weight omega := by
  unfold _root_.GD.N0232.N0720.N1124.d016503
  rw [_root_.GD.N0232.N0720.N1124.d016506,
    _root_.GD.N0232.N0720.N1124.d016505]
  have hc : _root_.GD.N0232.N0720.N1499.d015001 m n
      (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) ≠ 0 :=
    (_root_.GD.N0232.N0720.N1499.d015005 m n
      (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)).ne'
  have hm : _root_.GD.N0232.N0720.N1124.d016501 anchor packet weight omega ≠ 0 :=
    (_root_.GD.N0232.N0720.N1124.d016504 anchor packet weight hweight omega).ne'
  simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244]
  field_simp [hc, hm]






theorem d016508
    (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016415 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight
        (g • omega) =
      1 + _root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) := by
  unfold _root_.GD.N0232.N0720.N1126.d016415 _root_.GD.N0232.N0720.N1126.d016413 _root_.GD.N0230.N0617.d000163
  have hsum :
      (∑ i, weight i *
          _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g (packet i))
            (g • omega)) =
        _root_.GD.N0232.N0720.N1499.d015001 m n
            (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
          ∑ i, weight i * _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [_root_.GD.N0232.N0720.N1124.d016500]
    ring
  rw [hsum]
  ring



theorem d016509
    (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0230.N0617.d000164 weight
        (_root_.GD.N0232.N0720.N1126.d016413 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
        (_root_.GD.N0232.N0720.N1126.d016414 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))) (g • omega) =
      _root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
        (g.shift * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) +
          g.d009239 *
            _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
              (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) := by
  unfold _root_.GD.N0230.N0617.d000164 _root_.GD.N0232.N0720.N1126.d016413 _root_.GD.N0232.N0720.N1126.d016414 _root_.GD.N0232.N0720.N1126.d016415
    _root_.GD.N0230.N0617.d000163
  simp only [_root_.GD.N0232.N0720.N1215.d014273]
  let c := _root_.GD.N0232.N0720.N1499.d015001 m n
    (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)
  let li : ι → ℝ := fun i ↦ _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega
  let mu : ι → ℝ := fun i ↦ (packet i).location
  change
    ∑ i, weight i *
        _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g (packet i))
          (g • omega) * (g.shift + g.d009239 * mu i) =
      c *
        (g.shift * (1 + ∑ i, weight i * li i - 1) +
          g.d009239 * ∑ i, weight i * li i * mu i)
  calc
    (∑ i, weight i *
          _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g (packet i))
            (g • omega) *
          (g.shift + g.d009239 * mu i)) =
        ∑ i, weight i * (c * li i) *
          (g.shift + g.d009239 * mu i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [_root_.GD.N0232.N0720.N1124.d016500]
    _ =
        ∑ i,
          (c * g.shift * (weight i * li i) +
            c * g.d009239 * (weight i * li i * mu i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * g.shift * ∑ i, weight i * li i +
          c * g.d009239 * ∑ i, weight i * li i * mu i := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact (Finset.mul_sum Finset.univ
          (fun i ↦ weight i * li i) (c * g.shift)).symm
      · exact (Finset.mul_sum Finset.univ
          (fun i ↦ weight i * li i * mu i) (c * g.d009239)).symm
    _ = _ := by ring










theorem d016510
    (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016416
          (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight (g • omega) -
        g • _root_.GD.N0232.N0720.N1126.d016416 packet weight omega =
      (g.d009239 *
            _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
              (_root_.GD.N0232.N0720.N1126.d016414 packet) omega *
            (_root_.GD.N0232.N0720.N1499.d015001 m n
                (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) - 1) -
          g.shift * _root_.GD.N0232.N0720.N1126.d016415 packet weight omega) /
        ((1 + _root_.GD.N0232.N0720.N1499.d015001 m n
              (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
            (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) *
          _root_.GD.N0232.N0720.N1126.d016415 packet weight omega) := by
  unfold _root_.GD.N0232.N0720.N1126.d016416 _root_.GD.N0230.N0617.d000166
  change
    _root_.GD.N0230.N0617.d000164 weight
          (_root_.GD.N0232.N0720.N1126.d016413 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
          (_root_.GD.N0232.N0720.N1126.d016414 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
          (g • omega) /
        _root_.GD.N0232.N0720.N1126.d016415 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight
          (g • omega) -
      g •
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
              (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
          _root_.GD.N0232.N0720.N1126.d016415 packet weight omega) = _
  rw [_root_.GD.N0232.N0720.N1124.d016508,
    _root_.GD.N0232.N0720.N1124.d016509]
  have hA : _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega).ne'
  have htrans :
      1 + _root_.GD.N0232.N0720.N1499.d015001 m n
            (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
          (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) ≠ 0 := by
    rw [← _root_.GD.N0232.N0720.N1124.d016508]
    exact (_root_.GD.N0230.N0617.d000169 weight
      (_root_.GD.N0232.N0720.N1126.d016413 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))) hweight
      (_root_.GD.N0232.N0720.N1126.d016419
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))) (g • omega)).ne'
  simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244]
  field_simp [hA, htrans]
  ring




theorem d016511
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift ≠ 0)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016416
          (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) (fun _ ↦ 0) (g • omega) ≠
      g • _root_.GD.N0232.N0720.N1126.d016416 packet (fun _ ↦ 0) omega := by
  simpa [_root_.GD.N0232.N0720.N1126.d016416, _root_.GD.N0230.N0617.d000166,
    _root_.GD.N0230.N0617.d000164, _root_.GD.N0230.N0617.d000163, _root_.GD.N0232.N0719.N0946.d009229.d009244, eq_comm] using hg

end

end N1124
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1124.d016500
#print axioms _root_.GD.N0232.N0720.N1124.d016507
#print axioms _root_.GD.N0232.N0720.N1124.d016510
#print axioms _root_.GD.N0232.N0720.N1124.d016511
