import GD.Module0947
import GD.Module1205
import GD.Module1177
import GD.Module1207
import GD.Module0966


























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1287

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1106
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1424
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1437
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1456
open _root_.GD.N0232.N0720.N1457
open _root_.GD.N0232.N0720.N1458
open _root_.GD.N0232.N0720.N1468
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0720.N1459
open _root_.GD.N0232.N0720.N1460
open _root_.GD.N0232.N0720.N1467





def d019507
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  Classical.choose (_root_.GD.N0232.N0720.N1424.d014868 m n hm hn)

theorem d019508
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Measurable (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn) := by
  exact (Classical.choose_spec
    (_root_.GD.N0232.N0720.N1424.d014868 m n hm hn)).1

theorem d019509
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1287.d019507 m n hm hn x ∈ Set.Icc (0 : ℝ) 1 := by
  exact (Classical.choose_spec
    (_root_.GD.N0232.N0720.N1424.d014868 m n hm hn)).2.1 x

theorem d019510
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013705 m n t (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn) <
      _root_.GD.N0232.N0720.N1441.d013705 m n t _root_.GD.N0232.N0720.N1424.d014839 := by
  exact (Classical.choose_spec
    (_root_.GD.N0232.N0720.N1424.d014868 m n hm hn)).2.2.1 t

theorem d019511
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (competitor : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hcompetitor : Measurable competitor)
    (hcompetitorIcc : ∀ x, competitor x ∈ Set.Icc (0 : ℝ) 1)
    (hdom : ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      _root_.GD.N0232.N0720.N1441.d013705 m n t competitor ≤
        _root_.GD.N0232.N0720.N1441.d013705 m n t
          (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)) :
    competitor =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      _root_.GD.N0232.N0720.N1287.d019507 m n hm hn := by
  exact (Classical.choose_spec
    (_root_.GD.N0232.N0720.N1424.d014868 m n hm hn)).2.2.2
      competitor hcompetitor hcompetitorIcc hdom





def d019512
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) : ℝ → ℝ → ℝ :=
  _root_.GD.N0232.N0720.N1460.d003029 (_root_.GD.N0232.N0720.N1437.d002998 (fun r w ↦ g (r, w)))

theorem d019513
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (z q : ℝ) :
    _root_.GD.N0232.N0720.N1287.d019512 g z q =
      z * g (1 - q, z ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1287.d019512 _root_.GD.N0232.N0720.N1460.d003029
    _root_.GD.N0232.N0720.N1437.d002998 _root_.GD.N0232.N0720.N1437.d002996
    _root_.GD.N0232.N0720.N1437.d002997
  have hden : q + (1 - q) = 1 := by ring
  rw [hden]
  simp

theorem d019514
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) :
    Measurable (fun p : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1287.d019512 g p.1 p.2) := by
  rw [show (fun p : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1287.d019512 g p.1 p.2) =
    (fun p : ℝ × ℝ ↦ p.1 * g (1 - p.2, p.1 ^ 2)) by
      funext p
      exact _root_.GD.N0232.N0720.N1287.d019513 g p.1 p.2]
  exact measurable_fst.mul
    (hg.comp ((measurable_const.sub measurable_snd).prodMk
      (measurable_fst.pow_const 2)))

theorem d019515
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    _root_.GD.N0232.N0720.N1460.d003040 (_root_.GD.N0232.N0720.N1287.d019512 g) := by
  intro z q
  rw [_root_.GD.N0232.N0720.N1287.d019513,
    _root_.GD.N0232.N0720.N1287.d019513, neg_sq]
  ring



theorem d019516
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1456.d019471 m n (_root_.GD.N0232.N0720.N1287.d019512 g) =ᵐ[
        _root_.GD.N0232.N0720.N1080.d014171 m n theta]
      _root_.GD.N0232.N0720.N1425.d014719 m n g := by
  have hweld := _root_.GD.N0232.N0720.N1459.d018935
    m n hm hn
    (_root_.GD.N0232.N0720.N1437.d002998 (fun r w ↦ g (r, w)))
    (_root_.GD.N0232.N0720.N1437.d003003 _) theta
  filter_upwards [hweld] with omega hweldOmega
  calc
    _root_.GD.N0232.N0720.N1456.d019471 m n (_root_.GD.N0232.N0720.N1287.d019512 g) omega =
        _root_.GD.N0232.N0720.N1459.d018931 m n
          (_root_.GD.N0232.N0720.N1437.d002998 (fun r w ↦ g (r, w))) omega := rfl
    _ = _root_.GD.N0232.N0720.N1459.d018930 m n
          (_root_.GD.N0232.N0720.N1437.d002998 (fun r w ↦ g (r, w))) omega :=
      hweldOmega.symm
    _ = _root_.GD.N0232.N0720.N1425.d014719 m n g omega := by
      simp only [_root_.GD.N0232.N0720.N1459.d018930, _root_.GD.N0232.N0720.N1425.d014719,
        _root_.GD.N0232.N0720.N1467.d012545, _root_.GD.N0232.N0720.N1467.d012546,
        _root_.GD.N0232.N0720.N1467.d012547,
        _root_.GD.N0232.N0720.N1467.d012548,
        _root_.GD.N0232.N0720.N1084.d014252,
        _root_.GD.N0232.N0720.N1084.d014253]





theorem d019517
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgIcc : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  let e := _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂
  let Sigma := _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂
  have he0 : 0 < e := _root_.GD.N0107.d009050
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos
  have he1 : e < 1 := _root_.GD.N0107.d009051
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos
  let q : _root_.GD.N0232.N0720.N1436.d013217 → ℝ := fun x ↦ g x - e
  have hq : Measurable q := hg.sub measurable_const
  have hqBound : ∀ x, |q x| ≤ 1 := by
    intro x
    rw [abs_le]
    constructor <;> dsimp only [q] <;>
      linarith [(hgIcc x).1, (hgIcc x).2]
  have hcarrier := (_root_.GD.N0107.d012748
    m n hm hn theta.location theta.scale₁ theta.scale₂
    theta.scale₁_pos theta.scale₂_pos q hq
    (B := 1) (by norm_num) hqBound).2
  have horacle := _root_.GD.N0107.d012747
    m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos
  have hsum := horacle.add hcarrier
  apply (memLp_congr_ae ?_).2 (by simpa only [_root_.GD.N0232.N0720.N1080.d014171] using hsum)
  filter_upwards [] with omega
  rw [_root_.GD.N0232.N0720.N1425.d014721
    m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos g omega]
  unfold _root_.GD.N0141.d006685
  rfl



theorem d019518
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgIcc : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    MemLp
      (fun omega ↦
        _root_.GD.N0232.N0720.N1456.d019471 m n
          (_root_.GD.N0232.N0720.N1287.d019512 g) omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  apply (memLp_congr_ae ?_).2
    (_root_.GD.N0232.N0720.N1287.d019517
      m n hm hn theta g hg hgIcc)
  exact (_root_.GD.N0232.N0720.N1287.d019516
    m n hm hn g theta).fun_comp (fun y ↦ y - theta.location)



def d019519
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgIcc : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1456.d019472 m n where
  coefficient := _root_.GD.N0232.N0720.N1287.d019512 g
  measurable_coefficient :=
    _root_.GD.N0232.N0720.N1287.d019514 hg
  memLp := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      _root_.GD.N0232.N0720.N1287.d019518
        m n hm hn _root_.GD.N0232.N0720.N1080.d014169 g hg hgIcc



def d019520
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1456.d019472 m n :=
  _root_.GD.N0232.N0720.N1287.d019519 m n hm hn
    (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
    (_root_.GD.N0232.N0720.N1287.d019508 m n hm hn)
    (_root_.GD.N0232.N0720.N1287.d019509 m n hm hn)

@[simp] theorem d019521
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).coefficient =
      _root_.GD.N0232.N0720.N1287.d019512
        (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn) := rfl




theorem d019522
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1460.d003040
      (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).coefficient := by
  rw [_root_.GD.N0232.N0720.N1287.d019521]
  exact _root_.GD.N0232.N0720.N1287.d019515 _





theorem d019523
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgIcc : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun x ↦ (g x - t.1) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 m n t.1) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1436.d013289 m n t.1) :=
    _root_.GD.N0232.N0720.N1434.d013564 hm hn
      t.property.1 t.property.2
  apply Integrable.of_bound
    ((hg.sub measurable_const).pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_sq]
  have hdist : |g x - t.1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [
      (hgIcc x).1, (hgIcc x).2, t.property.1, t.property.2]
  have hsquare :=
    (sq_le_sq₀ (abs_nonneg (g x - t.1)) (by norm_num : (0 : ℝ) ≤ 1)).2
      hdist
  simpa only [sq_abs, one_pow] using hsquare



theorem d019524
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Integrable (fun x ↦ (_root_.GD.N0232.N0720.N1424.d014839 x - t.1) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 m n t.1) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1436.d013289 m n t.1) :=
    _root_.GD.N0232.N0720.N1434.d013564 hm hn
      t.property.1 t.property.2
  apply Integrable.of_bound
    (((_root_.GD.N0232.N0720.N1424.d014842.sub measurable_const).pow_const 2).aestronglyMeasurable)
    1
  filter_upwards [_root_.GD.N0232.N0720.N1458.d018947
    m n t.1] with x hx
  rw [Real.norm_eq_abs, abs_sq]
  have hcoefficient : _root_.GD.N0232.N0720.N1424.d014839 x ∈ Set.Icc (0 : ℝ) 1 := by
    unfold _root_.GD.N0232.N0720.N1424.d014839 _root_.GD.N0232.N0720.N1436.d013218 at *
    exact ⟨hx.1.1.le, hx.1.2.le⟩
  have hdist : |_root_.GD.N0232.N0720.N1424.d014839 x - t.1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [
      hcoefficient.1, hcoefficient.2,
      t.property.1, t.property.2]
  have hsquare :=
    (sq_le_sq₀
      (abs_nonneg (_root_.GD.N0232.N0720.N1424.d014839 x - t.1))
      (by norm_num : (0 : ℝ) ≤ 1)).2 hdist
  simpa only [sq_abs, one_pow] using hsquare



theorem d019525
    (m n : ℕ) (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hg : Integrable (fun x ↦ (g x - t.1) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 m n t.1)) :
    _root_.GD.N0232.N0720.N1441.d013705 m n t g =
      ENNReal.ofReal
        (∫ x, (g x - t.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1) := by
  unfold _root_.GD.N0232.N0720.N1441.d013705 _root_.GD.N0232.N0720.N1441.d013678
  exact (ofReal_integral_eq_lintegral_ofReal hg
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)).symm



theorem d019526
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgIcc : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta
        (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn g hg hgIcc).d019473 =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1456.d019471 m n
                (_root_.GD.N0232.N0720.N1287.d019512 g) omega -
              theta.location)) := by
  exact _root_.GD.N0232.N0720.N1080.d014183
    m n (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
    theta.location
    (_root_.GD.N0232.N0720.N1456.d019471 m n (_root_.GD.N0232.N0720.N1287.d019512 g))
    (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn g hg hgIcc).memLp
    (_root_.GD.N0232.N0720.N1287.d019518
      m n hm hn theta g hg hgIcc)



theorem d019527
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦
          _root_.GD.N0232.N0720.N1456.d019471 m n
              (_root_.GD.N0232.N0720.N1287.d019512 g) omega - theta.location) =
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - theta.location) := by
  unfold _root_.GD.N0141.d006684
  apply integral_congr_ae
  exact (_root_.GD.N0232.N0720.N1287.d019516
    m n hm hn g theta).fun_comp
      (fun y ↦ (y - theta.location) ^ 2)



theorem d019528
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgIcc : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta
        (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn g hg hgIcc).d019473 =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
            (_root_.GD.N0107.d012732 m n theta.location
              (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) +
          _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
            ∫ x,
              (g x - _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
              ∂_root_.GD.N0232.N0720.N1436.d013289 m n
                (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) := by
  rw [_root_.GD.N0232.N0720.N1287.d019526
    m n hm hn theta g hg hgIcc]
  congr 1
  rw [_root_.GD.N0232.N0720.N1287.d019527
    m n hm hn theta g]
  exact _root_.GD.N0232.N0720.N1425.d014726
    m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos g hg
      (B := 1) (by norm_num) (by
        intro x
        rw [abs_of_nonneg (hgIcc x).1]
        exact (hgIcc x).2)


theorem d019529
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
            (_root_.GD.N0107.d012732 m n theta.location
              (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) +
          _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
            ∫ x,
              (_root_.GD.N0232.N0720.N1424.d014839 x -
                _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
              ∂_root_.GD.N0232.N0720.N1436.d013289 m n
                (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) := by
  rw [_root_.GD.N0232.N0720.N1080.d014184 m n hm hn theta]
  congr 1
  have hcarrier : MemLp
      (fun omega ↦
        _root_.GD.N0107.d009038 m n theta.location theta.scale₁ theta.scale₂
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)
            (_root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂) omega *
          (_root_.GD.N0232.N0720.N1424.d014839
              (_root_.GD.N0107.d009039 m n theta.location theta.scale₁ theta.scale₂
                  (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) omega,
                _root_.GD.N0107.d009040 m n theta.location theta.scale₁ theta.scale₂
                  (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) omega) -
            _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂))
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    simpa [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1424.d014839] using
      (_root_.GD.N0107.d012748
        m n hm hn theta.location theta.scale₁ theta.scale₂
        theta.scale₁_pos theta.scale₂_pos
        (fun _ : _root_.GD.N0232.N0720.N1436.d013217 ↦ 0) measurable_const
        (B := 0) (by norm_num) (by intro x; simp)).1
  have hbridge :=
    _root_.GD.N0232.N0720.N1425.d014725
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos
      _root_.GD.N0232.N0720.N1424.d014839 _root_.GD.N0232.N0720.N1424.d014842 hcarrier
  have hraw :
      (fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - theta.location) =
        (fun omega ↦
          _root_.GD.N0232.N0720.N1425.d014719 m n _root_.GD.N0232.N0720.N1424.d014839 omega -
            theta.location) := by
    funext omega
    rw [_root_.GD.N0232.N0720.N1424.d014854]
    rfl
  rw [hraw]
  exact hbridge






theorem d019530
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    (∫ x,
        (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn x - t.1) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1) <
      ∫ x, (_root_.GD.N0232.N0720.N1424.d014839 x - t.1) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 := by
  have hselected := _root_.GD.N0232.N0720.N1287.d019523
    m n hm hn t
    (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
    (_root_.GD.N0232.N0720.N1287.d019508 m n hm hn)
    (_root_.GD.N0232.N0720.N1287.d019509 m n hm hn)
  have hbaseline := _root_.GD.N0232.N0720.N1287.d019524 m n hm hn t
  have hstrict := _root_.GD.N0232.N0720.N1287.d019510 m n hm hn t
  rw [_root_.GD.N0232.N0720.N1287.d019525 m n t _ hselected,
    _root_.GD.N0232.N0720.N1287.d019525 m n t _ hbaseline] at hstrict
  have hbaselinePosENN :
      0 < ENNReal.ofReal
        (∫ x, (_root_.GD.N0232.N0720.N1424.d014839 x - t.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1) :=
    lt_of_le_of_lt bot_le hstrict
  have hbaselinePos :
      0 < ∫ x, (_root_.GD.N0232.N0720.N1424.d014839 x - t.1) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 :=
    ENNReal.ofReal_pos.mp hbaselinePosENN
  exact (ENNReal.ofReal_lt_ofReal_iff hbaselinePos).1 hstrict



theorem d019531
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  intro theta
  let t : _root_.GD.N0232.N0720.N1441.d013676 :=
    ⟨_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂,
      _root_.GD.N0107.d009050 (by omega) (by omega)
        theta.scale₁_pos theta.scale₂_pos,
      _root_.GD.N0107.d009051 (by omega) (by omega)
        theta.scale₁_pos theta.scale₂_pos⟩
  have hIntegral :=
    _root_.GD.N0232.N0720.N1287.d019530
      m n hm hn t
  have hSigma :
      0 < _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ :=
    _root_.GD.N0107.d009049 (by omega) (by omega)
      theta.scale₁_pos theta.scale₂_pos
  have hbaselineIntegralPos :
      0 < ∫ x,
        (_root_.GD.N0232.N0720.N1424.d014839 x -
          _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n
          (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) := by
    simpa only [t] using
      (lt_of_le_of_lt
        (integral_nonneg fun x ↦ sq_nonneg
          (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn x - t.1))
        hIntegral)
  have hreal :
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) +
        _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
          (∫ x,
            (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn x -
              _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n
              (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) <
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) +
        _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
          (∫ x,
            (_root_.GD.N0232.N0720.N1424.d014839 x -
              _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n
              (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) := by
    have hmul := mul_lt_mul_of_pos_left
      (by simpa only [t] using hIntegral) hSigma
    linarith
  have hrightPos :
      0 < _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) +
        _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
          (∫ x,
            (_root_.GD.N0232.N0720.N1424.d014839 x -
              _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n
              (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) := by
    have horacleNonneg :
        0 ≤ _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) :=
      integral_nonneg fun _ ↦ sq_nonneg _
    have hproductPos := mul_pos hSigma hbaselineIntegralPos
    linarith
  rw [show
      (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473 =
        (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
          (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
          (_root_.GD.N0232.N0720.N1287.d019508 m n hm hn)
          (_root_.GD.N0232.N0720.N1287.d019509 m n hm hn)).d019473 by
        rfl,
    _root_.GD.N0232.N0720.N1287.d019528
      m n hm hn theta
      (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
      (_root_.GD.N0232.N0720.N1287.d019508 m n hm hn)
      (_root_.GD.N0232.N0720.N1287.d019509 m n hm hn),
    _root_.GD.N0232.N0720.N1287.d019529 m n hm hn theta]
  exact (ENNReal.ofReal_lt_ofReal_iff hrightPos).2 hreal



theorem d019532
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (rho : ℝ) (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 rho hrho)
        (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473 <
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 rho hrho) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
  _root_.GD.N0232.N0720.N1287.d019531
    m n hm hn (_root_.GD.N0232.N0720.N1106.d018682 rho hrho)



def d019533
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014639 m n :=
  _root_.GD.N0232.N0720.N1457.d019493 m n hm hn
    (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn)
    (_root_.GD.N0232.N0720.N1287.d019532 m n hm hn)

@[simp] theorem d019534
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0232.N0720.N1287.d019533 m n hm hn).value =
      (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473 := rfl



theorem d019535
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn
      (_root_.GD.N0232.N0720.N1287.d019533 m n hm hn) := by
  intro theta
  simpa only [_root_.GD.N0232.N0720.N1287.d019534] using
    _root_.GD.N0232.N0720.N1287.d019531
      m n hm hn theta








theorem d019536
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (competitor : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hcompetitor : Measurable competitor)
    (hcompetitorIcc : ∀ x, competitor x ∈ Set.Icc (0 : ℝ) 1)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
        competitor hcompetitor hcompetitorIcc).d019473
      (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473) :
    ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      _root_.GD.N0232.N0720.N1441.d013705 m n t competitor ≤
        _root_.GD.N0232.N0720.N1441.d013705 m n t
          (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn) := by
  intro t
  let sigma := _root_.GD.N0232.N0720.N1424.d014846 m t.1
  let tau := _root_.GD.N0232.N0720.N1424.d014847 n t.1
  have hsigma : 0 < sigma := _root_.GD.N0232.N0720.N1424.d014848 hm t.property.2
  have htau : 0 < tau := _root_.GD.N0232.N0720.N1424.d014849 hn t.property.1
  have hSigma : _root_.GD.N0107.d009045 m n sigma tau = 1 :=
    _root_.GD.N0232.N0720.N1424.d014852 hm hn t.property.1 t.property.2
  have hfrac : _root_.GD.N0107.d009046 m n sigma tau = t.1 :=
    _root_.GD.N0232.N0720.N1424.d014853 hm hn t.property.1 t.property.2
  let theta : _root_.GD.N0232.N0720.N1080.d014168 :=
    { location := 0
      scale₁ := sigma
      scale₂ := tau
      scale₁_pos := hsigma
      scale₂_pos := htau }
  have hphysical := hdom theta
  change
    _root_.GD.N0232.N0720.N1080.d014182 m n theta
        (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
          competitor hcompetitor hcompetitorIcc).d019473 ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n theta
        (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
          (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
          (_root_.GD.N0232.N0720.N1287.d019508 m n hm hn)
          (_root_.GD.N0232.N0720.N1287.d019509 m n hm hn)).d019473
      at hphysical
  rw [_root_.GD.N0232.N0720.N1287.d019528
      m n hm hn theta competitor hcompetitor hcompetitorIcc,
    _root_.GD.N0232.N0720.N1287.d019528
      m n hm hn theta
      (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
      (_root_.GD.N0232.N0720.N1287.d019508 m n hm hn)
      (_root_.GD.N0232.N0720.N1287.d019509 m n hm hn)] at hphysical
  have hrightNonneg :
      0 ≤ _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) +
        _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
          ∫ x,
            (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn x -
              _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n
              (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) := by
    exact add_nonneg
      (integral_nonneg fun _ ↦ sq_nonneg _)
      (mul_nonneg
        (le_of_lt (_root_.GD.N0107.d009049 (by omega) (by omega)
          theta.scale₁_pos theta.scale₂_pos))
        (integral_nonneg fun _ ↦ sq_nonneg _))
  have hreal :=
    (ENNReal.ofReal_le_ofReal_iff hrightNonneg).1 hphysical
  dsimp only [theta] at hreal
  rw [hSigma, hfrac, one_mul] at hreal
  have hintegral :
      (∫ x, (competitor x - t.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1) ≤
        ∫ x,
          (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn x - t.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 := by
    linarith
  have hcompetitorIntegral := _root_.GD.N0232.N0720.N1287.d019523
    m n hm hn t competitor hcompetitor hcompetitorIcc
  have hselectedIntegral := _root_.GD.N0232.N0720.N1287.d019523
    m n hm hn t
    (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
    (_root_.GD.N0232.N0720.N1287.d019508 m n hm hn)
    (_root_.GD.N0232.N0720.N1287.d019509 m n hm hn)
  rw [_root_.GD.N0232.N0720.N1287.d019525
      m n t competitor hcompetitorIntegral,
    _root_.GD.N0232.N0720.N1287.d019525
      m n t (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
        hselectedIntegral]
  exact ENNReal.ofReal_le_ofReal hintegral



theorem d019537
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (left right : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hleft : Measurable left)
    (hright : Measurable right)
    (hleftIcc : ∀ x, left x ∈ Set.Icc (0 : ℝ) 1)
    (hrightIcc : ∀ x, right x ∈ Set.Icc (0 : ℝ) 1)
    (hstrict :
      _root_.GD.N0232.N0720.N1080.d014182 m n theta
          (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
            left hleft hleftIcc).d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n theta
          (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
            right hright hrightIcc).d019473) :
    let t : _root_.GD.N0232.N0720.N1441.d013676 :=
      ⟨_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂,
        _root_.GD.N0107.d009050 (by omega) (by omega)
          theta.scale₁_pos theta.scale₂_pos,
        _root_.GD.N0107.d009051 (by omega) (by omega)
          theta.scale₁_pos theta.scale₂_pos⟩
    _root_.GD.N0232.N0720.N1441.d013705 m n t left < _root_.GD.N0232.N0720.N1441.d013705 m n t right := by
  let t : _root_.GD.N0232.N0720.N1441.d013676 :=
    ⟨_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂,
      _root_.GD.N0107.d009050 (by omega) (by omega)
        theta.scale₁_pos theta.scale₂_pos,
      _root_.GD.N0107.d009051 (by omega) (by omega)
        theta.scale₁_pos theta.scale₂_pos⟩
  change _root_.GD.N0232.N0720.N1441.d013705 m n t left < _root_.GD.N0232.N0720.N1441.d013705 m n t right
  have hSigma :
      0 < _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ :=
    _root_.GD.N0107.d009049 (by omega) (by omega)
      theta.scale₁_pos theta.scale₂_pos
  rw [_root_.GD.N0232.N0720.N1287.d019528
      m n hm hn theta left hleft hleftIcc,
    _root_.GD.N0232.N0720.N1287.d019528
      m n hm hn theta right hright hrightIcc] at hstrict
  have hrightRealPos :
      0 < _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) +
        _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
          (∫ x,
            (right x - _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n
              (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) := by
    exact ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hstrict)
  have hreal :=
    (ENNReal.ofReal_lt_ofReal_iff hrightRealPos).1 hstrict
  have hintegral :
      (∫ x,
          (left x - _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) <
        ∫ x,
          (right x - _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) := by
    have hmul :
        _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
            (∫ x,
              (left x - _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
              ∂_root_.GD.N0232.N0720.N1436.d013289 m n
                (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) <
          _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
            (∫ x,
              (right x - _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
              ∂_root_.GD.N0232.N0720.N1436.d013289 m n
                (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) := by
      linarith
    by_contra hnot
    have hle := le_of_not_gt hnot
    have hmul_le := mul_le_mul_of_nonneg_left hle hSigma.le
    exact (not_le_of_gt hmul) hmul_le
  have hrightIntegralPos :
      0 < ∫ x,
          (right x - _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) :=
    lt_of_le_of_lt (integral_nonneg fun _ ↦ sq_nonneg _) hintegral
  have hleftIntegral := _root_.GD.N0232.N0720.N1287.d019523
    m n hm hn t left hleft hleftIcc
  have hrightIntegral := _root_.GD.N0232.N0720.N1287.d019523
    m n hm hn t right hright hrightIcc
  rw [_root_.GD.N0232.N0720.N1287.d019525 m n t left hleftIntegral,
    _root_.GD.N0232.N0720.N1287.d019525 m n t right hrightIntegral]
  exact (ENNReal.ofReal_lt_ofReal_iff
    (by simpa only [t] using hrightIntegralPos)).2
      (by simpa only [t] using hintegral)




theorem d019538
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (left right : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hae : left =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] right)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013705 m n t left = _root_.GD.N0232.N0720.N1441.d013705 m n t right := by
  unfold _root_.GD.N0232.N0720.N1441.d013705
  apply lintegral_congr_ae
  filter_upwards [
    (_root_.GD.N0232.N0720.N1441.d013682 hm hn t).ae_le hae]
      with x hx
  rw [hx]




theorem d019539
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (competitor : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hcompetitor : Measurable competitor)
    (hcompetitorIcc : ∀ x, competitor x ∈ Set.Icc (0 : ℝ) 1)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
        competitor hcompetitor hcompetitorIcc).d019473
      (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473) :
    competitor =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      _root_.GD.N0232.N0720.N1287.d019507 m n hm hn := by
  apply _root_.GD.N0232.N0720.N1287.d019511
    m n hm hn competitor hcompetitor hcompetitorIcc
  exact _root_.GD.N0232.N0720.N1287.d019536
    m n hm hn competitor hcompetitor hcompetitorIcc hdom




theorem d019540
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ ∃ (competitor : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
        (hcompetitor : Measurable competitor)
        (hcompetitorIcc : ∀ x, competitor x ∈ Set.Icc (0 : ℝ) 1),
      _root_.GD.N0232.N0720.N1468.d018953 m n
        (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
          competitor hcompetitor hcompetitorIcc).d019473
        (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473 := by
  rintro ⟨competitor, hcompetitor, hcompetitorIcc, hstrict⟩
  have hae := _root_.GD.N0232.N0720.N1287.d019539
    m n hm hn competitor hcompetitor hcompetitorIcc hstrict.1
  obtain ⟨theta, htheta⟩ := hstrict.2
  let t : _root_.GD.N0232.N0720.N1441.d013676 :=
    ⟨_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂,
      _root_.GD.N0107.d009050 (by omega) (by omega)
        theta.scale₁_pos theta.scale₂_pos,
      _root_.GD.N0107.d009051 (by omega) (by omega)
        theta.scale₁_pos theta.scale₂_pos⟩
  have hreducedStrict :
      _root_.GD.N0232.N0720.N1441.d013705 m n t competitor <
        _root_.GD.N0232.N0720.N1441.d013705 m n t
          (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn) := by
    exact _root_.GD.N0232.N0720.N1287.d019537
      m n hm hn theta competitor
      (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
      hcompetitor
      (_root_.GD.N0232.N0720.N1287.d019508 m n hm hn)
      hcompetitorIcc
      (_root_.GD.N0232.N0720.N1287.d019509 m n hm hn)
      (by
        change
          _root_.GD.N0232.N0720.N1080.d014182 m n theta
              (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
                competitor hcompetitor hcompetitorIcc).d019473 <
            _root_.GD.N0232.N0720.N1080.d014182 m n theta
              (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn
                (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn)
                (_root_.GD.N0232.N0720.N1287.d019508 m n hm hn)
                (_root_.GD.N0232.N0720.N1287.d019509 m n hm hn)).d019473
        exact htheta)
  have hreducedEq := _root_.GD.N0232.N0720.N1287.d019538
    m n hm hn competitor
      (_root_.GD.N0232.N0720.N1287.d019507 m n hm hn) hae t
  exact (ne_of_lt hreducedStrict) hreducedEq


end

end N1287
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1287.d019508
#print axioms _root_.GD.N0232.N0720.N1287.d019509
#print axioms _root_.GD.N0232.N0720.N1287.d019510
#print axioms _root_.GD.N0232.N0720.N1287.d019511
#print axioms _root_.GD.N0232.N0720.N1287.d019513
#print axioms _root_.GD.N0232.N0720.N1287.d019514
#print axioms _root_.GD.N0232.N0720.N1287.d019515
#print axioms _root_.GD.N0232.N0720.N1287.d019516
#print axioms _root_.GD.N0232.N0720.N1287.d019517
#print axioms _root_.GD.N0232.N0720.N1287.d019518
#print axioms _root_.GD.N0232.N0720.N1287.d019521
#print axioms _root_.GD.N0232.N0720.N1287.d019522
#print axioms _root_.GD.N0232.N0720.N1287.d019523
#print axioms _root_.GD.N0232.N0720.N1287.d019524
#print axioms _root_.GD.N0232.N0720.N1287.d019525
#print axioms _root_.GD.N0232.N0720.N1287.d019526
#print axioms _root_.GD.N0232.N0720.N1287.d019527
#print axioms _root_.GD.N0232.N0720.N1287.d019528
#print axioms _root_.GD.N0232.N0720.N1287.d019529
#print axioms _root_.GD.N0232.N0720.N1287.d019530
#print axioms _root_.GD.N0232.N0720.N1287.d019531
#print axioms _root_.GD.N0232.N0720.N1287.d019532
#print axioms _root_.GD.N0232.N0720.N1287.d019534
#print axioms _root_.GD.N0232.N0720.N1287.d019535
#print axioms _root_.GD.N0232.N0720.N1287.d019536
#print axioms _root_.GD.N0232.N0720.N1287.d019537
#print axioms _root_.GD.N0232.N0720.N1287.d019538
#print axioms _root_.GD.N0232.N0720.N1287.d019539
#print axioms _root_.GD.N0232.N0720.N1287.d019540
