import GD.Module1208
import GD.Module1061
import GD.Module1209






















open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1286

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0637
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1207
open _root_.GD.N0232.N0720.N1287
open _root_.GD.N0232.N0720.N1418
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1456
open _root_.GD.N0232.N0720.N1458
open _root_.GD.N0232.N0720.N1460
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1468


def d019582 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    _root_.GD.N0232.N0720.N1436.d013217 → ℝ := fun x ↦ _root_.GD.N0230.N0637.d000240 (g x)

theorem d019583
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) :
    Measurable (_root_.GD.N0232.N0720.N1286.d019582 g) :=
  _root_.GD.N0230.N0660.d000890.measurable.comp hg

theorem d019584
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1286.d019582 g x ∈ Set.Icc (0 : ℝ) 1 :=
  _root_.GD.N0230.N0637.d000243 (g x)



theorem d019585
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hg : Measurable g)
    (hfinite : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n
          (_root_.GD.N0232.N0720.N1286.d019582 g) omega - theta.location) ≤
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - theta.location) := by
  let t := _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂
  let Sigma := _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂
  let D := _root_.GD.N0107.d009038 m n theta.location theta.scale₁ theta.scale₂ t Sigma
  let U := _root_.GD.N0107.d012732 m n theta.location t
  let L : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦ g
    (_root_.GD.N0107.d009039 m n theta.location theta.scale₁ theta.scale₂ t omega,
      _root_.GD.N0107.d009040 m n theta.location theta.scale₁ theta.scale₂ t omega)
  let Lc : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦ _root_.GD.N0230.N0637.d000240 (L omega)
  have ht0 : 0 < t := _root_.GD.N0107.d009050
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos
  have ht1 : t < 1 := _root_.GD.N0107.d009051
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos
  have hU : MemLp U 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    _root_.GD.N0107.d012747 m n hm hn theta.location
      theta.scale₁ theta.scale₂ theta.scale₁_pos theta.scale₂_pos
  have hWeight : MemLp (fun omega ↦ D omega * (L omega - t))
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    _root_.GD.N0232.N0720.N1425.d014722
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos g hfinite
  have hclipFinite := _root_.GD.N0232.N0720.N1287.d019517
    m n hm hn theta (_root_.GD.N0232.N0720.N1286.d019582 g)
    (_root_.GD.N0232.N0720.N1286.d019583 hg)
    (_root_.GD.N0232.N0720.N1286.d019584 g)
  have hClipWeight : MemLp (fun omega ↦ D omega * (Lc omega - t))
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    _root_.GD.N0232.N0720.N1425.d014722
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos (_root_.GD.N0232.N0720.N1286.d019582 g)
      hclipFinite
  have horth : (∫ omega, U omega * (D omega * (L omega - t))
      ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) = 0 :=
    _root_.GD.N0232.N0720.N1425.d014724
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos g hg hWeight
  have hclipOrth : (∫ omega, U omega * (D omega * (Lc omega - t))
      ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) = 0 :=
    _root_.GD.N0232.N0720.N1425.d014724
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos (_root_.GD.N0232.N0720.N1286.d019582 g)
      (_root_.GD.N0232.N0720.N1286.d019583 hg) hClipWeight
  have hregret := _root_.GD.N0232.N0720.N1207.d012751 hU hWeight horth
  have hclipRegret :=
    _root_.GD.N0232.N0720.N1207.d012751 hU hClipWeight hclipOrth
  have hmono :
      (∫ omega, D omega ^ 2 * (Lc omega - t) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) ≤
        ∫ omega, D omega ^ 2 * (L omega - t) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
    have hInt : Integrable (fun omega ↦ D omega ^ 2 * (L omega - t) ^ 2)
        (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
      simpa only [mul_pow] using hWeight.integrable_sq
    have hcInt : Integrable (fun omega ↦ D omega ^ 2 * (Lc omega - t) ^ 2)
        (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
      simpa only [mul_pow] using hClipWeight.integrable_sq
    apply integral_mono hcInt hInt
    intro omega
    exact _root_.GD.N0230.N0637.d000247 (sq_nonneg (D omega)) ⟨ht0.le, ht1.le⟩
  have herror :
      (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - theta.location) =
        _root_.GD.N0141.d006685 U D L t := by
    funext omega
    exact _root_.GD.N0232.N0720.N1425.d014721
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos g omega
  have hclipError :
      (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n
        (_root_.GD.N0232.N0720.N1286.d019582 g) omega - theta.location) =
        _root_.GD.N0141.d006685 U D Lc t := by
    funext omega
    exact _root_.GD.N0232.N0720.N1425.d014721
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos (_root_.GD.N0232.N0720.N1286.d019582 g) omega
  rw [herror, hclipError]
  linarith



theorem d019586
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (f : ℝ → ℝ → ℝ) (hfOdd : _root_.GD.N0232.N0720.N1460.d003040 f)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1456.d019471 m n f =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      _root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1458.d018936 f) := by
  have hpositive := (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
    (_root_.GD.N0232.N0720.N1459.d018933
      m n hm hn)
  filter_upwards [hpositive] with omega homega
  have heq := _root_.GD.N0232.N0720.N1458.d018941
    hfOdd (u := (_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0)
      (v := (_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1) homega
  simpa only [_root_.GD.N0232.N0720.N1456.d019471, _root_.GD.N0232.N0720.N1425.d014719,
    _root_.GD.N0232.N0720.N1467.d012545, _root_.GD.N0232.N0720.N1467.d012546,
    _root_.GD.N0232.N0720.N1467.d012547, _root_.GD.N0232.N0720.N1467.d012548,
    _root_.GD.N0232.N0720.N1084.d014252,
    _root_.GD.N0232.N0720.N1084.d014253] using heq



theorem d019587
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1456.d019472 m n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta c.d019473 ≠ ⊤) :
    MemLp (fun omega ↦ _root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hc := _root_.GD.N0232.N0720.N1418.d017030 m n theta c.d019473 hfinite
  apply (memLp_congr_ae ?_).2 hc
  have hclass : (fun omega ↦ c.d019473 omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      _root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient :=
    (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le c.memLp.coeFn_toLp
  filter_upwards [hclass] with omega homega
  exact congrArg (fun y ↦ y - theta.location) homega.symm


def d019588
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : _root_.GD.N0232.N0720.N1456.d019472 m n :=
  _root_.GD.N0232.N0720.N1287.d019519 m n hm hn
    (_root_.GD.N0232.N0720.N1286.d019582 (_root_.GD.N0232.N0720.N1458.d018936 c.coefficient))
    (_root_.GD.N0232.N0720.N1286.d019583
      (_root_.GD.N0232.N0720.N1458.d018937 c.measurable_coefficient))
    (_root_.GD.N0232.N0720.N1286.d019584 _)




theorem d019589
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hcOdd : _root_.GD.N0232.N0720.N1460.d003040 c.coefficient)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (hfinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta c.d019473 ≠ ⊤) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1286.d019588 m n hm hn c).d019473 ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n theta c.d019473 := by
  let g := _root_.GD.N0232.N0720.N1458.d018936 c.coefficient
  have hg : Measurable g := _root_.GD.N0232.N0720.N1458.d018937 c.measurable_coefficient
  have hraw := _root_.GD.N0232.N0720.N1286.d019586
    m n hm hn c.coefficient hcOdd theta
  have hrawFinite := _root_.GD.N0232.N0720.N1286.d019587
    m n c theta hfinite
  have hphysicalFinite : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    apply (memLp_congr_ae ?_).2 hrawFinite
    exact hraw.symm.fun_comp (fun y ↦ y - theta.location)
  have hrisk : _root_.GD.N0232.N0720.N1080.d014182 m n theta c.d019473 = ENNReal.ofReal
      (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - theta.location)) := by
    rw [show _root_.GD.N0232.N0720.N1080.d014182 m n theta c.d019473 = ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦ _root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient omega - theta.location)) from
      _root_.GD.N0232.N0720.N1080.d014183
        m n (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
        theta.location (_root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient) c.memLp hrawFinite]
    congr 1
    unfold _root_.GD.N0141.d006684
    apply integral_congr_ae
    exact hraw.fun_comp (fun y ↦ (y - theta.location) ^ 2)
  change _root_.GD.N0232.N0720.N1080.d014182 m n theta
    (_root_.GD.N0232.N0720.N1287.d019519 m n hm hn (_root_.GD.N0232.N0720.N1286.d019582 g)
      (_root_.GD.N0232.N0720.N1286.d019583 hg)
      (_root_.GD.N0232.N0720.N1286.d019584 g)).d019473 ≤ _
  rw [_root_.GD.N0232.N0720.N1287.d019526 m n hm hn theta,
    _root_.GD.N0232.N0720.N1287.d019527 m n hm hn theta, hrisk]
  exact ENNReal.ofReal_le_ofReal
    (_root_.GD.N0232.N0720.N1286.d019585 m n hm hn theta g hg hphysicalFinite)



theorem d019590
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ ∃ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
      _root_.GD.N0232.N0720.N1460.d003040 c.coefficient ∧
        _root_.GD.N0232.N0720.N1468.d018953 m n c.d019473
          (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473 := by
  rintro ⟨c, hcOdd, hcStrict⟩
  have hfinite : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta c.d019473 ≠ ⊤ := by
    intro theta
    exact ne_top_of_le_ne_top
      ((_root_.GD.N0232.N0720.N1287.d019533 m n hm hn).finiteRisk theta)
      (hcStrict.1 theta)
  apply _root_.GD.N0232.N0720.N1287.d019540 m n hm hn
  refine ⟨_root_.GD.N0232.N0720.N1286.d019582 (_root_.GD.N0232.N0720.N1458.d018936 c.coefficient),
    _root_.GD.N0232.N0720.N1286.d019583
      (_root_.GD.N0232.N0720.N1458.d018937 c.measurable_coefficient),
    _root_.GD.N0232.N0720.N1286.d019584 _, ?_⟩
  change _root_.GD.N0232.N0720.N1468.d018953 m n
    (_root_.GD.N0232.N0720.N1286.d019588 m n hm hn c).d019473
    (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473
  constructor
  · intro theta
    exact (_root_.GD.N0232.N0720.N1286.d019589
      m n hm hn c hcOdd theta (hfinite theta)).trans (hcStrict.1 theta)
  · obtain ⟨theta, htheta⟩ := hcStrict.2
    exact ⟨theta, (_root_.GD.N0232.N0720.N1286.d019589
      m n hm hn c hcOdd theta (hfinite theta)).trans_lt htheta⟩




def d019591 (f : ℝ → ℝ → ℝ) (z q : ℝ) : ℝ :=
  (f z q - f (-z) q) / 2

theorem d019592 (f : ℝ → ℝ → ℝ) :
    _root_.GD.N0232.N0720.N1460.d003040 (_root_.GD.N0232.N0720.N1286.d019591 f) := by
  intro z q
  simp only [_root_.GD.N0232.N0720.N1286.d019591, neg_neg]
  ring

theorem d019593
    {f : ℝ → ℝ → ℝ}
    (hf : Measurable (fun p : ℝ × ℝ ↦ f p.1 p.2)) :
    Measurable (fun p : ℝ × ℝ ↦ _root_.GD.N0232.N0720.N1286.d019591 f p.1 p.2) := by
  have href : Measurable (fun p : ℝ × ℝ ↦ f (-p.1) p.2) :=
    hf.comp (measurable_fst.neg.prodMk measurable_snd)
  exact (hf.sub href).div_const 2



theorem d019594
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (f : ℝ → ℝ → ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1456.d019471 m n (_root_.GD.N0232.N0720.N1286.d019591 f) omega =
      (_root_.GD.N0232.N0720.N1456.d019471 m n f omega -
        _root_.GD.N0232.N0720.N1456.d019471 m n f (_root_.GD.N0232.N0720.N1446.d019019 m n omega)) / 2 := by
  unfold _root_.GD.N0232.N0720.N1456.d019471
  rw [_root_.GD.N0232.N0720.N1472.d019543
    m n hm hn omega]
  change _root_.GD.N0232.N0720.N1460.d003027 (_root_.GD.N0232.N0720.N1286.d019591 f)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0) ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1) =
      (_root_.GD.N0232.N0720.N1460.d003027 f
        ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0) ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1)
        ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
        ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1) -
       _root_.GD.N0232.N0720.N1460.d003027 f
        (-((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0)) (-((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1))
        ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
        ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1)) / 2
  unfold _root_.GD.N0232.N0720.N1460.d003027
  rw [_root_.GD.N0232.N0720.N1460.d003042]
  unfold _root_.GD.N0232.N0720.N1286.d019591
  ring



theorem d019595
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n) :
    MemLp (_root_.GD.N0232.N0720.N1456.d019471 m n (_root_.GD.N0232.N0720.N1286.d019591 c.coefficient))
      2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have href := c.memLp.comp_measurePreserving (_root_.GD.N0232.N0720.N1446.d019031 m n)
  have havg := (c.memLp.sub href).const_smul ((2 : ℝ)⁻¹)
  apply (memLp_congr_ae ?_).2 havg
  filter_upwards [] with omega
  rw [_root_.GD.N0232.N0720.N1286.d019594 m n hm hn c.coefficient omega]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp_def]
  ring


def d019596
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : _root_.GD.N0232.N0720.N1456.d019472 m n where
  coefficient := _root_.GD.N0232.N0720.N1286.d019591 c.coefficient
  measurable_coefficient := _root_.GD.N0232.N0720.N1286.d019593 c.measurable_coefficient
  memLp := _root_.GD.N0232.N0720.N1286.d019595 m n hm hn c



theorem d019597
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n) :
    (_root_.GD.N0232.N0720.N1286.d019596 m n hm hn c).d019473 =
      (2 : ℝ)⁻¹ • (c.d019473 + _root_.GD.N0232.N0720.N1446.d019032 m n c.d019473) := by
  have hpres := _root_.GD.N0232.N0720.N1446.d019031 m n
  have hclass : (fun omega ↦ c.d019473 omega) =ᵐ[
      (_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1446.d019019 m n)] _root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient := by
    rw [hpres.map_eq]
    exact c.memLp.coeFn_toLp
  have hclassNeg := MeasureTheory.ae_eq_comp
    (_root_.GD.N0232.N0720.N1446.d019021 m n).aemeasurable hclass
  have href : (fun omega ↦ _root_.GD.N0232.N0720.N1446.d019032 m n c.d019473 omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      (fun omega ↦ -(_root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient (_root_.GD.N0232.N0720.N1446.d019019 m n omega))) := by
    unfold _root_.GD.N0232.N0720.N1446.d019032
    refine (Lp.coeFn_neg _).trans ?_
    filter_upwards [(Lp.coeFn_compMeasurePreserving c.d019473 hpres).trans hclassNeg]
      with omega homega
    simp only [Pi.neg_apply, homega, Function.comp_def]
  apply Lp.ext
  filter_upwards [
    (_root_.GD.N0232.N0720.N1286.d019596 m n hm hn c).memLp.coeFn_toLp,
    Lp.coeFn_smul ((2 : ℝ)⁻¹) (c.d019473 + _root_.GD.N0232.N0720.N1446.d019032 m n c.d019473),
    Lp.coeFn_add c.d019473 (_root_.GD.N0232.N0720.N1446.d019032 m n c.d019473),
    c.memLp.coeFn_toLp, href]
    with omega hodd hsmul hadd hc hr
  change (_root_.GD.N0232.N0720.N1286.d019596 m n hm hn c).d019473 omega =
    _root_.GD.N0232.N0720.N1456.d019471 m n (_root_.GD.N0232.N0720.N1286.d019596 m n hm hn c).coefficient omega at hodd
  change c.d019473 omega = _root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient omega at hc
  rw [hodd, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hc, hr]
  change _root_.GD.N0232.N0720.N1456.d019471 m n (_root_.GD.N0232.N0720.N1286.d019591 c.coefficient) omega = _
  rw [_root_.GD.N0232.N0720.N1286.d019594 m n hm hn c.coefficient omega]
  ring



theorem d019598
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ ∃ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
      _root_.GD.N0232.N0720.N1468.d018953 m n c.d019473
        (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473 := by
  rintro ⟨c, hc⟩
  apply _root_.GD.N0232.N0720.N1286.d019590 m n hm hn
  refine ⟨_root_.GD.N0232.N0720.N1286.d019596 m n hm hn c,
    _root_.GD.N0232.N0720.N1286.d019592 c.coefficient, ?_⟩
  rw [_root_.GD.N0232.N0720.N1286.d019597]
  exact _root_.GD.N0232.N0720.N1472.d019550
    m n (_root_.GD.N0232.N0720.N1287.d019520 m n hm hn).d019473 c.d019473
    (_root_.GD.N0232.N0720.N1287.d019533 m n hm hn).finiteRisk
    (_root_.GD.N0232.N0720.N1446.d019039 m n
      (_root_.GD.N0232.N0720.N1287.d019533 m n hm hn)) hc

#print axioms _root_.GD.N0232.N0720.N1286.d019585
#print axioms _root_.GD.N0232.N0720.N1286.d019586
#print axioms _root_.GD.N0232.N0720.N1286.d019587
#print axioms _root_.GD.N0232.N0720.N1286.d019589
#print axioms _root_.GD.N0232.N0720.N1286.d019590
#print axioms _root_.GD.N0232.N0720.N1286.d019594
#print axioms _root_.GD.N0232.N0720.N1286.d019595
#print axioms _root_.GD.N0232.N0720.N1286.d019597
#print axioms _root_.GD.N0232.N0720.N1286.d019598

end

end GD.N0232.N0720.N1286
