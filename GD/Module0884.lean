import GD.Module0072
import GD.Module0877




















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1441

noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0230
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0660
open _root_.GD.N0230.N0637


abbrev d013676 := Set.Ioo (0 : ℝ) 1


def d013677 : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1 / 2, by constructor <;> norm_num⟩


def d013678 (m n : ℕ) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  _root_.GD.N0232.N0720.N1436.d013289 m n t.1


def d013679 (m n : ℕ) : Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  _root_.GD.N0232.N0720.N1436.d013289 m n (1 / 2)


def d013680 (t : _root_.GD.N0232.N0720.N1441.d013676) : ℝ := t.1 - 1 / 2


abbrev d013681 (m n : ℕ) := Lp ℝ 2 (_root_.GD.N0232.N0720.N1441.d013679 m n)

theorem d013682
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013678 m n t ≪ _root_.GD.N0232.N0720.N1441.d013679 m n := by
  exact _root_.GD.N0232.N0720.N1436.d013292 hm hn
    t.property.1 t.property.2 (by norm_num) (by norm_num)

theorem d013683 (m n : ℕ) :
    _root_.GD.N0232.N0720.N1441.d013678 m n _root_.GD.N0232.N0720.N1441.d013677 = _root_.GD.N0232.N0720.N1441.d013679 m n := by
  rfl

theorem d013684 : _root_.GD.N0232.N0720.N1441.d013680 _root_.GD.N0232.N0720.N1441.d013677 = 0 := by
  norm_num [_root_.GD.N0232.N0720.N1441.d013680, _root_.GD.N0232.N0720.N1441.d013677]

private theorem d013685
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1441.d013679 m n) := by
  unfold _root_.GD.N0232.N0720.N1441.d013679
  exact _root_.GD.N0232.N0720.N1434.d013564 hm hn
    (by norm_num) (by norm_num)


def d013686 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  fun x ↦ g x - 1 / 2

theorem d013687
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgIcc : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (_root_.GD.N0232.N0720.N1441.d013686 g) 2 (_root_.GD.N0232.N0720.N1441.d013679 m n) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1441.d013679 m n) :=
    _root_.GD.N0232.N0720.N1441.d013685 hm hn
  apply memLp_of_bounded
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  · filter_upwards [] with x
    constructor <;> dsimp only [_root_.GD.N0232.N0720.N1441.d013686] <;> linarith [
      (hgIcc x).1, (hgIcc x).2]
  · exact (hg.sub measurable_const).aestronglyMeasurable


def d013688
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgIcc : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) : _root_.GD.N0232.N0720.N1441.d013681 m n :=
  (_root_.GD.N0232.N0720.N1441.d013687 hm hn g hg hgIcc).toLp (_root_.GD.N0232.N0720.N1441.d013686 g)


def d013689
    (m n : ℕ) (t : _root_.GD.N0232.N0720.N1441.d013676) (d : _root_.GD.N0232.N0720.N1441.d013681 m n) : ENNReal :=
  _root_.GD.N0230.N0602.d000117
    (_root_.GD.N0232.N0720.N1441.d013678 m n t) (_root_.GD.N0232.N0720.N1441.d013680 t) d


def d013690
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1) : _root_.GD.N0232.N0720.N1441.d013681 m n :=
  _root_.GD.N0230.N0660.d000887
    (_root_.GD.N0232.N0720.N1441.d013679 m n) (_root_.GD.N0232.N0720.N1441.d013678 m n) _root_.GD.N0232.N0720.N1441.d013680 _root_.GD.N0232.N0720.N1441.d013677
    (_root_.GD.N0232.N0720.N1441.d013688 hm hn seed hseed hseedIcc)
    (_root_.GD.N0232.N0720.N1441.d013682 hm hn)
    (_root_.GD.N0232.N0720.N1441.d013683 m n) _root_.GD.N0232.N0720.N1441.d013684

theorem d013691
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1441.d013689 m n)
        (_root_.GD.N0232.N0720.N1441.d013688 hm hn seed hseed hseedIcc)
        (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc) ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1441.d013689 m n)
        (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc) ∧
      (∀ d,
        _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1441.d013689 m n)
            (_root_.GD.N0232.N0720.N1441.d013688 hm hn seed hseed hseedIcc) d →
          ‖d - _root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc‖ ^ 2 ≤
            ‖d‖ ^ 2 -
              ‖_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc‖ ^ 2) := by
  have hspec := _root_.GD.N0230.N0660.d000888
    (_root_.GD.N0232.N0720.N1441.d013679 m n) (_root_.GD.N0232.N0720.N1441.d013678 m n) _root_.GD.N0232.N0720.N1441.d013680 _root_.GD.N0232.N0720.N1441.d013677
    (_root_.GD.N0232.N0720.N1441.d013688 hm hn seed hseed hseedIcc)
    (_root_.GD.N0232.N0720.N1441.d013682 hm hn)
    (_root_.GD.N0232.N0720.N1441.d013683 m n) _root_.GD.N0232.N0720.N1441.d013684
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.2⟩




def d013692 (x : ℝ) : ℝ :=
  _root_.GD.N0230.N0637.d000240 (x + 1 / 2) - 1 / 2

theorem d013693 : Measurable _root_.GD.N0232.N0720.N1441.d013692 := by
  unfold _root_.GD.N0232.N0720.N1441.d013692
  exact (_root_.GD.N0230.N0660.d000890.measurable.comp
    (measurable_id.add measurable_const)).sub measurable_const

theorem d013694 (x : ℝ) :
    _root_.GD.N0232.N0720.N1441.d013692 x ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
  have h := _root_.GD.N0230.N0637.d000243 (x + 1 / 2)
  constructor <;> unfold _root_.GD.N0232.N0720.N1441.d013692 <;> linarith [h.1, h.2]

theorem d013695
    {t x : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1441.d013692 x - (t - 1 / 2)) ^ 2 ≤
      (x - (t - 1 / 2)) ^ 2 := by
  have h := _root_.GD.N0230.N0637.d000246
    (t := t) (x := x + 1 / 2) ht
  unfold _root_.GD.N0232.N0720.N1441.d013692
  convert h using 1 <;> ring

theorem d013696
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (d : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    MemLp (fun x ↦ _root_.GD.N0232.N0720.N1441.d013692 (d x)) 2 (_root_.GD.N0232.N0720.N1441.d013679 m n) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1441.d013679 m n) :=
    _root_.GD.N0232.N0720.N1441.d013685 hm hn
  apply memLp_of_bounded
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  · filter_upwards [] with x
    exact _root_.GD.N0232.N0720.N1441.d013694 (d x)
  · exact _root_.GD.N0232.N0720.N1441.d013693.aestronglyMeasurable.comp_aemeasurable
      (Lp.aestronglyMeasurable d).aemeasurable


def d013697
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (d : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1441.d013681 m n :=
  (_root_.GD.N0232.N0720.N1441.d013696 hm hn d).toLp
    (fun x ↦ _root_.GD.N0232.N0720.N1441.d013692 (d x))

theorem d013698
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (d : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    (fun x ↦ _root_.GD.N0232.N0720.N1441.d013697 hm hn d x) =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      fun x ↦ _root_.GD.N0232.N0720.N1441.d013692 (d x) := by
  simpa only [_root_.GD.N0232.N0720.N1441.d013697] using
    (_root_.GD.N0232.N0720.N1441.d013696 hm hn d).coeFn_toLp

theorem d013699
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (d : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1441.d013689 m n t (_root_.GD.N0232.N0720.N1441.d013697 hm hn d) ≤
      _root_.GD.N0232.N0720.N1441.d013689 m n t d := by
  unfold _root_.GD.N0232.N0720.N1441.d013689
    _root_.GD.N0230.N0602.d000117
  apply lintegral_mono_ae
  filter_upwards [
    (_root_.GD.N0232.N0720.N1441.d013682 hm hn t).ae_le
      (_root_.GD.N0232.N0720.N1441.d013698 hm hn d)] with x hx
  rw [hx]
  exact ENNReal.ofReal_le_ofReal
    (_root_.GD.N0232.N0720.N1441.d013695 ⟨t.property.1.le, t.property.2.le⟩)

theorem d013700
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1441.d013697 hm hn (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc) =
      _root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc := by
  apply (_root_.GD.N0232.N0720.N1441.d013691 hm hn seed hseed hseedIcc).2.1
  intro t
  exact _root_.GD.N0232.N0720.N1441.d013699 hm hn t _




def d013701
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  fun x ↦ _root_.GD.N0230.N0637.d000240
    (_root_.GD.N0230.N0660.d000897 (_root_.GD.N0232.N0720.N1441.d013679 m n)
      (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc) x + 1 / 2)

theorem d013702
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1) :
    Measurable (_root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc) := by
  unfold _root_.GD.N0232.N0720.N1441.d013701
  exact _root_.GD.N0230.N0660.d000890.measurable.comp
    ((_root_.GD.N0230.N0660.d000898 _ _).add measurable_const)

theorem d013703
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1)
    (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc x ∈ Set.Icc (0 : ℝ) 1 :=
  _root_.GD.N0230.N0637.d000243 _

theorem d013704
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1441.d013686 (_root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc) =ᵐ[
        _root_.GD.N0232.N0720.N1441.d013679 m n]
      fun x ↦ _root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc x := by
  have hrep := _root_.GD.N0230.N0660.d000899 (_root_.GD.N0232.N0720.N1441.d013679 m n)
    (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc)
  have hclip := _root_.GD.N0232.N0720.N1441.d013698 hm hn
    (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc)
  have hfixed := _root_.GD.N0232.N0720.N1441.d013700
    hm hn seed hseed hseedIcc
  filter_upwards [hrep, hclip] with x hrepX hclipX
  change _root_.GD.N0230.N0637.d000240
      (_root_.GD.N0230.N0660.d000897 (_root_.GD.N0232.N0720.N1441.d013679 m n)
        (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc) x + 1 / 2) - 1 / 2 =
    _root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc x
  rw [hrepX]
  change _root_.GD.N0232.N0720.N1441.d013692
      (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc x) = _
  rw [← hclipX, hfixed]


def d013705
    (m n : ℕ) (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal ((g x - t.1) ^ 2) ∂_root_.GD.N0232.N0720.N1441.d013678 m n t

theorem d013706
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hgmem : MemLp (_root_.GD.N0232.N0720.N1441.d013686 g) 2 (_root_.GD.N0232.N0720.N1441.d013679 m n)) :
    _root_.GD.N0232.N0720.N1441.d013705 m n t g = _root_.GD.N0232.N0720.N1441.d013689 m n t
      (hgmem.toLp (_root_.GD.N0232.N0720.N1441.d013686 g)) := by
  unfold _root_.GD.N0232.N0720.N1441.d013705 _root_.GD.N0232.N0720.N1441.d013689
    _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [
    (_root_.GD.N0232.N0720.N1441.d013682 hm hn t).ae_le
      hgmem.coeFn_toLp] with x hx
  rw [hx]
  unfold _root_.GD.N0232.N0720.N1441.d013686 _root_.GD.N0232.N0720.N1441.d013680
  congr 2
  ring

theorem d013707
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013705 m n t (_root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc) =
      _root_.GD.N0232.N0720.N1441.d013689 m n t
        (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc) := by
  unfold _root_.GD.N0232.N0720.N1441.d013705 _root_.GD.N0232.N0720.N1441.d013689
    _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [
    (_root_.GD.N0232.N0720.N1441.d013682 hm hn t).ae_le
      (_root_.GD.N0232.N0720.N1441.d013704 hm hn seed hseed hseedIcc)]
      with x hx
  rw [← hx]
  unfold _root_.GD.N0232.N0720.N1441.d013686 _root_.GD.N0232.N0720.N1441.d013680
  congr 2
  ring

theorem d013708
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013705 m n t (_root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc) ≤
      _root_.GD.N0232.N0720.N1441.d013705 m n t seed := by
  rw [_root_.GD.N0232.N0720.N1441.d013707 hm hn seed hseed hseedIcc]
  have hbelow := (_root_.GD.N0232.N0720.N1441.d013691 hm hn seed hseed hseedIcc).1 t
  rw [_root_.GD.N0232.N0720.N1441.d013706 hm hn t seed
    (_root_.GD.N0232.N0720.N1441.d013687 hm hn seed hseed hseedIcc)]
  exact hbelow

theorem d013709
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed baseline : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1)
    (hstrict : ∀ t, _root_.GD.N0232.N0720.N1441.d013705 m n t seed < _root_.GD.N0232.N0720.N1441.d013705 m n t baseline) :
    ∀ t, _root_.GD.N0232.N0720.N1441.d013705 m n t
        (_root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc) <
      _root_.GD.N0232.N0720.N1441.d013705 m n t baseline := by
  intro t
  exact lt_of_le_of_lt
    (_root_.GD.N0232.N0720.N1441.d013708
      hm hn seed hseed hseedIcc t) (hstrict t)



theorem d013710
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1)
    (competitor : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hcompetitor : Measurable competitor)
    (hcompetitorIcc : ∀ x, competitor x ∈ Set.Icc (0 : ℝ) 1)
    (hdom : ∀ t,
      _root_.GD.N0232.N0720.N1441.d013705 m n t competitor ≤
        _root_.GD.N0232.N0720.N1441.d013705 m n t
          (_root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc)) :
    competitor =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      _root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc := by
  let competitorClass : _root_.GD.N0232.N0720.N1441.d013681 m n :=
    _root_.GD.N0232.N0720.N1441.d013688 hm hn competitor hcompetitor hcompetitorIcc
  have hweak : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1441.d013689 m n)
      competitorClass (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc) := by
    intro t
    calc
      _root_.GD.N0232.N0720.N1441.d013689 m n t competitorClass =
          _root_.GD.N0232.N0720.N1441.d013705 m n t competitor := by
        symm
        exact _root_.GD.N0232.N0720.N1441.d013706 hm hn t competitor
          (_root_.GD.N0232.N0720.N1441.d013687 hm hn competitor hcompetitor hcompetitorIcc)
      _ ≤ _root_.GD.N0232.N0720.N1441.d013705 m n t
          (_root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc) := hdom t
      _ = _root_.GD.N0232.N0720.N1441.d013689 m n t
          (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc) :=
        _root_.GD.N0232.N0720.N1441.d013707 hm hn seed hseed hseedIcc t
  have hclass : competitorClass =
      _root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc :=
    (_root_.GD.N0232.N0720.N1441.d013691 hm hn seed hseed hseedIcc).2.1
      competitorClass hweak
  have hcompAE :=
    (_root_.GD.N0232.N0720.N1441.d013687 hm hn competitor hcompetitor hcompetitorIcc).coeFn_toLp
  filter_upwards [hcompAE,
    _root_.GD.N0232.N0720.N1441.d013704 hm hn seed hseed hseedIcc] with x hx hstar
  have hxClass : competitorClass x =
      _root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedIcc x := by rw [hclass]
  unfold competitorClass _root_.GD.N0232.N0720.N1441.d013688 at hxClass
  rw [hx, ← hstar] at hxClass
  unfold _root_.GD.N0232.N0720.N1441.d013686 at hxClass
  linarith





theorem d013711
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed baseline : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hseed : Measurable seed)
    (hseedIcc : ∀ x, seed x ∈ Set.Icc (0 : ℝ) 1)
    (hstrict : ∀ t, _root_.GD.N0232.N0720.N1441.d013705 m n t seed < _root_.GD.N0232.N0720.N1441.d013705 m n t baseline) :
    ∃ selected : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable selected ∧
      (∀ x, selected x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, _root_.GD.N0232.N0720.N1441.d013705 m n t selected < _root_.GD.N0232.N0720.N1441.d013705 m n t baseline) ∧
      (∀ competitor : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
        Measurable competitor →
        (∀ x, competitor x ∈ Set.Icc (0 : ℝ) 1) →
        (∀ t, _root_.GD.N0232.N0720.N1441.d013705 m n t competitor ≤
          _root_.GD.N0232.N0720.N1441.d013705 m n t selected) →
        competitor =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] selected) := by
  refine ⟨_root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedIcc,
    _root_.GD.N0232.N0720.N1441.d013702 hm hn seed hseed hseedIcc,
    _root_.GD.N0232.N0720.N1441.d013703 hm hn seed hseed hseedIcc,
    _root_.GD.N0232.N0720.N1441.d013709
      hm hn seed baseline hseed hseedIcc hstrict, ?_⟩
  intro competitor hcompetitor hcompetitorIcc hdom
  exact _root_.GD.N0232.N0720.N1441.d013710 hm hn seed hseed hseedIcc
    competitor hcompetitor hcompetitorIcc hdom

end

end N1441
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1441.d013691
#print axioms _root_.GD.N0232.N0720.N1441.d013700
#print axioms _root_.GD.N0232.N0720.N1441.d013710
#print axioms _root_.GD.N0232.N0720.N1441.d013711
