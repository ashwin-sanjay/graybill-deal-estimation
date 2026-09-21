import GD.Module1625
import GD.Module1607
import GD.Module0955
import Mathlib.MeasureTheory.Function.L2Space





























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace GD.N0106.N0428.N0770.N1720
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1207
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1724
open _root_.GD.N0106.N0428.N0770.N1722
open _root_.GD.N0106.N0428.N0770.N1742
open _root_.GD.N0106.N0428.N0770.N1729




abbrev d027841 := _root_.GD.N0232.N0720.N1080.d014168



abbrev d027842 : Measure _root_.GD.N0106.N0428.N0770.N1724.d024295 := _root_.GD.N0107.d009030 2 2 0 1 1


abbrev d027843 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : Measure _root_.GD.N0106.N0428.N0770.N1724.d024295 :=
  _root_.GD.N0107.d009030 2 2 θ.location θ.scale₁ θ.scale₂


def d027844 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ :=
  _root_.GD.N0232.N0720.N1499.d015001 2 2 θ ω

def d027845 : _root_.GD.N0106.N0428.N0770.N1720.d027841 := _root_.GD.N0232.N0720.N1080.d014169

theorem d027846 : _root_.GD.N0106.N0428.N0770.N1720.d027845.location = 0 := rfl

theorem d027847 : _root_.GD.N0106.N0428.N0770.N1720.d027843 _root_.GD.N0106.N0428.N0770.N1720.d027845 = _root_.GD.N0106.N0428.N0770.N1720.d027842 := rfl

theorem d027848 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : 0 ≤ _root_.GD.N0106.N0428.N0770.N1720.d027844 θ ω :=
  _root_.GD.N0232.N0720.N1499.d015003 2 2 θ ω

theorem d027849 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : Measurable (_root_.GD.N0106.N0428.N0770.N1720.d027844 θ) :=
  _root_.GD.N0232.N0720.N1499.d015002 2 2 θ


theorem d027850 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) :
    _root_.GD.N0106.N0428.N0770.N1720.d027843 θ = _root_.GD.N0106.N0428.N0770.N1720.d027842.withDensity (fun ω => ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1720.d027844 θ ω)) :=
  _root_.GD.N0232.N0720.N1499.d015006 2 2 θ

theorem d027851 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) (g : _root_.GD.N0106.N0428.N0770.N1724.d024295 → ℝ) :
    ∫ ω, g ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027843 θ = ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027844 θ ω * g ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  rw [_root_.GD.N0106.N0428.N0770.N1720.d027850, integral_withDensity_eq_integral_toReal_smul (_root_.GD.N0106.N0428.N0770.N1720.d027849 θ).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (_root_.GD.N0106.N0428.N0770.N1720.d027848 θ ω), smul_eq_mul]

theorem d027852 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) {g : _root_.GD.N0106.N0428.N0770.N1724.d024295 → ℝ} (hg : Integrable g (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ)) :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027844 θ ω * g ω) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  rw [_root_.GD.N0106.N0428.N0770.N1720.d027850, integrable_withDensity_iff_integrable_smul' (_root_.GD.N0106.N0428.N0770.N1720.d027849 θ).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hg
  exact hg.congr (Filter.Eventually.of_forall fun ω => by
    dsimp only
    rw [ENNReal.toReal_ofReal (_root_.GD.N0106.N0428.N0770.N1720.d027848 θ ω), smul_eq_mul])

theorem d027853 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : Integrable (_root_.GD.N0106.N0428.N0770.N1720.d027844 θ) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  have h := _root_.GD.N0106.N0428.N0770.N1720.d027852 θ (integrable_const (1 : ℝ))
  simpa only [mul_one] using h



def d027854 (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1725.d024158 (_root_.GD.N0107.d009084 ω.1) (_root_.GD.N0107.d009084 ω.2)
    (_root_.GD.N0107.d009085 ω.1) (_root_.GD.N0107.d009085 ω.2)

def d027855 (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1725.d024159 (_root_.GD.N0107.d009084 ω.1) (_root_.GD.N0107.d009084 ω.2)
    (_root_.GD.N0107.d009085 ω.1) (_root_.GD.N0107.d009085 ω.2)

def d027856 (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1725.d024119 * _root_.GD.N0107.d009090 2 2 ω * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1724.d024300 ω)

theorem d027857 (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : _root_.GD.N0106.N0428.N0770.N1720.d027855 ω = _root_.GD.N0106.N0428.N0770.N1720.d027854 ω + _root_.GD.N0106.N0428.N0770.N1720.d027856 ω := by
  simp only [_root_.GD.N0106.N0428.N0770.N1720.d027855, _root_.GD.N0106.N0428.N0770.N1720.d027854, _root_.GD.N0106.N0428.N0770.N1720.d027856, _root_.GD.N0106.N0428.N0770.N1725.d024164, _root_.GD.N0106.N0428.N0770.N1724.d024307,
    _root_.GD.N0107.d009090]

theorem d027858 : Measurable _root_.GD.N0106.N0428.N0770.N1720.d027854 := by
  have hstats : Measurable (fun ω : _root_.GD.N0106.N0428.N0770.N1724.d024295 => (_root_.GD.N0107.d009084 ω.1, _root_.GD.N0107.d009084 ω.2,
      _root_.GD.N0107.d009085 ω.1, _root_.GD.N0107.d009085 ω.2)) := by
    unfold _root_.GD.N0107.d009084 _root_.GD.N0107.d009085 _root_.GD.N0126.d006422
      _root_.GD.N0126.d006421 _root_.GD.N0126.d006420
    fun_prop
  exact (_root_.GD.N0106.N0428.N0770.N1725.d024168 _root_.GD.N0106.N0428.N0770.N1725.d024117 0).comp hstats

theorem d027859 : Measurable _root_.GD.N0106.N0428.N0770.N1720.d027856 :=
  (measurable_const.mul _root_.GD.N0106.N0428.N0770.N1724.d024308.fst).mul (_root_.GD.N0106.N0428.N0770.N1725.d024138.comp _root_.GD.N0106.N0428.N0770.N1724.d024310)


theorem d027860 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : MemLp (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027855 ω - θ.location) 2 (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) :=
  (_root_.GD.N0106.N0428.N0770.N1724.d024328 θ.location θ.scale₁ θ.scale₂ _root_.GD.N0106.N0428.N0770.N1725.d024117 _root_.GD.N0106.N0428.N0770.N1725.d024119
    θ.scale₁_pos θ.scale₂_pos).1


theorem d027861 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : MemLp (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027854 ω - θ.location) 2 (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) :=
  (_root_.GD.N0106.N0428.N0770.N1724.d024328 θ.location θ.scale₁ θ.scale₂ _root_.GD.N0106.N0428.N0770.N1725.d024117 0
    θ.scale₁_pos θ.scale₂_pos).1

theorem d027862 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : MemLp _root_.GD.N0106.N0428.N0770.N1720.d027856 2 (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) :=
  ((_root_.GD.N0106.N0428.N0770.N1720.d027860 θ).sub (_root_.GD.N0106.N0428.N0770.N1720.d027861 θ)).ae_eq (Filter.Eventually.of_forall fun ω => by
    simp only [Pi.sub_apply, _root_.GD.N0106.N0428.N0770.N1720.d027857]
    ring)

theorem d027863 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : MemLp _root_.GD.N0106.N0428.N0770.N1720.d027854 2 (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) :=
  ((_root_.GD.N0106.N0428.N0770.N1720.d027861 θ).add (memLp_const θ.location)).ae_eq (Filter.Eventually.of_forall fun ω => by
    simp only [Pi.add_apply]
    ring)

theorem d027864 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2) (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) :=
  (_root_.GD.N0106.N0428.N0770.N1720.d027862 θ).integrable_sq

theorem d027865 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : Integrable _root_.GD.N0106.N0428.N0770.N1720.d027856 (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) :=
  (_root_.GD.N0106.N0428.N0770.N1720.d027862 θ).integrable one_le_two

theorem d027866 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2) (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) :=
  (_root_.GD.N0106.N0428.N0770.N1720.d027863 θ).integrable_sq


theorem d027867 : MemLp _root_.GD.N0106.N0428.N0770.N1720.d027856 2 _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  simpa only [_root_.GD.N0106.N0428.N0770.N1720.d027847] using _root_.GD.N0106.N0428.N0770.N1720.d027862 _root_.GD.N0106.N0428.N0770.N1720.d027845


def d027868 : Lp ℝ 2 _root_.GD.N0106.N0428.N0770.N1720.d027842 := _root_.GD.N0106.N0428.N0770.N1720.d027867.toLp _root_.GD.N0106.N0428.N0770.N1720.d027856

theorem d027869 : _root_.GD.N0106.N0428.N0770.N1720.d027868 =ᵐ[_root_.GD.N0106.N0428.N0770.N1720.d027842] _root_.GD.N0106.N0428.N0770.N1720.d027856 :=
  MemLp.coeFn_toLp _root_.GD.N0106.N0428.N0770.N1720.d027867


theorem d027870 : ‖_root_.GD.N0106.N0428.N0770.N1720.d027868‖ ^ 2 = ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0106.N0428.N0770.N1720.d027869] with ω hω
  simp only [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]


theorem d027871 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027856 ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω) (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) := by
  have hsum : MemLp (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027856 ω + _root_.GD.N0106.N0428.N0770.N1720.d027854 ω) 2 (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) :=
    ((_root_.GD.N0106.N0428.N0770.N1720.d027862 θ).add (_root_.GD.N0106.N0428.N0770.N1720.d027863 θ)).ae_eq (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.add_apply])
  have h := ((hsum.integrable_sq.sub (_root_.GD.N0106.N0428.N0770.N1720.d027864 θ)).sub (_root_.GD.N0106.N0428.N0770.N1720.d027866 θ)).const_mul
    (1 / 2)
  exact h.congr (Filter.Eventually.of_forall fun ω => by
    simp only [Pi.sub_apply]
    ring)




def d027872 (μ : ℝ) (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ := _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 + 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - μ))

theorem d027873 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : Integrable (_root_.GD.N0106.N0428.N0770.N1720.d027872 θ.location) (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) := by
  have h1 : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - θ.location)) (_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) :=
    ((_root_.GD.N0106.N0428.N0770.N1720.d027871 θ).sub ((_root_.GD.N0106.N0428.N0770.N1720.d027865 θ).const_mul θ.location)).congr
      (Filter.Eventually.of_forall fun ω => by
        simp only [Pi.sub_apply]
        ring)
  exact (_root_.GD.N0106.N0428.N0770.N1720.d027864 θ).add (h1.const_mul 2)


theorem d027874 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) : ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027872 θ.location ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027843 θ < 0 := by
  have hlt : (∫ ω, (_root_.GD.N0106.N0428.N0770.N1720.d027855 ω - θ.location) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) <
      ∫ ω, (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - θ.location) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027843 θ :=
    _root_.GD.N0106.N0428.N0770.N1742.d027798 θ.location θ.scale₁ θ.scale₂ θ.scale₁_pos θ.scale₂_pos
  have hid : (∫ ω, (_root_.GD.N0106.N0428.N0770.N1720.d027855 ω - θ.location) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027843 θ) -
      ∫ ω, (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - θ.location) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027843 θ = ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027872 θ.location ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027843 θ := by
    rw [← integral_sub (_root_.GD.N0106.N0428.N0770.N1720.d027860 θ).integrable_sq (_root_.GD.N0106.N0428.N0770.N1720.d027861 θ).integrable_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    unfold _root_.GD.N0106.N0428.N0770.N1720.d027872
    dsimp only
    rw [_root_.GD.N0106.N0428.N0770.N1720.d027857]
    ring
  linarith [hlt, hid]


theorem d027875 (θ : _root_.GD.N0106.N0428.N0770.N1720.d027841) :
    ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027844 θ ω * _root_.GD.N0106.N0428.N0770.N1720.d027872 θ.location ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 < 0 := by
  rw [← _root_.GD.N0106.N0428.N0770.N1720.d027851]
  exact _root_.GD.N0106.N0428.N0770.N1720.d027874 θ

theorem d027876 : ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027872 0 ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 < 0 := by
  have h := _root_.GD.N0106.N0428.N0770.N1720.d027874 _root_.GD.N0106.N0428.N0770.N1720.d027845
  rwa [_root_.GD.N0106.N0428.N0770.N1720.d027847, _root_.GD.N0106.N0428.N0770.N1720.d027846] at h




theorem d027877 :
    27 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 4096 ≤
      ∫ ω, _root_.GD.N0107.d009090 2 2 ω ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1724.d024300 ω) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  rw [_root_.GD.N0106.N0428.N0770.N1729.d027423, _root_.GD.N0106.N0428.N0770.N1729.d027420]
  have hI := _root_.GD.N0106.N0428.N0770.N1729.d027424
  have hpi := Real.pi_le_four
  have hK : 0 ≤ 3 / (32 * Real.pi) := by positivity
  calc
    27 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 4096 ≤ 27 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / (1024 * Real.pi) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [hpi])
    _ = 3 / (32 * Real.pi) * (9 / 32 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hI hK



section Packet

variable {ι : Type*} [Fintype ι] (θ : ι → _root_.GD.N0106.N0428.N0770.N1720.d027841) (w : ι → ℝ)


def d027878 (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ := ∑ i, w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω


def d027879 (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ := 1 + _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω


def d027880 (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ := ∑ i, w i * (θ i).location * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω


def d027881 (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ := _root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω / _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω


def d027882 : ℝ := ∑ i, |(θ i).location|


def d027883 : ℝ := ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842


def d027884 : ℝ := ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842

variable {θ w}

theorem d027885 (hw : ∀ i, 0 ≤ w i) (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : 0 ≤ _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (_root_.GD.N0106.N0428.N0770.N1720.d027848 _ _)

theorem d027886 (hw : ∀ i, 0 ≤ w i) (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : 1 ≤ _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω := by
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027879
  linarith [_root_.GD.N0106.N0428.N0770.N1720.d027885 (θ := θ) (w := w) hw ω]

theorem d027887 (hw : ∀ i, 0 ≤ w i) (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : 0 < _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω := by
  linarith [_root_.GD.N0106.N0428.N0770.N1720.d027886 (θ := θ) (w := w) hw ω]

theorem d027888 : 0 ≤ _root_.GD.N0106.N0428.N0770.N1720.d027882 θ := Finset.sum_nonneg fun i _ => abs_nonneg _

theorem d027889 (i : ι) : |(θ i).location| ≤ _root_.GD.N0106.N0428.N0770.N1720.d027882 θ :=
  Finset.single_le_sum (fun j _ => abs_nonneg ((θ j).location)) (Finset.mem_univ i)

theorem d027890 (hw : ∀ i, 0 ≤ w i) (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) : |_root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω| ≤ _root_.GD.N0106.N0428.N0770.N1720.d027882 θ * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω := by
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027880 _root_.GD.N0106.N0428.N0770.N1720.d027878
  calc |∑ i, w i * (θ i).location * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω|
      ≤ ∑ i, |w i * (θ i).location * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, _root_.GD.N0106.N0428.N0770.N1720.d027882 θ * (w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (hw i), abs_of_nonneg (_root_.GD.N0106.N0428.N0770.N1720.d027848 _ _)]
        have hμ := _root_.GD.N0106.N0428.N0770.N1720.d027889 (θ := θ) i
        have hwl : 0 ≤ w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω := mul_nonneg (hw i) (_root_.GD.N0106.N0428.N0770.N1720.d027848 _ _)
        calc w i * |(θ i).location| * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω = (w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) * |(θ i).location| := by ring
          _ ≤ (w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) * _root_.GD.N0106.N0428.N0770.N1720.d027882 θ := mul_le_mul_of_nonneg_left hμ hwl
          _ = _root_.GD.N0106.N0428.N0770.N1720.d027882 θ * (w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) := by ring
    _ = _root_.GD.N0106.N0428.N0770.N1720.d027882 θ * ∑ i, w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω := by rw [Finset.mul_sum]

theorem d027891 (hw : ∀ i, 0 ≤ w i) (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) :
    _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω ^ 2 ≤ _root_.GD.N0106.N0428.N0770.N1720.d027882 θ ^ 2 * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω := by
  have hM := _root_.GD.N0106.N0428.N0770.N1720.d027887 (θ := θ) (w := w) hw ω
  have hS := _root_.GD.N0106.N0428.N0770.N1720.d027885 (θ := θ) (w := w) hw ω
  have hK := _root_.GD.N0106.N0428.N0770.N1720.d027888 (θ := θ)
  have hA2 : _root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω ^ 2 ≤ (_root_.GD.N0106.N0428.N0770.N1720.d027882 θ * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω) ^ 2 := by
    rw [← sq_abs (_root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (_root_.GD.N0106.N0428.N0770.N1720.d027890 (θ := θ) (w := w) hw ω) 2
  have hM' := hM.ne'
  have hc : _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω ^ 2 = _root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω ^ 2 / _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω := by
    unfold _root_.GD.N0106.N0428.N0770.N1720.d027881
    field_simp [hM']
    <;> ring
  rw [hc, div_le_iff₀ hM]
  have hMS : _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω = 1 + _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω := rfl
  rw [hMS]
  calc _root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω ^ 2 ≤ (_root_.GD.N0106.N0428.N0770.N1720.d027882 θ * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω) ^ 2 := hA2
    _ = _root_.GD.N0106.N0428.N0770.N1720.d027882 θ ^ 2 * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω := by ring
    _ ≤ _root_.GD.N0106.N0428.N0770.N1720.d027882 θ ^ 2 * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω * (1 + _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (sq_nonneg _) hS)


theorem d027892 (hw : ∀ i, 0 ≤ w i) (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) :
    _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω) ^ 2 ≤ 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2) + 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027882 θ ^ 2 * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω) := by
  have hM := (_root_.GD.N0106.N0428.N0770.N1720.d027887 (θ := θ) (w := w) hw ω).le
  have h1 : (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω) ^ 2 ≤ 2 * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2 + 2 * _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω ^ 2 := by
    nlinarith [sq_nonneg (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω + _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω)]
  have h2 := _root_.GD.N0106.N0428.N0770.N1720.d027891 (θ := θ) (w := w) hw ω
  calc _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω) ^ 2 ≤ _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (2 * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2 + 2 * _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hM
    _ = 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2) + 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω ^ 2) := by ring
    _ ≤ 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2) + 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027882 θ ^ 2 * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω) := by linarith [h2]



theorem d027893 : Measurable (_root_.GD.N0106.N0428.N0770.N1720.d027878 θ w) := by
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027878
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul (_root_.GD.N0106.N0428.N0770.N1720.d027849 (θ i))

theorem d027894 : Measurable (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w) := by
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027879
  exact measurable_const.add _root_.GD.N0106.N0428.N0770.N1720.d027893

theorem d027895 : Measurable (_root_.GD.N0106.N0428.N0770.N1720.d027880 θ w) := by
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027880
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul (_root_.GD.N0106.N0428.N0770.N1720.d027849 (θ i))

theorem d027896 : Measurable (_root_.GD.N0106.N0428.N0770.N1720.d027881 θ w) := by
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027881
  exact _root_.GD.N0106.N0428.N0770.N1720.d027895.div _root_.GD.N0106.N0428.N0770.N1720.d027894

theorem d027897 : Integrable (_root_.GD.N0106.N0428.N0770.N1720.d027878 θ w) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027878
  exact integrable_finsetSum _ fun i _ => (_root_.GD.N0106.N0428.N0770.N1720.d027853 (θ i)).const_mul (w i)

theorem d027898 : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  have h0 : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
    have h := _root_.GD.N0106.N0428.N0770.N1720.d027864 _root_.GD.N0106.N0428.N0770.N1720.d027845
    rwa [_root_.GD.N0106.N0428.N0770.N1720.d027847] at h
  have hi : Integrable (fun ω => ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2)) _root_.GD.N0106.N0428.N0770.N1720.d027842 :=
    integrable_finsetSum _ fun i _ =>
      (_root_.GD.N0106.N0428.N0770.N1720.d027852 (θ i) (_root_.GD.N0106.N0428.N0770.N1720.d027864 (θ i))).const_mul (w i)
  refine (h0.add hi).congr (Filter.Eventually.of_forall fun ω => ?_)
  show _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 + ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2) =
    (1 + ∑ i, w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2
  rw [add_mul, one_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem d027899 : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  have h0 : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
    have h := _root_.GD.N0106.N0428.N0770.N1720.d027866 _root_.GD.N0106.N0428.N0770.N1720.d027845
    rwa [_root_.GD.N0106.N0428.N0770.N1720.d027847] at h
  have hi : Integrable (fun ω => ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2)) _root_.GD.N0106.N0428.N0770.N1720.d027842 :=
    integrable_finsetSum _ fun i _ =>
      (_root_.GD.N0106.N0428.N0770.N1720.d027852 (θ i) (_root_.GD.N0106.N0428.N0770.N1720.d027866 (θ i))).const_mul (w i)
  refine (h0.add hi).congr (Filter.Eventually.of_forall fun ω => ?_)
  show _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2 + ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2) =
    (1 + ∑ i, w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2
  rw [add_mul, one_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring


theorem d027900 :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω)) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  have h0 : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027856 ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
    have h := _root_.GD.N0106.N0428.N0770.N1720.d027871 _root_.GD.N0106.N0428.N0770.N1720.d027845
    rwa [_root_.GD.N0106.N0428.N0770.N1720.d027847] at h
  have h1 : Integrable (fun ω => ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω))) _root_.GD.N0106.N0428.N0770.N1720.d027842 :=
    integrable_finsetSum _ fun i _ =>
      (_root_.GD.N0106.N0428.N0770.N1720.d027852 (θ i) (_root_.GD.N0106.N0428.N0770.N1720.d027871 (θ i))).const_mul (w i)
  have h2 : Integrable (fun ω => ∑ i, (w i * (θ i).location) * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω)) _root_.GD.N0106.N0428.N0770.N1720.d027842 :=
    integrable_finsetSum _ fun i _ =>
      (_root_.GD.N0106.N0428.N0770.N1720.d027852 (θ i) (_root_.GD.N0106.N0428.N0770.N1720.d027865 (θ i))).const_mul (w i * (θ i).location)
  refine ((h0.add h1).sub h2).congr (Filter.Eventually.of_forall fun ω => ?_)
  show _root_.GD.N0106.N0428.N0770.N1720.d027856 ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω + ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω)) -
      ∑ i, w i * (θ i).location * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω) =
    _root_.GD.N0106.N0428.N0770.N1720.d027856 ω * ((1 + ∑ i, w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω - ∑ i, w i * (θ i).location * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω)
  have e1 : ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω)) =
      _root_.GD.N0106.N0428.N0770.N1720.d027856 ω * ((∑ i, w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, w i * (θ i).location * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω) =
      _root_.GD.N0106.N0428.N0770.N1720.d027856 ω * ∑ i, w i * (θ i).location * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  ring

theorem d027901 (hw : ∀ i, 0 ≤ w i) :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω))) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  refine (_root_.GD.N0106.N0428.N0770.N1720.d027900 (θ := θ) (w := w)).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  have hM := (_root_.GD.N0106.N0428.N0770.N1720.d027887 (θ := θ) (w := w) hw ω).ne'
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027881
  field_simp [hM]
  <;> ring


theorem d027902 (hw : ∀ i, 0 ≤ w i) :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω) ^ 2) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  have hg : Integrable (fun ω => 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω ^ 2) + 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027882 θ ^ 2 * _root_.GD.N0106.N0428.N0770.N1720.d027878 θ w ω)) _root_.GD.N0106.N0428.N0770.N1720.d027842 :=
    ((_root_.GD.N0106.N0428.N0770.N1720.d027899 (θ := θ) (w := w)).const_mul 2).add
      ((_root_.GD.N0106.N0428.N0770.N1720.d027897 (θ := θ) (w := w)).const_mul (_root_.GD.N0106.N0428.N0770.N1720.d027882 θ ^ 2) |>.const_mul 2)
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (_root_.GD.N0106.N0428.N0770.N1720.d027894.mul ((_root_.GD.N0106.N0428.N0770.N1720.d027858.sub _root_.GD.N0106.N0428.N0770.N1720.d027896).pow_const 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (_root_.GD.N0106.N0428.N0770.N1720.d027887 (θ := θ) (w := w) hw ω).le (sq_nonneg _))]
    exact _root_.GD.N0106.N0428.N0770.N1720.d027892 (θ := θ) (w := w) hw ω



theorem d027903 (ω : _root_.GD.N0106.N0428.N0770.N1724.d024295) :
    _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 + 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω)) =
      _root_.GD.N0106.N0428.N0770.N1720.d027872 0 ω + ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027872 (θ i).location ω) := by
  have e : ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027872 (θ i).location ω) =
      (∑ i, w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 +
        2 * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * ((∑ i, w i * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω) * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω -
          ∑ i, w i * (θ i).location * _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω)) := by
    first
      | (rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum,
            Finset.mul_sum, ← Finset.sum_add_distrib]
         exact Finset.sum_congr rfl fun i _ => by unfold _root_.GD.N0106.N0428.N0770.N1720.d027872; ring)
      | (simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
         exact Finset.sum_congr rfl fun i _ => by unfold _root_.GD.N0106.N0428.N0770.N1720.d027872; ring)
  rw [e]
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027879 _root_.GD.N0106.N0428.N0770.N1720.d027878 _root_.GD.N0106.N0428.N0770.N1720.d027880 _root_.GD.N0106.N0428.N0770.N1720.d027872
  ring



theorem d027904 (hw : ∀ i, 0 ≤ w i) :
    _root_.GD.N0106.N0428.N0770.N1720.d027883 θ w + 2 * ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω)) ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 < 0 := by
  have hint0 : Integrable (_root_.GD.N0106.N0428.N0770.N1720.d027872 0) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
    have h := _root_.GD.N0106.N0428.N0770.N1720.d027873 _root_.GD.N0106.N0428.N0770.N1720.d027845
    rwa [_root_.GD.N0106.N0428.N0770.N1720.d027847, _root_.GD.N0106.N0428.N0770.N1720.d027846] at h
  have hG : ∀ i, Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027872 (θ i).location ω) _root_.GD.N0106.N0428.N0770.N1720.d027842 :=
    fun i => _root_.GD.N0106.N0428.N0770.N1720.d027852 (θ i) (_root_.GD.N0106.N0428.N0770.N1720.d027873 (θ i))
  have hsum : Integrable (fun ω => ∑ i, w i * (_root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027872 (θ i).location ω)) _root_.GD.N0106.N0428.N0770.N1720.d027842 :=
    integrable_finsetSum _ fun i _ => (hG i).const_mul (w i)
  have hpieces : (∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027872 0 ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027842) + ∑ i, w i * ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027872 (θ i).location ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 < 0 := by
    have hneg : ∑ i, w i * ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027872 (θ i).location ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw i) (_root_.GD.N0106.N0428.N0770.N1720.d027875 (θ i)).le
    linarith [_root_.GD.N0106.N0428.N0770.N1720.d027876, hneg]
  have hcombined : (∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027872 0 ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027842) + ∑ i, w i * ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027844 (θ i) ω * _root_.GD.N0106.N0428.N0770.N1720.d027872 (θ i).location ω ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 =
      ∫ ω, (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 + 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω))) ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        _root_.GD.N0106.N0428.N0770.N1720.d027903 (θ := θ) (w := w) ω),
      integral_add hint0 hsum, integral_finsetSum _ fun i _ => (hG i).const_mul (w i)]
    simp only [integral_const_mul]
  have hsplit : ∫ ω, (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 + 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027880 θ w ω))) ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 =
      _root_.GD.N0106.N0428.N0770.N1720.d027883 θ w + 2 * ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω)) ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 := by
    unfold _root_.GD.N0106.N0428.N0770.N1720.d027883
    rw [integral_add (_root_.GD.N0106.N0428.N0770.N1720.d027898 (θ := θ) (w := w))
      ((_root_.GD.N0106.N0428.N0770.N1720.d027900 (θ := θ) (w := w)).const_mul 2), integral_const_mul]
    congr 2
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    have hM := (_root_.GD.N0106.N0428.N0770.N1720.d027887 (θ := θ) (w := w) hw ω).ne'
    unfold _root_.GD.N0106.N0428.N0770.N1720.d027881
    field_simp [hM]
    <;> ring
  linarith [hpieces, hcombined, hsplit]



theorem d027905 (hw : ∀ i, 0 ≤ w i) (lam : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1720.d027883 θ w + 2 * lam * (∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω)) ∂_root_.GD.N0106.N0428.N0770.N1720.d027842)
      + lam ^ 2 * _root_.GD.N0106.N0428.N0770.N1720.d027884 θ w := by
  have hnn : 0 ≤ ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω + lam * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω)) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 :=
    integral_nonneg fun ω => mul_nonneg (_root_.GD.N0106.N0428.N0770.N1720.d027887 (θ := θ) (w := w) hw ω).le (sq_nonneg _)
  have hexp : ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω + lam * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω)) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 =
      _root_.GD.N0106.N0428.N0770.N1720.d027883 θ w + 2 * lam * (∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω)) ∂_root_.GD.N0106.N0428.N0770.N1720.d027842)
        + lam ^ 2 * _root_.GD.N0106.N0428.N0770.N1720.d027884 θ w := by
    unfold _root_.GD.N0106.N0428.N0770.N1720.d027883 _root_.GD.N0106.N0428.N0770.N1720.d027884
    have hfirst : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 +
        2 * lam * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω)))) _root_.GD.N0106.N0428.N0770.N1720.d027842 :=
      (_root_.GD.N0106.N0428.N0770.N1720.d027898 (θ := θ) (w := w)).add
        ((_root_.GD.N0106.N0428.N0770.N1720.d027901 (θ := θ) (w := w) hw).const_mul (2 * lam))
    calc
      _ = ∫ ω, (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 +
          2 * lam * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027856 ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω)))) +
          lam ^ 2 * (_root_.GD.N0106.N0428.N0770.N1720.d027879 θ w ω * (_root_.GD.N0106.N0428.N0770.N1720.d027854 ω - _root_.GD.N0106.N0428.N0770.N1720.d027881 θ w ω) ^ 2) ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        dsimp only
        ring
      _ = _ := by
        rw [integral_add hfirst
          ((_root_.GD.N0106.N0428.N0770.N1720.d027902 (θ := θ) (w := w) hw).const_mul (lam ^ 2))]
        rw [integral_add (_root_.GD.N0106.N0428.N0770.N1720.d027898 (θ := θ) (w := w))
            ((_root_.GD.N0106.N0428.N0770.N1720.d027901 (θ := θ) (w := w) hw).const_mul (2 * lam))]
        simp only [integral_const_mul]
  linarith [hnn, hexp]


theorem d027906 (hw : ∀ i, 0 ≤ w i) : 0 < _root_.GD.N0106.N0428.N0770.N1720.d027884 θ w ∧ _root_.GD.N0106.N0428.N0770.N1720.d027883 θ w < 4 * _root_.GD.N0106.N0428.N0770.N1720.d027884 θ w := by
  have h1 := _root_.GD.N0106.N0428.N0770.N1720.d027905 (θ := θ) (w := w) hw 1
  have h2 := _root_.GD.N0106.N0428.N0770.N1720.d027905 (θ := θ) (w := w) hw 2
  have hd := _root_.GD.N0106.N0428.N0770.N1720.d027904 (θ := θ) (w := w) hw
  constructor
  · linarith [h1, hd]
  · linarith [h2, hd]


theorem d027907 (hw : ∀ i, 0 ≤ w i) : ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 ≤ _root_.GD.N0106.N0428.N0770.N1720.d027883 θ w := by
  have h0 : Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2) _root_.GD.N0106.N0428.N0770.N1720.d027842 := by
    have h := _root_.GD.N0106.N0428.N0770.N1720.d027864 _root_.GD.N0106.N0428.N0770.N1720.d027845
    rwa [_root_.GD.N0106.N0428.N0770.N1720.d027847] at h
  exact integral_mono h0 (_root_.GD.N0106.N0428.N0770.N1720.d027898 (θ := θ) (w := w))
    fun ω => le_mul_of_one_le_left (sq_nonneg _) (_root_.GD.N0106.N0428.N0770.N1720.d027886 (θ := θ) (w := w) hw ω)


theorem d027908 (hw : ∀ i, 0 ≤ w i) :
    (∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842) / 4 < _root_.GD.N0106.N0428.N0770.N1720.d027884 θ w := by
  have h := (_root_.GD.N0106.N0428.N0770.N1720.d027906 (θ := θ) (w := w) hw).2
  have h' := _root_.GD.N0106.N0428.N0770.N1720.d027907 (θ := θ) (w := w) hw
  linarith [h, h']


theorem d027909 (hw : ∀ i, 0 ≤ w i) :
    ‖_root_.GD.N0106.N0428.N0770.N1720.d027868‖ ^ 2 / 4 < _root_.GD.N0106.N0428.N0770.N1720.d027884 θ w := by
  rw [_root_.GD.N0106.N0428.N0770.N1720.d027870]
  exact _root_.GD.N0106.N0428.N0770.N1720.d027908 (θ := θ) (w := w) hw




theorem d027910 :
    ∫ ω, _root_.GD.N0106.N0428.N0770.N1720.d027856 ω ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 = _root_.GD.N0106.N0428.N0770.N1725.d024119 ^ 2 *
      ∫ ω, _root_.GD.N0107.d009090 2 2 ω ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1724.d024300 ω) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  unfold _root_.GD.N0106.N0428.N0770.N1720.d027856
  ring



theorem d027911 (hw : ∀ i, 0 ≤ w i) :
    27 * _root_.GD.N0106.N0428.N0770.N1725.d024119 ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 131072 < _root_.GD.N0106.N0428.N0770.N1720.d027884 θ w ∧
      (1 : ℝ) / 10 ^ 36 < 27 * _root_.GD.N0106.N0428.N0770.N1725.d024119 ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 131072 := by
  have hB := _root_.GD.N0106.N0428.N0770.N1720.d027908 (θ := θ) (w := w) hw
  have hE : 27 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 32768 <
      ∫ ω, _root_.GD.N0107.d009090 2 2 ω ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1724.d024300 ω) ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1720.d027842 :=
    _root_.GD.N0106.N0428.N0770.N1729.d027425
  have hn := _root_.GD.N0106.N0428.N0770.N1720.d027910
  have ht : _root_.GD.N0106.N0428.N0770.N1725.d024119 ^ 2 = 1 / 100000000 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024119]
  rw [ht] at hn
  constructor
  · rw [ht]
    linarith [hB, hE, hn]
  · norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024119, _root_.GD.N0106.N0428.N0770.N1725.d024118]




theorem d027912 (hw : ∀ i, 0 ≤ w i) :
    27 * _root_.GD.N0106.N0428.N0770.N1725.d024119 ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 16384 < _root_.GD.N0106.N0428.N0770.N1720.d027884 θ w ∧
      (1 : ℝ) / 10 ^ 35 < 27 * _root_.GD.N0106.N0428.N0770.N1725.d024119 ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 16384 := by
  have hB := _root_.GD.N0106.N0428.N0770.N1720.d027908 (θ := θ) (w := w) hw
  have hE := _root_.GD.N0106.N0428.N0770.N1720.d027877
  have hn := _root_.GD.N0106.N0428.N0770.N1720.d027910
  have ht : _root_.GD.N0106.N0428.N0770.N1725.d024119 ^ 2 = 1 / 100000000 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024119]
  rw [ht] at hn
  constructor
  · rw [ht]
    linarith [hB, hE, hn]
  · norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024119, _root_.GD.N0106.N0428.N0770.N1725.d024118]

end Packet

end
end GD.N0106.N0428.N0770.N1720

#print axioms _root_.GD.N0106.N0428.N0770.N1720.d027874
#print axioms _root_.GD.N0106.N0428.N0770.N1720.d027902
#print axioms _root_.GD.N0106.N0428.N0770.N1720.d027904
#print axioms _root_.GD.N0106.N0428.N0770.N1720.d027906
#print axioms _root_.GD.N0106.N0428.N0770.N1720.d027908
#print axioms _root_.GD.N0106.N0428.N0770.N1720.d027909
#print axioms _root_.GD.N0106.N0428.N0770.N1720.d027911
#print axioms _root_.GD.N0106.N0428.N0770.N1720.d027877
#print axioms _root_.GD.N0106.N0428.N0770.N1720.d027912
