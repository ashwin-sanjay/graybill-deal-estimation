import GD.Module0014
import GD.Module0055
import GD.Module0621
import GD.Module0911
























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1080

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608


structure d014168 where
  location : ℝ
  scale₁ : ℝ
  scale₂ : ℝ
  scale₁_pos : 0 < scale₁
  scale₂_pos : 0 < scale₂


def d014169 : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := 1
  scale₂ := 1
  scale₁_pos := zero_lt_one
  scale₂_pos := zero_lt_one

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)


abbrev d014170 := _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n


noncomputable def d014171 (θ : _root_.GD.N0232.N0720.N1080.d014168) : Measure (_root_.GD.N0232.N0720.N1080.d014170 m n) :=
  _root_.GD.N0107.d009030 m n θ.location θ.scale₁ θ.scale₂


noncomputable def d014172 : Measure (_root_.GD.N0232.N0720.N1080.d014170 m n) :=
  _root_.GD.N0232.N0720.N1080.d014171 m n _root_.GD.N0232.N0720.N1080.d014169



theorem d014173 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014171 m n θ ≪ _root_.GD.N0232.N0720.N1080.d014172 m n := by
  simpa [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
    (_root_.GD.N0232.N0720.d009063
      m n θ.location θ.scale₁ θ.scale₂ θ.scale₁_pos θ.scale₂_pos).1


noncomputable def d014174 : _root_.GD.N0232.N0720.d014158 m n hm hn :=
  Classical.choose
    (_root_.GD.N0232.N0720.d014167 m n hm hn)


noncomputable def d014175 : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  _root_.GD.N0107.d012733 m n



noncomputable def d014176 : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  _root_.GD.N0107.d012734 m n
    ((_root_.GD.N0232.N0720.N1080.d014174 m n hm hn).step : ℝ)
    (_root_.GD.N0232.N0720.d014159 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn))

include hm hn in

theorem d014177 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp
      (fun ω => _root_.GD.N0232.N0720.N1080.d014175 m n ω - θ.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n θ) := by
  have hOracle :=
    _root_.GD.N0107.d012747
      m n hm hn θ.location θ.scale₁ θ.scale₂
      θ.scale₁_pos θ.scale₂_pos
  have hWeight :=
    (_root_.GD.N0107.d012749
      m n hm hn θ.location θ.scale₁ θ.scale₂
      θ.scale₁_pos θ.scale₂_pos
      (fun _ : ℝ × ℝ => (0 : ℝ)) measurable_const
      (show 0 ≤ (0 : ℝ) by rfl) (fun _ => by simp)).1
  apply (memLp_congr_ae ?_).2 (hOracle.add hWeight)
  filter_upwards [] with ω
  simp only [_root_.GD.N0232.N0720.N1080.d014175]
  rw [_root_.GD.N0107.d012735
    m n θ.location (_root_.GD.N0107.d009046 m n θ.scale₁ θ.scale₂) ω]
  rfl


theorem d014178 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp
      (fun ω =>
        _root_.GD.N0107.d009090 m n ω *
          _root_.GD.N0232.N0720.d014159 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn) ω)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n θ) := by
  let U := _root_.GD.N0232.N0720.N1080.d014174 m n hm hn
  let q := U.emitted.table.d008659
  have hq : Measurable q := U.emitted.table.d008664
  have hB :
      0 ≤ _root_.GD.N0108.d008888
        U.emitted.table := by
    unfold _root_.GD.N0108.d008888
    positivity
  have hqBound :
      ∀ p, |q p| ≤
        _root_.GD.N0108.d008888
          U.emitted.table :=
    _root_.GD.N0108.d008891 U.emitted.table
  have hCarrier :=
    (_root_.GD.N0107.d012749
      m n hm hn θ.location θ.scale₁ θ.scale₂
      θ.scale₁_pos θ.scale₂_pos q hq hB hqBound).2
  simpa [_root_.GD.N0232.N0720.d014159, _root_.GD.N0232.N0720.d014159,
    _root_.GD.N0117.d014139, _root_.GD.N0232.N0720.N1080.d014171, U, q] using hCarrier



theorem d014179 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp
      (fun ω => _root_.GD.N0232.N0720.N1080.d014176 m n hm hn ω - θ.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n θ) := by
  have hBase := _root_.GD.N0232.N0720.N1080.d014177 m n hm hn θ
  have hCorrection :=
    (_root_.GD.N0232.N0720.N1080.d014178 m n hm hn θ).const_mul
      ((_root_.GD.N0232.N0720.N1080.d014174 m n hm hn).step : ℝ)
  apply (memLp_congr_ae ?_).2 (hBase.add hCorrection)
  filter_upwards [] with ω
  simp only [_root_.GD.N0232.N0720.N1080.d014176, _root_.GD.N0232.N0720.N1080.d014175, _root_.GD.N0107.d012734, Pi.add_apply]
  ring

include hm hn in

noncomputable def d014180 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1080.d014175 m n)
    (by
      simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
        _root_.GD.N0232.N0720.N1080.d014177 m n hm hn _root_.GD.N0232.N0720.N1080.d014169)



noncomputable def d014181 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn)
    (by
      simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
        _root_.GD.N0232.N0720.N1080.d014179 m n hm hn _root_.GD.N0232.N0720.N1080.d014169)


noncomputable def d014182
    (θ : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ≥0∞ :=
  _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n)
    (_root_.GD.N0232.N0720.N1080.d014171 m n θ) θ.location d




theorem d014183
    {μ₀ μ : Measure (_root_.GD.N0232.N0720.N1080.d014170 m n)}
    (hμ : μ ≪ μ₀) (target : ℝ)
    (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hf₀ : MemLp f 2 μ₀)
    (hfμ : MemLp (fun ω => f ω - target) 2 μ) :
    _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target (MemLp.toLp f hf₀) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 μ (fun ω => f ω - target)) := by
  have hae₀ :
      (fun ω => (MemLp.toLp f hf₀ : _root_.GD.N0230.N0602.d000116 μ₀) ω) =ᵐ[μ₀] f :=
    hf₀.coeFn_toLp
  have hae :
      (fun ω => (MemLp.toLp f hf₀ : _root_.GD.N0230.N0602.d000116 μ₀) ω) =ᵐ[μ] f :=
    hμ.ae_le hae₀
  rw [_root_.GD.N0230.N0602.d000117]
  calc
    (∫⁻ ω,
        ENNReal.ofReal
          (((MemLp.toLp f hf₀ : _root_.GD.N0230.N0602.d000116 μ₀) ω - target) ^ 2) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal ((f ω - target) ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ω hω
      rw [hω]
    _ =
        ENNReal.ofReal
          (∫ ω, (f ω - target) ^ 2 ∂μ) := by
      exact
        (ofReal_integral_eq_lintegral_ofReal
          hfμ.integrable_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ = _ := rfl



theorem d014184 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n θ)
          (fun ω => _root_.GD.N0232.N0720.N1080.d014175 m n ω - θ.location)) := by
  apply _root_.GD.N0232.N0720.N1080.d014183
    m n (_root_.GD.N0232.N0720.N1080.d014173 m n θ)
  exact _root_.GD.N0232.N0720.N1080.d014177 m n hm hn θ



theorem d014185 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n θ)
          (fun ω => _root_.GD.N0232.N0720.N1080.d014176 m n hm hn ω - θ.location)) := by
  apply _root_.GD.N0232.N0720.N1080.d014183
    m n (_root_.GD.N0232.N0720.N1080.d014173 m n θ)
  exact _root_.GD.N0232.N0720.N1080.d014179 m n hm hn θ




theorem d014186 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  intro θ
  have hstrict :=
    (_root_.GD.N0232.N0720.d014166
      (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn)
      θ.location θ.scale₁ θ.scale₂ θ.scale₁_pos θ.scale₂_pos).2
  have hbasePos :
      0 <
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n θ)
          (fun ω => _root_.GD.N0232.N0720.N1080.d014175 m n ω - θ.location) := by
    exact lt_of_le_of_lt (integral_nonneg fun _ => sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn θ,
    _root_.GD.N0232.N0720.N1080.d014184 m n hm hn θ]
  exact (ENNReal.ofReal_lt_ofReal_iff hbasePos).2 hstrict


def d014187 : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {d | _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) d}


theorem d014188 :
    IsClosed (_root_.GD.N0232.N0720.N1080.d014187 m n hm hn) := by
  simpa [_root_.GD.N0232.N0720.N1080.d014187, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun θ => _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))


theorem d014189 :
    Convex ℝ (_root_.GD.N0232.N0720.N1080.d014187 m n hm hn) := by
  simpa [_root_.GD.N0232.N0720.N1080.d014187, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun θ => _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))



theorem d014190 (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 d =
      ENNReal.ofReal
        (‖(0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) - d‖ ^ 2) := by
  simpa [_root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
    _root_.GD.N0230.N0602.d000124 (_root_.GD.N0232.N0720.N1080.d014172 m n) d






noncomputable def d014191 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0230.N0608.d000681
    (_root_.GD.N0232.N0720.N1080.d014182 m n) _root_.GD.N0232.N0720.N1080.d014169
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
    (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014188 m n hm hn)
    (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014189 m n hm hn)
    (_root_.GD.N0232.N0720.N1080.d014190 m n)



theorem d014192 :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
        (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
      ∧ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
      ∧ (∀ d,
        _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) d →
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 d) := by
  exact _root_.GD.N0230.N0608.d000682
    (_root_.GD.N0232.N0720.N1080.d014182 m n) _root_.GD.N0232.N0720.N1080.d014169
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
    (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014188 m n hm hn)
    (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014189 m n hm hn)
    (_root_.GD.N0232.N0720.N1080.d014190 m n)



theorem d014193 :
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  exact _root_.GD.N0230.N0608.d000683
    (_root_.GD.N0232.N0720.N1080.d014182 m n) _root_.GD.N0232.N0720.N1080.d014169
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)
    (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
    (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014188 m n hm hn)
    (by simpa [_root_.GD.N0232.N0720.N1080.d014187] using _root_.GD.N0232.N0720.N1080.d014189 m n hm hn)
    (_root_.GD.N0232.N0720.N1080.d014190 m n)
    (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn)


noncomputable def d014194 :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  AEStronglyMeasurable.mk
    (fun ω => _root_.GD.N0232.N0720.N1080.d014191 m n hm hn ω)
    (Lp.aestronglyMeasurable (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn))

theorem d014195 :
    Measurable (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn) :=
  AEStronglyMeasurable.measurable_mk
    (Lp.aestronglyMeasurable (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn))



theorem d014196 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014194 m n hm hn =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
      (fun ω => _root_.GD.N0232.N0720.N1080.d014191 m n hm hn ω) := by
  have href :=
    (Lp.aestronglyMeasurable
      (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)).ae_eq_mk.symm
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_le href








noncomputable def d014197
    (θ : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((d ω - θ.location) ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014171 m n θ






theorem d014198
    (θ : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ d =
      _root_.GD.N0232.N0720.N1080.d014182 m n θ (MemLp.toLp d hd) := by
  have href :
      (fun ω =>
        (MemLp.toLp d hd : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) ω) =ᵐ[
          _root_.GD.N0232.N0720.N1080.d014172 m n] d :=
    hd.coeFn_toLp
  have hθ :
      (fun ω =>
        (MemLp.toLp d hd : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) ω) =ᵐ[
          _root_.GD.N0232.N0720.N1080.d014171 m n θ] d :=
    (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_le href
  unfold _root_.GD.N0232.N0720.N1080.d014197 _root_.GD.N0232.N0720.N1080.d014182 _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [hθ] with ω hω
  rw [hω]


theorem d014199
    (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) =
      _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  exact _root_.GD.N0232.N0720.N1080.d014198 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)
    (by
      simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
        _root_.GD.N0232.N0720.N1080.d014177 m n hm hn _root_.GD.N0232.N0720.N1080.d014169)





theorem d014200 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ
        (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn) =
      _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
  unfold _root_.GD.N0232.N0720.N1080.d014197 _root_.GD.N0232.N0720.N1080.d014182 _root_.GD.N0230.N0602.d000117
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1080.d014196 m n hm hn θ] with ω hω
  rw [hω]






theorem d014201 :
    ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n θ
          (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn) <
        _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  intro θ
  rw [_root_.GD.N0232.N0720.N1080.d014200 m n hm hn θ,
    _root_.GD.N0232.N0720.N1080.d014199 m n hm hn θ]
  exact _root_.GD.N0232.N0720.N1080.d014193 m n hm hn θ













theorem d014202
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : Measurable d)
    (hdom :
      ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
          _root_.GD.N0232.N0720.N1080.d014197 m n θ
            (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn)) :
    ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
      d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] _root_.GD.N0232.N0720.N1080.d014194 m n hm hn := by
  have hdRisk_ne_top :
      _root_.GD.N0232.N0720.N1080.d014197 m n _root_.GD.N0232.N0720.N1080.d014169 d ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (hdom _root_.GD.N0232.N0720.N1080.d014169)
    rw [_root_.GD.N0232.N0720.N1080.d014200,
      _root_.GD.N0232.N0720.N1080.d014190]
    exact ENNReal.ofReal_ne_top
  have hdMemLp : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    apply
      (memLp_two_iff_integrable_sq
        hd.aestronglyMeasurable).2
    have hlin :
        (∫⁻ ω, ENNReal.ofReal (d ω ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≠ ⊤ := by
      simpa [_root_.GD.N0232.N0720.N1080.d014197, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
        hdRisk_ne_top
    have hint :=
      integrable_toReal_of_lintegral_ne_top
        ((hd.pow_const 2).ennreal_ofReal.aemeasurable) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  let dL2 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    MemLp.toLp d hdMemLp
  have hdomL2 :
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) dL2
        (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
    intro θ
    have hdRisk :
        _root_.GD.N0232.N0720.N1080.d014182 m n θ dL2 = _root_.GD.N0232.N0720.N1080.d014197 m n θ d := by
      simpa only [dL2] using
        (_root_.GD.N0232.N0720.N1080.d014198 m n θ d hdMemLp).symm
    have hcanonicalRisk :
        _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) =
          _root_.GD.N0232.N0720.N1080.d014197 m n θ
            (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn) :=
      (_root_.GD.N0232.N0720.N1080.d014200
        m n hm hn θ).symm
    rw [hdRisk, hcanonicalRisk]
    exact hdom θ
  have hdL2eq :
      dL2 = _root_.GD.N0232.N0720.N1080.d014191 m n hm hn :=
    (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).2.1 dL2 hdomL2
  have hraw_ref :
      d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1080.d014194 m n hm hn := by
    have hcoe :
        (fun ω => dL2 ω) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] d := by
      simpa [dL2] using hdMemLp.coeFn_toLp
    have hcanon :
        _root_.GD.N0232.N0720.N1080.d014194 m n hm hn =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          (fun ω => _root_.GD.N0232.N0720.N1080.d014191 m n hm hn ω) :=
      _root_.GD.N0232.N0720.N1080.d014196
        m n hm hn _root_.GD.N0232.N0720.N1080.d014169
    have hcoe' :
        (fun ω => dL2 ω) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          (fun ω => _root_.GD.N0232.N0720.N1080.d014191 m n hm hn ω) := by
      rw [hdL2eq]
    exact hcoe.symm.trans (hcoe'.trans hcanon.symm)
  intro θ
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_le hraw_ref

end

end N1080
end N0720
end N0232
end GD
