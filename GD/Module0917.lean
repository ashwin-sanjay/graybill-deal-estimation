import GD.Module0916




















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1215

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)




def d014272 (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := g.shift + g.d009239 * theta.location
  scale₁ := g.d009239 * theta.scale₁
  scale₂ := g.d009239 * theta.scale₂
  scale₁_pos := mul_pos g.d009240 theta.scale₁_pos
  scale₂_pos := mul_pos g.d009240 theta.scale₂_pos

@[simp] theorem d014273
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1215.d014272 g theta).location =
      g.shift + g.d009239 * theta.location := rfl

@[simp] theorem d014274
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1215.d014272 g theta).scale₁ =
      g.d009239 * theta.scale₁ := rfl

@[simp] theorem d014275
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1215.d014272 g theta).scale₂ =
      g.d009239 * theta.scale₂ := rfl

@[simp] theorem d014276 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1215.d014272 1 theta = theta := by
  cases theta
  simp [_root_.GD.N0232.N0720.N1215.d014272]



theorem d014277
    {theta eta : _root_.GD.N0232.N0720.N1080.d014168}
    (hlocation : theta.location = eta.location)
    (hscale₁ : theta.scale₁ = eta.scale₁)
    (hscale₂ : theta.scale₂ = eta.scale₂) : theta = eta := by
  cases theta
  cases eta
  cases hlocation
  cases hscale₁
  cases hscale₂
  rfl

theorem d014278
    (g h : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1215.d014272 h theta) =
      _root_.GD.N0232.N0720.N1215.d014272 (g * h) theta := by
  apply _root_.GD.N0232.N0720.N1215.d014277
  · simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0719.N0946.d009229.d009239]
    rw [Real.exp_add]
    ring
  · simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0719.N0946.d009229.d009243]
    ring
  · simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0719.N0946.d009229.d009243]
    ring

@[simp] theorem d014279
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta) = theta := by
  rw [_root_.GD.N0232.N0720.N1215.d014278]
  simp

@[simp] theorem d014280
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ (_root_.GD.N0232.N0720.N1215.d014272 g theta) = theta := by
  rw [_root_.GD.N0232.N0720.N1215.d014278]
  simp



theorem d014281
    (shift dilation location scale₁ scale₂ : ℝ) :
    _root_.GD.N0107.d009024 m n shift dilation dilation ∘
        _root_.GD.N0107.d009024
          m n location scale₁ scale₂ =
      _root_.GD.N0107.d009024 m n
        (shift + dilation * location)
        (dilation * scale₁) (dilation * scale₂) := by
  funext omega
  ext i <;>
    simp [Function.comp_apply, _root_.GD.N0107.d009024,
      _root_.GD.N0107.d009018] <;>
    ring



theorem d014282
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014171 m n theta).map
        (_root_.GD.N0107.d009024
          m n g.shift g.d009239 g.d009239) =
      _root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171 _root_.GD.N0107.d009030
  rw [Measure.map_map
    (_root_.GD.N0107.d009026
      m n g.shift g.d009239 g.d009239)
    (_root_.GD.N0107.d009026
      m n theta.location theta.scale₁ theta.scale₂)]
  rw [_root_.GD.N0232.N0720.N1215.d014281]
  rfl




theorem d014283
    (g : _root_.GD.N0232.N0719.N0946.d009229) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g d
        (_root_.GD.N0107.d009024
          m n g.shift g.d009239 g.d009239 omega) =
      g • d omega := by
  rw [← _root_.GD.N0232.N0720.N1214.d014259 m n g omega]
  change g • d (g⁻¹ • (g • omega)) = g • d omega
  rw [inv_smul_smul]



theorem d014284
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0720.N1080.d014197 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
        (_root_.GD.N0232.N0720.N1214.d014261 m n g d) =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
  have hmap := _root_.GD.N0232.N0720.N1215.d014282 m n g theta
  unfold _root_.GD.N0232.N0720.N1080.d014197
  rw [← hmap]
  rw [lintegral_map]
  · calc
      (∫⁻ omega,
          ENNReal.ofReal
            ((_root_.GD.N0232.N0720.N1214.d014261 m n g d
                (_root_.GD.N0107.d009024
                  m n g.shift g.d009239 g.d009239 omega) -
              (_root_.GD.N0232.N0720.N1215.d014272 g theta).location) ^ 2)
          ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
        ∫⁻ omega,
          ENNReal.ofReal (g.d009239 ^ 2) *
            ENNReal.ofReal ((d omega - theta.location) ^ 2)
          ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
            apply lintegral_congr
            intro omega
            rw [_root_.GD.N0232.N0720.N1215.d014283 m n g d omega]
            simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244, _root_.GD.N0232.N0720.N1215.d014273]
            have hreal :
                ((g.shift + g.d009239 * d omega) -
                    (g.shift + g.d009239 * theta.location)) ^ 2 =
                  g.d009239 ^ 2 * (d omega - theta.location) ^ 2 := by
              ring
            rw [hreal, ENNReal.ofReal_mul (sq_nonneg g.d009239)]
      _ = ENNReal.ofReal (g.d009239 ^ 2) *
          ∫⁻ omega, ENNReal.ofReal ((d omega - theta.location) ^ 2)
            ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
        rw [lintegral_const_mul]
        fun_prop
  · exact ENNReal.measurable_ofReal.comp
      (((_root_.GD.N0232.N0720.N1214.d014262 m n g d hd).sub measurable_const).pow_const 2)
  · exact _root_.GD.N0107.d009026
      m n g.shift g.d009239 g.d009239





theorem d014285
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n _root_.GD.N0232.N0720.N1080.d014169 d ≠ ⊤) :
    MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).2
  have hlin :
      (∫⁻ omega, ENNReal.ofReal (d omega ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≠ ⊤ := by
    simpa [_root_.GD.N0232.N0720.N1080.d014197, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using hfinite
  have hint :=
    integrable_toReal_of_lintegral_ne_top
      ((hd.pow_const 2).ennreal_ofReal.aemeasurable) hlin
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint



theorem d014286
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) =
      _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
  rw [_root_.GD.N0232.N0720.N1080.d014198 m n theta
    (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014268 m n p)]
  rw [_root_.GD.N0232.N0720.N1214.d014269]


theorem d014287
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) ≠ ⊤ := by
  rw [_root_.GD.N0232.N0720.N1215.d014286]
  apply ne_top_of_le_ne_top _ (hp theta)
  rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
  exact ENNReal.ofReal_ne_top




theorem d014288
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    MemLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  apply _root_.GD.N0232.N0720.N1215.d014285 m n
    (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
    (_root_.GD.N0232.N0720.N1214.d014262 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)
      (_root_.GD.N0232.N0720.N1214.d014266 m n p))
  let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = _root_.GD.N0232.N0720.N1080.d014169 := by
    simp [theta]
  have hrisk := _root_.GD.N0232.N0720.N1215.d014284
    m n g theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014266 m n p)
  rw [heta] at hrisk
  rw [hrisk]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (_root_.GD.N0232.N0720.N1215.d014287 m n hm hn p hp theta)


noncomputable def d014289
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
    (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p hp)



theorem d014290
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
        (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp) =
      ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
  unfold _root_.GD.N0232.N0720.N1215.d014289
  rw [← _root_.GD.N0232.N0720.N1080.d014198 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
    (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
    (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p hp)]
  rw [_root_.GD.N0232.N0720.N1215.d014284
    m n g theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014266 m n p)]
  rw [_root_.GD.N0232.N0720.N1215.d014286]



include hm hn in


theorem d014291
    (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1080.d014175 m n
        (_root_.GD.N0107.d009024
          m n g.shift g.d009239 g.d009239 omega) =
      g • _root_.GD.N0232.N0720.N1080.d014175 m n omega := by
  have hmy :=
    _root_.GD.N0107.d009086
      (by omega : 0 < n) g.shift g.d009239 omega.2
  have hx := _root_.GD.N0117.d014148
    hm g.shift g.d009239 omega.1
  have hy := _root_.GD.N0117.d014148
    hn g.shift g.d009239 omega.2
  have hD := _root_.GD.N0117.d014149
    hm hn g.shift g.d009239 omega
  have hD' :
      _root_.GD.N0107.d009090 m n
          (_root_.GD.N0107.d009018
            m g.shift g.d009239 omega.1,
           _root_.GD.N0107.d009018
            n g.shift g.d009239 omega.2) =
        g.d009239 * _root_.GD.N0107.d009090 m n omega := by
    simpa [_root_.GD.N0107.d009024] using hD
  unfold _root_.GD.N0232.N0720.N1080.d014175 _root_.GD.N0107.d012733
    _root_.GD.N0107.d009084
    _root_.GD.N0107.d009024
  simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244]
  rw [hmy, hx, hy,
    _root_.GD.N0117.d014150
      hm hn g.d009241, hD']
  ring

include hm hn in

theorem d014292
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1080.d014175 m n) = _root_.GD.N0232.N0720.N1080.d014175 m n := by
  funext omega
  calc
    _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1080.d014175 m n) omega =
        g • _root_.GD.N0232.N0720.N1080.d014175 m n (g⁻¹ • omega) := rfl
    _ = _root_.GD.N0232.N0720.N1080.d014175 m n (g • (g⁻¹ • omega)) := by
      symm
      simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
        (_root_.GD.N0232.N0720.N1215.d014291 m n hm hn g (g⁻¹ • omega))
    _ = _root_.GD.N0232.N0720.N1080.d014175 m n omega := by rw [smul_inv_smul]



theorem d014293
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  rw [← _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
  rw [← _root_.GD.N0232.N0720.N1215.d014292 m n hm hn g]
  rw [_root_.GD.N0232.N0720.N1215.d014284
    m n g theta (_root_.GD.N0232.N0720.N1080.d014175 m n)]
  · rw [_root_.GD.N0232.N0720.N1080.d014199]
  · simpa [_root_.GD.N0232.N0720.N1080.d014175] using
      (_root_.GD.N0117.d014146 m n)



theorem d014294
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) =
      _root_.GD.N0232.N0720.N1080.d014176 m n hm hn := by
  funext omega
  calc
    _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) omega =
        g • _root_.GD.N0232.N0720.N1080.d014176 m n hm hn (g⁻¹ • omega) := rfl
    _ = _root_.GD.N0232.N0720.N1080.d014176 m n hm hn (g • (g⁻¹ • omega)) := by
      symm
      simpa only [_root_.GD.N0232.N0720.N1080.d014176,
        _root_.GD.N0232.N0720.N1214.d014259, _root_.GD.N0232.N0719.N0946.d009229.d009244] using
        (_root_.GD.N0232.N0720.d014164
          (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn) g.shift g.d009241 (g⁻¹ • omega))
    _ = _root_.GD.N0232.N0720.N1080.d014176 m n hm hn omega := by rw [smul_inv_smul]



theorem d014295 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) =
      _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) := by
  simpa [_root_.GD.N0232.N0720.N1080.d014181] using
    (_root_.GD.N0232.N0720.N1080.d014198 m n theta (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn)
      (by
        simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
          _root_.GD.N0232.N0720.N1080.d014179 m n hm hn _root_.GD.N0232.N0720.N1080.d014169))



theorem d014296
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) := by
  rw [← _root_.GD.N0232.N0720.N1215.d014295 m n hm hn]
  rw [← _root_.GD.N0232.N0720.N1215.d014294 m n hm hn g]
  rw [_root_.GD.N0232.N0720.N1215.d014284
    m n g theta (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn)]
  · rw [_root_.GD.N0232.N0720.N1215.d014295]
  · simpa [_root_.GD.N0232.N0720.N1080.d014176] using
      (_root_.GD.N0232.N0720.d014162 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn))



theorem d014297
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn := by
  intro eta
  let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by
    simp [theta]
  rw [← heta]
  rw [_root_.GD.N0232.N0720.N1215.d014290, _root_.GD.N0232.N0720.N1215.d014296]
  exact mul_le_mul_left' (hp theta) _


noncomputable def d014298
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1080.d014187 m n hm hn → _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
  fun p ↦
    ⟨_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p.1 p.2,
      _root_.GD.N0232.N0720.N1215.d014297 m n hm hn g p.1 p.2⟩







theorem d014299
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g p = p) :
    ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        repaired =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1214.d014265 m n p.1) ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired := by
  apply
    _root_.GD.N0232.N0720.N1214.d014271
      m n hm hn p.1
      (fun g ↦ _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p.1 p.2)
  intro g
  have hvalue := congrArg Subtype.val (hfixed g)
  simpa [_root_.GD.N0232.N0720.N1215.d014298, _root_.GD.N0232.N0720.N1215.d014289] using hvalue






theorem
    d014300
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p.1)
    (hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g p = p) :
    ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable repaired ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired <
          _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      (∀ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
        Measurable d →
        (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
            _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired) →
        ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] repaired) := by
  obtain ⟨repaired, hrepairedMeasurable, hrepairedClass,
      hrepairedEquivariant⟩ :=
    _root_.GD.N0232.N0720.N1215.d014299
      m n hm hn p hfixed
  have hrepairedRisk : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired = _root_.GD.N0232.N0720.N1080.d014182 m n theta p.1 := by
    intro theta
    calc
      _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired =
          _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p.1) := by
        unfold _root_.GD.N0232.N0720.N1080.d014197
        apply lintegral_congr_ae
        filter_upwards [hrepairedClass theta] with omega homega
        rw [homega]
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta p.1 :=
        _root_.GD.N0232.N0720.N1215.d014286 m n theta p.1
  refine ⟨repaired, hrepairedMeasurable, hrepairedEquivariant, ?_, ?_⟩
  · intro theta
    rw [hrepairedRisk theta,
      _root_.GD.N0232.N0720.N1080.d014199 m n hm hn theta]
    exact lt_of_le_of_lt (p.2 theta)
      (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn theta)
  · intro d hd hdom
    have hdRisk_ne_top :
        _root_.GD.N0232.N0720.N1080.d014197 m n _root_.GD.N0232.N0720.N1080.d014169 d ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ (hdom _root_.GD.N0232.N0720.N1080.d014169)
      rw [hrepairedRisk, _root_.GD.N0232.N0720.N1080.d014190]
      exact ENNReal.ofReal_ne_top
    have hdMemLp : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
      _root_.GD.N0232.N0720.N1215.d014285 m n d hd hdRisk_ne_top
    let dL2 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := MemLp.toLp d hdMemLp
    have hdomL2 : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) dL2 p.1 := by
      intro theta
      rw [← _root_.GD.N0232.N0720.N1080.d014198 m n theta d hdMemLp]
      rw [← hrepairedRisk theta]
      exact hdom theta
    have hdL2eq : dL2 = p.1 := hterminal dL2 hdomL2
    have hrawReference :
        d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n p.1 := by
      have hcoe :
          (fun omega ↦ dL2 omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] d := by
        simpa [dL2] using hdMemLp.coeFn_toLp
      have hpBorel :
          _root_.GD.N0232.N0720.N1214.d014265 m n p.1 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
            (fun omega ↦ p.1 omega) :=
        _root_.GD.N0232.N0720.N1214.d014267 m n p.1
      have hcoe' :
          (fun omega ↦ dL2 omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
            (fun omega ↦ p.1 omega) := by
        rw [hdL2eq]
      exact hcoe.symm.trans (hcoe'.trans hpBorel.symm)
    intro theta
    filter_upwards [
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le hrawReference,
      hrepairedClass theta] with omega hdPoint hrepairedPoint
    calc
      d omega = _root_.GD.N0232.N0720.N1214.d014265 m n p.1 omega := hdPoint
      _ = repaired omega := hrepairedPoint.symm

end

end N1215
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1215.d014284
#print axioms _root_.GD.N0232.N0720.N1215.d014290
#print axioms _root_.GD.N0232.N0720.N1215.d014293
#print axioms _root_.GD.N0232.N0720.N1215.d014297
#print axioms _root_.GD.N0232.N0720.N1215.d014299
#print axioms _root_.GD.N0232.N0720.N1215.d014300
