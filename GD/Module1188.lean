import GD.Module1185



















open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1101

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1043
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0137
open _root_.GD.N0107

variable (m n : ℕ)




def d019094 : _root_.GD.N0232.N0720.N1080.d014170 m n → _root_.GD.N0232.N0720.N1080.d014170 n m := Prod.swap

theorem d019095 (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1101.d019094 n m (_root_.GD.N0232.N0720.N1101.d019094 m n ω) = ω := rfl

theorem d019096 : Measurable (_root_.GD.N0232.N0720.N1101.d019094 m n) := measurable_swap

theorem d019097 :
    MeasurePreserving (_root_.GD.N0232.N0720.N1101.d019094 m n) (_root_.GD.N0137.d008914 m n) (_root_.GD.N0137.d008914 n m) := by
  unfold _root_.GD.N0137.d008914
  exact Measure.measurePreserving_swap

theorem d019098 (μ σ τ : ℝ) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0107.d009024 n m μ τ σ (_root_.GD.N0232.N0720.N1101.d019094 m n ω) =
      _root_.GD.N0232.N0720.N1101.d019094 m n (_root_.GD.N0107.d009024 m n μ σ τ ω) := rfl



theorem d019099 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014171 m n θ).map (_root_.GD.N0232.N0720.N1101.d019094 m n) = _root_.GD.N0232.N0720.N1080.d014171 n m (_root_.GD.N0232.N0720.N1043.d019058 θ) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171 _root_.GD.N0107.d009030
  rw [Measure.map_map (_root_.GD.N0232.N0720.N1101.d019096 m n)
    (_root_.GD.N0107.d009026 m n _ _ _)]
  have hcomm :
      _root_.GD.N0232.N0720.N1101.d019094 m n ∘ _root_.GD.N0107.d009024 m n θ.location θ.scale₁ θ.scale₂ =
        _root_.GD.N0107.d009024 n m θ.location θ.scale₂ θ.scale₁ ∘ _root_.GD.N0232.N0720.N1101.d019094 m n := by
    funext ω
    exact (_root_.GD.N0232.N0720.N1101.d019098 m n θ.location θ.scale₁ θ.scale₂ ω).symm
  rw [hcomm, ← Measure.map_map (_root_.GD.N0107.d009026 n m _ _ _)
    (_root_.GD.N0232.N0720.N1101.d019096 m n),
    (_root_.GD.N0232.N0720.N1101.d019097 m n).map_eq]
  rfl

theorem d019100 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    MeasurePreserving (_root_.GD.N0232.N0720.N1101.d019094 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n θ) (_root_.GD.N0232.N0720.N1080.d014171 n m (_root_.GD.N0232.N0720.N1043.d019058 θ)) :=
  ⟨_root_.GD.N0232.N0720.N1101.d019096 m n, _root_.GD.N0232.N0720.N1101.d019099 m n θ⟩


theorem d019101 (θ : _root_.GD.N0232.N0720.N1080.d014168)
    (d : _root_.GD.N0232.N0720.N1080.d014170 n m → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (d ∘ _root_.GD.N0232.N0720.N1101.d019094 m n) =
      _root_.GD.N0232.N0720.N1080.d014197 n m (_root_.GD.N0232.N0720.N1043.d019058 θ) d := by
  unfold _root_.GD.N0232.N0720.N1080.d014197
  have hmeas : Measurable (fun ω =>
      ENNReal.ofReal ((d ω - (_root_.GD.N0232.N0720.N1043.d019058 θ).location) ^ 2)) :=
    ((hd.sub measurable_const).pow_const 2).ennreal_ofReal
  rw [← _root_.GD.N0232.N0720.N1101.d019099 m n θ, lintegral_map hmeas (_root_.GD.N0232.N0720.N1101.d019096 m n)]
  rfl



theorem d019102 (x y A B : ℝ) (hS : A + B ≠ 0) :
    x + A / (B + A) * (y - x) = y + B / (A + B) * (x - y) := by
  rw [add_comm B A]
  field_simp
  ring




theorem d019103 (ω : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hpos : 0 < _root_.GD.N0107.d009085 ω.1 / m + _root_.GD.N0107.d009085 ω.2 / n) :
    _root_.GD.N0232.N0720.N1080.d014175 n m (_root_.GD.N0232.N0720.N1101.d019094 m n ω) = _root_.GD.N0232.N0720.N1080.d014175 m n ω := by
  have hS : _root_.GD.N0107.d009085 ω.1 / m + _root_.GD.N0107.d009085 ω.2 / n ≠ 0 :=
    hpos.ne'
  simpa only [_root_.GD.N0232.N0720.N1080.d014175, _root_.GD.N0107.d012733, _root_.GD.N0107.d009091, _root_.GD.N0107.d009090,
    _root_.GD.N0232.N0720.N1101.d019094, Prod.swap] using
    _root_.GD.N0232.N0720.N1101.d019102 (_root_.GD.N0107.d009084 ω.1) (_root_.GD.N0107.d009084 ω.2)
      (_root_.GD.N0107.d009085 ω.1 / m) (_root_.GD.N0107.d009085 ω.2 / n) hS



theorem d019104 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (fun ω => _root_.GD.N0232.N0720.N1080.d014175 n m (_root_.GD.N0232.N0720.N1101.d019094 m n ω)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1080.d014175 m n := by
  have hpos := _root_.GD.N0119.d009075 m n hm hn
    (e := 1 / 2) (by norm_num) (by norm_num)
  have href : _root_.GD.N0232.N0720.N1080.d014172 m n = _root_.GD.N0137.d008914 m n := by
    rw [_root_.GD.N0232.N0720.N1449.d018839]
    rfl
  rw [href]
  filter_upwards [hpos] with ω hω
  apply _root_.GD.N0232.N0720.N1101.d019103 m n ω
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : 0 < _root_.GD.N0107.d009085 ω.1 / m := div_pos hω.1 hm0
  have h2 : 0 < _root_.GD.N0107.d009085 ω.2 / n := div_pos hω.2 hn0
  linarith


theorem d019105 (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (fun ω => _root_.GD.N0232.N0720.N1080.d014175 n m (_root_.GD.N0232.N0720.N1101.d019094 m n ω)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] _root_.GD.N0232.N0720.N1080.d014175 m n :=
  (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_le
    (_root_.GD.N0232.N0720.N1101.d019104 m n hm hn)

theorem d019106 (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) =
      _root_.GD.N0232.N0720.N1080.d014197 n m (_root_.GD.N0232.N0720.N1043.d019058 θ) (_root_.GD.N0232.N0720.N1080.d014175 n m) := by
  rw [← _root_.GD.N0232.N0720.N1101.d019101 m n θ (_root_.GD.N0232.N0720.N1080.d014175 n m)
    (_root_.GD.N0117.d014146 n m)]
  exact _root_.GD.N0232.N0720.N1159.d014662 m n θ (_root_.GD.N0232.N0720.N1101.d019105 m n hm hn θ).symm




theorem d019107 (g : _root_.GD.N0232.N0719.N0946.d009229) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1101.d019094 m n (g • ω) = g • _root_.GD.N0232.N0720.N1101.d019094 m n ω := rfl




theorem d019108 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    _root_.GD.N0232.N0720.N1159.d014660 n m (d ∘ _root_.GD.N0232.N0720.N1101.d019094 n m) := by
  obtain ⟨hmeas, hequiv, hstrict, hterm⟩ := hd
  refine ⟨hmeas.comp (_root_.GD.N0232.N0720.N1101.d019096 n m), ?_, ?_, ?_⟩
  · intro g ω
    show d (_root_.GD.N0232.N0720.N1101.d019094 n m (g • ω)) = g • d (_root_.GD.N0232.N0720.N1101.d019094 n m ω)
    rw [_root_.GD.N0232.N0720.N1101.d019107]
    exact hequiv g _
  · intro θ
    rw [_root_.GD.N0232.N0720.N1101.d019101 n m θ d hmeas,
      _root_.GD.N0232.N0720.N1101.d019106 n m hn hm θ]
    exact hstrict (_root_.GD.N0232.N0720.N1043.d019058 θ)
  · intro e he hdom θ
    have he' : Measurable (e ∘ _root_.GD.N0232.N0720.N1101.d019094 m n) := he.comp (_root_.GD.N0232.N0720.N1101.d019096 m n)
    have hdom' : ∀ θ', _root_.GD.N0232.N0720.N1080.d014197 m n θ' (e ∘ _root_.GD.N0232.N0720.N1101.d019094 m n) ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n θ' d := by
      intro θ'
      rw [_root_.GD.N0232.N0720.N1101.d019101 m n θ' e he]
      have h := hdom (_root_.GD.N0232.N0720.N1043.d019058 θ')
      rw [_root_.GD.N0232.N0720.N1101.d019101 n m (_root_.GD.N0232.N0720.N1043.d019058 θ') d hmeas,
        _root_.GD.N0232.N0720.N1043.d019062] at h
      exact h
    have hae := hterm (e ∘ _root_.GD.N0232.N0720.N1101.d019094 m n) he' hdom' (_root_.GD.N0232.N0720.N1043.d019058 θ)
    have hae' : e ∘ _root_.GD.N0232.N0720.N1101.d019094 m n =ᵐ[(_root_.GD.N0232.N0720.N1080.d014171 n m θ).map (_root_.GD.N0232.N0720.N1101.d019094 n m)] d := by
      rw [_root_.GD.N0232.N0720.N1101.d019099 n m θ]
      exact hae
    have h2 : (e ∘ _root_.GD.N0232.N0720.N1101.d019094 m n) ∘ _root_.GD.N0232.N0720.N1101.d019094 n m =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 n m θ] d ∘ _root_.GD.N0232.N0720.N1101.d019094 n m :=
      MeasureTheory.ae_eq_comp (_root_.GD.N0232.N0720.N1101.d019096 n m).aemeasurable hae'
    exact h2


theorem d019109 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔ _root_.GD.N0232.N0720.N1159.d014661 n m := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d ∘ _root_.GD.N0232.N0720.N1101.d019094 n m, _root_.GD.N0232.N0720.N1101.d019108 m n hm hn d hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d ∘ _root_.GD.N0232.N0720.N1101.d019094 m n, _root_.GD.N0232.N0720.N1101.d019108 n m hn hm d hd⟩


theorem d019110 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔ ¬ _root_.GD.N0232.N0720.N1159.d014661 n m :=
  not_congr (_root_.GD.N0232.N0720.N1101.d019109 m n hm hn)

end

end N1101
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1101.d019099
#print axioms _root_.GD.N0232.N0720.N1101.d019101
#print axioms _root_.GD.N0232.N0720.N1101.d019104
#print axioms _root_.GD.N0232.N0720.N1101.d019108
#print axioms _root_.GD.N0232.N0720.N1101.d019109
