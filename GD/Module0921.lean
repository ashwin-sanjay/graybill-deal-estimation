import GD.Module0920














namespace GD
namespace N0232
namespace N0720
namespace N1035

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1069
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



def d014376 (theta eta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1025.d014301 where
  shift := eta.location - (eta.scale₁ / theta.scale₁) * theta.location
  logScale := Real.log (eta.scale₁ / theta.scale₁)

@[simp] theorem d014377
    (theta eta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1035.d014376 theta eta).d009239 =
      eta.scale₁ / theta.scale₁ := by
  unfold _root_.GD.N0232.N0720.N1035.d014376 _root_.GD.N0232.N0719.N0946.d009229.d009239
  rw [Real.exp_log]
  exact div_pos eta.scale₁_pos theta.scale₁_pos

include hm hn



theorem d014378
    {theta eta : _root_.GD.N0232.N0720.N1080.d014168}
    (hfrac : _root_.GD.N0232.N0720.N1069.d014352 m n theta = _root_.GD.N0232.N0720.N1069.d014352 m n eta) :
    eta.scale₂ = (eta.scale₁ / theta.scale₁) * theta.scale₂ := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hthetaTotal :
      _root_.GD.N0107.d009045
          m n theta.scale₁ theta.scale₂ ≠ 0 :=
    (_root_.GD.N0107.d009049
      (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos).ne'
  have hetaTotal :
      _root_.GD.N0107.d009045
          m n eta.scale₁ eta.scale₂ ≠ 0 :=
    (_root_.GD.N0107.d009049
      (by omega) (by omega) eta.scale₁_pos eta.scale₂_pos).ne'
  unfold _root_.GD.N0232.N0720.N1069.d014352 _root_.GD.N0107.d009046 at hfrac
  have hcross := (div_eq_div_iff hthetaTotal hetaTotal).mp hfrac
  unfold _root_.GD.N0107.d009045
    _root_.GD.N0107.d009043
    _root_.GD.N0107.d009044 at hcross
  field_simp [hm0, hn0] at hcross
  ring_nf at hcross
  have hsquare :
      (theta.scale₂ * eta.scale₁) ^ 2 =
        (eta.scale₂ * theta.scale₁) ^ 2 := by
    apply mul_left_cancel₀ hn0
    nlinarith [hcross]
  have hproduct :
      theta.scale₂ * eta.scale₁ = eta.scale₂ * theta.scale₁ := by
    have hleft : 0 < theta.scale₂ * eta.scale₁ :=
      mul_pos theta.scale₂_pos eta.scale₁_pos
    have hright : 0 < eta.scale₂ * theta.scale₁ :=
      mul_pos eta.scale₂_pos theta.scale₁_pos
    nlinarith [hsquare]
  field_simp [theta.scale₁_pos.ne']
  nlinarith [hproduct]

omit hm hn

include hm hn



theorem d014379
    {theta eta : _root_.GD.N0232.N0720.N1080.d014168}
    (hfrac : _root_.GD.N0232.N0720.N1069.d014352 m n theta = _root_.GD.N0232.N0720.N1069.d014352 m n eta) :
    _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1035.d014376 theta eta) theta = eta := by
  apply _root_.GD.N0232.N0720.N1215.d014277
  · simp only [_root_.GD.N0232.N0720.N1215.d014273]
    rw [_root_.GD.N0232.N0720.N1035.d014377]
    simp [_root_.GD.N0232.N0720.N1035.d014376]
  · simp only [_root_.GD.N0232.N0720.N1215.d014274]
    rw [_root_.GD.N0232.N0720.N1035.d014377]
    field_simp [theta.scale₁_pos.ne']
  · simp only [_root_.GD.N0232.N0720.N1215.d014275]
    rw [_root_.GD.N0232.N0720.N1035.d014377]
    exact (_root_.GD.N0232.N0720.N1035.d014378
      m n hm hn hfrac).symm

omit hm hn



theorem d014380
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {g h : _root_.GD.N0232.N0720.N1025.d014301}
    (heq : _root_.GD.N0232.N0720.N1215.d014272 g theta = _root_.GD.N0232.N0720.N1215.d014272 h theta) :
    g = h := by
  have hscale : g.d009239 = h.d009239 := by
    have h := congrArg _root_.GD.N0232.N0720.N1080.d014168.scale₁ heq
    simp only [_root_.GD.N0232.N0720.N1215.d014274] at h
    nlinarith [theta.scale₁_pos]
  have hlog : g.logScale = h.logScale := by
    exact Real.exp_injective hscale
  have hshift : g.shift = h.shift := by
    have h := congrArg _root_.GD.N0232.N0720.N1080.d014168.location heq
    simp only [_root_.GD.N0232.N0720.N1215.d014273] at h
    rw [hscale] at h
    linarith
  exact
    _root_.GD.N0232.N0719.N0946.d009229.ext
      hshift hlog

include hm hn



theorem d014381
    {theta eta : _root_.GD.N0232.N0720.N1080.d014168} :
    _root_.GD.N0232.N0720.N1069.d014352 m n theta = _root_.GD.N0232.N0720.N1069.d014352 m n eta ↔
      ∃! g : _root_.GD.N0232.N0720.N1025.d014301, _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by
  constructor
  · intro hfrac
    refine ⟨_root_.GD.N0232.N0720.N1035.d014376 theta eta,
      _root_.GD.N0232.N0720.N1035.d014379 m n hm hn hfrac, ?_⟩
    intro g hg
    apply _root_.GD.N0232.N0720.N1035.d014380 theta
    rw [hg, _root_.GD.N0232.N0720.N1035.d014379 m n hm hn hfrac]
  · rintro ⟨g, hg, _⟩
    calc
      _root_.GD.N0232.N0720.N1069.d014352 m n theta =
          _root_.GD.N0232.N0720.N1069.d014352 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) :=
        (_root_.GD.N0232.N0720.N1069.d014355 m n hm hn g theta).symm
      _ = _root_.GD.N0232.N0720.N1069.d014352 m n eta := congrArg _ hg

omit hm hn

include hm hn



theorem d014382
    {theta eta : _root_.GD.N0232.N0720.N1080.d014168} :
    _root_.GD.N0232.N0720.N1069.d014352 m n theta = _root_.GD.N0232.N0720.N1069.d014352 m n eta ↔
      ∃ g : _root_.GD.N0232.N0720.N1025.d014301, _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by
  constructor
  · intro hfrac
    exact (_root_.GD.N0232.N0720.N1035.d014381
      m n hm hn).1 hfrac |>.exists
  · rintro ⟨g, hg⟩
    calc
      _root_.GD.N0232.N0720.N1069.d014352 m n theta =
          _root_.GD.N0232.N0720.N1069.d014352 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) :=
        (_root_.GD.N0232.N0720.N1069.d014355 m n hm hn g theta).symm
      _ = _root_.GD.N0232.N0720.N1069.d014352 m n eta := congrArg _ hg

omit hm hn

include hm hn



theorem d014383
    (theta eta : _root_.GD.N0232.N0720.N1080.d014168) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hg : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta) :
    g = _root_.GD.N0232.N0720.N1035.d014376 theta eta := by
  apply _root_.GD.N0232.N0720.N1035.d014380 theta
  rw [hg]
  symm
  apply _root_.GD.N0232.N0720.N1035.d014379 m n hm hn
  calc
    _root_.GD.N0232.N0720.N1069.d014352 m n theta =
        _root_.GD.N0232.N0720.N1069.d014352 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) :=
      (_root_.GD.N0232.N0720.N1069.d014355 m n hm hn g theta).symm
    _ = _root_.GD.N0232.N0720.N1069.d014352 m n eta := congrArg _ hg

omit hm hn

end

end N1035
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1035.d014378
#print axioms _root_.GD.N0232.N0720.N1035.d014379
#print axioms _root_.GD.N0232.N0720.N1035.d014380
#print axioms _root_.GD.N0232.N0720.N1035.d014381
#print axioms _root_.GD.N0232.N0720.N1035.d014382
#print axioms _root_.GD.N0232.N0720.N1035.d014383
