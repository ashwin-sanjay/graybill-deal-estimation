import GD.Module0922





























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1067

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1070
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0230.N0567
open _root_.GD.N0230.N0718
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

noncomputable local instance : Nonempty _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨_root_.GD.N0232.N0720.N1080.d014169⟩





def d014398 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  theta.scale₁ + theta.scale₂

theorem d014399 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1067.d014398 theta := by
  exact add_pos theta.scale₁_pos theta.scale₂_pos


def d014400 (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1025.d014301 where
  shift := theta.location
  logScale := Real.log (_root_.GD.N0232.N0720.N1067.d014398 theta)

theorem d014401 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1067.d014400 theta).d009239 = _root_.GD.N0232.N0720.N1067.d014398 theta := by
  exact Real.exp_log (_root_.GD.N0232.N0720.N1067.d014399 theta)



def d014402 (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹ theta

@[simp] theorem d014403 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1067.d014402 theta).location = 0 := by
  unfold _root_.GD.N0232.N0720.N1067.d014402 _root_.GD.N0232.N0720.N1067.d014400
  simp only [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0719.N0946.d009229.d009237, _root_.GD.N0232.N0719.N0946.d009229.d009238,
    _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_neg, Real.exp_log (_root_.GD.N0232.N0720.N1067.d014399 theta)]
  field_simp [(_root_.GD.N0232.N0720.N1067.d014399 theta).ne']
  ring_nf

@[simp] theorem d014404 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1067.d014402 theta).scale₁ =
      theta.scale₁ / _root_.GD.N0232.N0720.N1067.d014398 theta := by
  unfold _root_.GD.N0232.N0720.N1067.d014402 _root_.GD.N0232.N0720.N1067.d014400
  simp only [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0719.N0946.d009229.d009238, _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_neg,
    Real.exp_log (_root_.GD.N0232.N0720.N1067.d014399 theta)]
  field_simp [(_root_.GD.N0232.N0720.N1067.d014399 theta).ne']

@[simp] theorem d014405 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1067.d014402 theta).scale₂ =
      theta.scale₂ / _root_.GD.N0232.N0720.N1067.d014398 theta := by
  unfold _root_.GD.N0232.N0720.N1067.d014402 _root_.GD.N0232.N0720.N1067.d014400
  simp only [_root_.GD.N0232.N0720.N1215.d014275, _root_.GD.N0232.N0719.N0946.d009229.d009238, _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_neg,
    Real.exp_log (_root_.GD.N0232.N0720.N1067.d014399 theta)]
  field_simp [(_root_.GD.N0232.N0720.N1067.d014399 theta).ne']

@[simp] theorem d014406 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1067.d014398 (_root_.GD.N0232.N0720.N1067.d014402 theta) = 1 := by
  unfold _root_.GD.N0232.N0720.N1067.d014398
  rw [_root_.GD.N0232.N0720.N1067.d014404, _root_.GD.N0232.N0720.N1067.d014405]
  field_simp [(_root_.GD.N0232.N0720.N1067.d014399 theta).ne']
  simp [_root_.GD.N0232.N0720.N1067.d014398]

theorem d014407
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1067.d014400 theta) (_root_.GD.N0232.N0720.N1067.d014402 theta) =
      theta := by
  simp [_root_.GD.N0232.N0720.N1067.d014402]



def d014408 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0107.d009046
    m n theta.scale₁ theta.scale₂

include hm hn in
theorem d014409 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1067.d014408 m n theta := by
  exact _root_.GD.N0107.d009050
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos

include hm hn in
theorem d014410 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1067.d014408 m n theta < 1 := by
  exact _root_.GD.N0107.d009051
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos

include hm hn in
theorem d014411 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1067.d014408 m n theta ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(_root_.GD.N0232.N0720.N1067.d014409 m n hm hn theta).le,
    (_root_.GD.N0232.N0720.N1067.d014410 m n hm hn theta).le⟩

include hm hn in

theorem d014412
    (sigma tau dilation : ℝ)
    (hsigma : 0 < sigma) (htau : 0 < tau)
    (hdilation : 0 < dilation) :
    _root_.GD.N0107.d009046
        m n (dilation * sigma) (dilation * tau) =
      _root_.GD.N0107.d009046 m n sigma tau := by
  have hmNat : m ≠ 0 := by omega
  have hnNat : n ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmNat
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnNat
  have hd0 : dilation ≠ 0 := hdilation.ne'
  unfold _root_.GD.N0107.d009046
    _root_.GD.N0107.d009045
    _root_.GD.N0107.d009043
    _root_.GD.N0107.d009044
  field_simp [hm0, hn0, hd0]

include hm hn in
@[simp] theorem d014413
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1067.d014408 m n (_root_.GD.N0232.N0720.N1067.d014402 theta) =
      _root_.GD.N0232.N0720.N1067.d014408 m n theta := by
  unfold _root_.GD.N0232.N0720.N1067.d014408 _root_.GD.N0232.N0720.N1067.d014402
  apply _root_.GD.N0232.N0720.N1067.d014412 m n hm hn
  · exact theta.scale₁_pos
  · exact theta.scale₂_pos
  · exact (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹.d009240





def d014414
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
  _root_.GD.N0232.N0720.N1025.d014316 m n hm hn (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹ p


theorem d014415
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1 =
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p.1 := by
  rw [_root_.GD.N0232.N0720.N1067.d014414,
    _root_.GD.N0232.N0720.N1066.d014349
      m n hm hn (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹ (_root_.GD.N0232.N0720.N1067.d014402 theta) p]
  simp [_root_.GD.N0232.N0720.N1067.d014402]



theorem d014416
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1 =
      _root_.GD.N0232.N0720.N1066.d014332 m n hm hn p.1 := by
  exact _root_.GD.N0232.N0720.N1066.d014350
    m n hm hn (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹ p


def d014417
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
  _root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta
    ⟨_root_.GD.N0230.N0718.d001528 p.1 q.1,
      _root_.GD.N0232.N0720.N1025.d014312 m n hm hn p.2 q.2
        (by norm_num) (by norm_num) (by norm_num)⟩





def d014418
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) : ℝ :=
  (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1 +
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)
        (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1) / 2 -
    _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)
      (_root_.GD.N0232.N0720.N1067.d014417 m n hm hn theta p q).1



theorem d014419
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p.1 q.1 =
      _root_.GD.N0232.N0720.N1067.d014418 m n hm hn theta p q := by
  unfold _root_.GD.N0232.N0720.N1070.d014386 _root_.GD.N0230.N0567.d001641 _root_.GD.N0232.N0720.N1067.d014418
  rw [_root_.GD.N0230.N0567.d001633
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta p.2,
    _root_.GD.N0230.N0567.d001633
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta q.2]
  have hmid : _root_.GD.N0230.N0718.d001528 p.1 q.1 ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1025.d014312 m n hm hn p.2 q.2
      (by norm_num) (by norm_num) (by norm_num)
  rw [_root_.GD.N0230.N0567.d001633
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta hmid]
  rw [_root_.GD.N0232.N0720.N1067.d014415 m n hm hn theta p,
    _root_.GD.N0232.N0720.N1067.d014415 m n hm hn theta q]
  change
    (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p.1 +
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q.1) / 2 -
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p.1 q.1) =
      (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p.1 +
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q.1) / 2 -
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)
          (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta
            ⟨_root_.GD.N0230.N0718.d001528 p.1 q.1, hmid⟩).1
  rw [_root_.GD.N0232.N0720.N1067.d014415
    m n hm hn theta ⟨_root_.GD.N0230.N0718.d001528 p.1 q.1, hmid⟩]



include hm hn in


theorem d014420
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ extraction : ℕ → ℕ,
        StrictMono extraction ∧
        Tendsto
          ((fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n (thetaSeq j)) ∘
            extraction)
          atTop (nhds t) := by
  have hmem : ∀ j,
      _root_.GD.N0232.N0720.N1067.d014408 m n (thetaSeq j) ∈
    Set.Icc (0 : ℝ) 1 :=
    fun j ↦ _root_.GD.N0232.N0720.N1067.d014411
      m n hm hn (thetaSeq j)
  obtain ⟨t, ht, extraction, hextraction, htendsto⟩ :=
    (isCompact_Icc.tendsto_subseq hmem)
  exact ⟨t, ht, extraction, hextraction, htendsto⟩



theorem d014421
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (0 < t ∧ t < 1) ∨ t = 0 ∨ t = 1 := by
  rcases lt_or_eq_of_le ht.1 with hpos | hzero
  · rcases lt_or_eq_of_le ht.2 with hone | hone
    · exact Or.inl ⟨hpos, hone⟩
    · exact Or.inr (Or.inr hone)
  · exact Or.inr (Or.inl hzero.symm)





theorem d014422
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hcollapse : _root_.GD.N0232.N0720.N1070.d014388 m n hm hn p q) :
    ∃ thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168,
      ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ extraction : ℕ → ℕ,
        StrictMono extraction ∧
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
            (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq (extraction j))))
          atTop (nhds t) ∧
        ((0 < t ∧ t < 1) ∨ t = 0 ∨ t = 1) ∧
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1067.d014418 m n hm hn
            (thetaSeq (extraction j))
            ⟨p, hp⟩ ⟨q, hq⟩)
          atTop (nhds 0) ∧
        Tendsto
          (fun j ↦
            _root_.GD.N0232.N0720.N1066.d014332 m n hm hn
                (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn
                  (thetaSeq (extraction j)) ⟨p, hp⟩).1 -
              _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
                (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq (extraction j)))
                (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn
                  (thetaSeq (extraction j)) ⟨p, hp⟩).1)
          atTop (nhds 0) ∧
        Tendsto
          (fun j ↦
            _root_.GD.N0232.N0720.N1066.d014332 m n hm hn
                (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn
                  (thetaSeq (extraction j)) ⟨q, hq⟩).1 -
              _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
                (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq (extraction j)))
                (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn
                  (thetaSeq (extraction j)) ⟨q, hq⟩).1)
          atTop (nhds 0) := by
  obtain ⟨thetaSeq, htax, hpSlack, hqSlack⟩ := hcollapse
  obtain ⟨t, ht, extraction, hextraction, htendsto⟩ :=
    _root_.GD.N0232.N0720.N1067.d014420
      m n hm hn thetaSeq
  refine ⟨thetaSeq, t, ht, extraction, hextraction, ?_,
    _root_.GD.N0232.N0720.N1067.d014421 ht, ?_, ?_, ?_⟩
  · simpa only [_root_.GD.N0232.N0720.N1067.d014413 m n hm hn,
      Function.comp_def] using htendsto
  · have hsub := htax.comp hextraction.tendsto_atTop
    simpa only [_root_.GD.N0232.N0720.N1067.d014419
      m n hm hn (p := ⟨p, hp⟩) (q := ⟨q, hq⟩),
      Function.comp_def] using hsub
  · have hsub := hpSlack.comp hextraction.tendsto_atTop
    simpa only [_root_.GD.N0232.N0720.N1067.d014416,
      _root_.GD.N0232.N0720.N1067.d014415,
      Function.comp_def] using hsub
  · have hsub := hqSlack.comp hextraction.tendsto_atTop
    simpa only [_root_.GD.N0232.N0720.N1067.d014416,
      _root_.GD.N0232.N0720.N1067.d014415,
      Function.comp_def] using hsub





theorem d014423
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (hprofile : Tendsto
      (fun j ↦ _root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) (thetaSeq j))
      atTop
      (nhds (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta)))
    (htax : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1070.d014386 m n hm hn (thetaSeq j) p q)
      atTop (nhds 0)) :
    p = q := by
  have htaxAtLimit : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1070.d014386 m n hm hn (thetaSeq j) p q)
      atTop
      (nhds (_root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q)) := by
    exact (_root_.GD.N0230.N0567.d001643
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) p q).continuousAt.tendsto.comp hprofile
  have hzero : _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q = 0 :=
    tendsto_nhds_unique htaxAtLimit htax
  exact _root_.GD.N0232.N0720.N1066.d014342
    m n hm hn theta hp hq hzero




theorem d014424
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hpq : p ≠ q)
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168)
    (htax : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1070.d014386 m n hm hn (thetaSeq j) p q)
      atTop (nhds 0)) :
    ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      ¬ Tendsto
        (fun j ↦ _root_.GD.N0230.N0567.d001626
          (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) (thetaSeq j))
        atTop
        (nhds (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta)) := by
  intro theta hprofile
  exact hpq (_root_.GD.N0232.N0720.N1067.d014423
    m n hm hn hp hq thetaSeq theta hprofile htax)

end

end N1067
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1067.d014407
#print axioms _root_.GD.N0232.N0720.N1067.d014413
#print axioms _root_.GD.N0232.N0720.N1067.d014415
#print axioms _root_.GD.N0232.N0720.N1067.d014419
#print axioms _root_.GD.N0232.N0720.N1067.d014422
#print axioms _root_.GD.N0232.N0720.N1067.d014423
#print axioms _root_.GD.N0232.N0720.N1067.d014424
