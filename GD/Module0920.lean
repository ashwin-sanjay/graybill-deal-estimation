import GD.Module0919
import GD.Module0062




















open Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1069

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0596
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn



def d014352 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0107.d009046
    m n theta.scale₁ theta.scale₂

theorem d014353 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1069.d014352 m n theta := by
  exact _root_.GD.N0107.d009050
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos

theorem d014354 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1069.d014352 m n theta < 1 := by
  exact _root_.GD.N0107.d009051
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos



theorem d014355
    (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1069.d014352 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) =
      _root_.GD.N0232.N0720.N1069.d014352 m n theta := by
  unfold _root_.GD.N0232.N0720.N1069.d014352 _root_.GD.N0107.d009046
    _root_.GD.N0107.d009045
    _root_.GD.N0107.d009043
    _root_.GD.N0107.d009044
  simp only [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1215.d014275]
  have hg : g.d009239 ≠ 0 := g.d009240.ne'
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp [hg, hm0, hn0]


def d014356
    (collar : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) : ENNReal :=
  ⨆ theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // collar theta},
    _root_.GD.N0232.N0720.N1066.d014324 m n hm hn theta.1 p.1



theorem d014357
    (collar : _root_.GD.N0232.N0720.N1080.d014168 → Prop) :
    LowerSemicontinuous
      (_root_.GD.N0232.N0720.N1069.d014356 m n hm hn collar) := by
  unfold _root_.GD.N0232.N0720.N1069.d014356
  exact lowerSemicontinuous_iSup fun theta ↦
    (_root_.GD.N0232.N0720.N1066.d014334
      m n hm hn theta.1).comp continuous_subtype_val



theorem d014358
    (collar : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    {e d : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn}
    (hed : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) e.1 d.1) :
    _root_.GD.N0232.N0720.N1069.d014356 m n hm hn collar e ≤
      _root_.GD.N0232.N0720.N1069.d014356 m n hm hn collar d := by
  unfold _root_.GD.N0232.N0720.N1069.d014356
  apply iSup_mono
  intro theta
  unfold _root_.GD.N0232.N0720.N1066.d014324
  exact ENNReal.div_le_div_right (hed theta.1)
    (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta.1)



theorem d014359
    (collar : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    (hcollar : ∀ (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168),
      collar (_root_.GD.N0232.N0720.N1215.d014272 g theta) ↔ collar theta)
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1069.d014356 m n hm hn collar
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p) =
      _root_.GD.N0232.N0720.N1069.d014356 m n hm hn collar p := by
  unfold _root_.GD.N0232.N0720.N1069.d014356
  apply le_antisymm
  · apply iSup_le
    intro theta
    rw [_root_.GD.N0232.N0720.N1066.d014348 m n hm hn g theta.1 p]
    exact le_iSup
      (fun eta : {eta : _root_.GD.N0232.N0720.N1080.d014168 // collar eta} ↦
        _root_.GD.N0232.N0720.N1066.d014324 m n hm hn eta.1 p.1)
      ⟨_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta.1,
        (hcollar g⁻¹ theta.1).2 theta.2⟩
  · apply iSup_le
    intro eta
    have hmem : collar (_root_.GD.N0232.N0720.N1215.d014272 g eta.1) :=
      (hcollar g eta.1).2 eta.2
    have hle := le_iSup
      (fun theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // collar theta} ↦
        _root_.GD.N0232.N0720.N1066.d014324 m n hm hn theta.1
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1)
      ⟨_root_.GD.N0232.N0720.N1215.d014272 g eta.1, hmem⟩
    rw [_root_.GD.N0232.N0720.N1066.d014348
      m n hm hn g (_root_.GD.N0232.N0720.N1215.d014272 g eta.1) p] at hle
    simpa using hle


def d014360 (j : ℕ) : ℝ :=
  1 / (j + 1 : ℝ)

omit hm hn in theorem collarRadius_pos (j : ℕ) :
    0 < _root_.GD.N0232.N0720.N1069.d014360 j := by
  unfold _root_.GD.N0232.N0720.N1069.d014360
  positivity


def d014361 (epsilon : ℝ)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) : ENNReal :=
  _root_.GD.N0232.N0720.N1069.d014356 m n hm hn
    (fun theta ↦ _root_.GD.N0232.N0720.N1069.d014352 m n theta ≤ epsilon) p


def d014362 (epsilon : ℝ)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) : ENNReal :=
  _root_.GD.N0232.N0720.N1069.d014356 m n hm hn
    (fun theta ↦ 1 - _root_.GD.N0232.N0720.N1069.d014352 m n theta ≤ epsilon) p


def d014363
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) : ENNReal :=
  ⨅ j : ℕ, _root_.GD.N0232.N0720.N1069.d014361 m n hm hn (_root_.GD.N0232.N0720.N1069.d014360 j) p


def d014364
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) : ENNReal :=
  ⨅ j : ℕ, _root_.GD.N0232.N0720.N1069.d014362 m n hm hn (_root_.GD.N0232.N0720.N1069.d014360 j) p



def d014365
    (collar : ℕ → _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    (j : ℕ) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) : ENNReal :=
  _root_.GD.N0232.N0720.N1069.d014356 m n hm hn (collar j) p

theorem d014366
    (collar : ℕ → _root_.GD.N0232.N0720.N1080.d014168 → Prop) :
    ∀ j, LowerSemicontinuous
      (_root_.GD.N0232.N0720.N1069.d014365 m n hm hn collar j) := by
  intro j
  exact _root_.GD.N0232.N0720.N1069.d014357
    m n hm hn (collar j)






theorem d014367
    (collar : ℕ → _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    (C : Set (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn))
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn))
    (htower : _root_.GD.N0230.N0583.d000745
      (_root_.GD.N0232.N0720.N1069.d014365 m n hm hn collar) C face)
    (hCnonempty : C.Nonempty) (hCcompact : IsCompact C) :
    ∃ p, (∀ j, p ∈ face j) ∧
      _root_.GD.N0230.N0596.d000730
        (_root_.GD.N0232.N0720.N1069.d014365 m n hm hn collar) C p := by
  exact _root_.GD.N0230.N0583.d000750
    (_root_.GD.N0232.N0720.N1069.d014365 m n hm hn collar) C face htower
    hCnonempty hCcompact
    (fun j ↦
      (_root_.GD.N0232.N0720.N1069.d014366
        m n hm hn collar j).lowerSemicontinuousOn (face j))

theorem d014368
    {e d : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn}
    (hed : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) e.1 d.1)
    (epsilon : ℝ) :
    _root_.GD.N0232.N0720.N1069.d014361 m n hm hn epsilon e ≤
      _root_.GD.N0232.N0720.N1069.d014361 m n hm hn epsilon d :=
  _root_.GD.N0232.N0720.N1069.d014358 m n hm hn _ hed

theorem d014369
    {e d : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn}
    (hed : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) e.1 d.1)
    (epsilon : ℝ) :
    _root_.GD.N0232.N0720.N1069.d014362 m n hm hn epsilon e ≤
      _root_.GD.N0232.N0720.N1069.d014362 m n hm hn epsilon d :=
  _root_.GD.N0232.N0720.N1069.d014358 m n hm hn _ hed

theorem d014370
    {e d : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn}
    (hed : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) e.1 d.1) :
    _root_.GD.N0232.N0720.N1069.d014363 m n hm hn e ≤
      _root_.GD.N0232.N0720.N1069.d014363 m n hm hn d := by
  unfold _root_.GD.N0232.N0720.N1069.d014363
  exact iInf_mono fun j ↦ _root_.GD.N0232.N0720.N1069.d014368
    m n hm hn hed (_root_.GD.N0232.N0720.N1069.d014360 j)

theorem d014371
    {e d : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn}
    (hed : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) e.1 d.1) :
    _root_.GD.N0232.N0720.N1069.d014364 m n hm hn e ≤
      _root_.GD.N0232.N0720.N1069.d014364 m n hm hn d := by
  unfold _root_.GD.N0232.N0720.N1069.d014364
  exact iInf_mono fun j ↦ _root_.GD.N0232.N0720.N1069.d014369
    m n hm hn hed (_root_.GD.N0232.N0720.N1069.d014360 j)

theorem d014372
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (epsilon : ℝ) :
    _root_.GD.N0232.N0720.N1069.d014361 m n hm hn epsilon
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p) =
      _root_.GD.N0232.N0720.N1069.d014361 m n hm hn epsilon p := by
  apply _root_.GD.N0232.N0720.N1069.d014359
  intro h theta
  rw [_root_.GD.N0232.N0720.N1069.d014355 m n hm hn h theta]

theorem d014373
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (epsilon : ℝ) :
    _root_.GD.N0232.N0720.N1069.d014362 m n hm hn epsilon
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p) =
      _root_.GD.N0232.N0720.N1069.d014362 m n hm hn epsilon p := by
  apply _root_.GD.N0232.N0720.N1069.d014359
  intro h theta
  rw [_root_.GD.N0232.N0720.N1069.d014355 m n hm hn h theta]

theorem d014374
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1069.d014363 m n hm hn
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p) =
      _root_.GD.N0232.N0720.N1069.d014363 m n hm hn p := by
  unfold _root_.GD.N0232.N0720.N1069.d014363
  congr 1
  funext j
  exact _root_.GD.N0232.N0720.N1069.d014372
    m n hm hn g p (_root_.GD.N0232.N0720.N1069.d014360 j)

theorem d014375
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1069.d014364 m n hm hn
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p) =
      _root_.GD.N0232.N0720.N1069.d014364 m n hm hn p := by
  unfold _root_.GD.N0232.N0720.N1069.d014364
  congr 1
  funext j
  exact _root_.GD.N0232.N0720.N1069.d014373
    m n hm hn g p (_root_.GD.N0232.N0720.N1069.d014360 j)

end

end N1069
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1069.d014355
#print axioms _root_.GD.N0232.N0720.N1069.d014357
#print axioms _root_.GD.N0232.N0720.N1069.d014367
#print axioms _root_.GD.N0232.N0720.N1069.d014370
#print axioms _root_.GD.N0232.N0720.N1069.d014371
#print axioms _root_.GD.N0232.N0720.N1069.d014374
#print axioms _root_.GD.N0232.N0720.N1069.d014375
