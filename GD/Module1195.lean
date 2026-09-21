import GD.Module1174
import GD.Module1184
import Mathlib.Topology.Algebra.Order.Archimedean




























open Filter Topology MeasureTheory
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1445

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1288
open _root_.GD.N0232.N0720.N1453
open _root_.GD.N0232.N0720.N1048
open _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

local notation "PA" => _root_.GD.N0232.N0720.N1482.d015118

variable (m n : ℕ)




def d019275 (g : PA) : PA := ⟨-g.shift, g.logScale⟩

@[simp] theorem d019276 (g : PA) : (_root_.GD.N0232.N0720.N1445.d019275 g).shift = -g.shift := rfl

@[simp] theorem d019277 (g : PA) :
    (_root_.GD.N0232.N0720.N1445.d019275 g).logScale = g.logScale := rfl

@[simp] theorem d019278 (g : PA) :
    (_root_.GD.N0232.N0720.N1445.d019275 g).d009239 = g.d009239 := rfl

theorem d019279 (g : PA) : _root_.GD.N0232.N0720.N1445.d019275 (_root_.GD.N0232.N0720.N1445.d019275 g) = g := by
  obtain ⟨b, l⟩ := g
  show (⟨- -b, l⟩ : PA) = ⟨b, l⟩
  rw [neg_neg]

theorem d019280 (g : PA) : _root_.GD.N0232.N0720.N1445.d019275 g⁻¹ = (_root_.GD.N0232.N0720.N1445.d019275 g)⁻¹ := by
  obtain ⟨b, l⟩ := g
  show (⟨-(-(Real.exp (-l) * b)), -l⟩ : PA) = ⟨-(Real.exp (-l) * -b), -l⟩
  rw [neg_neg, mul_neg, neg_neg]

theorem d019281 (g : PA) :
    _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1445.d019275 g) _root_.GD.N0232.N0720.N1080.d014169 =
      _root_.GD.N0232.N0720.N1446.d019024 (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) := by
  apply _root_.GD.N0232.N0720.N1215.d014277
  · simp [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1446.d019024, _root_.GD.N0232.N0720.N1080.d014169]
  · simp [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1446.d019024, _root_.GD.N0232.N0720.N1080.d014169]
  · simp [_root_.GD.N0232.N0720.N1215.d014275, _root_.GD.N0232.N0720.N1446.d019024, _root_.GD.N0232.N0720.N1080.d014169]




theorem d019282 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : PA) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s (_root_.GD.N0232.N0720.N1445.d019275 g) = _root_.GD.N0232.N0720.N1159.d014647 m n s g := by
  rw [_root_.GD.N0232.N0720.N1288.d015630, _root_.GD.N0232.N0720.N1288.d015630,
    _root_.GD.N0232.N0720.N1445.d019278, ← _root_.GD.N0232.N0720.N1445.d019280, _root_.GD.N0232.N0720.N1445.d019281,
    _root_.GD.N0232.N0720.N1048.d019047]


theorem d019283 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) {g : PA}
    (hg : g ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s) : _root_.GD.N0232.N0720.N1445.d019275 g ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s := by
  rw [_root_.GD.N0232.N0720.N1453.d018887] at hg ⊢
  rw [_root_.GD.N0232.N0720.N1445.d019282]
  exact hg



theorem d019284 (g : PA) :
    g * (_root_.GD.N0232.N0720.N1445.d019275 g)⁻¹ = _root_.GD.N0232.N0720.N1482.d015128 (2 * g.shift) := by
  obtain ⟨b, l⟩ := g
  show (⟨b + Real.exp l * (-(Real.exp (-l) * -b)), l + -l⟩ : PA) = ⟨2 * b, 0⟩
  have h1 : b + Real.exp l * (-(Real.exp (-l) * -b)) = 2 * b := by
    rw [Real.exp_neg]
    have hne : Real.exp l ≠ 0 := Real.exp_ne_zero l
    field_simp
    ring
  have h2 : l + -l = 0 := by ring
  rw [h1, h2]

theorem d019285 (g : PA) (t : ℝ) :
    g * _root_.GD.N0232.N0720.N1482.d015128 t * g⁻¹ = _root_.GD.N0232.N0720.N1482.d015128 (g.d009239 * t) := by
  obtain ⟨b, l⟩ := g
  show (⟨(b + Real.exp l * t) + Real.exp (l + 0) * (-(Real.exp (-l) * b)), (l + 0) + -l⟩ :
      PA) = ⟨Real.exp l * t, 0⟩
  have h1 : (b + Real.exp l * t) + Real.exp (l + 0) * (-(Real.exp (-l) * b)) = Real.exp l * t := by
    rw [add_zero, Real.exp_neg]
    have hne : Real.exp l ≠ 0 := Real.exp_ne_zero l
    field_simp
    ring
  have h2 : (l + 0) + -l = 0 := by ring
  rw [h1, h2]

theorem d019286 (g : PA) : g⁻¹.d009239 = g.d009239⁻¹ := by
  show Real.exp (-g.logScale) = (Real.exp g.logScale)⁻¹
  exact Real.exp_neg g.logScale


def d019287 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : AddSubgroup ℝ where
  carrier := {t | _root_.GD.N0232.N0720.N1482.d015128 t ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s}
  zero_mem' := by
    show _root_.GD.N0232.N0720.N1482.d015128 0 ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s
    rw [_root_.GD.N0232.N0720.N1482.d015137]
    exact one_mem _
  add_mem' := by
    intro a b ha hb
    show _root_.GD.N0232.N0720.N1482.d015128 (a + b) ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s
    rw [← _root_.GD.N0232.N0720.N1482.d015139]
    exact mul_mem ha hb
  neg_mem' := by
    intro a ha
    show _root_.GD.N0232.N0720.N1482.d015128 (-a) ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s
    rw [← _root_.GD.N0232.N0720.N1482.d015141]
    exact inv_mem ha

theorem d019288 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (t : ℝ) :
    t ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s ↔ _root_.GD.N0232.N0720.N1482.d015128 t ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s := Iff.rfl

theorem d019289 : Continuous _root_.GD.N0232.N0720.N1482.d015128 := by
  refine continuous_induced_rng.2 ?_
  show Continuous (fun t : ℝ => ((0 : ℝ), t))
  fun_prop

theorem d019290 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    IsClosed (_root_.GD.N0232.N0720.N1445.d019287 m n s : Set ℝ) :=
  (_root_.GD.N0232.N0720.N1453.d018889 m n s).preimage _root_.GD.N0232.N0720.N1445.d019289

theorem d019291 {c x : ℝ}
    (hx : x ∈ AddSubgroup.closure ({c} : Set ℝ)) (hx0 : x ≠ 0) : |c| ≤ |x| := by
  rcases AddSubgroup.mem_closure_singleton.1 hx with ⟨k, rfl⟩
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hx0
  rw [zsmul_eq_mul, abs_mul]
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have := Int.one_le_abs hk
    exact_mod_cast this
  exact le_mul_of_one_le_left (abs_nonneg c) h1



theorem d019292 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) {g : PA}
    (hg : g ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s) (hb : g.shift ≠ 0) (hl : g.logScale ≠ 0) :
    _root_.GD.N0232.N0720.N1445.d019287 m n s = ⊤ := by
  have h2b : 2 * g.shift ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s := by
    show _root_.GD.N0232.N0720.N1482.d015128 (2 * g.shift) ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s
    rw [← _root_.GD.N0232.N0720.N1445.d019284]
    exact mul_mem hg (inv_mem (_root_.GD.N0232.N0720.N1445.d019283 m n s hg))
  have hscale : ∀ t ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s, g.d009239 * t ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s := by
    intro t ht
    show _root_.GD.N0232.N0720.N1482.d015128 (g.d009239 * t) ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s
    rw [← _root_.GD.N0232.N0720.N1445.d019285]
    exact mul_mem (mul_mem hg ht) (inv_mem hg)
  have hscale_inv : ∀ t ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s,
      g.d009239⁻¹ * t ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s := by
    intro t ht
    show _root_.GD.N0232.N0720.N1482.d015128 (g.d009239⁻¹ * t) ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s
    rw [← _root_.GD.N0232.N0720.N1445.d019286, ← _root_.GD.N0232.N0720.N1445.d019285 g⁻¹, inv_inv]
    exact mul_mem (mul_mem (inv_mem hg) ht) hg
  have hpow : ∀ k : ℕ, 2 * g.shift * g.d009239 ^ k ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s ∧
      2 * g.shift * (g.d009239⁻¹) ^ k ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, mul_one]
      exact ⟨h2b, h2b⟩
    | succ k ih =>
      refine ⟨?_, ?_⟩
      · have := hscale _ ih.1
        rw [pow_succ]
        convert this using 1
        ring
      · have := hscale_inv _ ih.2
        rw [pow_succ]
        convert this using 1
        ring
  have h2b0 : 2 * g.shift ≠ 0 := mul_ne_zero two_ne_zero hb
  have ha : 0 < g.d009239 := g.d009240
  have ha1 : g.d009239 ≠ 1 := by
    intro h
    apply hl
    have := congrArg Real.log h
    rwa [_root_.GD.N0232.N0719.N0946.d009229.d009239, Real.log_exp, Real.log_one] at this
  rcases AddSubgroup.dense_or_cyclic (_root_.GD.N0232.N0720.N1445.d019287 m n s) with hdense | ⟨c, hc⟩
  · have hcl := _root_.GD.N0232.N0720.N1445.d019290 m n s
    have huniv : (_root_.GD.N0232.N0720.N1445.d019287 m n s : Set ℝ) = Set.univ := by
      rw [← hcl.closure_eq]
      exact hdense.closure_eq
    rw [AddSubgroup.eq_top_iff']
    intro t
    have : t ∈ (_root_.GD.N0232.N0720.N1445.d019287 m n s : Set ℝ) := by rw [huniv]; exact Set.mem_univ t
    exact this
  · exfalso
    have hmem : ∀ x ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s, x ≠ 0 → |c| ≤ |x| := by
      intro x hx hx0
      rw [hc] at hx
      exact _root_.GD.N0232.N0720.N1445.d019291 hx hx0
    have hc0 : c ≠ 0 := by
      intro hc0
      have hx := h2b
      rw [hc, hc0] at hx
      rcases AddSubgroup.mem_closure_singleton.1 hx with ⟨k, hk⟩
      rw [zsmul_zero] at hk
      exact h2b0 hk.symm
    rcases lt_or_gt_of_ne ha1 with hlt | hgt
    · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (abs_pos.2 hc0) (abs_pos.2 h2b0)) hlt
      have hx0 : 2 * g.shift * g.d009239 ^ k ≠ 0 := mul_ne_zero h2b0 (pow_ne_zero _ ha.ne')
      have hle := hmem _ (hpow k).1 hx0
      rw [abs_mul, abs_of_pos (pow_pos ha k)] at hle
      have hlt' : |2 * g.shift| * g.d009239 ^ k < |c| := (lt_div_iff₀' (abs_pos.2 h2b0)).1 hk
      exact lt_irrefl _ (lt_of_le_of_lt hle hlt')
    · have hinv : g.d009239⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (abs_pos.2 hc0) (abs_pos.2 h2b0)) hinv
      have hx0 : 2 * g.shift * (g.d009239⁻¹) ^ k ≠ 0 :=
        mul_ne_zero h2b0 (pow_ne_zero _ (inv_pos.2 ha).ne')
      have hle := hmem _ (hpow k).2 hx0
      rw [abs_mul, abs_of_pos (pow_pos (inv_pos.2 ha) k)] at hle
      have hlt' : |2 * g.shift| * (g.d009239⁻¹) ^ k < |c| :=
        (lt_div_iff₀' (abs_pos.2 h2b0)).1 hk
      exact lt_irrefl _ (lt_of_le_of_lt hle hlt')

theorem d019293 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    {g : PA} (hg : g ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s) (hb : g.shift ≠ 0)
    (hl : g.logScale ≠ 0) (t : ℝ) :
    _root_.GD.N0232.N0720.N1482.d015128 t ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s := by
  have h := _root_.GD.N0232.N0720.N1445.d019292 m n s hg hb hl
  have : t ∈ _root_.GD.N0232.N0720.N1445.d019287 m n s := by
    rw [h]
    exact AddSubgroup.mem_top t
  exact this



theorem d019294
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) {g : PA}
    (hg : _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0) (hb : g.shift ≠ 0) (hl : g.logScale ≠ 0)
    (t : ℝ) : _root_.GD.N0232.N0720.N1159.d014647 m n s (_root_.GD.N0232.N0720.N1482.d015128 t) = 0 := by
  rw [← _root_.GD.N0232.N0720.N1453.d018887] at hg ⊢
  exact _root_.GD.N0232.N0720.N1445.d019293 m n s hg hb hl t



theorem d019295
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h : _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0) (t : ℝ) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s (_root_.GD.N0232.N0720.N1482.d015128 t) = 0 := by
  refine _root_.GD.N0232.N0720.N1445.d019294 m n s h ?_ ?_ t
  · show (1 : ℝ) ≠ 0
    norm_num
  · show Real.log 3 ≠ 0
    exact (Real.log_pos (by norm_num)).ne'



theorem d019296
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h : _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0) (t : ℝ) :
    _root_.GD.N0232.N0720.N1159.d014642 m n (_root_.GD.N0232.N0720.N1482.d015128 t) (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1159.d014644 m n s _
          (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1) =
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  have := _root_.GD.N0232.N0720.N1445.d019295 m n s h t
  rw [← _root_.GD.N0232.N0720.N1453.d018887, _root_.GD.N0232.N0720.N1453.d018886] at this
  exact this




def d019297 : Subgroup PA where
  carrier := {g | g.shift = 0}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    show (g * h).shift = 0
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009235, hg, hh, mul_zero, add_zero]
  inv_mem' := by
    intro g hg
    show g⁻¹.shift = 0
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009237, hg, mul_zero, neg_zero]


def d019298 : Subgroup PA where
  carrier := {g | g.logScale = 0}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    show (g * h).logScale = 0
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009236, hg, hh, add_zero]
  inv_mem' := by
    intro g hg
    show g⁻¹.logScale = 0
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009238, hg, neg_zero]

theorem d019299 (g : PA) : g ∈ _root_.GD.N0232.N0720.N1445.d019297 ↔ g.shift = 0 := Iff.rfl

theorem d019300 (g : PA) : g ∈ _root_.GD.N0232.N0720.N1445.d019298 ↔ g.logScale = 0 := Iff.rfl




theorem d019301 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1453.d018885 m n s ≤ _root_.GD.N0232.N0720.N1445.d019297 ∨
      _root_.GD.N0232.N0720.N1453.d018885 m n s ≤ _root_.GD.N0232.N0720.N1445.d019298 ∨
        ∀ t : ℝ, _root_.GD.N0232.N0720.N1482.d015128 t ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s := by
  by_cases hmixed : ∃ g ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s, g.shift ≠ 0 ∧ g.logScale ≠ 0
  · obtain ⟨g, hg, hb, hl⟩ := hmixed
    exact Or.inr (Or.inr (_root_.GD.N0232.N0720.N1445.d019293 m n s hg hb hl))
  · push Not at hmixed
    by_cases hdil : ∀ g ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s, g.shift = 0
    · exact Or.inl hdil
    · push Not at hdil
      obtain ⟨g, hg, hb⟩ := hdil
      have hgl : g.logScale = 0 := hmixed g hg hb
      refine Or.inr (Or.inl ?_)
      intro h hh
      by_contra hl
      have hb' : h.shift = 0 := by
        by_contra hb'
        exact hl (hmixed h hh hb')

      have hprod : h * g ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s := mul_mem hh hg
      have hps : (h * g).shift ≠ 0 := by
        rw [_root_.GD.N0232.N0719.N0946.d009229.d009235, hb', zero_add]
        exact mul_ne_zero (Real.exp_ne_zero _) hb
      have hpl : (h * g).logScale ≠ 0 := by
        rw [_root_.GD.N0232.N0719.N0946.d009229.d009236, hgl, add_zero]
        exact hl
      exact hpl (hmixed _ hprod hps)


def d019302 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : AddSubgroup ℝ where
  carrier := {l | _root_.GD.N0232.N0720.N1482.d015129 l ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s}
  zero_mem' := by
    show _root_.GD.N0232.N0720.N1482.d015129 0 ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s
    exact one_mem _
  add_mem' := by
    intro a b ha hb
    show _root_.GD.N0232.N0720.N1482.d015129 (a + b) ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s
    rw [← _root_.GD.N0232.N0720.N1482.d015140]
    exact mul_mem ha hb
  neg_mem' := by
    intro a ha
    show _root_.GD.N0232.N0720.N1482.d015129 (-a) ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s
    rw [← _root_.GD.N0232.N0720.N1482.d015142]
    exact inv_mem ha

theorem d019303 : Continuous _root_.GD.N0232.N0720.N1482.d015129 := by
  refine continuous_induced_rng.2 ?_
  show Continuous (fun l : ℝ => (l, (0 : ℝ)))
  fun_prop

theorem d019304 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    IsClosed (_root_.GD.N0232.N0720.N1445.d019302 m n s : Set ℝ) :=
  (_root_.GD.N0232.N0720.N1453.d018889 m n s).preimage _root_.GD.N0232.N0720.N1445.d019303

theorem d019305 (b l : ℝ) :
    _root_.GD.N0232.N0720.N1482.d015128 b * _root_.GD.N0232.N0720.N1482.d015129 l = ⟨b, l⟩ := by
  show (⟨b + Real.exp 0 * 0, 0 + l⟩ : PA) = ⟨b, l⟩
  rw [mul_zero, add_zero, zero_add]



theorem d019306 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (htrans : ∀ t : ℝ, _root_.GD.N0232.N0720.N1482.d015128 t ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s)
    (hdense : Dense (_root_.GD.N0232.N0720.N1445.d019302 m n s : Set ℝ)) :
    _root_.GD.N0232.N0720.N1453.d018885 m n s = ⊤ := by
  have hcl := _root_.GD.N0232.N0720.N1445.d019304 m n s
  have huniv : (_root_.GD.N0232.N0720.N1445.d019302 m n s : Set ℝ) = Set.univ := by
    rw [← hcl.closure_eq]
    exact hdense.closure_eq
  rw [eq_top_iff]
  intro g _
  obtain ⟨b, l⟩ := g
  rw [← _root_.GD.N0232.N0720.N1445.d019305]
  refine mul_mem (htrans b) ?_
  have : l ∈ (_root_.GD.N0232.N0720.N1445.d019302 m n s : Set ℝ) := by rw [huniv]; exact Set.mem_univ l
  exact this



theorem d019307 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (htrans : ∀ t : ℝ, _root_.GD.N0232.N0720.N1482.d015128 t ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s)
    (hdef : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s ≠ 0) :
    ∃ c : ℝ, _root_.GD.N0232.N0720.N1445.d019302 m n s = AddSubgroup.closure {c} := by
  rcases AddSubgroup.dense_or_cyclic (_root_.GD.N0232.N0720.N1445.d019302 m n s) with hdense | hcyc
  · exfalso
    apply hdef
    rw [_root_.GD.N0232.N0720.N1453.d018896]
    exact _root_.GD.N0232.N0720.N1445.d019306 m n s htrans hdense
  · exact hcyc

end

end N1445
end N0720
end N0232
end GD
