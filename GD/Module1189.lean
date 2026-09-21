import GD.Module0987
import GD.Module1184
import GD.Module0965
import GD.Module0994
import GD.Module0028
































open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace GD
namespace N0232
namespace N0720
namespace N1107

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0647
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1356
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1048
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1477

variable (m n : ℕ)




theorem d019111 (θ : _root_.GD.N0232.N0720.N1080.d014168) (c : ℝ≥0∞) :
    {d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) | _root_.GD.N0232.N0720.N1080.d014182 m n θ d ≤ c} =
      _root_.GD.N0230.N0602.d000118 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
        (fun θ' => if θ' = θ then c else ⊤) := by
  ext d
  simp only [_root_.GD.N0230.N0602.d000118, Set.mem_setOf_eq]
  constructor
  · intro hd θ'
    by_cases hθ : θ' = θ
    · subst hθ
      simpa [_root_.GD.N0232.N0720.N1080.d014182] using hd
    · simp [hθ]
  · intro hd
    simpa [_root_.GD.N0232.N0720.N1080.d014182] using hd θ

theorem d019112 (θ : _root_.GD.N0232.N0720.N1080.d014168) (c : ℝ≥0∞) :
    IsClosed {d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) | _root_.GD.N0232.N0720.N1080.d014182 m n θ d ≤ c} := by
  rw [_root_.GD.N0232.N0720.N1107.d019111]
  exact _root_.GD.N0230.N0602.d000122 _ _ _ _ (_root_.GD.N0232.N0720.N1080.d014173 m n)

theorem d019113 (θ : _root_.GD.N0232.N0720.N1080.d014168) (c : ℝ≥0∞) :
    Convex ℝ {d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) | _root_.GD.N0232.N0720.N1080.d014182 m n θ d ≤ c} := by
  rw [_root_.GD.N0232.N0720.N1107.d019111]
  exact _root_.GD.N0230.N0602.d000123 _ _ _ _ (_root_.GD.N0232.N0720.N1080.d014173 m n)




def d019114 (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ε : ℝ) :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {d | ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ s + ENNReal.ofReal ε}

theorem d019115 (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ε : ℝ) :
    _root_.GD.N0232.N0720.N1107.d019114 m n s ε =
      _root_.GD.N0230.N0602.d000118 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
        (fun θ => _root_.GD.N0232.N0720.N1080.d014182 m n θ s + ENNReal.ofReal ε) := rfl

theorem d019116 (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ε : ℝ) :
    IsClosed (_root_.GD.N0232.N0720.N1107.d019114 m n s ε) := by
  rw [_root_.GD.N0232.N0720.N1107.d019115]
  exact _root_.GD.N0230.N0602.d000122 _ _ _ _ (_root_.GD.N0232.N0720.N1080.d014173 m n)

theorem d019117 (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ε : ℝ) :
    Convex ℝ (_root_.GD.N0232.N0720.N1107.d019114 m n s ε) := by
  rw [_root_.GD.N0232.N0720.N1107.d019115]
  exact _root_.GD.N0230.N0602.d000123 _ _ _ _ (_root_.GD.N0232.N0720.N1080.d014173 m n)

theorem d019118 (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ε : ℝ) :
    _root_.GD.N0232.N0720.N1159.d014630 m n s ⊆ _root_.GD.N0232.N0720.N1107.d019114 m n s ε := by
  intro d hd θ
  exact le_trans (hd θ) le_self_add

theorem d019119 (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    _root_.GD.N0232.N0720.N1107.d019114 m n s ε₁ ⊆ _root_.GD.N0232.N0720.N1107.d019114 m n s ε₂ := by
  intro d hd θ
  exact le_trans (hd θ) (add_le_add le_rfl (ENNReal.ofReal_le_ofReal h))


def d019120 (θ : _root_.GD.N0232.N0720.N1080.d014168) (c ε : ℝ) : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {d | _root_.GD.N0232.N0720.N1080.d014182 m n θ d ≤ ENNReal.ofReal (c + ε)}

theorem d019121 (θ : _root_.GD.N0232.N0720.N1080.d014168) (c ε : ℝ) : IsClosed (_root_.GD.N0232.N0720.N1107.d019120 m n θ c ε) :=
  _root_.GD.N0232.N0720.N1107.d019112 m n θ _

theorem d019122 (θ : _root_.GD.N0232.N0720.N1080.d014168) (c ε : ℝ) : Convex ℝ (_root_.GD.N0232.N0720.N1107.d019120 m n θ c ε) :=
  _root_.GD.N0232.N0720.N1107.d019113 m n θ _

theorem d019123 (θ : _root_.GD.N0232.N0720.N1080.d014168) (c : ℝ) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    _root_.GD.N0232.N0720.N1107.d019120 m n θ c ε₁ ⊆ _root_.GD.N0232.N0720.N1107.d019120 m n θ c ε₂ :=
  fun _ hd => le_trans hd (ENNReal.ofReal_le_ofReal (by linarith))




def d019124 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) : ℝ :=
  g.d009239 ^ 2 * ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2

theorem d019125 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    0 ≤ _root_.GD.N0232.N0720.N1107.d019124 m n s g :=
  mul_nonneg (sq_nonneg _) (sq_nonneg _)


theorem d019126 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1107.d019124 m n s g) := by
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _ (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  change _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP) = _
  rw [_root_.GD.N0232.N0720.N1159.d014643, _root_.GD.N0232.N0720.N1080.d014190 m n]
  simp only [zero_sub, norm_neg]
  rw [_root_.GD.N0232.N0720.N1107.d019124, ENNReal.ofReal_mul (sq_nonneg _)]





def d019127 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (ε : ℝ) : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  _root_.GD.N0232.N0720.N1107.d019114 m n s.value ε ∩
    _root_.GD.N0232.N0720.N1107.d019120 m n _root_.GD.N0232.N0720.N1080.d014169 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) ε ∩
    _root_.GD.N0232.N0720.N1107.d019120 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1107.d019124 m n s _root_.GD.N0232.N0720.N1482.d015130) ε ∩
    _root_.GD.N0232.N0720.N1107.d019120 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131 _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1107.d019124 m n s _root_.GD.N0232.N0720.N1482.d015131) ε


def d019128 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (_root_.GD.N0232.N0720.N1107.d019127 m n s ε).Nonempty

theorem d019129 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (ε : ℝ) : IsClosed (_root_.GD.N0232.N0720.N1107.d019127 m n s ε) :=
  (((_root_.GD.N0232.N0720.N1107.d019116 m n _ ε).inter (_root_.GD.N0232.N0720.N1107.d019121 m n _ _ ε)).inter
    (_root_.GD.N0232.N0720.N1107.d019121 m n _ _ ε)).inter (_root_.GD.N0232.N0720.N1107.d019121 m n _ _ ε)

theorem d019130 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (ε : ℝ) : Convex ℝ (_root_.GD.N0232.N0720.N1107.d019127 m n s ε) :=
  (((_root_.GD.N0232.N0720.N1107.d019117 m n _ ε).inter (_root_.GD.N0232.N0720.N1107.d019122 m n _ _ ε)).inter
    (_root_.GD.N0232.N0720.N1107.d019122 m n _ _ ε)).inter (_root_.GD.N0232.N0720.N1107.d019122 m n _ _ ε)

theorem d019131 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    _root_.GD.N0232.N0720.N1107.d019127 m n s ε₁ ⊆ _root_.GD.N0232.N0720.N1107.d019127 m n s ε₂ := by
  intro d hd
  exact ⟨⟨⟨_root_.GD.N0232.N0720.N1107.d019119 m n _ h hd.1.1.1, _root_.GD.N0232.N0720.N1107.d019123 m n _ _ h hd.1.1.2⟩,
    _root_.GD.N0232.N0720.N1107.d019123 m n _ _ h hd.1.2⟩, _root_.GD.N0232.N0720.N1107.d019123 m n _ _ h hd.2⟩



theorem d019132 (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hd : d ∈ _root_.GD.N0232.N0720.N1107.d019114 m n w ε) :
    ‖d‖ ≤ Real.sqrt (‖w‖ ^ 2 + 1) := by
  have h := hd _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at h
  simp only [zero_sub, norm_neg] at h
  have h2 : ENNReal.ofReal (‖d‖ ^ 2) ≤ ENNReal.ofReal (‖w‖ ^ 2 + 1) := by
    refine le_trans h ?_
    rw [← ENNReal.ofReal_add (sq_nonneg _) hε0]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h3 : ‖d‖ ^ 2 ≤ ‖w‖ ^ 2 + 1 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
  have h4 := Real.sqrt_le_sqrt h3
  rwa [Real.sqrt_sq (norm_nonneg _)] at h4


theorem d019133 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hd : d ∈ _root_.GD.N0232.N0720.N1107.d019127 m n s ε) :
    ‖d‖ ≤ Real.sqrt (‖s.value‖ ^ 2 + 1) :=
  _root_.GD.N0232.N0720.N1107.d019132 m n s.value hε0 hε1 hd.1.1.1



theorem d019134 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (h : _root_.GD.N0232.N0720.N1107.d019128 m n s) :
    ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), ∀ ε : ℝ, 0 < ε → ε ≤ 1 → d ∈ _root_.GD.N0232.N0720.N1107.d019127 m n s ε := by
  haveI : Nonempty {ε : ℝ // 0 < ε ∧ ε ≤ 1} := ⟨⟨1, one_pos, le_rfl⟩⟩
  have hres := _root_.GD.N0230.N0647.d000348
    (fun e : {ε : ℝ // 0 < ε ∧ ε ≤ 1} => _root_.GD.N0232.N0720.N1107.d019127 m n s e.1)
    (fun e => h e.1 e.2.1 e.2.2)
    (fun e => _root_.GD.N0232.N0720.N1107.d019129 m n s e.1)
    (fun e => _root_.GD.N0232.N0720.N1107.d019130 m n s e.1)
    (Real.sqrt (‖s.value‖ ^ 2 + 1))
    (fun e _ hd => _root_.GD.N0232.N0720.N1107.d019133 m n s e.2.1.le e.2.2 hd)
    (fun e₁ e₂ => ⟨⟨min e₁.1 e₂.1, lt_min e₁.2.1 e₂.2.1, le_trans (min_le_left _ _) e₁.2.2⟩,
      _root_.GD.N0232.N0720.N1107.d019131 m n s (min_le_left _ _), _root_.GD.N0232.N0720.N1107.d019131 m n s (min_le_right _ _)⟩)
  obtain ⟨d, hd⟩ := hres
  exact ⟨d, fun ε hε hε1 => Set.mem_iInter.1 hd ⟨ε, hε, hε1⟩⟩



theorem d019135 (a b : ℝ≥0∞)
    (hab : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → a ≤ b + ENNReal.ofReal ε) : a ≤ b := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hpos : (0 : ℝ) < min (ε : ℝ) 1 := lt_min (NNReal.coe_pos.2 hε) one_pos
  refine le_trans (hab (min (ε : ℝ) 1) hpos (min_le_right _ _)) ?_
  refine add_le_add le_rfl ?_
  calc ENNReal.ofReal (min (ε : ℝ) 1) ≤ ENNReal.ofReal (ε : ℝ) :=
        ENNReal.ofReal_le_ofReal (min_le_left _ _)
    _ = ε := ENNReal.ofReal_coe_nnreal

theorem d019136 (a : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c)
    (hab : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → a ≤ ENNReal.ofReal (c + ε)) :
    a ≤ ENNReal.ofReal c := by
  refine _root_.GD.N0232.N0720.N1107.d019135 a _ fun ε hε hε1 => ?_
  rw [← ENNReal.ofReal_add hc hε.le]
  exact hab ε hε hε1




theorem d019137 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h : _root_.GD.N0232.N0720.N1107.d019128 m n s) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  obtain ⟨d, hd⟩ := _root_.GD.N0232.N0720.N1107.d019134 m n s h
  have hcone : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
    intro θ
    exact _root_.GD.N0232.N0720.N1107.d019135 _ _ (fun ε hε hε1 => (hd ε hε hε1).1.1.1 θ)
  have href : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 d ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)]
    simp only [zero_sub, norm_neg]
    exact _root_.GD.N0232.N0720.N1107.d019136 _ _ (sq_nonneg _)
      (fun ε hε hε1 => (hd ε hε hε1).1.1.2)
  have hdP : d = _root_.GD.N0232.N0720.N1159.d014633 m n s.value :=
    _root_.GD.N0232.N0720.N1356.d015640 m n s.value d hcone href
  have hg2 : d = (_root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015130 (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 := by
    apply _root_.GD.N0232.N0720.N1356.d015643 m n s _root_.GD.N0232.N0720.N1482.d015130 d hcone
    rw [_root_.GD.N0232.N0720.N1107.d019126]
    exact _root_.GD.N0232.N0720.N1107.d019136 _ _ (_root_.GD.N0232.N0720.N1107.d019125 m n s _)
      (fun ε hε hε1 => (hd ε hε hε1).1.2)
  have hg3 : d = (_root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015131
      (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 := by
    apply _root_.GD.N0232.N0720.N1356.d015643 m n s _root_.GD.N0232.N0720.N1482.d015131 d hcone
    rw [_root_.GD.N0232.N0720.N1107.d019126]
    exact _root_.GD.N0232.N0720.N1107.d019136 _ _ (_root_.GD.N0232.N0720.N1107.d019125 m n s _)
      (fun ε hε hε1 => (hd ε hε hε1).2)
  have hfix2 : _root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015130 (_root_.GD.N0232.N0720.N1159.d014646 m n s) =
      _root_.GD.N0232.N0720.N1159.d014646 m n s := by
    apply Subtype.ext
    rw [← hg2]
    exact hdP
  have hfix3 : _root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015131
      (_root_.GD.N0232.N0720.N1159.d014646 m n s) = _root_.GD.N0232.N0720.N1159.d014646 m n s := by
    apply Subtype.ext
    rw [← hg3]
    exact hdP
  rw [_root_.GD.N0232.N0720.N1482.d015169,
    (_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015130).2 hfix2,
    (_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015131).2 hfix3, add_zero]



theorem d019138 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0) :
    _root_.GD.N0232.N0720.N1107.d019128 m n s := by
  intro ε hε _
  have hall := (_root_.GD.N0232.N0720.N1482.d015171
    (m := m) (n := n) s).1 h
  have hfix : ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
    intro g
    have := (_root_.GD.N0232.N0720.N1159.d014651 m n s g).1 (hall g)
    exact congrArg Subtype.val this
  refine ⟨_root_.GD.N0232.N0720.N1159.d014633 m n s.value, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  · exact _root_.GD.N0232.N0720.N1107.d019118 m n _ ε (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  · show _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 _ ≤ _
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n]
    simp only [zero_sub, norm_neg]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · show _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1080.d014169) _ ≤ _
    rw [← hfix _root_.GD.N0232.N0720.N1482.d015130, _root_.GD.N0232.N0720.N1107.d019126]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · show _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131 _root_.GD.N0232.N0720.N1080.d014169) _ ≤ _
    rw [← hfix _root_.GD.N0232.N0720.N1482.d015131, _root_.GD.N0232.N0720.N1107.d019126]
    exact ENNReal.ofReal_le_ofReal (by linarith)


theorem d019139 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 ↔ _root_.GD.N0232.N0720.N1107.d019128 m n s :=
  ⟨_root_.GD.N0232.N0720.N1107.d019138 m n s, _root_.GD.N0232.N0720.N1107.d019137 m n s⟩


theorem d019140 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value,
      d ∈ _root_.GD.N0232.N0720.N1107.d019120 m n _root_.GD.N0232.N0720.N1080.d014169 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) ε ∧
      d ∈ _root_.GD.N0232.N0720.N1107.d019120 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1107.d019124 m n s _root_.GD.N0232.N0720.N1482.d015130) ε ∧
      d ∈ _root_.GD.N0232.N0720.N1107.d019120 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131 _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1107.d019124 m n s _root_.GD.N0232.N0720.N1482.d015131) ε) :
    _root_.GD.N0232.N0720.N1107.d019128 m n s := by
  intro ε hε hε1
  obtain ⟨d, hd, h0, h2, h3⟩ := h ε hε hε1
  exact ⟨d, ⟨⟨⟨_root_.GD.N0232.N0720.N1107.d019118 m n _ ε hd, h0⟩, h2⟩, h3⟩⟩





theorem d019141
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1107.d019128 m n s := by
  rw [_root_.GD.N0232.N0720.N1482.d015173 (hm := hm) (hn := hn)]
  constructor
  · rintro ⟨s, hs, hz⟩
    exact ⟨s, hs, _root_.GD.N0232.N0720.N1107.d019138 m n s hz⟩
  · rintro ⟨s, hs, ha⟩
    exact ⟨s, hs, _root_.GD.N0232.N0720.N1107.d019137 m n s ha⟩




theorem d019142
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) →
          ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ _root_.GD.N0232.N0720.N1107.d019127 m n s ε = ∅ := by
  rw [_root_.GD.N0232.N0720.N1107.d019141 m n hm hn]
  constructor
  · intro hnot s hs
    by_contra hcon
    apply hnot
    refine ⟨s, hs, fun ε hε hε1 => ?_⟩
    by_contra hempty
    apply hcon
    exact ⟨ε, hε, hε1, Set.not_nonempty_iff_eq_empty.mp hempty⟩
  · rintro hall ⟨s, hs, ha⟩
    obtain ⟨ε, hε, hε1, hempty⟩ := hall s hs
    have := ha ε hε hε1
    rw [hempty] at this
    exact Set.not_nonempty_empty this



theorem d019143 (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ε : ℝ) :
    w ∈ _root_.GD.N0232.N0720.N1107.d019114 m n w ε :=
  fun _ => le_self_add

theorem d019144 (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1159.d014630 m n w = ⋂ e : {ε : ℝ // 0 < ε ∧ ε ≤ 1}, _root_.GD.N0232.N0720.N1107.d019114 m n w e.1 := by
  ext d
  constructor
  · intro hd
    exact Set.mem_iInter.2 fun e => _root_.GD.N0232.N0720.N1107.d019118 m n w e.1 hd
  · intro hd θ
    exact _root_.GD.N0232.N0720.N1107.d019135 _ _
      (fun ε hε hε1 => Set.mem_iInter.1 hd ⟨ε, hε, hε1⟩ θ)


theorem d019145 (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ε : ℝ) :
    ∃ d ∈ _root_.GD.N0232.N0720.N1107.d019114 m n w ε, ∀ e ∈ _root_.GD.N0232.N0720.N1107.d019114 m n w ε, ‖d‖ ≤ ‖e‖ :=
  _root_.GD.N0230.N0647.d000344 ⟨w, _root_.GD.N0232.N0720.N1107.d019143 m n w ε⟩ (_root_.GD.N0232.N0720.N1107.d019116 m n w ε)
    (_root_.GD.N0232.N0720.N1107.d019117 m n w ε)




theorem d019146
    (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (mδ : {ε : ℝ // 0 < ε ∧ ε ≤ 1} → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hm : ∀ e, mδ e ∈ _root_.GD.N0232.N0720.N1107.d019114 m n w e.1)
    (hmin : ∀ e, ∀ d ∈ _root_.GD.N0232.N0720.N1107.d019114 m n w e.1, ‖mδ e‖ ≤ ‖d‖) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n w‖ ^ 2 = sSup (Set.range fun e => ‖mδ e‖ ^ 2) := by
  haveI : Nonempty {ε : ℝ // 0 < ε ∧ ε ≤ 1} := ⟨⟨1, one_pos, le_rfl⟩⟩
  obtain ⟨x, hxmem, hxmin, hxsup⟩ := _root_.GD.N0230.N0647.d000346
    (fun e : {ε : ℝ // 0 < ε ∧ ε ≤ 1} => _root_.GD.N0232.N0720.N1107.d019114 m n w e.1)
    (fun e => ⟨w, _root_.GD.N0232.N0720.N1107.d019143 m n w e.1⟩)
    (fun e => _root_.GD.N0232.N0720.N1107.d019116 m n w e.1)
    (fun e => _root_.GD.N0232.N0720.N1107.d019117 m n w e.1)
    (Real.sqrt (‖w‖ ^ 2 + 1))
    (fun e _ hd => _root_.GD.N0232.N0720.N1107.d019132 m n w e.2.1.le e.2.2 hd)
    (fun e₁ e₂ => ⟨⟨min e₁.1 e₂.1, lt_min e₁.2.1 e₂.2.1, le_trans (min_le_left _ _) e₁.2.2⟩,
      _root_.GD.N0232.N0720.N1107.d019119 m n w (min_le_left _ _), _root_.GD.N0232.N0720.N1107.d019119 m n w (min_le_right _ _)⟩)
    mδ hm hmin
  rw [← _root_.GD.N0232.N0720.N1107.d019144] at hxmem hxmin
  have hxP : x = _root_.GD.N0232.N0720.N1159.d014633 m n w := by
    apply _root_.GD.N0232.N0720.N1356.d015639 m n w x hxmem
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hxmin _ (_root_.GD.N0232.N0720.N1159.d014634 m n w).1) 2
  rw [← hxP]
  exact hxsup




theorem d019147 (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) w ↔
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
        ∀ d ∈ _root_.GD.N0232.N0720.N1107.d019114 m n w δ, ‖w‖ ^ 2 - η ≤ ‖d‖ ^ 2 := by
  constructor
  · intro hterm η hη
    haveI : Nonempty {ε : ℝ // 0 < ε ∧ ε ≤ 1} := ⟨⟨1, one_pos, le_rfl⟩⟩
    choose mδ hm hmin using
      fun e : {ε : ℝ // 0 < ε ∧ ε ≤ 1} => _root_.GD.N0232.N0720.N1107.d019145 m n w e.1
    have hsup := _root_.GD.N0232.N0720.N1107.d019146 m n w mδ hm hmin
    have hPw : _root_.GD.N0232.N0720.N1159.d014633 m n w = w :=
      (_root_.GD.N0232.N0720.N1159.d014635 m n w).2 hterm
    rw [hPw] at hsup
    have hlt : ‖w‖ ^ 2 - η < sSup (Set.range fun e => ‖mδ e‖ ^ 2) := by
      rw [← hsup]; linarith
    obtain ⟨_, ⟨e, rfl⟩, he⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hlt
    refine ⟨e.1, e.2.1, e.2.2, fun d hd => ?_⟩
    have h2 : ‖mδ e‖ ^ 2 ≤ ‖d‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hmin e d hd) 2
    linarith
  · intro h
    have hle : ‖w‖ ^ 2 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n w‖ ^ 2 := by
      refine le_of_forall_pos_le_add fun η hη => ?_
      obtain ⟨δ, _, _, hδd⟩ := h η hη
      have := hδd _ (_root_.GD.N0232.N0720.N1107.d019118 m n w δ
        (_root_.GD.N0232.N0720.N1159.d014634 m n w).1)
      linarith
    have hwle : ‖w‖ ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n w‖ := by
      have h4 := Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h4
    have hwP : w = _root_.GD.N0232.N0720.N1159.d014633 m n w :=
      _root_.GD.N0232.N0720.N1048.d019044 m n w w
        (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) w) hwle
    exact (_root_.GD.N0232.N0720.N1159.d014635 m n w).1 hwP.symm




def d019148 (ρ : ℝ) (hρ : 0 < ρ) : _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨0, 1, ρ, one_pos, hρ⟩


def d019149 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1482.d015118 :=
  ⟨θ.location, Real.log θ.scale₁⟩

theorem d019150 (θ : _root_.GD.N0232.N0720.N1080.d014168) : (_root_.GD.N0232.N0720.N1107.d019149 θ).d009239 = θ.scale₁ := by
  show Real.exp (Real.log θ.scale₁) = θ.scale₁
  exact Real.exp_log θ.scale₁_pos

theorem d019151 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1107.d019149 θ)
        (_root_.GD.N0232.N0720.N1107.d019148 (θ.scale₂ / θ.scale₁) (div_pos θ.scale₂_pos θ.scale₁_pos)) = θ := by
  apply _root_.GD.N0232.N0720.N1215.d014277
  · simp [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1107.d019148, _root_.GD.N0232.N0720.N1107.d019149]
  · show (_root_.GD.N0232.N0720.N1107.d019149 θ).d009239 * 1 = θ.scale₁
    rw [_root_.GD.N0232.N0720.N1107.d019150, mul_one]
  · show (_root_.GD.N0232.N0720.N1107.d019149 θ).d009239 * (θ.scale₂ / θ.scale₁) = θ.scale₂
    rw [_root_.GD.N0232.N0720.N1107.d019150]
    field_simp
    try exact mul_div_cancel_left₀ _ θ.scale₁_pos.ne'




theorem d019152
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p q ↔
      ∀ (ρ : ℝ) (hρ : 0 < ρ),
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1107.d019148 ρ hρ) p < _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1107.d019148 ρ hρ) q := by
  constructor
  · intro h ρ hρ
    exact h _
  · intro h θ
    rw [← _root_.GD.N0232.N0720.N1107.d019151 θ, hp, hq]
    refine ENNReal.mul_lt_mul_right ?_ ENNReal.ofReal_ne_top (h _ _)
    exact (ENNReal.ofReal_pos.2 (pow_pos (_root_.GD.N0232.N0720.N1107.d019149 θ).d009240 2)).ne'


theorem d019153 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ↔
      ∀ (ρ : ℝ) (hρ : 0 < ρ),
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1107.d019148 ρ hρ) p < _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1107.d019148 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
  _root_.GD.N0232.N0720.N1107.d019152 m n p _ hp
    (_root_.GD.N0232.N0720.N1047.d018647 m n hm hn)







theorem d019154
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        (∀ (ρ : ℝ) (hρ : 0 < ρ),
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1107.d019148 ρ hρ) s.value <
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1107.d019148 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) ∧
        ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
          ∀ d ∈ _root_.GD.N0232.N0720.N1107.d019114 m n s.value δ, ‖s.value‖ ^ 2 - η ≤ ‖d‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (hm := hm) (hn := hn)]
  constructor
  · rintro ⟨s, hs, hterm⟩
    exact ⟨s,
      (_root_.GD.N0232.N0720.N1107.d019153 m n hm hn s.value s.riskCharacter).1 hs,
      (_root_.GD.N0232.N0720.N1107.d019147 m n s.value).1 hterm⟩
  · rintro ⟨s, hs, hterm⟩
    exact ⟨s,
      (_root_.GD.N0232.N0720.N1107.d019153 m n hm hn s.value s.riskCharacter).2 hs,
      (_root_.GD.N0232.N0720.N1107.d019147 m n s.value).2 hterm⟩





theorem d019155
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : _root_.GD.N0232.N0720.N1107.d019128 m n (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  rw [_root_.GD.N0232.N0720.N1107.d019141 m n hm hn]
  exact ⟨_root_.GD.N0232.N0720.N1288.d015634 m n hm hn,
    _root_.GD.N0232.N0720.N1080.d014186 m n hm hn, h⟩




theorem d019156 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) {ε : ℝ} (hε : 0 ≤ ε)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (h0 : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 d ≤
      ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε)) :
    ‖d - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ≤ Real.sqrt ε := by
  have htax := _root_.GD.N0232.N0720.N1159.d014648 m n s.value d hd
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n] at h0
  simp only [zero_sub, norm_neg] at h0
  have h1 : ‖d‖ ^ 2 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h0
  have h2 : ‖d - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ ε := by linarith
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _)] at h3





theorem d019157 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0720.N1482.d015118) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
      (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q),
      ‖_root_.GD.N0232.N0720.N1159.d014642 m n g p hp - _root_.GD.N0232.N0720.N1159.d014642 m n g q hq‖ ≤ K * ‖p - q‖)
    {ε : ℝ} (hε : 0 ≤ ε)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (h0 : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 d ≤
      ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε))
    (hg : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d ≤
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1107.d019124 m n s g + ε)) :
    ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ≤ (1 + K / g.d009239) * Real.sqrt ε := by
  set P := _root_.GD.N0232.N0720.N1159.d014633 m n s.value with hPdef
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n P :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _ (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hdF : _root_.GD.N0232.N0720.N1159.d014637 m n d := _root_.GD.N0232.N0720.N1159.d014644 m n s d hd
  have ha : 0 < g.d009239 := g.d009240

  set e := _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d hdF with hedef
  have he_mem : e ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := (_root_.GD.N0232.N0720.N1159.d014645 m n s g⁻¹ ⟨d, hd⟩).2
  have heF : _root_.GD.N0232.N0720.N1159.d014637 m n e :=
    _root_.GD.N0232.N0720.N1482.d015158 (m := m) (n := n) g⁻¹ d hdF

  have he_risk : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e ≤ ENNReal.ofReal (‖P‖ ^ 2 + ε / g.d009239 ^ 2) := by
    have h1 := _root_.GD.N0232.N0720.N1159.d014643 m n g⁻¹
      (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d hdF
    rw [_root_.GD.N0232.N0720.N1215.d014280, _root_.GD.N0232.N0720.N1146.d015204] at h1
    rw [h1]
    calc ENNReal.ofReal ((g.d009239⁻¹) ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d
        ≤ ENNReal.ofReal ((g.d009239⁻¹) ^ 2) * ENNReal.ofReal (_root_.GD.N0232.N0720.N1107.d019124 m n s g + ε) :=
          mul_le_mul_left' hg _
      _ = ENNReal.ofReal ((g.d009239⁻¹) ^ 2 * (_root_.GD.N0232.N0720.N1107.d019124 m n s g + ε)) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (‖P‖ ^ 2 + ε / g.d009239 ^ 2) := by
          congr 1
          unfold _root_.GD.N0232.N0720.N1107.d019124
          rw [← hPdef]
          have ha' : g.d009239 ≠ 0 := ha.ne'
          field_simp
  have he_close : ‖e - P‖ ≤ Real.sqrt ε / g.d009239 := by
    have h := _root_.GD.N0232.N0720.N1107.d019156 m n s (by positivity) e he_mem he_risk
    rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq ha.le] at h
    exact h

  have hback : _root_.GD.N0232.N0720.N1159.d014642 m n g e heF = d := by
    have h := _root_.GD.N0232.N0720.N1482.d015161 (m := m) (n := n) g g⁻¹ d hdF
    rw [mul_inv_cancel, _root_.GD.N0232.N0720.N1482.d015159] at h
    exact h
  have hlip := hK e P heF hP
  rw [hback] at hlip
  have hTP : (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 =
      _root_.GD.N0232.N0720.N1159.d014642 m n g P hP := rfl
  have hd_close : ‖d - P‖ ≤ Real.sqrt ε :=
    _root_.GD.N0232.N0720.N1107.d019156 m n s hε d hd h0
  rw [hTP]
  calc ‖_root_.GD.N0232.N0720.N1159.d014642 m n g P hP - P‖
      ≤ ‖_root_.GD.N0232.N0720.N1159.d014642 m n g P hP - d‖ + ‖d - P‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖d - _root_.GD.N0232.N0720.N1159.d014642 m n g P hP‖ + ‖d - P‖ := by rw [norm_sub_rev]
    _ ≤ K * ‖e - P‖ + Real.sqrt ε := add_le_add hlip hd_close
    _ ≤ K * (Real.sqrt ε / g.d009239) + Real.sqrt ε :=
        add_le_add (mul_le_mul_of_nonneg_left he_close hK0) le_rfl
    _ = (1 + K / g.d009239) * Real.sqrt ε := by field_simp; ring


def d019158 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (ε : ℝ) : Prop :=
  ∃ d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value,
    d ∈ _root_.GD.N0232.N0720.N1107.d019120 m n _root_.GD.N0232.N0720.N1080.d014169 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) ε ∧
    d ∈ _root_.GD.N0232.N0720.N1107.d019120 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1107.d019124 m n s _root_.GD.N0232.N0720.N1482.d015130) ε ∧
    d ∈ _root_.GD.N0232.N0720.N1107.d019120 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131 _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1107.d019124 m n s _root_.GD.N0232.N0720.N1482.d015131) ε


def d019159 : ℝ :=
  (1 + 2 * Real.sqrt ((2 : ℝ) ^ (m + n)) / 2) ^ 2 +
    (1 + 3 * Real.sqrt ((3 * Real.exp (1 / 16 : ℝ)) ^ (m + n)) / 3) ^ 2





theorem d019160 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    {ε : ℝ} (hε : 0 ≤ ε) (h : _root_.GD.N0232.N0720.N1107.d019158 m n s ε) :
    _root_.GD.N0232.N0720.N1477.d015749 (m := m) (n := n) s ≤ _root_.GD.N0232.N0720.N1107.d019159 m n * ε := by
  obtain ⟨d, hd, h0, h2, h3⟩ := h
  have hb2 := _root_.GD.N0232.N0720.N1107.d019157 m n s _root_.GD.N0232.N0720.N1482.d015130
    (2 * Real.sqrt ((2 : ℝ) ^ (m + n))) (by positivity)
    (fun p q hp hq => _root_.GD.N0232.N0720.N1146.d015232 m n p q hp hq) hε d hd h0 h2
  have hb3 := _root_.GD.N0232.N0720.N1107.d019157 m n s _root_.GD.N0232.N0720.N1482.d015131
    (3 * Real.sqrt ((3 * Real.exp (1 / 16 : ℝ)) ^ (m + n))) (by positivity)
    (fun p q hp hq => _root_.GD.N0232.N0720.N1146.d015233 m n p q hp hq)
    hε d hd h0 h3
  rw [_root_.GD.N0232.N0720.N1146.d015219] at hb2
  rw [_root_.GD.N0232.N0720.N1146.d015220] at hb3
  have hsq2 := pow_le_pow_left₀ (norm_nonneg _) hb2 2
  have hsq3 := pow_le_pow_left₀ (norm_nonneg _) hb3 2
  rw [mul_pow, Real.sq_sqrt hε] at hsq2 hsq3
  unfold _root_.GD.N0232.N0720.N1477.d015749 _root_.GD.N0232.N0720.N1477.d015744 _root_.GD.N0232.N0720.N1107.d019159
  linarith


theorem d019161 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hlt : _root_.GD.N0232.N0720.N1107.d019159 m n * ε < _root_.GD.N0232.N0720.N1477.d015749 (m := m) (n := n) s) :
    ¬ _root_.GD.N0232.N0720.N1107.d019158 m n s ε := fun h =>
  absurd (_root_.GD.N0232.N0720.N1107.d019160 m n s hε h) (not_le.mpr hlt)

end

end N1107
end N0720
end N0232
end GD
