import GD.Module0242











set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal

namespace GD.N0106.N0428.N0769
noncomputable section

open _root_.GD.N0230.N0611

variable {Θ Ξ D : Type*}

def d006066 (risk : Θ → D → ℝ≥0∞) (scale : Θ → ℝ≥0∞) : Θ → D → ℝ≥0∞ :=
  fun θ d => scale θ * risk θ d

def d006067 (risk : Θ → D → ℝ≥0∞) (gauge : Θ → ℝ≥0∞) : Θ → D → ℝ≥0∞ :=
  fun θ d => risk θ d / gauge θ


def d006068 (risk : Θ → D → ℝ≥0∞) (S : Set D) : Set D :=
  {d | d ∈ S ∧ ∀ θ, risk θ d ≠ ⊤}

theorem d006069 (risk : Θ → D → ℝ≥0∞) (scale : Θ → ℝ≥0∞)
    (hzero : ∀ θ, scale θ ≠ 0) (hfinite : ∀ θ, scale θ ≠ ⊤)
    (θ : Θ) (e d : D) :
    _root_.GD.N0106.N0428.N0769.d006066 risk scale θ e ≤ _root_.GD.N0106.N0428.N0769.d006066 risk scale θ d ↔ risk θ e ≤ risk θ d :=
  ENNReal.mul_le_mul_iff_right (hzero θ) (hfinite θ)

theorem d006070 (risk : Θ → D → ℝ≥0∞) (scale : Θ → ℝ≥0∞)
    (hzero : ∀ θ, scale θ ≠ 0) (hfinite : ∀ θ, scale θ ≠ ⊤)
    (θ : Θ) (e d : D) :
    _root_.GD.N0106.N0428.N0769.d006066 risk scale θ e < _root_.GD.N0106.N0428.N0769.d006066 risk scale θ d ↔ risk θ e < risk θ d :=
  ENNReal.mul_lt_mul_iff_right (hzero θ) (hfinite θ)

theorem d006071 (risk : Θ → D → ℝ≥0∞) (scale : Θ → ℝ≥0∞)
    (hzero : ∀ θ, scale θ ≠ 0) (hfinite : ∀ θ, scale θ ≠ ⊤) (e d : D) :
    (∀ θ, _root_.GD.N0106.N0428.N0769.d006066 risk scale θ e ≤ _root_.GD.N0106.N0428.N0769.d006066 risk scale θ d) ↔
      ∀ θ, risk θ e ≤ risk θ d := by
  simp only [_root_.GD.N0106.N0428.N0769.d006069 risk scale hzero hfinite]

theorem d006072 (risk : Θ → D → ℝ≥0∞) (scale : Θ → ℝ≥0∞)
    (hzero : ∀ θ, scale θ ≠ 0) (hfinite : ∀ θ, scale θ ≠ ⊤) (e d : D) :
    ((∀ θ, _root_.GD.N0106.N0428.N0769.d006066 risk scale θ e ≤ _root_.GD.N0106.N0428.N0769.d006066 risk scale θ d) ∧
      ∃ θ, _root_.GD.N0106.N0428.N0769.d006066 risk scale θ e < _root_.GD.N0106.N0428.N0769.d006066 risk scale θ d) ↔
      (∀ θ, risk θ e ≤ risk θ d) ∧ ∃ θ, risk θ e < risk θ d := by
  simp only [_root_.GD.N0106.N0428.N0769.d006071 risk scale hzero hfinite,
    _root_.GD.N0106.N0428.N0769.d006070 risk scale hzero hfinite]

theorem d006073
    (risk : Θ → D → ℝ≥0∞) (scale : Θ → ℝ≥0∞)
    (hzero : ∀ θ, scale θ ≠ 0) (hfinite : ∀ θ, scale θ ≠ ⊤) (e d : D) :
    (∀ θ, _root_.GD.N0106.N0428.N0769.d006066 risk scale θ e < _root_.GD.N0106.N0428.N0769.d006066 risk scale θ d) ↔
      ∀ θ, risk θ e < risk θ d := by
  simp only [_root_.GD.N0106.N0428.N0769.d006070 risk scale hzero hfinite]


theorem d006074 (risk : Θ → D → ℝ≥0∞) (scale : Θ → ℝ≥0∞)
    (hzero : ∀ θ, scale θ ≠ 0) (hfinite : ∀ θ, scale θ ≠ ⊤)
    (S : Set D) (d : D) :
    (¬ ∃ e ∈ S, (∀ θ, _root_.GD.N0106.N0428.N0769.d006066 risk scale θ e ≤ _root_.GD.N0106.N0428.N0769.d006066 risk scale θ d) ∧
      ∃ θ, _root_.GD.N0106.N0428.N0769.d006066 risk scale θ e < _root_.GD.N0106.N0428.N0769.d006066 risk scale θ d) ↔
      ¬ ∃ e ∈ S, (∀ θ, risk θ e ≤ risk θ d) ∧ ∃ θ, risk θ e < risk θ d := by
  simp only [_root_.GD.N0106.N0428.N0769.d006072 risk scale hzero hfinite]


theorem d006075 (risk : Θ → D → ℝ≥0∞) (scale : Θ → ℝ≥0∞)
    (hzero : ∀ θ, scale θ ≠ 0) (hfinite : ∀ θ, scale θ ≠ ⊤)
    (S : Set D) (same : D → D → Prop) (d : D) :
    (∀ e ∈ S, (∀ θ, _root_.GD.N0106.N0428.N0769.d006066 risk scale θ e ≤ _root_.GD.N0106.N0428.N0769.d006066 risk scale θ d) → same e d) ↔
      ∀ e ∈ S, (∀ θ, risk θ e ≤ risk θ d) → same e d := by
  simp only [_root_.GD.N0106.N0428.N0769.d006071 risk scale hzero hfinite]


theorem d006076 (scale : Θ → ℝ) (hscale : ∀ θ, 0 < scale θ) :
    (∀ θ, ENNReal.ofReal (scale θ) ≠ 0) ∧
      ∀ θ, ENNReal.ofReal (scale θ) ≠ ⊤ :=
  ⟨fun θ => (ENNReal.ofReal_pos.mpr (hscale θ)).ne', fun _ => ENNReal.ofReal_ne_top⟩

theorem d006077 (risk : Θ → D → ℝ≥0∞) (scale : Θ → ℝ)
    (hscale : ∀ θ, 0 < scale θ) (S : Set D) (same : D → D → Prop) (d : D) :
    (∀ e ∈ S, (∀ θ, ENNReal.ofReal (scale θ) * risk θ e ≤
      ENNReal.ofReal (scale θ) * risk θ d) → same e d) ↔
      ∀ e ∈ S, (∀ θ, risk θ e ≤ risk θ d) → same e d :=
  _root_.GD.N0106.N0428.N0769.d006075 risk (fun θ => ENNReal.ofReal (scale θ))
    (_root_.GD.N0106.N0428.N0769.d006076 scale hscale).1 (_root_.GD.N0106.N0428.N0769.d006076 scale hscale).2 S same d


theorem d006078 (risk : Θ → D → ℝ≥0∞) (inclusion : Ξ → Θ)
    {e d : D} (hweak : ∀ θ, risk θ e ≤ risk θ d) :
    ∀ ξ, risk (inclusion ξ) e ≤ risk (inclusion ξ) d :=
  fun ξ => hweak (inclusion ξ)

theorem d006079
    (risk : Θ → D → ℝ≥0∞) (inclusion : Ξ → Θ)
    {e d : D} (hweak : ∀ θ, risk θ e ≤ risk θ d) :
    ((∀ ξ, risk (inclusion ξ) e ≤ risk (inclusion ξ) d) ∧
      ∃ ξ, risk (inclusion ξ) e < risk (inclusion ξ) d) ↔
      ∃ ξ, risk (inclusion ξ) e < risk (inclusion ξ) d :=
  ⟨fun h => h.2, fun h => ⟨_root_.GD.N0106.N0428.N0769.d006078 risk inclusion hweak, h⟩⟩

theorem d006080 (risk : Θ → D → ℝ≥0∞) (gauge : Θ → ℝ≥0∞)
    (hzero : ∀ θ, gauge θ ≠ 0) (hfinite : ∀ θ, gauge θ ≠ ⊤)
    (θ : Θ) (d : D) (C : ℝ≥0∞) :
    _root_.GD.N0106.N0428.N0769.d006067 risk gauge θ d ≤ C ↔ risk θ d ≤ C * gauge θ :=
  ENNReal.div_le_iff (hzero θ) (hfinite θ)

theorem d006081 (risk : Θ → D → ℝ≥0∞) (gauge : Θ → ℝ≥0∞)
    (hzero : ∀ θ, gauge θ ≠ 0) (hfinite : ∀ θ, gauge θ ≠ ⊤)
    (θ : Θ) (d : D) :
    _root_.GD.N0106.N0428.N0769.d006067 risk gauge θ d = ⊤ ↔ risk θ d = ⊤ := by
  constructor
  · intro h
    by_contra hrisk
    exact (ENNReal.div_ne_top hrisk (hzero θ)) h
  · intro h
    change risk θ d / gauge θ = ⊤
    rw [h, ENNReal.top_div_of_ne_top (hfinite θ)]

theorem d006082 (risk : Θ → D → ℝ≥0∞) (gauge : Θ → ℝ≥0∞)
    (hzero : ∀ θ, gauge θ ≠ 0) (hfinite : ∀ θ, gauge θ ≠ ⊤)
    (θ : Θ) (d : D) :
    _root_.GD.N0106.N0428.N0769.d006067 risk gauge θ d ≠ ⊤ ↔ risk θ d ≠ ⊤ :=
  not_congr (_root_.GD.N0106.N0428.N0769.d006081 risk gauge hzero hfinite θ d)


theorem d006083
    (risk : Θ → D → ℝ≥0∞) (gauge : Θ → ℝ≥0∞)
    (hzero : ∀ θ, gauge θ ≠ 0) (hfinite : ∀ θ, gauge θ ≠ ⊤)
    (d : D) (θ : Θ) (htop : risk θ d = ⊤) :
    _root_.GD.N0230.N0611.d003516 (_root_.GD.N0106.N0428.N0769.d006067 risk gauge) d = ⊤ := by
  apply top_unique
  calc
    ⊤ = _root_.GD.N0106.N0428.N0769.d006067 risk gauge θ d :=
      ((_root_.GD.N0106.N0428.N0769.d006081 risk gauge hzero hfinite θ d).2 htop).symm
    _ ≤ _root_.GD.N0230.N0611.d003516 (_root_.GD.N0106.N0428.N0769.d006067 risk gauge) d :=
      le_iSup (fun η => _root_.GD.N0106.N0428.N0769.d006067 risk gauge η d) θ


theorem d006084
    (risk : Θ → D → ℝ≥0∞) (gauge : Θ → ℝ≥0∞)
    (hzero : ∀ θ, gauge θ ≠ 0) (hfinite : ∀ θ, gauge θ ≠ ⊤)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (d : D)
    (hbound : ∀ θ, _root_.GD.N0106.N0428.N0769.d006067 risk gauge θ d ≤ C) :
    ∀ θ, risk θ d ≠ ⊤ := by
  intro θ
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (hfinite θ))
    ((_root_.GD.N0106.N0428.N0769.d006080 risk gauge hzero hfinite θ d C).1 (hbound θ))


theorem d006085
    (risk : Θ → D → ℝ≥0∞) (gauge : Θ → ℝ≥0∞)
    (hzero : ∀ θ, gauge θ ≠ 0) (hfinite : ∀ θ, gauge θ ≠ ⊤) (S : Set D) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0106.N0428.N0769.d006067 risk gauge) S =
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0106.N0428.N0769.d006067 risk gauge) (_root_.GD.N0106.N0428.N0769.d006068 risk S) := by
  apply _root_.GD.N0230.N0611.d003524 (_root_.GD.N0106.N0428.N0769.d006067 risk gauge) S (_root_.GD.N0106.N0428.N0769.d006068 risk S)
    (fun _ hd => hd.1)
  intro C hC hcap
  obtain ⟨d, hd, hbound⟩ := hcap
  exact ⟨d, ⟨hd, _root_.GD.N0106.N0428.N0769.d006084 risk gauge hzero hfinite C hC.ne d hbound⟩,
    hbound⟩


theorem d006086 (risk : Θ → D → ℝ≥0∞) (S : Set D)
    {baseline d : D} (hd : d ∈ S) (hbaseline : ∀ θ, risk θ baseline ≠ ⊤)
    (hdom : ∀ θ, risk θ d ≤ risk θ baseline) :
    d ∈ _root_.GD.N0106.N0428.N0769.d006068 risk S :=
  ⟨hd, fun θ => ne_top_of_le_ne_top (hbaseline θ) (hdom θ)⟩

end
end GD.N0106.N0428.N0769

#print axioms _root_.GD.N0106.N0428.N0769.d006071
#print axioms _root_.GD.N0106.N0428.N0769.d006072
#print axioms _root_.GD.N0106.N0428.N0769.d006073
#print axioms _root_.GD.N0106.N0428.N0769.d006074
#print axioms _root_.GD.N0106.N0428.N0769.d006075
#print axioms _root_.GD.N0106.N0428.N0769.d006077
#print axioms _root_.GD.N0106.N0428.N0769.d006079
#print axioms _root_.GD.N0106.N0428.N0769.d006083
#print axioms _root_.GD.N0106.N0428.N0769.d006085
#print axioms _root_.GD.N0106.N0428.N0769.d006086
