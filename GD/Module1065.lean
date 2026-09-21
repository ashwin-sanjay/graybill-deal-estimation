import GD.Module1064
































open Filter

namespace GD
namespace N0232
namespace N0720
namespace N1130

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1461




structure d017074 where
  width : ℕ
  packet : Fin width → _root_.GD.N0232.N0720.N1080.d014168
  weight : Fin width → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i



def d017075
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
    c.packet c.weight c.weight_nonneg


def d017076
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  Metric.infDist (_root_.GD.N0232.N0720.N1130.d017075 m n c)
    (_root_.GD.N0232.N0720.N1159.d014630 m n s.value)




def d017077
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  max (‖_root_.GD.N0232.N0720.N1130.d017075 m n c‖ ^ 2 -
    _root_.GD.N0232.N0720.N1126.d016432 s c.packet c.weight) 0


def d017078
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  ‖_root_.GD.N0232.N0720.N1146.d015228 m n (_root_.GD.N0232.N0720.N1130.d017075 m n c) -
    _root_.GD.N0232.N0720.N1130.d017075 m n c‖


def d017079
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  ‖_root_.GD.N0232.N0720.N1146.d015229 m n
      (_root_.GD.N0232.N0720.N1130.d017075 m n c) - _root_.GD.N0232.N0720.N1130.d017075 m n c‖



def d017080
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  _root_.GD.N0232.N0720.N1130.d017076 m n s c +
    _root_.GD.N0232.N0720.N1130.d017077 m n s c +
    _root_.GD.N0232.N0720.N1130.d017078 m n c +
    _root_.GD.N0232.N0720.N1130.d017079 m n c

theorem d017081
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1130.d017076 m n s c :=
  Metric.infDist_nonneg

theorem d017082
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1130.d017077 m n s c :=
  le_max_right _ _

theorem d017083
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1130.d017078 m n c :=
  norm_nonneg _

theorem d017084
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1130.d017079 m n c :=
  norm_nonneg _


theorem d017085
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1130.d017080 m n s c := by
  unfold _root_.GD.N0232.N0720.N1130.d017080
  linarith [_root_.GD.N0232.N0720.N1130.d017081 m n s c,
    _root_.GD.N0232.N0720.N1130.d017082 m n s c,
    _root_.GD.N0232.N0720.N1130.d017083 m n c,
    _root_.GD.N0232.N0720.N1130.d017084 m n c]

theorem d017086
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1130.d017076 m n s c ≤ _root_.GD.N0232.N0720.N1130.d017080 m n s c := by
  unfold _root_.GD.N0232.N0720.N1130.d017080
  linarith [_root_.GD.N0232.N0720.N1130.d017082 m n s c,
    _root_.GD.N0232.N0720.N1130.d017083 m n c,
    _root_.GD.N0232.N0720.N1130.d017084 m n c]

theorem d017087
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1130.d017077 m n s c ≤ _root_.GD.N0232.N0720.N1130.d017080 m n s c := by
  unfold _root_.GD.N0232.N0720.N1130.d017080
  linarith [_root_.GD.N0232.N0720.N1130.d017081 m n s c,
    _root_.GD.N0232.N0720.N1130.d017083 m n c,
    _root_.GD.N0232.N0720.N1130.d017084 m n c]

theorem d017088
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1130.d017078 m n c ≤ _root_.GD.N0232.N0720.N1130.d017080 m n s c := by
  unfold _root_.GD.N0232.N0720.N1130.d017080
  linarith [_root_.GD.N0232.N0720.N1130.d017081 m n s c,
    _root_.GD.N0232.N0720.N1130.d017082 m n s c,
    _root_.GD.N0232.N0720.N1130.d017084 m n c]

theorem d017089
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1130.d017079 m n c ≤
      _root_.GD.N0232.N0720.N1130.d017080 m n s c := by
  unfold _root_.GD.N0232.N0720.N1130.d017080
  linarith [_root_.GD.N0232.N0720.N1130.d017081 m n s c,
    _root_.GD.N0232.N0720.N1130.d017082 m n s c,
    _root_.GD.N0232.N0720.N1130.d017083 m n c]






theorem d017090
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hdefect : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017080 m n s (candidate j))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)
  let epsilon : ℕ → ℝ := fun j ↦
    _root_.GD.N0232.N0720.N1130.d017077 m n s (candidate j)
  have houter : Tendsto
      (fun j ↦ Metric.infDist (r j) (_root_.GD.N0232.N0720.N1159.d014630 m n s.value))
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun _ ↦ Metric.infDist_nonneg)
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017086 m n s (candidate j))
      hdefect
  have hepsilon : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017077 m n s (candidate j))
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017082 m n s (candidate j))
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017087 m n s (candidate j))
      hdefect
  have htwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun _ ↦ norm_nonneg _)
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017088 m n s (candidate j))
      hdefect
  have hthree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun _ ↦ norm_nonneg _)
      (fun j ↦
        _root_.GD.N0232.N0720.N1130.d017089 m n s (candidate j))
      hdefect
  apply _root_.GD.N0232.N0720.N1461.d015690
    m n hm hn s hstrict r epsilon houter
  · intro j
    have hreserve :=
      _root_.GD.N0232.N0720.N1126.d016437
        s (candidate j).packet (candidate j).weight
          (candidate j).weight_nonneg
    have hdistanceNonneg :
        0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value - r j‖ ^ 2 :=
      sq_nonneg _
    have hgapLe :
        ‖r j‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s
            (candidate j).packet (candidate j).weight ≤ epsilon j := by
      dsimp only [epsilon, _root_.GD.N0232.N0720.N1130.d017077]
      exact le_max_left _ _
    dsimp only [r, _root_.GD.N0232.N0720.N1130.d017075] at hreserve hdistanceNonneg hgapLe ⊢
    linarith
  · exact hepsilon
  · exact htwo
  · exact hthree





def d017091
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ c : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1130.d017080 m n s c < epsilon



theorem d017092
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hsmall : _root_.GD.N0232.N0720.N1130.d017091 m n s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  classical
  have hchoose : ∀ j : ℕ, ∃ c : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1130.d017080 m n s c < 1 / ((j : ℝ) + 1) := by
    intro j
    exact hsmall (1 / ((j : ℝ) + 1)) (by positivity)
  choose candidate hcandidate using hchoose
  apply _root_.GD.N0232.N0720.N1130.d017090
    m n hm hn s hstrict candidate
  exact squeeze_zero
    (fun j ↦ _root_.GD.N0232.N0720.N1130.d017085 m n s (candidate j))
    (fun j ↦ (hcandidate j).le)
    tendsto_one_div_add_atTop_nhds_zero_nat





theorem d017093
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ c : _root_.GD.N0232.N0720.N1130.d017074,
        eta ≤ _root_.GD.N0232.N0720.N1130.d017080 m n s c := by
  by_contra hfloor
  have hsmall : _root_.GD.N0232.N0720.N1130.d017091 m n s := by
    intro epsilon hepsilon
    by_contra hnone
    have hall : ∀ c : _root_.GD.N0232.N0720.N1130.d017074,
        epsilon ≤ _root_.GD.N0232.N0720.N1130.d017080 m n s c := by
      intro c
      exact le_of_not_gt (fun hlt ↦ hnone ⟨c, hlt⟩)
    exact hfloor ⟨epsilon, hepsilon, hall⟩
  exact hno
    (_root_.GD.N0232.N0720.N1130.d017092
      m n hm hn s hstrict hsmall)

end

end N1130
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1130.d017090
#print axioms _root_.GD.N0232.N0720.N1130.d017092
#print axioms _root_.GD.N0232.N0720.N1130.d017093
