import GD.Module0232











open Set
open scoped ENNReal

namespace GD.N0230.N0611

noncomputable section

variable {Θ D : Type*}


def d003516 (risk : Θ → D → ℝ≥0∞) (d : D) : ℝ≥0∞ :=
  ⨆ θ, risk θ d


def d003517 (risk : Θ → D → ℝ≥0∞) (S : Set D) : ℝ≥0∞ :=
  ⨅ d ∈ S, _root_.GD.N0230.N0611.d003516 risk d


def d003518 (risk : Θ → D → ℝ≥0∞) (S : Set D) (c : ℝ≥0∞) : Set D :=
  {d | d ∈ S ∧ ∀ θ, risk θ d ≤ c}

theorem d003519 (risk : Θ → D → ℝ≥0∞) (d : D) (c : ℝ≥0∞) :
    _root_.GD.N0230.N0611.d003516 risk d ≤ c ↔ ∀ θ, risk θ d ≤ c :=
  iSup_le_iff

theorem d003520 (risk : Θ → D → ℝ≥0∞)
    {S : Set D} {d : D} (hd : d ∈ S) :
    _root_.GD.N0230.N0611.d003517 risk S ≤ _root_.GD.N0230.N0611.d003516 risk d :=
  iInf_le_of_le d (iInf_le_of_le hd le_rfl)

theorem d003521 (risk : Θ → D → ℝ≥0∞)
    {S T : Set D} (hST : S ⊆ T) :
    _root_.GD.N0230.N0611.d003517 risk T ≤ _root_.GD.N0230.N0611.d003517 risk S := by
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact _root_.GD.N0230.N0611.d003520 risk (hST hd)


theorem d003522 (risk : Θ → D → ℝ≥0∞) (S T : Set D) :
    _root_.GD.N0230.N0611.d003517 risk T ≤ _root_.GD.N0230.N0611.d003517 risk S ↔
      ∀ d ∈ S, _root_.GD.N0230.N0611.d003517 risk T ≤ _root_.GD.N0230.N0611.d003516 risk d := by
  constructor
  · intro h d hd
    exact h.trans (_root_.GD.N0230.N0611.d003520 risk hd)
  · intro h
    exact le_iInf fun d => le_iInf fun hd => h d hd




theorem d003523
    (risk : Θ → D → ℝ≥0∞) (S T : Set D)
    (hcap : ∀ c : ℝ≥0∞, c < ⊤ →
      (_root_.GD.N0230.N0611.d003518 risk S c).Nonempty → (_root_.GD.N0230.N0611.d003518 risk T c).Nonempty)
    {d : D} (hd : d ∈ S) :
    _root_.GD.N0230.N0611.d003517 risk T ≤ _root_.GD.N0230.N0611.d003516 risk d := by
  by_cases htop : _root_.GD.N0230.N0611.d003516 risk d = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨e, heT, hecap⟩ := hcap (_root_.GD.N0230.N0611.d003516 risk d) (lt_top_iff_ne_top.mpr htop)
      ⟨d, hd, fun θ => le_iSup (fun θ => risk θ d) θ⟩
    exact (_root_.GD.N0230.N0611.d003520 risk heT).trans
      ((_root_.GD.N0230.N0611.d003519 risk e _).2 hecap)



theorem d003524
    (risk : Θ → D → ℝ≥0∞) (S T : Set D) (hTS : T ⊆ S)
    (hcap : ∀ c : ℝ≥0∞, c < ⊤ →
      (_root_.GD.N0230.N0611.d003518 risk S c).Nonempty → (_root_.GD.N0230.N0611.d003518 risk T c).Nonempty) :
    _root_.GD.N0230.N0611.d003517 risk S = _root_.GD.N0230.N0611.d003517 risk T := by
  apply le_antisymm (_root_.GD.N0230.N0611.d003521 risk hTS)
  exact (_root_.GD.N0230.N0611.d003522 risk S T).2
    (fun _ hd => _root_.GD.N0230.N0611.d003523 risk S T hcap hd)



theorem d003525
    (risk : Θ → D → ℝ≥0∞) (S T : Set D) (hTS : T ⊆ S)
    (hcap : ∀ c : ℝ, 0 ≤ c →
      (_root_.GD.N0230.N0611.d003518 risk S (ENNReal.ofReal c)).Nonempty →
        (_root_.GD.N0230.N0611.d003518 risk T (ENNReal.ofReal c)).Nonempty) :
    _root_.GD.N0230.N0611.d003517 risk S = _root_.GD.N0230.N0611.d003517 risk T := by
  apply _root_.GD.N0230.N0611.d003524 risk S T hTS
  intro c hc hS
  have hfinite : c ≠ ⊤ := ne_of_lt hc
  have hreal : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hfinite
  rw [← hreal] at hS ⊢
  exact hcap c.toReal ENNReal.toReal_nonneg hS

end

end GD.N0230.N0611

#print axioms _root_.GD.N0230.N0611.d003524
#print axioms _root_.GD.N0230.N0611.d003525
