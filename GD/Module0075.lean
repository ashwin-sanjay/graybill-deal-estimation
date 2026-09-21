import GD.Module0066


























namespace GD
namespace N0230
namespace N0683

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630

variable {Θ Rule : Type*}


def d000933
    (risk : Θ → Rule → ℝ) (d e : Rule) : Prop :=
  ∀ θ, risk θ d = risk θ e


theorem d000934
    (risk : Θ → Rule → ℝ) (d : Rule) :
    _root_.GD.N0230.N0683.d000933 risk d d := by
  intro θ
  rfl


theorem d000935
    (risk : Θ → Rule → ℝ) {d e : Rule}
    (h : _root_.GD.N0230.N0683.d000933 risk d e) :
    _root_.GD.N0230.N0683.d000933 risk e d := by
  intro θ
  exact (h θ).symm


theorem d000936
    (risk : Θ → Rule → ℝ) {d e f : Rule}
    (hde : _root_.GD.N0230.N0683.d000933 risk d e)
    (hef : _root_.GD.N0230.N0683.d000933 risk e f) :
    _root_.GD.N0230.N0683.d000933 risk d f := by
  intro θ
  exact (hde θ).trans (hef θ)


theorem d000937
    (risk : Θ → Rule → ℝ) (d e : Rule) :
    _root_.GD.N0230.N0683.d000933 risk d e ↔
      _root_.GD.N0230.N0556.d000028 risk d e ∧
        _root_.GD.N0230.N0556.d000028 risk e d := by
  constructor
  · intro h
    exact
      ⟨fun θ => (h θ).le,
        fun θ => (h θ).ge⟩
  · rintro ⟨hde, hed⟩ θ
    exact le_antisymm (hde θ) (hed θ)


def d000938
    (risk : Θ → Rule → ℝ) : Setoid Rule where
  r := _root_.GD.N0230.N0683.d000933 risk
  iseqv :=
    ⟨_root_.GD.N0230.N0683.d000934 risk,
      fun h => _root_.GD.N0230.N0683.d000935 risk h,
      fun h₁ h₂ => _root_.GD.N0230.N0683.d000936 risk h₁ h₂⟩


def d000939
    (risk : Θ → Rule → ℝ) : Type _ :=
  Quotient (_root_.GD.N0230.N0683.d000938 risk)


def d000940
    (risk : Θ → Rule → ℝ) (d : Rule) :
    _root_.GD.N0230.N0683.d000939 risk :=
  Quotient.mk (_root_.GD.N0230.N0683.d000938 risk) d


theorem d000941
    (risk : Θ → Rule → ℝ) (d e : Rule) :
    _root_.GD.N0230.N0683.d000940 risk d = _root_.GD.N0230.N0683.d000940 risk e ↔
      _root_.GD.N0230.N0683.d000933 risk d e := by
  exact
    Quotient.eq
      (r := _root_.GD.N0230.N0683.d000938 risk)
      (x := d) (y := e)







def d000942
    (risk : Θ → Rule → ℝ)
    (θ : Θ) :
    _root_.GD.N0230.N0683.d000939 risk → ℝ :=
  Quotient.lift
    (fun d => risk θ d)
    (by
      intro d e hde
      exact hde θ)


theorem d000943
    (risk : Θ → Rule → ℝ)
    (θ : Θ) (d : Rule) :
    _root_.GD.N0230.N0683.d000942 risk θ (_root_.GD.N0230.N0683.d000940 risk d) = risk θ d :=
  rfl





def d000944
    (risk : Θ → Rule → ℝ) (d : Rule) : Prop :=
  ∀ e, _root_.GD.N0230.N0556.d000028 risk e d →
    _root_.GD.N0230.N0683.d000933 risk e d








theorem d000945
    (risk : Θ → Rule → ℝ) (d : Rule) :
    _root_.GD.N0230.N0683.d000944 risk d ↔
      _root_.GD.N0230.N0630.d000786
        (_root_.GD.N0230.N0683.d000942 risk) (_root_.GD.N0230.N0683.d000940 risk d) := by
  constructor
  · intro hterminal q hqd
    induction q using Quotient.inductionOn with
    | _ e =>
        apply
          (_root_.GD.N0230.N0683.d000941 risk e d).2
        apply hterminal e
        intro θ
        have hqθ := hqd θ
        change risk θ e ≤ risk θ d at hqθ
        exact hqθ
  · intro hterminal e hed
    apply
      (_root_.GD.N0230.N0683.d000941 risk e d).1
    apply hterminal (_root_.GD.N0230.N0683.d000940 risk e)
    intro θ
    simpa only [_root_.GD.N0230.N0683.d000943] using hed θ





theorem d000946
    (risk : Θ → Rule → ℝ) (d : Rule) :
    _root_.GD.N0230.N0556.d000031 risk d ↔ _root_.GD.N0230.N0683.d000944 risk d := by
  constructor
  · intro hadmissible e heWeak θ
    apply le_antisymm (heWeak θ)
    by_contra hnot
    have hstrict : risk θ e < risk θ d :=
      lt_of_not_ge hnot
    exact hadmissible
      ⟨e, heWeak, ⟨θ, hstrict⟩⟩
  · intro hterminal
    rintro ⟨e, heWeak, ⟨θ, hstrict⟩⟩
    have heq : risk θ e = risk θ d :=
      hterminal e heWeak θ
    exact (ne_of_lt hstrict) heq









theorem d000947
    (risk : Θ → Rule → ℝ) (d : Rule) :
    _root_.GD.N0230.N0556.d000031 risk d ↔
      _root_.GD.N0230.N0630.d000786
        (_root_.GD.N0230.N0683.d000942 risk) (_root_.GD.N0230.N0683.d000940 risk d) := by
  rw [_root_.GD.N0230.N0683.d000946,
    _root_.GD.N0230.N0683.d000945]





def d000948
    (risk : Θ → Rule → ℝ) (d : Rule) : Prop :=
  ∀ e, _root_.GD.N0230.N0683.d000933 risk e d → e = d


theorem d000949
    (risk : Θ → Rule → ℝ) {d : Rule}
    (h : _root_.GD.N0230.N0630.d000786 risk d) :
    _root_.GD.N0230.N0683.d000944 risk d := by
  intro e heWeak
  rw [h e heWeak]
  exact _root_.GD.N0230.N0683.d000934 risk d


theorem d000950
    (risk : Θ → Rule → ℝ) {d : Rule}
    (h : _root_.GD.N0230.N0630.d000786 risk d) :
    _root_.GD.N0230.N0683.d000948 risk d := by
  intro e heq
  exact h e ((_root_.GD.N0230.N0683.d000937 risk e d).mp heq).1





theorem d000951
    (risk : Θ → Rule → ℝ) {d : Rule}
    (hterminal : _root_.GD.N0230.N0683.d000944 risk d)
    (hseparates : _root_.GD.N0230.N0683.d000948 risk d) :
    _root_.GD.N0230.N0630.d000786 risk d := by
  intro e heWeak
  exact hseparates e (hterminal e heWeak)





theorem d000952
    (risk : Θ → Rule → ℝ) (d : Rule) :
    _root_.GD.N0230.N0630.d000786 risk d ↔
      _root_.GD.N0230.N0683.d000944 risk d ∧
        _root_.GD.N0230.N0683.d000948 risk d := by
  constructor
  · intro h
    exact
      ⟨_root_.GD.N0230.N0683.d000949 risk h,
        _root_.GD.N0230.N0683.d000950 risk h⟩
  · rintro ⟨hterminal, hseparates⟩
    exact
      _root_.GD.N0230.N0683.d000951
        risk hterminal hseparates



theorem d000953
    (risk : Θ → Rule → ℝ) (d : Rule) :
    _root_.GD.N0230.N0630.d000786 risk d ↔
      _root_.GD.N0230.N0556.d000031 risk d ∧
        _root_.GD.N0230.N0683.d000948 risk d := by
  rw [_root_.GD.N0230.N0683.d000952,
    ← _root_.GD.N0230.N0683.d000946]




def d000954 (_ : Unit) (_ : Bool) : ℝ := 0


theorem d000955 (d e : Bool) :
    _root_.GD.N0230.N0683.d000933 _root_.GD.N0230.N0683.d000954 d e := by
  intro θ
  rfl


theorem d000956 :
    _root_.GD.N0230.N0683.d000940 _root_.GD.N0230.N0683.d000954 false = _root_.GD.N0230.N0683.d000940 _root_.GD.N0230.N0683.d000954 true := by
  exact
    (_root_.GD.N0230.N0683.d000941 _root_.GD.N0230.N0683.d000954 false true).2
      (_root_.GD.N0230.N0683.d000955 false true)


theorem d000957 (d : Bool) :
    _root_.GD.N0230.N0683.d000944 _root_.GD.N0230.N0683.d000954 d := by
  intro e he
  exact _root_.GD.N0230.N0683.d000955 e d


theorem d000958 (d : Bool) :
    _root_.GD.N0230.N0556.d000031 _root_.GD.N0230.N0683.d000954 d :=
  (_root_.GD.N0230.N0683.d000946 _root_.GD.N0230.N0683.d000954 d).2
    (_root_.GD.N0230.N0683.d000957 d)


theorem d000959 (d : Bool) :
    ¬ _root_.GD.N0230.N0683.d000948 _root_.GD.N0230.N0683.d000954 d := by
  cases d with
  | false =>
      intro h
      have heq : true = false :=
        h true (_root_.GD.N0230.N0683.d000955 true false)
      simp at heq
  | true =>
      intro h
      have heq : false = true :=
        h false (_root_.GD.N0230.N0683.d000955 false true)
      simp at heq





theorem d000960 :
    ∀ d : Bool, ¬ _root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0683.d000954 d := by
  intro d hstrong
  exact
    _root_.GD.N0230.N0683.d000959 d
      (_root_.GD.N0230.N0683.d000950 _root_.GD.N0230.N0683.d000954 hstrong)

end N0683
end N0230
end GD
