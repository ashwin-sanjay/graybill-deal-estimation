import GD.Module0831










open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0107

noncomputable section

open _root_.GD.N0137


def d012732
    (m n : ℕ) (μ e : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0107.d009084 ω.2 + e * _root_.GD.N0107.d009090 m n ω - μ


def d012733
    (m n : ℕ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0107.d009084 ω.2 +
    _root_.GD.N0107.d009091 m n
      (_root_.GD.N0107.d009085 ω.1)
      (_root_.GD.N0107.d009085 ω.2) *
    _root_.GD.N0107.d009090 m n ω


def d012734
    (m n : ℕ) (ε : ℝ)
    (q : (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0107.d012733 m n ω +
    ε * _root_.GD.N0107.d009090 m n ω * q ω



theorem d012735
    (m n : ℕ) (μ e : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d012733 m n ω - μ =
      _root_.GD.N0141.d006685
        (_root_.GD.N0107.d012732 m n μ e)
        (_root_.GD.N0107.d009090 m n)
        (fun x =>
          _root_.GD.N0107.d009091 m n
            (_root_.GD.N0107.d009085 x.1)
            (_root_.GD.N0107.d009085 x.2))
        e ω := by
  unfold _root_.GD.N0107.d012733 _root_.GD.N0107.d012732
    _root_.GD.N0141.d006685
  ring



theorem d012736
    (m n : ℕ) (μ e ε : ℝ)
    (q : (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d012734 m n ε q ω - μ =
      _root_.GD.N0141.d006686
        (_root_.GD.N0107.d012732 m n μ e)
        (_root_.GD.N0107.d009090 m n)
        (fun x =>
          _root_.GD.N0107.d009091 m n
            (_root_.GD.N0107.d009085 x.1)
            (_root_.GD.N0107.d009085 x.2))
        q e ε ω := by
  unfold _root_.GD.N0107.d012734 _root_.GD.N0141.d006686
  calc
    _root_.GD.N0107.d012733 m n ω +
          ε * _root_.GD.N0107.d009090 m n ω * q ω - μ =
        (_root_.GD.N0107.d012733 m n ω - μ) +
          ε * _root_.GD.N0107.d009090 m n ω * q ω := by ring
    _ = _ := by
      rw [_root_.GD.N0107.d012735 m n μ e ω]


theorem d012737
    (m n : ℕ) (μ σ τ ε : ℝ)
    (q : (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d012734 m n ε q ω - μ =
      _root_.GD.N0141.d006686
        (_root_.GD.N0107.d012732 m n μ
          (_root_.GD.N0107.d009046 m n σ τ))
        (_root_.GD.N0107.d009090 m n)
        (fun x =>
          _root_.GD.N0107.d009091 m n
            (_root_.GD.N0107.d009085 x.1)
            (_root_.GD.N0107.d009085 x.2))
        q (_root_.GD.N0107.d009046 m n σ τ) ε ω :=
  _root_.GD.N0107.d012736
    m n μ (_root_.GD.N0107.d009046 m n σ τ) ε q ω

end

end GD.N0107
