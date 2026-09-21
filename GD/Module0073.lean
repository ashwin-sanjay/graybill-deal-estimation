import GD.Module0056


















namespace GD
namespace N0230
namespace N0676

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0571

variable {G Theta D : Type*}
variable [Group G] [MulAction G Theta] [MulAction G D]



def d000914
    (risk : Theta → D → ENNReal) (weight : G → ENNReal) : Prop :=
  ∀ (g : G) (theta : Theta) (d : D),
    risk (g • theta) (g • d) = weight g * risk theta d


def d000915
    (cap : Theta → ENNReal) (weight : G → ENNReal) : Prop :=
  ∀ (g : G) (theta : Theta),
    cap (g • theta) = weight g * cap theta



theorem d000916
    (risk : Theta → D → ENNReal) (cap : Theta → ENNReal)
    (weight : G → ENNReal)
    (hRisk : _root_.GD.N0230.N0676.d000914 risk weight)
    (hCap : _root_.GD.N0230.N0676.d000915 cap weight)
    {d : D} (hd : _root_.GD.N0230.N0571.d000684 risk cap d) (g : G) :
    _root_.GD.N0230.N0571.d000684 risk cap (g • d) := by
  intro theta
  calc
    risk theta (g • d) =
        risk (g • (g⁻¹ • theta)) (g • d) := by simp
    _ = weight g * risk (g⁻¹ • theta) d :=
      hRisk g (g⁻¹ • theta) d
    _ ≤ weight g * cap (g⁻¹ • theta) :=
      mul_le_mul_left' (hd (g⁻¹ • theta)) (weight g)
    _ = cap (g • (g⁻¹ • theta)) :=
      (hCap g (g⁻¹ • theta)).symm
    _ = cap theta := by simp



theorem d000917
    (risk : Theta → D → ENNReal) (cap : Theta → ENNReal)
    (weight : G → ENNReal)
    (hRisk : _root_.GD.N0230.N0676.d000914 risk weight)
    (hCap : _root_.GD.N0230.N0676.d000915 cap weight)
    (d : D) (g : G) :
    _root_.GD.N0230.N0571.d000684 risk cap (g • d) ↔ _root_.GD.N0230.N0571.d000684 risk cap d := by
  constructor
  · intro hgd
    have h := _root_.GD.N0230.N0676.d000916 risk cap weight hRisk hCap hgd g⁻¹
    simpa only [inv_smul_smul] using h
  · intro hd
    exact _root_.GD.N0230.N0676.d000916 risk cap weight hRisk hCap hd g



theorem d000918
    (risk : Theta → D → ENNReal) (weight : G → ENNReal)
    (hRisk : _root_.GD.N0230.N0676.d000914 risk weight)
    (e d : D) (g : G) :
    _root_.GD.N0230.N0608.d000672 risk (g • e) (g • d) ↔
      _root_.GD.N0230.N0608.d000672 risk e d := by
  constructor
  · intro h theta
    calc
      risk theta e =
          weight g⁻¹ * risk (g • theta) (g • e) := by
            simpa using (hRisk g⁻¹ (g • theta) (g • e))
      _ ≤ weight g⁻¹ * risk (g • theta) (g • d) :=
        mul_le_mul_left' (h (g • theta)) (weight g⁻¹)
      _ = risk theta d := by
        simpa using (hRisk g⁻¹ (g • theta) (g • d)).symm
  · intro h theta
    calc
      risk theta (g • e) =
          weight g * risk (g⁻¹ • theta) e := by
            simpa using (hRisk g (g⁻¹ • theta) e)
      _ ≤ weight g * risk (g⁻¹ • theta) d :=
        mul_le_mul_left' (h (g⁻¹ • theta)) (weight g)
      _ = risk theta (g • d) := by
        simpa using (hRisk g (g⁻¹ • theta) d).symm



theorem d000919
    (risk : Theta → D → ENNReal) (weight : G → ENNReal)
    (hRisk : _root_.GD.N0230.N0676.d000914 risk weight)
    (d : D) (g : G) :
    _root_.GD.N0230.N0608.d000674 risk (g • d) ↔ _root_.GD.N0230.N0608.d000674 risk d := by
  constructor
  · intro hgd e he
    have hdom : _root_.GD.N0230.N0608.d000672 risk (g • e) (g • d) :=
      (_root_.GD.N0230.N0676.d000918 risk weight hRisk e d g).2 he
    have heq := hgd (g • e) hdom
    exact (smul_left_cancel g heq)
  · intro hd e he
    have hdom : _root_.GD.N0230.N0608.d000672 risk (g⁻¹ • e) d := by
      have := (_root_.GD.N0230.N0676.d000918
        risk weight hRisk (g⁻¹ • e) d g).1
      apply this
      simpa only [smul_inv_smul] using he
    have heq := hd (g⁻¹ • e) hdom
    have := congrArg (fun x ↦ g • x) heq
    simpa only [smul_inv_smul] using this



def d000920
    (risk : Theta → D → ENNReal) (cap : Theta → ENNReal) : Set D :=
  {d | _root_.GD.N0230.N0571.d000684 risk cap d ∧ _root_.GD.N0230.N0608.d000674 risk d}





theorem d000921
    (risk : Theta → D → ENNReal) (cap : Theta → ENNReal)
    (weight : G → ENNReal)
    (hRisk : _root_.GD.N0230.N0676.d000914 risk weight)
    (hCap : _root_.GD.N0230.N0676.d000915 cap weight)
    (d : D) (g : G) :
    g • d ∈ _root_.GD.N0230.N0676.d000920 risk cap ↔
      d ∈ _root_.GD.N0230.N0676.d000920 risk cap := by
  exact and_congr
    (_root_.GD.N0230.N0676.d000917 risk cap weight hRisk hCap d g)
    (_root_.GD.N0230.N0676.d000919 risk weight hRisk d g)


def d000922 (slice : Set Theta) : Prop :=
  ∀ theta : Theta, ∃ (g : G) (eta : Theta), eta ∈ slice ∧ g • eta = theta







theorem d000923
    (risk : Theta → D → ENNReal) (cap : Theta → ENNReal)
    (weight : G → ENNReal)
    (hRisk : _root_.GD.N0230.N0676.d000914 risk weight)
    (hCap : _root_.GD.N0230.N0676.d000915 cap weight)
    (slice : Set Theta) (hslice : _root_.GD.N0230.N0676.d000922 (G := G) slice)
    (d : D) :
    _root_.GD.N0230.N0571.d000684 risk cap d ↔
      ∀ (g : G) (theta : Theta), theta ∈ slice →
        risk theta (g • d) ≤ cap theta := by
  constructor
  · intro hd g theta _
    exact _root_.GD.N0230.N0676.d000916 risk cap weight hRisk hCap hd g theta
  · intro h theta
    obtain ⟨g, eta, heta, rfl⟩ := hslice theta
    have hsliceRisk := h g⁻¹ eta heta
    calc
      risk (g • eta) d =
          risk (g • eta) (g • (g⁻¹ • d)) := by simp
      _ = weight g * risk eta (g⁻¹ • d) :=
        hRisk g eta (g⁻¹ • d)
      _ ≤ weight g * cap eta :=
        mul_le_mul_left' hsliceRisk (weight g)
      _ = cap (g • eta) := (hCap g eta).symm

end N0676
end N0230
end GD

#print axioms _root_.GD.N0230.N0676.d000916
#print axioms _root_.GD.N0230.N0676.d000917
#print axioms _root_.GD.N0230.N0676.d000918
#print axioms _root_.GD.N0230.N0676.d000919
#print axioms _root_.GD.N0230.N0676.d000921
#print axioms _root_.GD.N0230.N0676.d000923
