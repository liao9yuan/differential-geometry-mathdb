import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']

theorem bilinPerturb {B : E' →L[Real] E' →L[Real] Real}
    {A : E' →L[Real] E'} (v w : E') :
    |B (A v) (A w) - B v w| ≤
      ‖B‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) * (‖v‖ * ‖w‖) := by
  have hsplit : B (A v) (A w) - B v w
      = B ((A - ContinuousLinearMap.id Real E') v) (A w)
        + B v ((A - ContinuousLinearMap.id Real E') w) := by
    simp only [sub_apply, ContinuousLinearMap.coe_id', id_eq, map_sub, sub_apply]
    abel
  rw [hsplit]
  have h1 : |B ((A - ContinuousLinearMap.id Real E') v) (A w)| ≤
      ‖B‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖v‖) * (‖A‖ * ‖w‖) := by
    calc
      |B ((A - ContinuousLinearMap.id Real E') v) (A w)|
          ≤ ‖B‖ * ‖(A - ContinuousLinearMap.id Real E') v‖ * ‖A w‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm₂ B _ _
      _ ≤ ‖B‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖v‖) * (‖A‖ * ‖w‖) := by
            gcongr
            · exact ContinuousLinearMap.le_opNorm _ v
            · exact ContinuousLinearMap.le_opNorm A w
  have h2 : |B v ((A - ContinuousLinearMap.id Real E') w)| ≤
      ‖B‖ * ‖v‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖w‖) := by
    calc
      |B v ((A - ContinuousLinearMap.id Real E') w)|
          ≤ ‖B‖ * ‖v‖ * ‖(A - ContinuousLinearMap.id Real E') w‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm₂ B _ _
      _ ≤ ‖B‖ * ‖v‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖w‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ w
  calc
    |B ((A - ContinuousLinearMap.id Real E') v) (A w)
        + B v ((A - ContinuousLinearMap.id Real E') w)|
        ≤ |B ((A - ContinuousLinearMap.id Real E') v) (A w)|
          + |B v ((A - ContinuousLinearMap.id Real E') w)| := abs_add_le _ _
    _ ≤ ‖B‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖v‖) * (‖A‖ * ‖w‖)
        + ‖B‖ * ‖v‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖w‖) := add_le_add h1 h2
    _ = ‖B‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) *
        (‖v‖ * ‖w‖) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.bilinPerturb then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.bilinPerturb"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.bilinPerturb ``Submission.DifferentialGeometry.CheegerGromovCompactness.bilinPerturb

theorem quadPerturbTri {B₀ B₁ : E' →L[Real] E' →L[Real] Real}
    {A : E' →L[Real] E'} (v : E') :
    |B₁ (A v) (A v) - B₀ v v| ≤
      (‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) *
        (‖v‖ * ‖v‖) := by
  have h1 := bilinPerturb (B := B₁) (A := A) v v
  have h2 : |B₁ v v - B₀ v v| ≤ ‖B₁ - B₀‖ * (‖v‖ * ‖v‖) := by
    have : B₁ v v - B₀ v v = (B₁ - B₀) v v := by
      simp [sub_apply]
    rw [this, ← Real.norm_eq_abs]
    calc
      ‖(B₁ - B₀) v v‖ ≤ ‖B₁ - B₀‖ * ‖v‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm₂ _ v v
      _ = ‖B₁ - B₀‖ * (‖v‖ * ‖v‖) := by ring
  calc
    |B₁ (A v) (A v) - B₀ v v|
        = |(B₁ (A v) (A v) - B₁ v v) + (B₁ v v - B₀ v v)| := by ring_nf
    _ ≤ |B₁ (A v) (A v) - B₁ v v| + |B₁ v v - B₀ v v| := abs_add_le _ _
    _ ≤ ‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) * (‖v‖ * ‖v‖)
        + ‖B₁ - B₀‖ * (‖v‖ * ‖v‖) := add_le_add h1 h2
    _ = (‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) *
        (‖v‖ * ‖v‖) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.quadPerturbTri then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.quadPerturbTri"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.quadPerturbTri ``Submission.DifferentialGeometry.CheegerGromovCompactness.quadPerturbTri

theorem bilinPerturbTri {B₀ B₁ : E' →L[Real] E' →L[Real] Real}
    {A : E' →L[Real] E'} (v w : E') :
    |B₁ (A v) (A w) - B₀ v w| ≤
      (‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) *
        (‖v‖ * ‖w‖) := by
  have h1 := bilinPerturb (B := B₁) (A := A) v w
  have h2 : |B₁ v w - B₀ v w| ≤ ‖B₁ - B₀‖ * (‖v‖ * ‖w‖) := by
    have hsub : B₁ v w - B₀ v w = (B₁ - B₀) v w := by
      simp [sub_apply]
    rw [hsub, ← Real.norm_eq_abs]
    calc
      ‖(B₁ - B₀) v w‖ ≤ ‖B₁ - B₀‖ * ‖v‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm₂ _ v w
      _ = ‖B₁ - B₀‖ * (‖v‖ * ‖w‖) := by ring
  calc
    |B₁ (A v) (A w) - B₀ v w|
        = |(B₁ (A v) (A w) - B₁ v w) + (B₁ v w - B₀ v w)| := by ring_nf
    _ ≤ |B₁ (A v) (A w) - B₁ v w| + |B₁ v w - B₀ v w| := abs_add_le _ _
    _ ≤ ‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) * (‖v‖ * ‖w‖)
        + ‖B₁ - B₀‖ * (‖v‖ * ‖w‖) := add_le_add h1 h2
    _ = (‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) *
        (‖v‖ * ‖w‖) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.bilinPerturbTri then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.bilinPerturbTri"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.bilinPerturbTri ``Submission.DifferentialGeometry.CheegerGromovCompactness.bilinPerturbTri

theorem norm_pullbackForm_sub_le
    (B₀ B₁ : E' →L[Real] E' →L[Real] Real) (A : E' →L[Real] E') :
    ‖pullbackForm (B₁, A) - B₀‖ ≤
      ‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w ↦ ?_
  simpa only [sub_apply, pullbackForm_apply, Real.norm_eq_abs, mul_assoc] using
    (bilinPerturbTri (B₀ := B₀) (B₁ := B₁) (A := A) v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.norm_pullbackForm_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.norm_pullbackForm_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.norm_pullbackForm_sub_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.norm_pullbackForm_sub_le

theorem quadPerturbNeumann {B₀ B₁ : E' →L[Real] E' →L[Real] Real}
    {A : E' →L[Real] E'} {ε : Real}
    (hA : ‖A - ContinuousLinearMap.id Real E'‖ ≤ ε) (v : E') :
    |B₁ (A v) (A v) - B₀ v v| ≤
      (‖B₁‖ * ε * (2 + ε) + ‖B₁ - B₀‖) * (‖v‖ * ‖v‖) := by
  refine (quadPerturbTri v).trans ?_
  have hAle : ‖A‖ ≤ 1 + ε := by
    calc
      ‖A‖ = ‖ContinuousLinearMap.id Real E' +
          (A - ContinuousLinearMap.id Real E')‖ := by
            congr 1
            abel
      _ ≤ ‖ContinuousLinearMap.id Real E'‖ +
          ‖A - ContinuousLinearMap.id Real E'‖ := norm_add_le _ _
      _ ≤ 1 + ε := add_le_add ContinuousLinearMap.norm_id_le hA
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hA
  have hcoef : ‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) ≤
      ‖B₁‖ * ε * (2 + ε) := by
    have h2 : (1 : Real) + ‖A‖ ≤ 2 + ε := by linarith [hAle]
    gcongr
  gcongr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.quadPerturbNeumann then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.quadPerturbNeumann"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.quadPerturbNeumann ``Submission.DifferentialGeometry.CheegerGromovCompactness.quadPerturbNeumann

end CheegerGromovCompactness
end DifferentialGeometry
