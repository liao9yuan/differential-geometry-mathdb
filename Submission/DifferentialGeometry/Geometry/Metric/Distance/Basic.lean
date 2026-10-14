import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

noncomputable def riemannianEDistOf
    (g : SmoothRiemannianMetric I M) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianEDistOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianEDistOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianEDistOf ``Submission.DifferentialGeometry.riemannianEDistOf

theorem riemannianEDistOf_self
    (g : SmoothRiemannianMetric I M) (x : M) :
    riemannianEDistOf (I := I) g x x = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x x = 0
  exact Manifold.riemannianEDist_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianEDistOf_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianEDistOf_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianEDistOf_self ``Submission.DifferentialGeometry.riemannianEDistOf_self

theorem edistOf_iInf
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y =
      ⨅ (γ : Path x y) (_ : CMDiff 1 γ),
        ∫⁻ t, ENNReal.ofReal (Real.sqrt
          (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x y = _
  rw [Manifold.riemannianEDist]
  refine iInf_congr fun γ => ?_
  refine iInf_congr fun hγ => ?_
  refine _root_.MeasureTheory.lintegral_congr fun t => ?_
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  congr 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.edistOf_iInf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.edistOf_iInf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.edistOf_iInf ``Submission.DifferentialGeometry.edistOf_iInf

theorem riemannianEDistOf_comm
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y = riemannianEDistOf (I := I) g y x := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianEDistOf_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianEDistOf_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianEDistOf_comm ``Submission.DifferentialGeometry.riemannianEDistOf_comm

theorem riemannianEDistOf_triangle
    (g : SmoothRiemannianMetric I M) (x y z : M) :
    riemannianEDistOf (I := I) g x z ≤
      riemannianEDistOf (I := I) g x y + riemannianEDistOf (I := I) g y z := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianEDistOf_triangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianEDistOf_triangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianEDistOf_triangle ``Submission.DifferentialGeometry.riemannianEDistOf_triangle

theorem riemannianEDistOf_toReal_triangle
    (g : SmoothRiemannianMetric I M) (x y z : M)
    (hxy : riemannianEDistOf g x y ≠ ⊤) (hyz : riemannianEDistOf g y z ≠ ⊤) :
    (riemannianEDistOf g x z).toReal ≤
      (riemannianEDistOf g x y).toReal + (riemannianEDistOf g y z).toReal := by
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩)
    (riemannianEDistOf_triangle g x y z)
  rwa [ENNReal.toReal_add hxy hyz] at hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianEDistOf_toReal_triangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianEDistOf_toReal_triangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianEDistOf_toReal_triangle ``Submission.DifferentialGeometry.riemannianEDistOf_toReal_triangle

end DifferentialGeometry

end
