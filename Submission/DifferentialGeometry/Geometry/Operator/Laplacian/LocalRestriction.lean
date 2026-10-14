import Submission.DifferentialGeometry.Geometry.Operator.Restriction
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import Submission.DifferentialGeometry.Bundle.SmoothScalarGerm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem laplacian_restrictOpen_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    {f : M → ℝ} {V : Set M} (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V) (x : U) (hxV : (x : M) ∈ V) :
    laplacian (Connection.LeviCivita (g.restrictOpen U)) (g.restrictOpen U)
      (fun y : U => f (y : M)) x =
        laplacian (Connection.LeviCivita g) g f (x : M) := by
  obtain ⟨F, hF, heq⟩ := exists_smooth_germ hV hxV hf
  have hinc : ContMDiffAt I I ∞ (Subtype.val : U → M) x :=
    (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
  have hfU : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y : U => f (y : M)) x :=
    (hf.contMDiffAt (hV.mem_nhds hxV)).comp x hinc
  have hFU : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : U => F (y : M)) :=
    hF.comp (contMDiff_subtype_val (I := I) (U := U))
  calc
    laplacian (Connection.LeviCivita (g.restrictOpen U)) (g.restrictOpen U)
        (fun y : U => f (y : M)) x =
      laplacian (Connection.LeviCivita (g.restrictOpen U)) (g.restrictOpen U)
        (fun y : U => F (y : M)) x :=
      laplacian_congr_of_eventuallyEq _ _ hfU hFU.contMDiffAt
        (heq.symm.comp_tendsto hinc.continuousAt.tendsto)
    _ = laplacian (Connection.LeviCivita g) g F (x : M) :=
      laplacian_restrictOpen g U F hF x
    _ = laplacian (Connection.LeviCivita g) g f (x : M) :=
      laplacian_congr_of_eventuallyEq _ _ hF.contMDiffAt
        (hf.contMDiffAt (hV.mem_nhds hxV)) heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_restrictOpen_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_restrictOpen_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_restrictOpen_of_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_restrictOpen_of_contMDiffOn

end DifferentialGeometry.Geometry.Operator
