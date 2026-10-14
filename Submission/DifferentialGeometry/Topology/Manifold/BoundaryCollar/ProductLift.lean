import Submission.DifferentialGeometry.Topology.Manifold.Boundary.SmoothMap
import Mathlib.Geometry.Manifold.Instances.Icc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Manifold _root_.Topology
open scoped _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
  {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] [TopologicalSpace X] [ChartedSpace G X]
  {J : ModelWithCorners ℝ F G} {ε : ℝ} [Fact ((0 : ℝ) < ε)]

theorem contMDiffAt_boundary_product_iff {k : ℕ∞ω} (hk : k ≤ ∞)
    {f : X → BoundaryManifold I M × _root_.Set.Icc (0 : ℝ) ε} {x : X} :
    ContMDiffAt J (hI.boundaryI.prod (𝓡∂ 1)) k f x ↔
      ContMDiffAt J (I.prod 𝓘(ℝ, ℝ)) k
        (fun y => ((f y).1.val, (f y).2.val)) x := by
  constructor
  · intro h
    have hf := (DifferentialGeometry.Manifold.Boundary.contMDiffAt_boundary_iff hk).mp h.fst
    have ht := (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ε) (n := k)).contMDiffAt.comp x h.snd
    exact hf.prodMk ht
  · intro h
    have hf := (DifferentialGeometry.Manifold.Boundary.contMDiffAt_boundary_iff hk).mpr h.fst
    have ht : ContMDiffAt J (𝓡∂ 1) k (fun y => (f y).2) x := by
      apply (ContMDiffAt.iff_comp_isImmersionAtOfComplement (f := fun y : X => (f y).2)
        (isImmersionOfComplement_subtypeVal_Icc (x := (0 : ℝ)) (y := ε) (n := k) (f x).2)).mpr
      exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr h.snd.continuousAt, h.snd⟩
    exact hf.prodMk ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.contMDiffAt_boundary_product_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.contMDiffAt_boundary_product_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.contMDiffAt_boundary_product_iff ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.contMDiffAt_boundary_product_iff


theorem contMDiff_boundary_product_iff {k : ℕ∞ω} (hk : k ≤ ∞)
    {f : X → BoundaryManifold I M × _root_.Set.Icc (0 : ℝ) ε} :
    ContMDiff J (hI.boundaryI.prod (𝓡∂ 1)) k f ↔
      ContMDiff J (I.prod 𝓘(ℝ, ℝ)) k (fun y => ((f y).1.val, (f y).2.val)) := by
  exact forall_congr' fun _ => contMDiffAt_boundary_product_iff hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.contMDiff_boundary_product_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.contMDiff_boundary_product_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.contMDiff_boundary_product_iff ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.contMDiff_boundary_product_iff

end DifferentialGeometry.Manifold.BoundaryCollar
