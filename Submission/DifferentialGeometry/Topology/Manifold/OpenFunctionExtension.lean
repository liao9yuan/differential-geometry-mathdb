import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem contMDiffOn_extend_from_open
    {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (U : TopologicalSpace.Opens M) (f : U → N) (d : M → N)
    {A : Set U} (hA : IsOpen A) (hf : ContMDiffOn I J ∞ f A) :
    ContMDiffOn I J ∞ (Subtype.val.extend f d) (Subtype.val '' A) := by
  rintro x ⟨y, hy, rfl⟩
  have hlocal : ContMDiffAt I J ∞ (fun z : U ↦ Subtype.val.extend f d (z : M)) y := by
    change ContMDiffAt I J ∞ ((Subtype.val.extend f d) ∘ Subtype.val) y
    rw [Function.extend_comp Subtype.val_injective]
    exact (hf y hy).contMDiffAt (hA.mem_nhds hy)
  exact (contMDiffAt_subtype_iff.mp hlocal).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiffOn_extend_from_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiffOn_extend_from_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiffOn_extend_from_open ``Submission.DifferentialGeometry.Topology.Manifold.contMDiffOn_extend_from_open

theorem mvfderiv_extend_from_open
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (f : U → ℝ) (d : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : U) (v : TangentSpace I x) :
    mvfderiv I (Subtype.val.extend f d) (x : M) (mfderiv I I (Subtype.val : U → M) x v) =
      mvfderiv I f x v := by
  have hlocal : ContMDiffAt I 𝓘(ℝ) ∞ (Subtype.val.extend f d) (x : M) := by
    rw [← contMDiffAt_subtype_iff (x := x)]
    change ContMDiffAt I 𝓘(ℝ) ∞ ((Subtype.val.extend f d) ∘ Subtype.val) x
    rw [Function.extend_comp Subtype.val_injective]
    exact hf.contMDiffAt
  have h := mvfderiv_comp_apply x (hlocal.mdifferentiableAt (by decide))
    ((contMDiff_subtype_val (I := I) (n := ∞)).mdifferentiable (by decide) x) v
  rw [Function.extend_comp Subtype.val_injective] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.mvfderiv_extend_from_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.mvfderiv_extend_from_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.mvfderiv_extend_from_open ``Submission.DifferentialGeometry.Topology.Manifold.mvfderiv_extend_from_open

end DifferentialGeometry.Topology.Manifold
