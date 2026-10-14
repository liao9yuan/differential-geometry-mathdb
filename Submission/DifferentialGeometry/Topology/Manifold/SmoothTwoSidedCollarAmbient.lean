import Submission.DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable {E H F G K H' S M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {L : ModelWithCorners ℝ K H'}
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {e : S → M} (c : SmoothTwoSidedCollar I J e)

def mapAmbient (f : M → N) (hf : IsLocalDiffeomorph J L ∞ f) (hinj : Function.Injective f) :
    SmoothTwoSidedCollar I L (f ∘ e) := by
  have hc : IsLocalDiffeomorph (I.prod 𝓘(ℝ)) J ∞ c.toFun :=
    DifferentialGeometry.isLocalDiffeomorph_comp
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val c.neighborhood)
      c.toDiffeomorph.isLocalDiffeomorph
  have hcomp : IsLocalDiffeomorph (I.prod 𝓘(ℝ)) L ∞ (f ∘ c.toFun) :=
    DifferentialGeometry.isLocalDiffeomorph_comp hf hc
  have hcomp_inj : Function.Injective (f ∘ c.toFun) :=
    hinj.comp c.isOpenEmbedding_toFun.injective
  exact {
    radius := c.radius
    radius_pos := c.radius_pos
    neighborhood := hcomp.image
    toDiffeomorph := diffeomorphRangeOfInjective hcomp hcomp_inj
    zero_eq := fun s ↦ congrArg f (c.toFun_zero s) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient

@[simp] theorem mapAmbient_radius (f : M → N) (hf : IsLocalDiffeomorph J L ∞ f)
    (hinj : Function.Injective f) : (c.mapAmbient f hf hinj).radius = c.radius := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_radius ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_radius

@[simp] theorem mapAmbient_toFun (f : M → N) (hf : IsLocalDiffeomorph J L ∞ f)
    (hinj : Function.Injective f) (p : S × symmetricOpenInterval c.radius) :
    (c.mapAmbient f hf hinj).toFun p = f (c.toFun p) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_toFun ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_toFun

@[simp] theorem mapAmbient_neighborhood (f : M → N) (hf : IsLocalDiffeomorph J L ∞ f)
    (hinj : Function.Injective f) :
    ((c.mapAmbient f hf hinj).neighborhood : Set N) = f '' (c.neighborhood : Set M) := by
  change _root_.Set.range (f ∘ c.toFun) = f '' (c.neighborhood : Set M)
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨c.toFun p, (c.toDiffeomorph p).property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c.toDiffeomorph.symm ⟨x, hx⟩, ?_⟩
    exact congrArg (fun z : c.neighborhood ↦ f z.val) (c.toDiffeomorph.apply_symm_apply ⟨x, hx⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_neighborhood ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.mapAmbient_neighborhood

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
