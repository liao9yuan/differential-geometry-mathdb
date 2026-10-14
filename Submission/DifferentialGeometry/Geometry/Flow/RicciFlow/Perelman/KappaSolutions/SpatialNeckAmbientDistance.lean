import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompleteMetricMinimizingCurve
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreCurves
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderSphereLength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance ambientNeckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambientNeckSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambientNeckSphereDimension target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance ambientNeckC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambientNeckC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambientNeckC1 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)

theorem exists_minimizing_core_lift (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi) :
    ∃ β : ℝ → spatialNeckBuffer epsilon,
      ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 β (_root_.Set.Icc 0 1) ∧
      β 0 = x ∧ β 1 = y ∧
      (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, β t ∈ spatialNeckClosedCore epsilon) ∧
      metricPathELength (I := I) h ((W.embedding : spatialNeckBuffer epsilon → N) ∘ β) 0 1 =
        riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [W.dimension_three]; norm_num⟩
  have hfin : riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) ≠ ⊤ :=
    ne_of_lt ((W.band_edist_lt hsmall x y hx hy).trans_le le_top)
  obtain ⟨γ, hγ, hγ0, hγ1, hlength⟩ :=
    completeMetric_exists_minimizing_curve h W.complete (W.embedding x) (W.embedding y) hfin
  have hcore := W.minimizing_curve_stays_core hsmall x y hx hy hγ hγ0 hlength
  obtain ⟨β, hβ, hβcore, hβeq⟩ := W.lift_core_curve hγ hcore
  have hβ0 : β 0 = x := W.smooth_embedding.isEmbedding.injective
    ((hβeq 0 ⟨le_rfl, zero_le_one⟩).trans hγ0)
  have hβ1 : β 1 = y := W.smooth_embedding.isEmbedding.injective
    ((hβeq 1 ⟨zero_le_one, le_rfl⟩).trans hγ1)
  have hsame : metricPathELength (I := I) h
      ((W.embedding : spatialNeckBuffer epsilon → N) ∘ β) 0 1 =
      metricPathELength (I := I) h γ 0 1 := by
    let _ : _root_.Bundle.RiemannianBundle (fun q : N => TangentSpace I q) := ⟨h.toRiemannianMetric⟩
    exact Manifold.pathELength_congr hβeq
  exact ⟨β, hβ, hβ0, hβ1, hβcore, hsame.trans hlength⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_minimizing_core_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_minimizing_core_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_minimizing_core_lift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_minimizing_core_lift

theorem band_axial_edist_lower (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * |y.val.2 - x.val.2|) ≤
      riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) := by
  obtain ⟨β, hβ, hβ0, hβ1, hcore, hlength⟩ := W.exists_minimizing_core_lift hsmall x y hx hy
  have hlower := W.axial_displacement_le_pathELength hsmall zero_le_one hβ hcore
  rw [hβ0, hβ1, hlength] at hlower
  exact hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_axial_edist_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_axial_edist_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_axial_edist_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_axial_edist_lower

theorem band_antipodal_edist_lower (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi)
    (hanti : y.val.1 = -x.val.1) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * Real.pi) ≤
      riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) := by
  obtain ⟨β, hβ, hβ0, hβ1, hcore, hlength⟩ := W.exists_minimizing_core_lift hsmall x y hx hy
  have hanti' : (β 1).val.1 = -(β 0).val.1 := by rw [hβ0, hβ1]; exact hanti
  have hsphere := unitCylinder_antipodal_length_lower_on_open
    (spatialNeckBuffer epsilon) zero_le_one hβ hanti'
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hlower := (mul_le_mul_of_nonneg_left hsphere
    (zero_le : 0 ≤ ENNReal.ofReal (11 / 12 * spatialNeckScale h p))).trans
      (W.pathELength_bilipschitz hsmall hβ hcore).1
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 11 / 12 * spatialNeckScale h p),
    hlength] at hlower
  exact hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_antipodal_edist_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_antipodal_edist_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_antipodal_edist_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_antipodal_edist_lower

omit [I.Boundaryless] in
theorem slice_edist_upper (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : x ∈ spatialNeckClosedCore epsilon) (hy : y ∈ spatialNeckClosedCore epsilon)
    (hslice : y.val.2 = x.val.2) :
    riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) ≤
      ENNReal.ofReal (13 / 12 * spatialNeckScale h p * Real.pi) := by
  have hupper := W.core_edist_upper hsmall x y hx hy
  simpa only [hslice, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero,
    Real.sqrt_sq Real.pi_pos.le] using hupper

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.slice_edist_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.slice_edist_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.slice_edist_upper ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.slice_edist_upper

theorem band_axial_length_lower (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi)
    {γ : ℝ → N} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (_root_.Set.Icc a b))
    (hγa : γ a = W.embedding x) (hγb : γ b = W.embedding y) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * |y.val.2 - x.val.2|) ≤
      metricPathELength (I := I) h γ a b := by
  let _ : _root_.Bundle.RiemannianBundle (fun q : N => TangentSpace I q) := ⟨h.toRiemannianMetric⟩
  exact (W.band_axial_edist_lower hsmall x y hx hy).trans
    (Manifold.riemannianEDist_le_pathELength hγ hγa hγb hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_axial_length_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_axial_length_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_axial_length_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_axial_length_lower

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
