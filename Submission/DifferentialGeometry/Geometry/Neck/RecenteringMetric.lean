import Submission.DifferentialGeometry.Geometry.Neck.RecenteringChart
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens (O : _root_.TopologicalSpace.Opens (S2 × ℝ)) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens target :: scope.openDecls } }

def recenteringMetric {ε δ σ : ℝ} (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹)
    (H : SmoothRiemannianMetric IC (bufferedCylinder δ)) :
    SmoothRiemannianMetric IC (bufferedCylinder ε) :=
  Diffeomorph.pullbackMetric
    (H.restrictOpenOfSubset (cylinderAxialImage_bufferedCylinder_le hσ hfit))
    (cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.recenteringMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.recenteringMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.recenteringMetric ``Submission.DifferentialGeometry.Geometry.Neck.recenteringMetric

theorem recenteringMetric_inner {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) (H : SmoothRiemannianMetric IC (bufferedCylinder δ))
    (x : bufferedCylinder ε) (v w : TangentSpace IC x) :
    (recenteringMetric hσ hfit H).inner x v w =
      H.inner (recenteringCylinderMap hσ hfit x)
        (mfderiv IC IC (recenteringCylinderMap hσ hfit) x v)
        (mfderiv IC IC (recenteringCylinderMap hσ hfit) x w) := by
  rw [recenteringMetric, Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictSubset_inner]
  rw [cylinderAxialRestrict_mfderiv, cylinderAxialRestrict_mfderiv,
    recenteringCylinderMap_mfderiv, recenteringCylinderMap_mfderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.recenteringMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.recenteringMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.recenteringMetric_inner ``Submission.DifferentialGeometry.Geometry.Neck.recenteringMetric_inner

theorem recenteringMetric_reference {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    recenteringMetric hσ hfit (referenceMetric δ) = referenceMetric ε := by
  rw [recenteringMetric, referenceMetric, SmoothRiemannianMetric.restrictOpen_flat]
  exact pullback_cylinderMetric_cylinderAxialRestrict
    (scaleMetric 2 (by norm_num) (roundMetric (E := E3) (n := 2))) σ σ hσ
      (bufferedCylinder ε)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.recenteringMetric_reference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.recenteringMetric_reference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.recenteringMetric_reference ``Submission.DifferentialGeometry.Geometry.Neck.recenteringMetric_reference

theorem metricDerivNorm_recenteringMetric {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹)
    (H HInf : SmoothRiemannianMetric IC (bufferedCylinder δ))
    (j : ℕ) (x : bufferedCylinder ε) :
    metricDerivNorm j (recenteringMetric hσ hfit H) (recenteringMetric hσ hfit HInf)
      (referenceMetric ε) x =
    metricDerivNorm j H HInf (referenceMetric δ) (recenteringCylinderMap hσ hfit x) := by
  have h := metricDerivNorm_pullback
    (H.restrictOpenOfSubset (cylinderAxialImage_bufferedCylinder_le hσ hfit))
    (HInf.restrictOpenOfSubset (cylinderAxialImage_bufferedCylinder_le hσ hfit))
    ((referenceMetric δ).restrictOpenOfSubset (cylinderAxialImage_bufferedCylinder_le hσ hfit))
    (cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε)) j x
  rw [metricDerivNorm_flat] at h
  change metricDerivNorm j (recenteringMetric hσ hfit H) (recenteringMetric hσ hfit HInf)
    (recenteringMetric hσ hfit (referenceMetric δ)) x = _ at h
  rw [recenteringMetric_reference] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.metricDerivNorm_recenteringMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.metricDerivNorm_recenteringMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.metricDerivNorm_recenteringMetric ``Submission.DifferentialGeometry.Geometry.Neck.metricDerivNorm_recenteringMetric

theorem metricDerivENormSupOn_recenteringMetric {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹)
    (H HInf : SmoothRiemannianMetric IC (bufferedCylinder δ))
    (K : Set (bufferedCylinder ε)) (p : ℕ) :
    metricDerivENormSupOn K p (recenteringMetric hσ hfit H) (recenteringMetric hσ hfit HInf)
      (referenceMetric ε) =
    metricDerivENormSupOn (recenteringCylinderMap hσ hfit '' K) p H HInf
      (referenceMetric δ) := by
  simp only [metricDerivENormSupOn, metricDerivNorm_recenteringMetric, iSup_image]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.metricDerivENormSupOn_recenteringMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.metricDerivENormSupOn_recenteringMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.metricDerivENormSupOn_recenteringMetric ``Submission.DifferentialGeometry.Geometry.Neck.metricDerivENormSupOn_recenteringMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem recenteringMetric_error_lt (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    metricDerivENormSupOn (controlledCylinder ε) k
      (recenteringMetric hσ hfit d.normalizedMetric) (referenceMetric ε) (referenceMetric ε) <
      ENNReal.ofReal δ := by
  have h := metricDerivENormSupOn_recenteringMetric hσ hfit d.normalizedMetric
    (referenceMetric δ) (controlledCylinder ε) k
  rw [recenteringMetric_reference] at h
  rw [h]
  exact (metricDerivENormSupOn_mono
    (image_recenteringCylinderMap_controlledCylinder_subset hσ hfit) le_rfl
      d.normalizedMetric (referenceMetric δ) (referenceMetric δ)).trans_lt
    d.normalizedMetric_error_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.recenteringMetric_error_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.recenteringMetric_error_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.recenteringMetric_error_lt ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.recenteringMetric_error_lt

private theorem recenteringMap_local (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    IsLocalDiffeomorph IC I ∞ (d.recenteringMap hσ hfit) :=
  isLocalDiffeomorph_of_injective_mfderiv _ (d.contMDiff_recenteringMap hσ hfit)
    (d.immersion_recenteringMap hσ hfit) (by
      rw [show Module.finrank ℝ E = 3 from Fact.out]
      simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.recenteringMap_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.recenteringMap_local target :: scope.openDecls } }

theorem scale_recenteringMetric_eq_pullback (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) (qNew : ℝ) (hqNew : 0 < qNew) :
    scaleMetric (qNew / metricScalarAt g x₀) (div_pos hqNew d.scalar_pos)
      (recenteringMetric hσ hfit d.normalizedMetric) =
    pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric qNew hqNew g)
      (d.recenteringMap hσ hfit) (d.recenteringMap_local hσ hfit)
      (d.injective_recenteringMap hσ hfit) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [scaleMetric_inner, recenteringMetric_inner, d.normalizedMetric_inner,
    pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner]
  have hd := d.smooth.mdifferentiable (by simp)
  have hc := (contMDiff_recenteringCylinderMap hσ hfit).mdifferentiable (by simp)
  rw [recenteringMap, mfderiv_comp x (hd _) (hc _)]
  change qNew / metricScalarAt g x₀ *
      (metricScalarAt g x₀ * g.inner (d.map (recenteringCylinderMap hσ hfit x))
        (mfderiv IC I d.map (recenteringCylinderMap hσ hfit x)
          (mfderiv IC IC (recenteringCylinderMap hσ hfit) x v))
        (mfderiv IC I d.map (recenteringCylinderMap hσ hfit x)
          (mfderiv IC IC (recenteringCylinderMap hσ hfit) x w))) =
    qNew * g.inner (d.map (recenteringCylinderMap hσ hfit x))
        (mfderiv IC I d.map (recenteringCylinderMap hσ hfit x)
          (mfderiv IC IC (recenteringCylinderMap hσ hfit) x v))
        (mfderiv IC I d.map (recenteringCylinderMap hσ hfit x)
          (mfderiv IC IC (recenteringCylinderMap hσ hfit) x w))
  field_simp [ne_of_gt d.scalar_pos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.scale_recenteringMetric_eq_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.scale_recenteringMetric_eq_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.scale_recenteringMetric_eq_pullback ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.scale_recenteringMetric_eq_pullback

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
