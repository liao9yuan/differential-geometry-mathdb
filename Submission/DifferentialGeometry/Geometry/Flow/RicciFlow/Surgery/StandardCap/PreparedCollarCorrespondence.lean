import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RecenteredStaticPreparation
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.PositiveCuttingCoordinates
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollar
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.PreparedCapWidth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u v w
private abbrev PreparedIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.PreparedIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.PreparedIC target :: scope.openDecls } }

theorem positiveCuttingCylinder_subset_controlled {B r : ℝ} (hfit : r ≤ B) :
    positiveCuttingCylinder r ≤ openCylinder B := by
  intro q hq
  change 0 < q.2 ∧ q.2 < r at hq
  change -B < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2.trans_le hfit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveCuttingCylinder_subset_controlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveCuttingCylinder_subset_controlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveCuttingCylinder_subset_controlled ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveCuttingCylinder_subset_controlled

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ δ' r : ℝ} {k k' : ℕ}

theorem preparedDatum_positive_collar (d : normalizedDatum g x₀ δ k) (b : Bool)
    (hrec : δ'⁻¹ + 1 ≤ δ⁻¹)
    (d' : normalizedDatum g (d.offsetPoint (cuttingSign_sq b)) δ' k')
    (hmap : d'.map = d.recenteringMap (cuttingSign_sq b) hrec) (hside : d'.retainedSide = _root_.Bool.true)
    (hfit : r ≤ cuttingCollarWidth δ) (hstatic : r ≤ δ'⁻¹) (q : positiveCuttingCylinder r) :
    d'.oriented.controlledMap
      (Opens.inclusion (positiveCuttingCylinder_subset_controlled hstatic) q) =
        d.map (cuttingCollarCylinderMap d.precision_pos b
          (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hfit⟩)) := by
  rw [normalizedDatum.controlledMap_apply, normalizedDatum.oriented_map_of_retainedSide_true d' hside,
    hmap, normalizedDatum.recenteringMap_apply]
  apply congrArg d.map
  apply Subtype.ext
  rw [cuttingCollarCylinderMap_val]
  change (q.val.1, cuttingSign b * (1 + q.val.2)) = (q.val.1, cuttingSign b + cuttingSign b * q.val.2)
  exact Prod.ext rfl (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.preparedDatum_positive_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.preparedDatum_positive_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.preparedDatum_positive_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.preparedDatum_positive_collar

theorem exists_uniform_prepared_collar_correspondence :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ {E : Type u} {H : Type v} {M : Type w}
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 6)),
        ∀ b : Bool, ∃ hrec : (c * δ)⁻¹ + 1 ≤ δ⁻¹,
          ∃ d' : normalizedDatum g (d.offsetPoint (cuttingSign_sq b)) (c * δ) (m + 4),
            d'.map = d.recenteringMap (cuttingSign_sq b) hrec ∧ d'.retainedSide = _root_.Bool.true ∧
            |metricScalarAt g (d.offsetPoint (cuttingSign_sq b)) / metricScalarAt g x₀ - 1| ≤ c * δ ∧
            ∃ out : CanonicalStaticInsertionWitness d' A hA D m ε,
              StaticInsertionAdditionalProperties C out ∧
              ∀ (q : positiveCuttingCylinder (preparedCapWidth c δ)),
                ∃ qorig : bufferedCylinder δ, qorig.val = (q.val.1, cuttingSign b + cuttingSign b * q.val.2) ∧
                  ∃ qnew : openCylinder (c * δ)⁻¹, qnew.val = q.val ∧
                    d'.oriented.controlledMap qnew = d.map qorig := by
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hmod⟩ := exists_uniform_recentered_static_preparation.{u, v, w}
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, hquarter, hprep⟩ := hmod D hD m ε hε
  refine ⟨δ₀, hδ₀, hquarter, ?_⟩
  intro δ hδ hle E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d b
  obtain ⟨hrec, d', hmap, hside, hratio, out, hout⟩ := hprep δ hδ hle g x₀ d (cuttingSign b) (cuttingSign_sq b)
  refine ⟨hrec, d', hmap, hside, hratio, out, hout, ?_⟩
  intro q
  have hwidth := preparedCapWidth_bounds c δ hc hδ
  let qorig := cuttingCollarCylinderMap hδ b
    (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hwidth.2.1⟩)
  let qnew := Opens.inclusion (positiveCuttingCylinder_subset_controlled hwidth.2.2.le) q
  exact ⟨qorig, cuttingCollarCylinderMap_val hδ b _, qnew, rfl,
    preparedDatum_positive_collar d b hrec d' hmap hside hwidth.2.1 hwidth.2.2.le q⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_prepared_collar_correspondence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_prepared_collar_correspondence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_prepared_collar_correspondence ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_prepared_collar_correspondence
end DifferentialGeometry.PDE.RicciFlow.StandardCap
