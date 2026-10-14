import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteMetricOverlap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PreparedCollarCorrespondence
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeckManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev PreparedOverlapE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.PreparedOverlapE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.PreparedOverlapE3 target :: scope.openDecls } }
private abbrev PreparedOverlapIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.PreparedOverlapIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.PreparedOverlapIC target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph PreparedOverlapIC I ∞ (f i))
local notation "PreparedOverlapQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (b : ι × Bool) (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R)
variable (r : ℝ) (hfit : r ≤ cuttingCollarWidth (precision b.1))

variable {x₀ : U} {k₀ k : ℕ} {δ : ℝ}
variable (d₀ : normalizedDatum g x₀ (precision b.1) k₀)
variable (hOriginal : f b.1 = neckAmbientMap U d₀)
variable (hrec : δ⁻¹ + 1 ≤ (precision b.1)⁻¹)
variable (d : normalizedDatum g (d₀.offsetPoint (cuttingSign_sq b.2)) δ k)
variable (hmap : d.map = d₀.recenteringMap (cuttingSign_sq b.2) hrec) (hside : d.retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ} (w : CanonicalStaticInsertionWitness d A hA D m ε)
variable (hstatic : r ≤ δ⁻¹)
local notation "PreparedOverlapPatch" => finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b r

include hOriginal hmap hside in
theorem finitePreparedMetricOverlap_inner :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace PreparedOverlapE3 PreparedOverlapQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ PreparedOverlapQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : PreparedOverlapPatch)
      (hq : q.val ∈ finiteCoreInterior transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj)
      (v z : TangentSpace (𝓡 3) q),
      (finiteOldMetric I hdim transitionEnd_pos hδ f hf hdisj hs U g R hRet).inner
        ⟨q.val, finiteCapRestrictedNeighborhood_subset_retained transitionEnd_pos hδ f hf hdisj R b hb r q.property, hq⟩ v z =
          (finiteCapWitnessMetric I hdim hδ f hf hdisj hs d w b r hfit hstatic).inner q v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace PreparedOverlapE3 PreparedOverlapQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ PreparedOverlapQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
  apply finiteMetricOverlap_inner I hdim hδ f hf hdisj hs U g R hRet b hb r hfit d w hstatic
  intro p
  have h := preparedDatum_positive_collar d₀ b.2 hrec d hmap hside hfit hstatic p
  have hv := congrArg (fun x : U => x.val) h
  refine hv.trans ?_
  change (neckAmbientMap U d₀) (cuttingCollarCylinderMap (hδ b.1) b.2
    (p.val.1, ⟨p.val.2, p.property.1.le, p.property.2.trans_le hfit⟩)) =
      f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2
        (p.val.1, ⟨p.val.2, p.property.1.le, p.property.2.trans_le hfit⟩))
  rw [hOriginal]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finitePreparedMetricOverlap_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finitePreparedMetricOverlap_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finitePreparedMetricOverlap_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finitePreparedMetricOverlap_inner
end DifferentialGeometry.PDE.RicciFlow.StandardCap
