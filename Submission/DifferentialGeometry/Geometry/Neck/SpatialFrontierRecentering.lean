import Submission.DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering
import Submission.DifferentialGeometry.Geometry.Neck.SpatialFrontierOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {p : M} {eps alpha a : ℝ}

theorem SpatialNeck.exists_outward_at_coordinate_of_tolerance
    (nk : SpatialNeck g eps p) (hsmall : alpha < 1 / 11)
    (hreserve : 13000 * eps ≤ alpha) (u : Sphere 2) (ha : |a| ≤ 4)
    {W S : Set M} (hregular : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W = _root_.Set.range (fun q => nk.map (q, a)) ∪ S)
    (hdisjoint : Disjoint (_root_.Set.range (fun q => nk.map (q, a))) S) :
    ∃ out : SpatialNeck g alpha (nk.map (u, a)), out.center = u ∧
      (∀ q, out.map (q, 0) = nk.map (q, a)) ∧
      ((∀ q t, out.map (q, t) = nk.map (q, a + t)) ∨
        (∀ q t, out.map (q, t) = nk.map (q, a - t))) ∧
      ∃ r > 0, ∀ t, 0 < t → t < r → out.map (out.center, t) ∉ W := by
  obtain ⟨seed, hcenter, hmap⟩ := nk.exists_at_coordinate hsmall hreserve u ha
  have htranslate := nk.translated_map_apply u seed hmap
  have hzero (q : Sphere 2) : seed.map (q, 0) = nk.map (q, a) := by
    simpa only [add_zero] using nk.translated_map_apply u seed hmap q 0
  have hrange : _root_.Set.range (fun q => seed.map (q, 0)) = _root_.Set.range (fun q => nk.map (q, a)) :=
    congrArg _root_.Set.range (funext hzero)
  have hfront' : frontier W = _root_.Set.range (fun q => seed.map (q, 0)) ∪ S := by
    rw [hrange]
    exact hfront
  have hdisjoint' : Disjoint (_root_.Set.range (fun q => seed.map (q, 0))) S := by
    rw [hrange]
    exact hdisjoint
  obtain ⟨out, _, horient, _, _, _, _, hout⟩ :=
    seed.exists_outward_graph_orientation (fun _ => 0) contMDiff_const
      (fun _ => by norm_num) rfl hregular hS hfront' hdisjoint'
  refine ⟨out, ?_, ?_, ?_, hout⟩
  · rcases horient with rfl | rfl
    · exact hcenter
    · exact hcenter
  · intro q
    rcases horient with rfl | rfl
    · exact hzero q
    · simpa only [SpatialNeck.axialReflection_apply, neg_zero] using hzero q
  · rcases horient with rfl | rfl
    · exact Or.inl htranslate
    · right
      intro q t
      rw [SpatialNeck.axialReflection_apply, htranslate]
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_outward_at_coordinate_of_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_outward_at_coordinate_of_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_outward_at_coordinate_of_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_outward_at_coordinate_of_tolerance

theorem SpatialNeck.exists_outward_at_coordinate_mul
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 156000)
    (u : Sphere 2) (ha : |a| ≤ 4)
    {W S : Set M} (hregular : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W = _root_.Set.range (fun q => nk.map (q, a)) ∪ S)
    (hdisjoint : Disjoint (_root_.Set.range (fun q => nk.map (q, a))) S) :
    ∃ out : SpatialNeck g (13000 * eps) (nk.map (u, a)), out.center = u ∧
      (∀ q, out.map (q, 0) = nk.map (q, a)) ∧
      ((∀ q t, out.map (q, t) = nk.map (q, a + t)) ∨
        (∀ q t, out.map (q, t) = nk.map (q, a - t))) ∧
      ∃ r > 0, ∀ t, 0 < t → t < r → out.map (out.center, t) ∉ W := by
  exact nk.exists_outward_at_coordinate_of_tolerance (by linarith) le_rfl u ha
    hregular hS hfront hdisjoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_outward_at_coordinate_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_outward_at_coordinate_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_outward_at_coordinate_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_outward_at_coordinate_mul

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
