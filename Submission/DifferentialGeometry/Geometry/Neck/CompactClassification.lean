import Submission.DifferentialGeometry.Geometry.Neck.SpatialClosedNeckTube
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleFactor
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderClosing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Topology.DoubleCylinder
  (nonempty_diffeomorph_sphereTwoTimesCircle_of_oriented_opposite_slabs)

universe u

theorem exists_spatial_neck_sphereTwoTimesCircle_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [ConnectedSpace M] [CompactSpace M]
          (g : SmoothRiemannianMetric I3 M),
          DifferentialGeometry.Topology.Manifold.SmoothOrientation I3 M →
          (∀ x : M, Nonempty (SpatialNeck g eps x)) →
          Nonempty (Diffeomorph I3 ((𝓡 2).prod (𝓡 1)) M
            DifferentialGeometry.Topology.SphereTwoTimesCircle ∞) := by
  obtain ⟨eta, heta, htubes⟩ := exists_spatial_neck_two_cylinders_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ g o hall
  let p : M := Classical.choice inferInstance
  obtain ⟨initial⟩ := hall p
  obtain ⟨P, A, η, κ, hP, hA, hlower, hzero, hone, hmeet, hcover⟩ :=
    htubes eps heps M g p initial hall
  have hboundary : A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
      P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
      P '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) ∪ P '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) := by
    rw [hmeet]
    rintro x ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    rcases ht with ht | ht
    · have : t = 0 := ht
      subst t
      exact Or.inl ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    · have : t = 1 := ht
      subst t
      exact Or.inr ⟨(q, 1), ⟨mem_univ _, rfl⟩, rfl⟩
  exact nonempty_diffeomorph_sphereTwoTimesCircle_of_oriented_opposite_slabs
      o A P η κ hA hP hzero hone hboundary (_root_.Set.union_comm _ _ ▸ hcover)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_sphereTwoTimesCircle_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_sphereTwoTimesCircle_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_sphereTwoTimesCircle_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_sphereTwoTimesCircle_tolerance

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.Topology

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem exists_spatial_neck_standard_factor_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ M : ConnectedClosedOrientedManifold.{u} 3,
        ∀ g : SmoothRiemannianMetric (𝓡 3) M.Carrier,
          (∀ x : M.Carrier, Nonempty (SpatialNeck g eps x)) → isStandardFactor M := by
  obtain ⟨eta, heta, hprod⟩ := exists_spatial_neck_sphereTwoTimesCircle_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M g hall
  let o : Manifold.SmoothOrientation (𝓡 3) M.Carrier :=
    Manifold.smoothOrientationOfManifoldOrientation (𝓡 3) (by simpa using M.orientation)
  obtain ⟨D⟩ := hprod eps heps M.Carrier g o hall
  exact isStandardFactor_of_diffeomorph_sphereTwoTimesCircle M D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_spatial_neck_standard_factor_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_spatial_neck_standard_factor_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_spatial_neck_standard_factor_tolerance ``Submission.DifferentialGeometry.Topology.exists_spatial_neck_standard_factor_tolerance

end DifferentialGeometry.Topology
