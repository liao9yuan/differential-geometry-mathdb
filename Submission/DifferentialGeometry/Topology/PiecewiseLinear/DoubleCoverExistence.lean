/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CoveringTriangulation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DoubleCoverComplex
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.HomologyCocycle
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SimplicialBoolCocycle

variable {K : Geometry.SimplicialComplex ℝ E}

open _root_.Classical in
theorem finite_fiber [Finite K.faces] (ε : SimplicialBoolCocycle K) (x : K.space) :
    (ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {x}).Finite := by
  rw [← Set.finite_coe_iff]
  apply Nat.finite_of_card_ne_zero
  rw [ε.card_fiber]
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.finite_fiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.finite_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.finite_fiber ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.finite_fiber

open _root_.Classical in
theorem exists_lift_simplicialComplex [FiniteDimensional ℝ E] [Finite K.faces]
    (ε : SimplicialBoolCocycle K) :
    ∃ (N : ℕ)
      (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (e : K'.space ≃ₜ ε.toBoolCocycle.toFiberBundleCore.TotalSpace),
      K'.faces.Finite ∧
      (∀ q, ∀ hq : q ∈ K'.faces,
        ∃ t ∈ K.faces,
        ∃ A : EuclideanSpace ℝ (Fin N) →ᵃ[ℝ] E,
          (∀ x (hx : x ∈ convexHull ℝ (q : Set _)),
            ((ε.toBoolCocycle.toFiberBundleCore.proj
              (e ⟨x, K'.convexHull_subset_space hq hx⟩) : K.space) : E) = A x) ∧
          A '' convexHull ℝ (q : Set _) = convexHull ℝ (t : Set E)) ∧
      ∀ n, IsCombinatorialManifoldWithBoundary n K →
        IsCombinatorialManifoldWithBoundary n K' :=
  PiecewiseLinear.exists_lift_simplicialComplex K ε.isCoveringMap ε.finite_fiber

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.exists_lift_simplicialComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.exists_lift_simplicialComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.exists_lift_simplicialComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.exists_lift_simplicialComplex

open _root_.Classical in
theorem exists_connected_double_cover_complex [FiniteDimensional ℝ E]
    [Finite K.faces] [ConnectedSpace K.space]
    (ε : SimplicialBoolCocycle K) (hε : ¬ ε.IsCoboundary)
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary n K) :
    ∃ (N : ℕ)
      (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (_ : K'.space ≃ₜ ε.toBoolCocycle.toFiberBundleCore.TotalSpace),
      K'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary n K' ∧
      IsCoveringMap ε.toBoolCocycle.toFiberBundleCore.proj ∧
      (∀ x, Nat.card (ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {x}) = 2) ∧
      ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace := by
  obtain ⟨N, K', e, hfinite, -, hmanifold⟩ := ε.exists_lift_simplicialComplex
  exact ⟨N, K', e, hfinite, hmanifold n hK, ε.isCoveringMap,
    ε.card_fiber, ε.connectedSpace_iff.mpr hε⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.exists_connected_double_cover_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.exists_connected_double_cover_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.exists_connected_double_cover_complex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.exists_connected_double_cover_complex

end SimplicialBoolCocycle

open _root_.Classical in
theorem exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere
    {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    (K : Geometry.SimplicialComplex ℝ E₀) [Finite K.faces] [ConnectedSpace K.space]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hor : IsOrientable 3 K)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (hnot : ¬ IsPLSphere 2
      (connectedComponentComplex (boundaryComplex 3 K) c).space) :
    ∃ (ε : SimplicialBoolCocycle K)
      (N : ℕ)
      (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (_ : K'.space ≃ₜ ε.toBoolCocycle.toFiberBundleCore.TotalSpace),
      ¬ ε.IsCoboundary ∧
      K'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 K' ∧
      IsCoveringMap ε.toBoolCocycle.toFiberBundleCore.proj ∧
      (∀ x, Nat.card (ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {x}) = 2) ∧
      ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace := by
  have hconnected : IsConnected K.space :=
    isConnected_iff_connectedSpace.mpr inferInstance
  have hbetti := bettiNumber_one_pos_of_boundary_component_not_sphere
    (ZMod 2) K hK hor hconnected c hnot
  obtain ⟨ε, hε⟩ :=
    SimplicialBoolCocycle.exists_not_isCoboundary_of_bettiNumber_one_pos K hbetti
  obtain ⟨N, K', e, hfinite, hmanifold, hcover, hfiber, hconnected'⟩ :=
    ε.exists_connected_double_cover_complex hε hK
  exact ⟨ε, N, K', e, hε, hfinite, hmanifold, hcover, hfiber, hconnected'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere

open _root_.Classical in
theorem exists_connected_double_cover_complex_of_not_isOrientable
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [ConnectedSpace K.space]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hI4 : ¬ IsOrientable 3 K →
      ∃ ε : SimplicialBoolCocycle (barycentricSubdivision K), ¬ ε.IsCoboundary)
    (hnot : ¬ IsOrientable 3 K) :
    ∃ (ε : SimplicialBoolCocycle (barycentricSubdivision K))
      (N : ℕ)
      (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (_ : K'.space ≃ₜ ε.toBoolCocycle.toFiberBundleCore.TotalSpace),
      ¬ ε.IsCoboundary ∧
      K'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 K' ∧
      IsCoveringMap ε.toBoolCocycle.toFiberBundleCore.proj ∧
      (∀ x, Nat.card (ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {x}) = 2) ∧
      ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace := by
  let _ : ConnectedSpace (barycentricSubdivision K).space := by
    rw [(barycentricSubdivision_isSubdivision K).space_eq]
    infer_instance
  obtain ⟨ε, hε⟩ := hI4 hnot
  obtain ⟨N, K', e, hfinite, hmanifold, hcover, hfiber, hconnected⟩ :=
    ε.exists_connected_double_cover_complex hε hK.barycentricSubdivision
  exact ⟨ε, N, K', e, hε, hfinite, hmanifold, hcover, hfiber, hconnected⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_connected_double_cover_complex_of_not_isOrientable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_connected_double_cover_complex_of_not_isOrientable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_connected_double_cover_complex_of_not_isOrientable ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_connected_double_cover_complex_of_not_isOrientable

end DifferentialGeometry.Topology.PiecewiseLinear
