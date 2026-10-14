import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifold.supported_image_preserving_carrier {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S K N : Geometry.SimplicialComplex ℝ E)
    [Finite S.faces] [Finite K.faces] [Finite N.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (hKS : K.space ⊆ interior S.space) (hgen : CarriesFundamentalGroupOnto K.space S.space)
    {Φ : E → E} (hΦ : IsPLHomeomorphOn Φ _root_.Set.univ _root_.Set.univ)
    (hfix : _root_.Set.EqOn Φ id (interior S.space)ᶜ) (hNspace : N.space = Φ '' K.space) :
    IsCombinatorialManifold 2 N ∧ IsConnected N.space ∧ IsCompact N.space ∧
      N.space ⊆ interior S.space ∧ CarriesFundamentalGroupOnto N.space S.space ∧
      Φ '' S.space = S.space ∧ Φ '' interior S.space = interior S.space := by
  let H : E ≃ₜ E :=
    { toFun := Φ
      invFun := Function.invFunOn Φ _root_.Set.univ
      left_inv := fun x => hΦ.bijOn.invOn_invFunOn.1 (_root_.Set.mem_univ x)
      right_inv := fun x => hΦ.bijOn.invOn_invFunOn.2 (_root_.Set.mem_univ x)
      continuous_toFun := continuousOn_univ.mp hΦ.isPiecewiseAffineOn.continuousOn
      continuous_invFun := continuousOn_univ.mp hΦ.isPiecewiseAffineOn_invFunOn.continuousOn }
  have hHS : Φ '' S.space = S.space :=
    image_eq_of_homeomorph_eqOn_compl_of_subset H hfix interior_subset
  have hHint : Φ '' interior S.space = interior S.space :=
    (H.image_interior S.space).trans (congrArg interior hHS)
  have hKN : IsPLHomeomorphOn Φ K.space N.space := by
    rw [hNspace]
    exact hΦ.restrict (isPolyhedron_space K) (_root_.Set.subset_univ K.space)
  have hNconn : IsConnected N.space := by
    rw [hNspace]
    exact hconn.image H H.continuous.continuousOn
  have hNint : N.space ⊆ interior S.space := by
    rw [hNspace, ← hHint]
    exact _root_.Set.image_mono hKS
  have hNgen := hgen.image_of_compact (isPolyhedron_space S).isCompact
    H.continuous.continuousOn H.injective.injOn
  change CarriesFundamentalGroupOnto (Φ '' K.space) (Φ '' S.space) at hNgen
  rw [hHS, ← hNspace] at hNgen
  exact ⟨hK.of_isPLHomeomorphOn hKN, hNconn, (isPolyhedron_space N).isCompact,
    hNint, hNgen, hHS, hHint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.supported_image_preserving_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.supported_image_preserving_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.supported_image_preserving_carrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.supported_image_preserving_carrier

theorem IsCombinatorialManifold.exists_supported_image_preserving_carrier {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S K : Geometry.SimplicialComplex ℝ E) [Finite S.faces] [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (hKS : K.space ⊆ interior S.space) (hgen : CarriesFundamentalGroupOnto K.space S.space)
    {Φ : E → E} (hΦ : IsPLHomeomorphOn Φ _root_.Set.univ _root_.Set.univ)
    (hfix : _root_.Set.EqOn Φ id (interior S.space)ᶜ) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧ N.space = Φ '' K.space ∧
      IsCombinatorialManifold 2 N ∧ IsConnected N.space ∧ IsCompact N.space ∧
      N.space ⊆ interior S.space ∧ CarriesFundamentalGroupOnto N.space S.space ∧
      Φ '' S.space = S.space ∧ Φ '' interior S.space = interior S.space := by
  have hΦK := hΦ.isPiecewiseAffineOn.mono_of_isPolyhedron
    (isPolyhedron_space K) (_root_.Set.subset_univ K.space)
  obtain ⟨N, hNfin, hNspace, -⟩ := exists_isPLHomeomorphOn_image K hΦK
    (hΦ.bijOn.injOn.mono (_root_.Set.subset_univ K.space))
  let _ : Finite N.faces := hNfin.to_subtype
  exact ⟨N, hNfin, hNspace,
    hK.supported_image_preserving_carrier S K N hconn hKS hgen hΦ hfix hNspace⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_supported_image_preserving_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_supported_image_preserving_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_supported_image_preserving_carrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_supported_image_preserving_carrier

end DifferentialGeometry.Topology.PiecewiseLinear
