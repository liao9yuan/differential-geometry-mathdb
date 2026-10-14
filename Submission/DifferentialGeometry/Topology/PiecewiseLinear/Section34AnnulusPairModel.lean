import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusUnionTorus
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularRegionFilling
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphInto.isPLTorus_invFunOn_of_annulus_pair
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P D A : Set (EuclideanSpace ℝ (Fin 3))}
    {u v w : EuclideanSpace ℝ (Fin 3) → M} (hu : IsPLHomeomorphInto 3 u P)
    (hv : IsPLHomeomorphInto 3 v D) (hw : IsPLHomeomorphInto 3 w A)
    {J : Set E} {K : Set F} (hJ : IsPLSphere 1 J) (hK : IsPLSphere 1 K)
    {ρ : E × ℝ → EuclideanSpace ℝ (Fin 3)}
    {σ : F × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ _root_.Set.Icc (0 : ℝ) 1) D)
    (hσ : IsPLHomeomorphOn σ (K ×ˢ _root_.Set.Icc (0 : ℝ) 1) A)
    (hDP : v '' D ⊆ u '' P) (hAP : w '' A ⊆ u '' P)
    (hmeet : v '' D ∩ w '' A = (v ∘ ρ) '' (J ×ˢ {(0 : ℝ), 1}))
    (hends : (v ∘ ρ) '' (J ×ˢ {(0 : ℝ), 1}) =
      (w ∘ σ) '' (K ×ˢ {(0 : ℝ), 1})) :
    IsPLTorus (Function.invFunOn u P '' (v '' D ∪ w '' A)) := by
  let τ := Function.invFunOn u P
  have hright : _root_.Set.RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτ : _root_.Set.InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hDpoly : IsPolyhedron D := hρ.image_eq ▸
    (hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  have hApoly : IsPolyhedron A := hσ.image_eq ▸
    (hK.isPolyhedron.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hσ.isPiecewiseAffineOn hσ.bijOn.injOn
  have hρ' : IsPLHomeomorphOn ((τ ∘ v) ∘ ρ) (J ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      (τ '' (v '' D)) := by
    rw [← _root_.Set.image_comp]
    exact hρ.trans (hv.isPLHomeomorphOn_invFunOn_comp hDpoly hu hDP)
  have hσ' : IsPLHomeomorphOn ((τ ∘ w) ∘ σ) (K ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      (τ '' (w '' A)) := by
    rw [← _root_.Set.image_comp]
    exact hσ.trans (hw.isPLHomeomorphOn_invFunOn_comp hApoly hu hAP)
  have hinter : τ '' (v '' D) ∩ τ '' (w '' A) =
      ((τ ∘ v) ∘ ρ) '' (J ×ˢ {(0 : ℝ), 1}) := by
    rw [← hτ.image_inter hDP hAP, hmeet]
    simp only [_root_.Set.image_comp]
  have hrims : ((τ ∘ v) ∘ ρ) '' (J ×ˢ {(0 : ℝ), 1}) =
      ((τ ∘ w) ∘ σ) '' (K ×ˢ {(0 : ℝ), 1}) := by
    simpa only [_root_.Set.image_comp] using congrArg (_root_.Set.image τ) hends
  have htorus := isPLTorus_union_of_isPLHomeomorphOn_annuli hJ hK hρ' hσ'
    hinter (hinter.trans hrims)
  simpa only [_root_.Set.image_union] using htorus

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.isPLTorus_invFunOn_of_annulus_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.isPLTorus_invFunOn_of_annulus_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.isPLTorus_invFunOn_of_annulus_pair ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.isPLTorus_invFunOn_of_annulus_pair

theorem IsPLHomeomorphInto.exists_manifold_filling_of_annulus_pair_in_torus
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P D A : Set (EuclideanSpace ℝ (Fin 3))}
    {u v w : EuclideanSpace ℝ (Fin 3) → M} (hu : IsPLHomeomorphInto 3 u P)
    (hv : IsPLHomeomorphInto 3 v D) (hw : IsPLHomeomorphInto 3 w A)
    (N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite N.faces]
    (hN : IsCombinatorialManifoldWithBoundary 3 N) (hNP : N.space ⊆ P)
    (hsolid : IsTopologicalSolidTorus N.space)
    {J : Set E} {K : Set F} (hJ : IsPLSphere 1 J) (hK : IsPLSphere 1 K)
    {ρ : E × ℝ → EuclideanSpace ℝ (Fin 3)}
    {σ : F × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ _root_.Set.Icc (0 : ℝ) 1) D)
    (hσ : IsPLHomeomorphOn σ (K ×ˢ _root_.Set.Icc (0 : ℝ) 1) A)
    (hDN : v '' D ⊆ u '' N.space) (hAN : w '' A ⊆ u '' N.space)
    (hmeet : v '' D ∩ w '' A = (v ∘ ρ) '' (J ×ˢ {(0 : ℝ), 1}))
    (hends : (v ∘ ρ) '' (J ×ˢ {(0 : ℝ), 1}) =
      (w ∘ σ) '' (K ×ˢ {(0 : ℝ), 1})) :
    ∃ R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      u '' frontier R.space = v '' D ∪ w '' A ∧
      closure (interior R.space) = R.space ∧ IsConnected (interior R.space) ∧
      IsConnected R.spaceᶜ ∧ R.space ⊆ N.space := by
  have hDP := hDN.trans (_root_.Set.image_mono hNP)
  have hAP := hAN.trans (_root_.Set.image_mono hNP)
  have htorus := hu.isPLTorus_invFunOn_of_annulus_pair hv hw hJ hK hρ hσ hDP hAP
    hmeet hends
  have hsub : Function.invFunOn u P '' (v '' D ∪ w '' A) ⊆ N.space := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := _root_.Set.union_subset hDN hAN hx
    rw [hu.injOn.leftInvOn_invFunOn (hNP hy)]
    exact hy
  obtain ⟨R, hRfin, hR, hfront, hreg, hint, hext, hRN⟩ :=
    htorus.exists_manifold_filling_in_solid_torus hN hsolid hsub
  refine ⟨R, hRfin, hR, ?_, hreg, hint, hext, hRN⟩
  rw [hfront, _root_.Set.image_image]
  exact (_root_.Set.image_congr fun x hx =>
    hu.injOn.bijOn_image.invOn_invFunOn.2 (_root_.Set.union_subset hDP hAP hx)).trans (_root_.Set.image_id' _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_manifold_filling_of_annulus_pair_in_torus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_manifold_filling_of_annulus_pair_in_torus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_manifold_filling_of_annulus_pair_in_torus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_manifold_filling_of_annulus_pair_in_torus

end DifferentialGeometry.Topology.PiecewiseLinear
