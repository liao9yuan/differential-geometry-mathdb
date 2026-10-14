import Submission.DifferentialGeometry.Topology.ThreeManifold.ChartLocalOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.OrientedChartNeighborhood
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalCompactHomology
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ManifoldFundamentalClass

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

omit [T2Space M] in
private theorem localOrientationClass_chart_normalization_of_chart_eq
    {o : TangentOrientationSection M} {x : M} (S : OrientedChartSimplex o x) (e : OpenPartialHomeomorph M ThreeSpace)
    (he : S.chart = e) (hx : x ∈ e.source) :
    let eU := e.trans
      (Homeomorph.ulift (X := ThreeSpace) : liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.toOpenPartialHomeomorph
    let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
    integralRelativeHomologyMap 3 (toContinuousMap (Homeomorph.subRight (eU x)))
      (show _root_.Set.MapsTo (Homeomorph.subRight (eU x)) ({eU x}ᶜ : Set (liftedSphereSpace.{u} 1))
        ({0}ᶜ : Set (liftedSphereSpace.{u} 1)) from fun _ hz => sub_ne_zero.mpr hz)
      ((integralLocalHomologyOpenPartialHomeomorphIso 3 eU x
        (show x ∈ eU.source from ⟨hx, Set.mem_univ _⟩)).hom.hom
        (localOrientationClass o x)) = euclideanStandardSimplexClass.{u} := by
  subst e
  exact S.localOrientationClass_chart_normalization

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_chart_normalization_of_chart_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_chart_normalization_of_chart_eq target :: scope.openDecls } }


private theorem localOrientationClass_locally_realized_of_chart_neighborhood
    (o : TangentOrientationSection M) (p : M)
    (e : OpenPartialHomeomorph M ThreeSpace) (U : Set M) (hU : IsOpen U) (hpU : p ∈ U)
    (hchart : ∀ y ∈ U, ∃ S : OrientedChartSimplex o y, S.chart = e) :
    ∃ L : Set M, IsCompact L ∧ p ∈ interior L ∧
      ∃ a : integralRelativeHomology 3 Lᶜ, ∀ y (hy : y ∈ L),
        integralRelativeHomologyMap 3 (ContinuousMap.id M)
          (show Lᶜ ⊆ ({y}ᶜ : Set M) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy)) a = localOrientationClass o y := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  let eU := e.trans
    (Homeomorph.ulift (X := ThreeSpace) : liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.toOpenPartialHomeomorph
  obtain ⟨S, hS⟩ := hchart p hpU
  have hp : p ∈ eU.source := by
    exact ⟨hS ▸ S.center_mem, Set.mem_univ _⟩
  obtain ⟨K, hKs, hK, hpK, a, ha, _⟩ := exists_compact_chart_neighborhood_class 3 eU p hp
    euclideanStandardSimplexClass.{u}
  obtain ⟨L, hL, hpL, hLU⟩ := exists_compact_between isCompact_singleton
    (isOpen_interior.inter hU) (singleton_subset_iff.mpr ⟨hpK, hpU⟩)
  have hLK : L ⊆ K := hLU.trans (inter_subset_left.trans interior_subset)
  let hKL : _root_.Set.MapsTo (ContinuousMap.id M) Kᶜ Lᶜ := compl_subset_compl.mpr hLK
  let b := integralRelativeHomologyMap 3 (ContinuousMap.id M) hKL a
  refine ⟨L, hL, hpL (_root_.Set.mem_singleton p), b, ?_⟩
  intro y hy
  obtain ⟨T, hT⟩ := hchart y (hLU hy).2
  let J := integralLocalHomologyOpenPartialHomeomorphIso 3 eU y (hKs (hLK hy))
  let Z := integralRelativeHomologyHomeomorphIso 3 (Homeomorph.subRight (eU y))
    ({eU y}ᶜ : Set (liftedSphereSpace.{u} 1)) ({0}ᶜ : Set (liftedSphereSpace.{u} 1))
    (fun _ hz => sub_ne_zero.mpr hz)
    (fun z hz heq => by
      apply hz
      change z + eU y = eU y at heq
      exact add_right_cancel (heq.trans (zero_add _).symm))
  apply (J ≪≫ Z).toLinearEquiv.injective
  change Z.hom.hom (J.hom.hom _) = Z.hom.hom (J.hom.hom (localOrientationClass o y))
  have hpoint := localOrientationClass_chart_normalization_of_chart_eq T e hT
    (show y ∈ e.source from (hKs (hLK hy)).1)
  rw [show Z.hom.hom (J.hom.hom (localOrientationClass o y)) =
    euclideanStandardSimplexClass.{u} from hpoint]
  let hLy : _root_.Set.MapsTo (ContinuousMap.id M) Lᶜ ({y}ᶜ : Set M) :=
    compl_subset_compl.mpr (singleton_subset_iff.mpr hy)
  have hcomp := LinearMap.congr_fun (integralRelativeHomologyMap_comp 3
    (ContinuousMap.id M) (ContinuousMap.id M) hKL hLy) a
  exact (congrArg (fun c => Z.hom.hom (J.hom.hom c)) hcomp.symm).trans (ha y (hLK hy))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_locally_realized_of_chart_neighborhood
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_locally_realized_of_chart_neighborhood target :: scope.openDecls } }

theorem localOrientationClass_locally_realized (o : TangentOrientationSection M) (p : M) :
    ∃ L : Set M, IsCompact L ∧ p ∈ interior L ∧
      ∃ a : integralRelativeHomology 3 Lᶜ, ∀ y (hy : y ∈ L),
        integralRelativeHomologyMap 3 (ContinuousMap.id M)
          (show Lᶜ ⊆ ({y}ᶜ : Set M) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy)) a = localOrientationClass o y := by
  obtain ⟨e, U, hU, hpU, hchart⟩ := exists_open_orientedChartSimplex o p
  exact localOrientationClass_locally_realized_of_chart_neighborhood o p e U hU hpU hchart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_locally_realized then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_locally_realized"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_locally_realized ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_locally_realized


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
