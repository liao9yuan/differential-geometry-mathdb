import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Manifold _root_.Set _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped _root_.Manifold _root_.ContDiff _root_.Simplicial
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel ∞ N]

private theorem orientation_map_comp_native
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℝ A] [Module ℝ B] [Module ℝ C]
    (a : A ≃ₗ[ℝ] B) (b : B ≃ₗ[ℝ] C) (o : Orientation ℝ A (Fin 3)) :
    Orientation.map (Fin 3) b (Orientation.map (Fin 3) a o) =
      Orientation.map (Fin 3) (a.trans b) o := by
  induction o using Quotient.inductionOn with
  | h o => rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientation_map_comp_native
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientation_map_comp_native target :: scope.openDecls } }

theorem orientedChartSimplex_map
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (he : PreservesTangentOrientation oM oN e)
    (x : M) (S : OrientedChartSimplex oM x) :
    ∃ S' : OrientedChartSimplex oN (e x), S'.simplex = (⟨e, e.continuous⟩ : C(M, N)).comp S.simplex := by
  let chart : OpenPartialHomeomorph N ThreeSpace :=
    e.symm.toHomeomorph.toOpenPartialHomeomorph.trans S.chart
  have hchart : MDifferentiableAt ThreeModel ThreeModel chart (e x) := by
    have h := S.differentiableAt.comp_of_eq (e x)
      (e.symm.contMDiff.contMDiffAt.mdifferentiableAt (by decide)) (e.symm_apply_apply x)
    exact h
  obtain ⟨hebij, hepositive⟩ := he.2 x
  have hcomp : mfderiv ThreeModel ThreeModel S.chart x =
      (mfderiv ThreeModel ThreeModel chart (e x)).comp
        (mfderiv ThreeModel ThreeModel e x) := by
    have h := mfderiv_comp x hchart
      (e.contMDiff.contMDiffAt.mdifferentiableAt (by decide))
    have hfun : (fun z : M => chart (e z)) = S.chart := by
      funext z
      change S.chart (e.symm (e z)) = S.chart z
      rw [e.symm_apply_apply]
    change mfderiv ThreeModel ThreeModel (fun z : M => chart (e z)) x = _ at h
    rw [hfun] at h
    exact h
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel chart (e x)) := by
    apply (Function.Bijective.of_comp_iff _ hebij).mp
    change Function.Bijective ((mfderiv ThreeModel ThreeModel chart (e x)).comp
      (mfderiv ThreeModel ThreeModel e x))
    rw [← hcomp]
    exact S.derivative_bijective
  have hpositive : Orientation.map (Fin 3)
      (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel chart (e x)).toLinearMap hbij)
        (oN.orientation (e x)) = standardThreeOrientation := by
    unfold PreservesTangentOrientationAt at hepositive
    have hlinear :
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel e x).toLinearMap hebij).trans
          (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel chart (e x)).toLinearMap hbij) =
        LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel S.chart x).toLinearMap
          S.derivative_bijective := by
      ext v
      exact (DFunLike.congr_fun hcomp v).symm
    let a := LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel e x).toLinearMap hebij
    let b := LinearEquiv.ofBijective
      (mfderiv ThreeModel ThreeModel chart (e x)).toLinearMap hbij
    exact (congrArg (Orientation.map (Fin 3) b) hepositive.symm).trans
      ((orientation_map_comp_native a b (oM.orientation x)).trans
        ((congrArg (fun f => Orientation.map (Fin 3) f (oM.orientation x)) hlinear).trans
          S.positive))
  let S' : OrientedChartSimplex oN (e x) :=
    { chart := chart
      center_mem := by
        change e x ∈ Set.univ ∩ (fun y => e.symm y) ⁻¹' S.chart.source
        refine ⟨Set.mem_univ _, ?_⟩
        change e.symm (e x) ∈ S.chart.source
        simpa only [e.symm_apply_apply] using S.center_mem
      differentiableAt := hchart
      derivative_bijective := hbij
      positive := hpositive
      radius := S.radius
      radius_pos := S.radius_pos
      simplex_inside := by
        intro q
        change S.chart (e.symm (e x)) + S.radius • positiveTetrahedron q ∈
          S.chart.target ∩ S.chart.symm ⁻¹' Set.univ
        exact ⟨by simpa only [e.symm_apply_apply] using S.simplex_inside q, Set.mem_univ _⟩ }
  refine ⟨S', ?_⟩
  ext q
  change e (S.chart.symm (S.chart (e.symm (e x)) + S.radius • positiveTetrahedron q)) =
    e (S.chart.symm (S.chart x + S.radius • positiveTetrahedron q))
  rw [e.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedChartSimplex_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedChartSimplex_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedChartSimplex_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedChartSimplex_map

omit [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel ∞ N] in
private theorem degree_simplex_chain_map (f : C(M, N)) {n : ℕ}
    (s : C(stdSimplex ℝ (Fin (n + 1)), M)) :
    singularSimplexChain s ≫ (integralChainsFunctor.map (TopCat.ofHom f)).f n =
      singularSimplexChain (f.comp s) := by
  exact SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of M))
    (TopCat.toSSet.obj (TopCat.of N)) (TopCat.toSSet.map (TopCat.ofHom f))
    integralCoefficients ((TopCat.toSSetObjEquiv (TopCat.of M) (.op ⦋n⦌)).symm s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.degree_simplex_chain_map
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.degree_simplex_chain_map target :: scope.openDecls } }

omit [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel ∞ N] in
private theorem diffeomorph_punctured_mapsTo (e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (x : M) :
    Set.MapsTo e ({x}ᶜ) ({e x}ᶜ) := by
  intro z hz
  exact fun h => hz (e.injective h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.diffeomorph_punctured_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.diffeomorph_punctured_mapsTo target :: scope.openDecls } }

private theorem local_simplex_chain_natural
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (x : M)
    (S : OrientedChartSimplex oM x) (S' : OrientedChartSimplex oN (e x))
    (hS : S'.simplex = (⟨e, e.continuous⟩ : C(M, N)).comp S.simplex) :
    S.relativeChain ≫ (relativeIntegralChainMap ⟨e, e.continuous⟩ ({x}ᶜ) ({e x}ᶜ)
      (diffeomorph_punctured_mapsTo e x)).f 3 = S'.relativeChain := by
  let F := integralChainsFunctor.map (TopCat.ofHom (⟨e, e.continuous⟩ : C(M, N)))
  let G := relativeIntegralChainMap (⟨e, e.continuous⟩ : C(M, N)) ({x}ᶜ) ({e x}ᶜ)
    (diffeomorph_punctured_mapsTo e x)
  have hc : cokernel.π (subspaceChainInclusion M ({x}ᶜ)) ≫ G =
      F ≫ cokernel.π (subspaceChainInclusion N ({e x}ᶜ)) := cokernel.π_desc _ _ _
  have hc3 := congrArg (fun k => k.f 3) hc
  change (cokernel.π (subspaceChainInclusion M ({x}ᶜ))).f 3 ≫ G.f 3 =
    F.f 3 ≫ (cokernel.π (subspaceChainInclusion N ({e x}ᶜ))).f 3 at hc3
  unfold OrientedChartSimplex.relativeChain
  rw [Category.assoc, hc3, ← Category.assoc]
  change (singularSimplexChain S.simplex ≫
    (integralChainsFunctor.map (TopCat.ofHom (⟨e, e.continuous⟩ : C(M, N)))).f 3) ≫ _ = _
  rw [degree_simplex_chain_map, ← hS]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.local_simplex_chain_natural
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.local_simplex_chain_natural target :: scope.openDecls } }

private theorem local_simplex_class_natural
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (x : M)
    (S : OrientedChartSimplex oM x) (S' : OrientedChartSimplex oN (e x))
    (hS : S'.simplex = (⟨e, e.continuous⟩ : C(M, N)).comp S.simplex) :
    relativeIntegralHomologyMap 3 (⟨e, e.continuous⟩ : C(M, N)) ({x}ᶜ) ({e x}ᶜ)
      (diffeomorph_punctured_mapsTo e x) S.localClass = S'.localClass := by
  let F := relativeIntegralChainMap (⟨e, e.continuous⟩ : C(M, N)) ({x}ᶜ) ({e x}ᶜ)
    (diffeomorph_punctured_mapsTo e x)
  have hc :
      (RelativeIntegralChains M ({x}ᶜ)).liftCycles S.relativeChain 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) S.relativeChain_boundary ≫
        (RelativeIntegralChains M ({x}ᶜ)).homologyπ 3 ≫ HomologicalComplex.homologyMap F 3 =
      (RelativeIntegralChains N ({e x}ᶜ)).liftCycles S'.relativeChain 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) S'.relativeChain_boundary ≫
        (RelativeIntegralChains N ({e x}ᶜ)).homologyπ 3 := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      HomologicalComplex.liftCycles_comp_cyclesMap]
    apply congrArg (fun k : integralCoefficients ⟶ (RelativeIntegralChains N ({e x}ᶜ)).cycles 3 =>
      k ≫ (RelativeIntegralChains N ({e x}ᶜ)).homologyπ 3)
    apply (_root_.CategoryTheory.cancel_mono ((RelativeIntegralChains N ({e x}ᶜ)).iCycles 3)).1
    simp only [HomologicalComplex.liftCycles_i]
    exact local_simplex_chain_natural oM oN e x S S' hS
  exact congrArg (fun k : integralCoefficients ⟶ LocalIntegralHomology N (e x) 3 => k (ULift.up 1)) hc

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.local_simplex_class_natural
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.local_simplex_class_natural target :: scope.openDecls } }


theorem localOrientationClass_natural_diffeomorph
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (he : PreservesTangentOrientation oM oN e) (x : M) :
    relativeIntegralHomologyMap 3 (⟨e, e.continuous⟩ : C(M, N)) ({x}ᶜ) ({e x}ᶜ)
      (diffeomorph_punctured_mapsTo e x) (localOrientationClass oM x) =
      localOrientationClass oN (e x) := by
  obtain ⟨S⟩ := exists_orientedChartSimplex oM x
  obtain ⟨S', hS⟩ := orientedChartSimplex_map oM oN e he x S
  rw [← localOrientationClass_spec oM x S, ← localOrientationClass_spec oN (e x) S']
  exact local_simplex_class_natural oM oN e x S S' hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_diffeomorph

variable [T2Space M] [CompactSpace M] [T2Space N] [CompactSpace N]


theorem fundamentalClass_natural_diffeomorph
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (he : PreservesTangentOrientation oM oN e) :
    integralHomologyMap 3 (⟨e, e.continuous⟩ : C(M, N)) (fundamentalClass oM) =
      fundamentalClass oN := by
  apply (exists_unique_fundamentalClass oN).unique
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hc := absoluteToRelative_naturality 3 (⟨e, e.continuous⟩ : C(M, N))
      ({x}ᶜ) ({e x}ᶜ) (diffeomorph_punctured_mapsTo e x)
    have hv := congrArg (fun k : IntegralHomology M 3 ⟶ LocalIntegralHomology N (e x) 3 =>
      k (fundamentalClass oM)) hc
    have hn := localOrientationClass_natural_diffeomorph oM oN e he x
    change relativeIntegralHomologyMap 3 (⟨e, e.continuous⟩ : C(M, N)) ({x}ᶜ) ({e x}ᶜ)
      (diffeomorph_punctured_mapsTo e x)
      (absoluteToRelative M ({x}ᶜ) 3 (fundamentalClass oM)) = _ at hv
    rw [fundamentalClass_local] at hv
    exact hv.symm.trans hn
  · exact fundamentalClass_local oN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClass_natural_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClass_natural_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClass_natural_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClass_natural_diffeomorph

variable [ConnectedSpace M] [ConnectedSpace N]

omit [ConnectedSpace M] in
theorem orientedDegree_diffeomorph
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (he : PreservesTangentOrientation oM oN e) :
    orientedDegree oM oN (⟨e, e.continuous⟩ : C(M, N)) = 1 := by
  apply (orientedDegree_eq_iff oM oN (⟨e, e.continuous⟩ : C(M, N)) 1).mpr
  simpa only [one_smul] using fundamentalClass_natural_diffeomorph oM oN e he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedDegree_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedDegree_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedDegree_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedDegree_diffeomorph

omit [ConnectedSpace M] in
theorem integralHomologyMap_fundamentalClass_eq_iff_orientedDegree_eq_one
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N) (f : C(M, N)) :
    integralHomologyMap 3 f (fundamentalClass oM) = fundamentalClass oN ↔
      orientedDegree oM oN f = 1 := by
  rw [orientedDegree_eq_iff, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralHomologyMap_fundamentalClass_eq_iff_orientedDegree_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralHomologyMap_fundamentalClass_eq_iff_orientedDegree_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralHomologyMap_fundamentalClass_eq_iff_orientedDegree_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralHomologyMap_fundamentalClass_eq_iff_orientedDegree_eq_one

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
