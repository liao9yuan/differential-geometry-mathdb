import Submission.DifferentialGeometry.Topology.ThreeManifold.LocalOrientation
import Submission.DifferentialGeometry.Topology.Homology.SimplexDegreeNaturality
import Submission.DifferentialGeometry.Tensor.LinearAlgebra.Orientation
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Submission.DifferentialGeometry.Topology.Homology.LocalGerm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.Pointwise

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Topology

universe u
variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel ∞ N]

private theorem exists_tetrahedron_radius_mem {U : Set ThreeSpace} (hU : IsOpen U)
    {y : ThreeSpace} (hy : y ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : stdSimplex ℝ (Fin 4),
      y + r • positiveTetrahedron q ∈ U := by
  have h := eventually_singleton_add_smul_subset
    (𝕜 := ℝ) (x := y) (s := _root_.Set.range positiveTetrahedron)
    ((isCompact_range positiveTetrahedron.continuous).isBounded)
    (hU.mem_nhds hy)
  obtain ⟨ε, hε, hεmem⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro q
  have hsubset := hεmem (ε / 2) (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      using half_lt_self hε)
  apply hsubset
  exact Set.add_mem_add (_root_.Set.mem_singleton y)
    (Set.smul_mem_smul_set (_root_.Set.mem_range_self q))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tetrahedron_radius_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tetrahedron_radius_mem target :: scope.openDecls } }


theorem exists_orientedChartSimplex_chart_source_subset (o : TangentOrientationSection M)
    (x : M) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ S : OrientedChartSimplex o x, S.chart.source ⊆ U := by
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨S⟩ := exists_orientedChartSimplex o x
  let e := S.chart.restrOpen V hV
  have hx : x ∈ e.source := ⟨S.center_mem, hxV⟩
  obtain ⟨r, hr, hins⟩ := exists_tetrahedron_radius_mem e.open_target (e.map_source hx)
  refine ⟨{
    chart := e
    center_mem := hx
    differentiableAt := S.differentiableAt
    derivative_bijective := S.derivative_bijective
    positive := S.positive
    radius := r
    radius_pos := hr
    simplex_inside := hins }, ?_⟩
  exact fun _ hy => hVU hy.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientedChartSimplex_chart_source_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientedChartSimplex_chart_source_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientedChartSimplex_chart_source_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientedChartSimplex_chart_source_subset

theorem exists_orientedChartSimplex_range_subset (o : TangentOrientationSection M)
    (x : M) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ S : OrientedChartSimplex o x, _root_.Set.range S.simplex ⊆ U := by
  obtain ⟨S, hS⟩ := exists_orientedChartSimplex_chart_source_subset o x hU
  refine ⟨S, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact hS (S.chart.map_target (S.simplex_inside q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientedChartSimplex_range_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientedChartSimplex_range_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientedChartSimplex_range_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientedChartSimplex_range_subset

theorem orientedChartSimplex_partial_map
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    {n : ℕ∞ω} (Φ : PartialDiffeomorph ThreeModel ThreeModel M N n) (hn : n ≠ 0)
    (x : M) (hx : x ∈ Φ.source)
    (hebij : Function.Bijective (mfderiv ThreeModel ThreeModel Φ x))
    (hpos : PreservesTangentOrientationAt oM oN Φ x hebij)
    (S : OrientedChartSimplex oM x) (hS : ∀ q, S.simplex q ∈ Φ.source) :
    ∃ S' : OrientedChartSimplex oN (Φ x),
      ∀ q, S'.simplex q = Φ (S.simplex q) := by
  let e := Φ.toOpenPartialHomeomorph
  let chart : OpenPartialHomeomorph N ThreeSpace := e.symm.trans S.chart
  have hchart : MDifferentiableAt ThreeModel ThreeModel chart (Φ x) := by
    have hinv : MDifferentiableAt ThreeModel ThreeModel e.symm (Φ x) := by
      exact Φ.symm.mdifferentiableAt hn (e.map_source hx)
    exact S.differentiableAt.comp_of_eq (Φ x) hinv (e.left_inv hx)
  have hcomp : mfderiv ThreeModel ThreeModel S.chart x =
      (mfderiv ThreeModel ThreeModel chart (Φ x)).comp
        (mfderiv ThreeModel ThreeModel Φ x) := by
    have h := mfderiv_comp x hchart (Φ.mdifferentiableAt hn hx)
    have hfun : (fun z : M => chart (Φ z)) =ᶠ[𝓝 x] S.chart := by
      filter_upwards [Φ.open_source.mem_nhds hx] with z hz
      change S.chart (e.symm (e z)) = S.chart z
      rw [e.left_inv hz]
    change mfderiv ThreeModel ThreeModel (fun z : M => chart (Φ z)) x = _ at h
    rw [hfun.mfderiv_eq] at h
    exact h
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel chart (Φ x)) := by
    apply (Function.Bijective.of_comp_iff _ hebij).mp
    change Function.Bijective ((mfderiv ThreeModel ThreeModel chart (Φ x)).comp
      (mfderiv ThreeModel ThreeModel Φ x))
    rw [← hcomp]
    exact S.derivative_bijective
  have hpositive : Orientation.map (Fin 3)
      (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel chart (Φ x)).toLinearMap hbij)
      (oN.orientation (Φ x)) = standardThreeOrientation := by
    unfold PreservesTangentOrientationAt at hpos
    have hlinear :
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel Φ x).toLinearMap
          hebij).trans
          (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel chart (Φ x)).toLinearMap hbij) =
        LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel S.chart x).toLinearMap
          S.derivative_bijective := by
      ext v
      exact (DFunLike.congr_fun hcomp v).symm
    let a := LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel Φ x).toLinearMap
      hebij
    let b := LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel chart (Φ x)).toLinearMap hbij
    exact (congrArg (Orientation.map (Fin 3) b) hpos.symm).trans
      ((DifferentialGeometry.orientation_map_trans a b (oM.orientation x)).symm.trans
        ((congrArg (fun f => Orientation.map (Fin 3) f (oM.orientation x)) hlinear).trans
          S.positive))
  have hcenter : Φ x ∈ chart.source := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ S.chart.source
    simpa only [e.left_inv hx] using S.center_mem
  let S' : OrientedChartSimplex oN (Φ x) := {
    chart := chart
    center_mem := hcenter
    differentiableAt := hchart
    derivative_bijective := hbij
    positive := hpositive
    radius := S.radius
    radius_pos := S.radius_pos
    simplex_inside := by
      intro q
      change S.chart (e.symm (e x)) + S.radius • positiveTetrahedron q ∈
        S.chart.target ∩ S.chart.symm ⁻¹' e.source
      rw [e.left_inv hx]
      exact ⟨S.simplex_inside q, hS q⟩ }
  refine ⟨S', ?_⟩
  intro q
  change e (S.chart.symm (S.chart (e.symm (e x)) + S.radius • positiveTetrahedron q)) =
    e (S.chart.symm (S.chart x + S.radius • positiveTetrahedron q))
  rw [e.left_inv hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedChartSimplex_partial_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedChartSimplex_partial_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedChartSimplex_partial_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedChartSimplex_partial_map

private theorem simplex_face_ne (o : TangentOrientationSection M) (x : M)
    (S : OrientedChartSimplex o x) (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    S.simplex (SimplexDegree.orientedSimplexFace i q) ≠ x := by
  intro heq
  have he := congrArg S.chart heq
  change S.chart (S.chart.symm
    (S.chart x + S.radius • positiveTetrahedron (SimplexDegree.orientedSimplexFace i q))) = S.chart x at he
  rw [S.chart.right_inv (S.simplex_inside (SimplexDegree.orientedSimplexFace i q))] at he
  have hs : S.radius • positiveTetrahedron (SimplexDegree.orientedSimplexFace i q) = 0 := by
    have h := congrArg (fun y : ThreeSpace => y - S.chart x) he
    simpa only [add_sub_cancel_left, sub_self] using h
  apply SimplexDegree.standardTetrahedronSimplex_face_ne_zero.{u} i q
  exact congrArg ULift.up ((smul_eq_zero.mp hs).resolve_left (ne_of_gt S.radius_pos))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplex_face_ne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplex_face_ne target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
theorem OrientedChartSimplex.localClass_natural_openPartialHomeomorph
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (e : OpenPartialHomeomorph M N) (x : M) (hx : x ∈ e.source)
    (S : OrientedChartSimplex oM x) (S' : OrientedChartSimplex oN (e x))
    (hS : ∀ q, S.simplex q ∈ e.source)
    (hmap : ∀ q, S'.simplex q = e (S.simplex q)) :
    let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
    let _ : T1Space N := ChartedSpace.t1Space ThreeSpace N
    (integralLocalHomologyOpenPartialHomeomorphIso 3 e x hx).hom.hom S.localClass =
      S'.localClass := by
  let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
  let _ : T1Space N := ChartedSpace.t1Space ThreeSpace N
  have h := SimplexDegree.integralLocalHomologyOpenPartialHomeomorphIso_simplexLocalClass
    e x hx S.simplex hS (simplex_face_ne oM x S)
  have hmap' : (⟨fun q => e (S.simplex q),
      e.continuousOn.comp_continuous S.simplex.continuous hS⟩ : C(stdSimplex ℝ (Fin 4), N)) =
      S'.simplex := ContinuousMap.ext fun q => (hmap q).symm
  simp only [hmap'] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedChartSimplex.localClass_natural_openPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedChartSimplex.localClass_natural_openPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedChartSimplex.localClass_natural_openPartialHomeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedChartSimplex.localClass_natural_openPartialHomeomorph

theorem localOrientationClass_natural_partialDiffeomorph
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    {n : ℕ∞ω} (Φ : PartialDiffeomorph ThreeModel ThreeModel M N n) (hn : n ≠ 0)
    (x : M) (hx : x ∈ Φ.source)
    (hpos : PreservesTangentOrientationAt oM oN Φ x
      ((Φ.isLocalDiffeomorphAt ThreeModel ThreeModel n hx).mfderivToContinuousLinearEquiv hn).bijective) :
    let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
    let _ : T1Space N := ChartedSpace.t1Space ThreeSpace N
    (integralLocalHomologyOpenPartialHomeomorphIso 3
      Φ.toOpenPartialHomeomorph x hx).hom.hom (localOrientationClass oM x) =
      localOrientationClass oN (Φ x) := by
  let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
  let _ : T1Space N := ChartedSpace.t1Space ThreeSpace N
  obtain ⟨S, hS⟩ := exists_orientedChartSimplex_range_subset oM x
    (Φ.open_source.mem_nhds hx)
  have hsrc : ∀ q, S.simplex q ∈ Φ.source := fun q => hS ⟨q, rfl⟩
  obtain ⟨S', hmap⟩ := orientedChartSimplex_partial_map oM oN Φ hn x hx _ hpos S hsrc
  rw [← localOrientationClass_spec oM x S,
    ← localOrientationClass_spec oN (Φ x) S']
  exact OrientedChartSimplex.localClass_natural_openPartialHomeomorph
    oM oN Φ.toOpenPartialHomeomorph x hx S S' hsrc hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_partialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_partialDiffeomorph

theorem localOrientationClass_natural_of_isLocalDiffeomorphAt
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    {n : ℕ∞ω} (hn : n ≠ 0) (f : C(M, N)) (x : M)
    (hloc : IsLocalDiffeomorphAt ThreeModel ThreeModel n f x)
    (hf : _root_.Set.MapsTo f ({x}ᶜ : Set M) ({f x}ᶜ : Set N))
    (hpos : PreservesTangentOrientationAt oM oN f x
      (hloc.mfderivToContinuousLinearEquiv hn).bijective) :
    integralRelativeHomologyMap 3 f hf (localOrientationClass oM x) =
      localOrientationClass oN (f x) := by
  let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
  let _ : T1Space N := ChartedSpace.t1Space ThreeSpace N
  have hebij := (hloc.mfderivToContinuousLinearEquiv hn).bijective
  obtain ⟨Φ, hx, hfe⟩ := hloc
  have hex : f x = Φ x := hfe hx
  have hnear : (f : M → N) =ᶠ[𝓝 x] Φ :=
    Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hx) hfe
  have hder := hnear.mfderiv_eq (I := ThreeModel) (I' := ThreeModel)
  have hΦbij : Function.Bijective (mfderiv ThreeModel ThreeModel Φ x) := by
    rw [← hder]
    exact hebij
  have hΦpos : PreservesTangentOrientationAt oM oN Φ x hΦbij := by
    unfold PreservesTangentOrientationAt at hpos ⊢
    have htransport (y : N) (hy : f x = y)
        (D : TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel y)
        (hD : D = mfderiv ThreeModel ThreeModel f x) (hDbij : Function.Bijective D) :
        Orientation.map (Fin 3) (LinearEquiv.ofBijective D.toLinearMap hDbij)
          (oM.orientation x) = oN.orientation y := by
      subst y
      subst D
      exact hpos
    exact htransport (Φ x) hex (mfderiv ThreeModel ThreeModel Φ x) hder.symm hΦbij
  have hnat := localOrientationClass_natural_partialDiffeomorph
    oM oN Φ hn x hx hΦpos
  have hmap := integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph
    3 f Φ.toOpenPartialHomeomorph x Φ.source Φ.open_source hx (Subset.refl _) hfe
    (show _root_.Set.MapsTo f ({x}ᶜ : Set M) ({Φ x}ᶜ : Set N) by simpa only [← hex] using hf)
  have hclass := (LinearMap.congr_fun hmap (localOrientationClass oM x)).trans hnat
  have htransfer (y : N) (hxy : f x = y)
      (hfy : _root_.Set.MapsTo f ({x}ᶜ : Set M) ({y}ᶜ : Set N))
      (hc : integralRelativeHomologyMap 3 f hfy (localOrientationClass oM x) =
        localOrientationClass oN y) :
      integralRelativeHomologyMap 3 f hf (localOrientationClass oM x) =
        localOrientationClass oN (f x) := by
    subst y
    exact hc
  exact htransfer (Φ x) hex _ hclass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_of_isLocalDiffeomorphAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_of_isLocalDiffeomorphAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_of_isLocalDiffeomorphAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_natural_of_isLocalDiffeomorphAt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
