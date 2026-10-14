import Submission.DifferentialGeometry.Geometry.Metric.Cylinder.IsometryExtension
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialSplitting
import Submission.DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Rigidity
import Submission.DifferentialGeometry.Geometry.Operator.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.euclideanThreeFinrankFact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.euclideanThreeFinrankFact target :: scope.openDecls } }

private theorem tangent_cast_equiv_inner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    {z z' : M} (h : z = z') (D : V ≃L[Real] TangentSpace I z) (v w : V) :
    g.inner z (D v) (D w) = g.inner z' ((h ▸ D) v) ((h ▸ D) w) := by
  cases h
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.tangent_cast_equiv_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.tangent_cast_equiv_inner target :: scope.openDecls } }

private theorem tangent_cast_equiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    {z z' : M} (h : z = z') (D : V ≃L[Real] TangentSpace I z) (v : V) :
    D v = (h ▸ D) v := by
  cases h
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.tangent_cast_equiv_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.tangent_cast_equiv_apply target :: scope.openDecls } }

private theorem roundThreeCylinderShrinkerMetric_eq_product :
    roundThreeCylinderShrinkerMetric =
      (scaleMetric 2 (by norm_num)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
        (euclideanMetric (E := Real)) := by
  have hs : roundTwoSphereShrinkerMetric =
      scaleMetric 2 (by norm_num)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
      roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2)]
    norm_num
  rw [roundThreeCylinderShrinkerMetric, hs]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_eq_product
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_eq_product target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private theorem solitonModelCovering_cylinder_hessian
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {p : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → M}
    (hp : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f p)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    (1 / 2 : Real) * (u.2 * v.2) = Operator.hessFun (I := I) g f (p x)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) I p x u)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) I p x v) := by
  have hh := Operator.hessFun_localPull g p
    (solitonModelCovering_isLocalDiffeomorph hp) f x u v
  rw [← solitonModelCovering_metric_eq_localPull hp] at hh
  have hf : (f : M → Real) ∘ p = roundThreeCylinderShrinkerPotential :=
    (funext (solitonModelCovering_potential hp)).symm
  rw [hf, roundThreeCylinderShrinkerPotential_hessian] at hh
  change (1 / 2 : Real) * (v.2 * u.2) = _ at hh
  simpa only [mul_comm] using hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.solitonModelCovering_cylinder_hessian
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.solitonModelCovering_cylinder_hessian target :: scope.openDecls } }

theorem exists_coveringDeckGroup_apply_eq_of_solitonModelCovering_roundThreeCylinder
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {p : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → M}
    (hcover : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f p)
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} (hxy : p x = p y) :
    ∃ gamma : coveringDeckGroup p, gamma.1 x = y := by
  let _ : PreconnectedSpace (_root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 1)
  have hp := solitonModelCovering_isLocalDiffeomorph hcover
  let D (z : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
    hp.mfderivToContinuousLinearEquiv (by simp) z
  let Dy : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) y ≃L[Real] TangentSpace I (p x) :=
    hxy.symm ▸ D y
  let L := (D x).trans Dy.symm
  have hD (v) : D y (L v) = D x v :=
    (tangent_cast_equiv_apply hxy.symm (D y) (L v)).trans (Dy.apply_symm_apply _)
  have hL : ∀ u v,
      roundThreeCylinderShrinkerMetric.inner y (L u) (L v) =
        roundThreeCylinderShrinkerMetric.inner x u v := by
    intro u v
    rw [solitonModelCovering_metric hcover, solitonModelCovering_metric hcover]
    have heval : g.inner (p y) (D y (L u)) (D y (L v)) =
        g.inner (p x) (Dy (L u)) (Dy (L v)) :=
      tangent_cast_equiv_inner g hxy.symm (D y) (L u) (L v)
    change g.inner (p y) (D y (L u)) (D y (L v)) = _
    have hu : Dy (L u) = D x u := Dy.apply_symm_apply _
    have hv : Dy (L v) = D x v := Dy.apply_symm_apply _
    rw [heval, hu, hv]
    rfl
  have hsnd : ∀ u v, (L u).2 * (L v).2 = u.2 * v.2 := by
    intro u v
    have hx := solitonModelCovering_cylinder_hessian hcover x u v
    have hy := solitonModelCovering_cylinder_hessian hcover y (L u) (L v)
    change (1 / 2 : Real) * ((L u).2 * (L v).2) =
      Operator.hessFun (I := I) g f (p y) (D y (L u)) (D y (L v)) at hy
    erw [hD, hD, ← hxy] at hy
    change (1 / 2 : Real) * (u.2 * v.2) =
      Operator.hessFun (I := I) g f (p x) (D x u) (D x v) at hx
    linarith [hx, hy]
  obtain ⟨Φ, hΦ, hdΦ, hΦmetric⟩ := exists_diffeomorph_of_round_cylinder_tangent_isometry_preserving_vertical
    2 (by norm_num) x y L (by
      simpa only [← roundThreeCylinderShrinkerMetric_eq_product] using hL) hsnd
  have hΦmetric' : ∀ z u v,
      roundThreeCylinderShrinkerMetric.inner (Φ z)
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real)) Φ z u)
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real)) Φ z v) =
      roundThreeCylinderShrinkerMetric.inner z u v := by
    simpa only [← roundThreeCylinderShrinkerMetric_eq_product] using hΦmetric
  have hcomp : p ∘ Φ = p := by
    apply Riemannian.localIso_rigid roundThreeCylinderShrinkerMetric g
      (isLocalDiffeomorph_comp hp Φ.isLocalDiffeomorph) hp (p := x)
    · intro z u v
      rw [mfderiv_comp_apply z (hp.contMDiff.mdifferentiableAt (by simp))
        (Φ.contMDiff.mdifferentiableAt (by simp)),
        mfderiv_comp_apply z (hp.contMDiff.mdifferentiableAt (by simp))
        (Φ.contMDiff.mdifferentiableAt (by simp))]
      exact (hΦmetric' z u v).symm.trans (solitonModelCovering_metric hcover (Φ z) _ _)
    · exact solitonModelCovering_metric hcover
    · exact (congrArg p hΦ).trans hxy.symm
    · ext v
      rw [mfderiv_comp_apply x (hp.contMDiff.mdifferentiableAt (by simp))
        (Φ.contMDiff.mdifferentiableAt (by simp)), hΦ]
      erw [hdΦ]
      exact hD v
  exact ⟨⟨Φ.toEquiv, Φ.contMDiff.continuous, Φ.symm.contMDiff.continuous, congrFun hcomp⟩, hΦ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_coveringDeckGroup_apply_eq_of_solitonModelCovering_roundThreeCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_coveringDeckGroup_apply_eq_of_solitonModelCovering_roundThreeCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_coveringDeckGroup_apply_eq_of_solitonModelCovering_roundThreeCylinder ``Submission.DifferentialGeometry.Geometry.exists_coveringDeckGroup_apply_eq_of_solitonModelCovering_roundThreeCylinder

theorem solitonModelCovering_roundThreeCylinder_isQuotientCoveringMap
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {p : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → M}
    (hcover : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f p) :
    IsQuotientCoveringMap p (coveringDeckGroup p) := by
  let _ : PreconnectedSpace (_root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 1)
  exact isQuotientCoveringMap_coveringDeckGroup_of_fiber_transitive
    (solitonModelCovering_isCoveringMap hcover) (solitonModelCovering_surjective hcover)
    (fun hxy => exists_coveringDeckGroup_apply_eq_of_solitonModelCovering_roundThreeCylinder hcover hxy.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelCovering_roundThreeCylinder_isQuotientCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelCovering_roundThreeCylinder_isQuotientCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelCovering_roundThreeCylinder_isQuotientCoveringMap ``Submission.DifferentialGeometry.Geometry.solitonModelCovering_roundThreeCylinder_isQuotientCoveringMap

end DifferentialGeometry.Geometry
