import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientHomeomorph
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThreeManifold
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import Submission.DifferentialGeometry.Geometry.Metric.ProjectiveSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Filter _root_.Topology

namespace DifferentialGeometry.Geometry

local instance _root_.Submission.DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry ``Submission.DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry

noncomputable def cylinderAntipodalQuotientDiffeomorph :
    CylinderAntipodalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real),
      (𝓡 2).prod 𝓘(Real, Real)⟯ RealProjectivePlane × Real where
  toEquiv := cylinderAntipodalQuotientHomeomorph.toEquiv
  contMDiff_toFun := by
    apply cylinderAntipodalQuotientMap_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
      cylinderAntipodalQuotientMap_surjective
    change ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞
      (fun x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real =>
        (realProjectivePlaneQuotientMap x.1, x.2))
    exact ((realProjectiveSpaceQuotientMap_isLocalDiffeomorph
      (E := EuclideanSpace Real (Fin 3)) (n := 2)).contMDiff.comp
      contMDiff_fst).prodMk contMDiff_snd
  contMDiff_invFun := by
    rintro ⟨y, s⟩
    obtain ⟨x, rfl⟩ := realProjectivePlaneQuotientMap_surjective y
    let hlocal := realProjectiveSpaceQuotientMap_isLocalDiffeomorph
      (E := EuclideanSpace Real (Fin 3)) (n := 2) x
    have hinv : ContMDiffAt ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2) ∞
        (fun z : RealProjectivePlane × Real => hlocal.localInverse z.1)
        (realProjectivePlaneQuotientMap x, s) :=
      hlocal.localInverse_contMDiffAt.comp
        (f := fun z : RealProjectivePlane × Real => z.1)
        (realProjectivePlaneQuotientMap x, s) contMDiffAt_fst
    have hsmooth := cylinderAntipodalQuotientMap_isLocalDiffeomorph.contMDiff.contMDiffAt.comp
      (realProjectivePlaneQuotientMap x, s) (hinv.prodMk contMDiffAt_snd)
    apply hsmooth.congr_of_eventuallyEq
    have hevent := hlocal.localInverse_eventuallyEq_right.comp_tendsto
      (continuous_fst.tendsto (realProjectivePlaneQuotientMap x, s))
    filter_upwards [hevent] with z hz
    change cylinderAntipodalQuotientHomeomorph.symm z =
      cylinderAntipodalQuotientMap (hlocal.localInverse z.1, z.2)
    apply cylinderAntipodalQuotientHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, cylinderAntipodalQuotientHomeomorph_apply]
    exact Prod.ext hz.symm rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph

@[simp] theorem cylinderAntipodalQuotientDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalQuotientDiffeomorph (cylinderAntipodalQuotientMap x) =
      (realProjectivePlaneQuotientMap x.1, x.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_apply ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_apply

@[simp] theorem cylinderAntipodalQuotientDiffeomorph_symm_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real) :
    cylinderAntipodalQuotientDiffeomorph.symm (realProjectivePlaneQuotientMap x, s) =
      cylinderAntipodalQuotientMap (x, s) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_symm_apply

noncomputable def cylinderDiagonalQuotientDiffeomorph :
    CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), 𝓡 3⟯
      PuncturedRealProjectiveThreeSpace where
  toEquiv := cylinderDiagonalQuotientHomeomorph.toEquiv
  contMDiff_toFun := by
    apply cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
      cylinderDiagonalQuotientMap_surjective
    apply (ContMDiff.subtypeVal_comp_iff
      (⟨{q : RealProjectiveThreeSpace | q ≠ realProjectiveThreeSpacePuncture},
        isOpen_compl_singleton⟩ : TopologicalSpace.Opens RealProjectiveThreeSpace) _).mp
    change ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 3) ∞
      (fun x => realProjectiveSpaceQuotientMap
        (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture x).1)
    let _ : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) := ⟨by simp⟩
    exact (realProjectiveSpaceQuotientMap_isLocalDiffeomorph
      (E := EuclideanSpace Real (Fin 4)) (n := 3)).contMDiff.comp
      ((contMDiff_subtype_val (U := ⟨_, isOpen_threeSphereAwayFromRealProjectivePuncture⟩)).comp
        twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture.contMDiff)
  contMDiff_invFun := by
    intro y
    let _ : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) := ⟨by simp⟩
    obtain ⟨z, hz⟩ := realProjectiveSpaceQuotientMap_surjective y.1
    let z' : threeSphereAwayFromRealProjectivePuncture := ⟨z, by
      change realProjectiveSpaceQuotientMap z ≠ realProjectiveThreeSpacePuncture
      rw [hz]
      exact y.2⟩
    have hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
        (fun z : threeSphereAwayFromRealProjectivePuncture => realProjectiveSpaceQuotientMap z.1) :=
      isLocalDiffeomorph_restrict_open
        (⟨_, isOpen_threeSphereAwayFromRealProjectivePuncture⟩ :
          TopologicalSpace.Opens (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1))
        (realProjectiveSpaceQuotientMap_isLocalDiffeomorph.isLocalDiffeomorphOn _)
    let hlocal := hp z'
    have hv : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        (Subtype.val : PuncturedRealProjectiveThreeSpace → RealProjectiveThreeSpace) y :=
      (contMDiff_subtype_val (U :=
        ⟨{q : RealProjectiveThreeSpace | q ≠ realProjectiveThreeSpacePuncture},
          isOpen_compl_singleton⟩)).contMDiffAt
    have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        (fun q : PuncturedRealProjectiveThreeSpace => hlocal.localInverse q.1) y := by
      have hl := hlocal.localInverse_contMDiffAt
      change ContMDiffAt (𝓡 3) (𝓡 3) ∞ hlocal.localInverse
        (realProjectiveSpaceQuotientMap z) at hl
      rw [hz] at hl
      exact hl.comp y hv
    have hsmooth := cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff.contMDiffAt.comp y
      (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture.symm.contMDiff.contMDiffAt.comp y hi)
    apply hsmooth.congr_of_eventuallyEq
    have hevent := hlocal.localInverse_eventuallyEq_right
    change (fun q => realProjectiveSpaceQuotientMap (hlocal.localInverse q).1) =ᶠ[
      𝓝 (realProjectiveSpaceQuotientMap z)] id at hevent
    rw [hz] at hevent
    have hevent' := hevent.comp_tendsto (continuous_subtype_val.tendsto y)
    filter_upwards [hevent'] with q hq
    change cylinderDiagonalQuotientHomeomorph.symm q =
      cylinderDiagonalQuotientMap
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.symm
          (hlocal.localInverse q.1))
    rw [← cylinderDiagonalQuotientHomeomorph_symm_apply]
    congr 1
    exact Subtype.ext hq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph

@[simp] theorem cylinderDiagonalQuotientDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalQuotientDiffeomorph (cylinderDiagonalQuotientMap x) =
      ⟨realProjectiveSpaceQuotientMap
          (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture x).1,
        (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture x).2⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_apply ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_apply

@[simp] theorem cylinderDiagonalQuotientDiffeomorph_symm_apply
    (z : threeSphereAwayFromRealProjectivePuncture) :
    cylinderDiagonalQuotientDiffeomorph.symm
        ⟨realProjectiveSpaceQuotientMap z.1, z.2⟩ =
      cylinderDiagonalQuotientMap
        (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture.symm z) :=
  cylinderDiagonalQuotientHomeomorph_symm_apply z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_symm_apply

theorem cylinderAntipodalQuotientDiffeomorph_potential
    (x : RealProjectivePlane × Real) :
    cylinderAntipodalQuotientPotential (cylinderAntipodalQuotientDiffeomorph.symm x) =
      1 + x.2 ^ 2 / 4 := by
  obtain ⟨y, hy⟩ := realProjectivePlaneQuotientMap_surjective x.1
  have heq : x = (realProjectivePlaneQuotientMap y, x.2) := Prod.ext hy.symm rfl
  rw [heq, cylinderAntipodalQuotientDiffeomorph_symm_apply,
    cylinderAntipodalQuotientPotential_apply, roundThreeCylinderShrinkerPotential_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_potential ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_potential

theorem cylinderDiagonalQuotientDiffeomorph_potential
    (z : threeSphereAwayFromRealProjectivePuncture) :
    cylinderDiagonalQuotientPotential
        (cylinderDiagonalQuotientDiffeomorph.symm
          ⟨realProjectiveSpaceQuotientMap z.1, z.2⟩) =
      1 + (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture.symm z).2 ^ 2 / 4 := by
  rw [cylinderDiagonalQuotientDiffeomorph_symm_apply,
    cylinderDiagonalQuotientPotential_apply, roundThreeCylinderShrinkerPotential_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_potential ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_potential

private theorem roundProjectiveQuotientMap_inner
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (v w : TangentSpace (𝓡 2) x) :
    (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner
      (realProjectivePlaneQuotientMap x)
      (mfderiv (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap x v)
      (mfderiv (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap x w) =
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x v w := by
  have hround := congrArg
    (fun k : SmoothRiemannianMetric (𝓡 2) (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) =>
      k.inner x v w)
    (localPullMetric_roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
  exact hround

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.roundProjectiveQuotientMap_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.roundProjectiveQuotientMap_inner target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem sphereRealProduct_inner
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace Real (Fin 2)) M]
    [T2Space M]
    [IsManifold (𝓡 2) ∞ M]
    (g : SmoothRiemannianMetric (𝓡 2) M) (h : SmoothRiemannianMetric 𝓘(Real, Real) Real)
    (x : M × Real) (v w : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    (g.prod h).inner x v w = g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 := by
  exact SmoothRiemannianMetric.prod_inner g h x v w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereRealProduct_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereRealProduct_inner target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem cylinderProjectiveQuotientMap_inner
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    ((scaleMetric 2 (by norm_num)
        (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
        (euclideanMetric (E := Real))).inner
      (realProjectivePlaneQuotientMap x.1, x.2)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        (Prod.map realProjectivePlaneQuotientMap id) x v)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        (Prod.map realProjectivePlaneQuotientMap id) x w) =
      roundThreeCylinderShrinkerMetric.inner x v w := by
  change EuclideanSpace Real (Fin 2) × Real at v w
  have hp : MDifferentiable (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap :=
    (realProjectiveSpaceQuotientMap_isLocalDiffeomorph
      (E := EuclideanSpace Real (Fin 3)) (n := 2)).mdifferentiable (by simp)
  erw [mfderiv_prodMap hp.mdifferentiableAt mdifferentiable_id.mdifferentiableAt,
    sphereRealProduct_inner, roundThreeCylinderShrinkerMetric, sphereRealProduct_inner]
  change (scaleMetric 2 (by norm_num)
      (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).inner
      (realProjectivePlaneQuotientMap x.1)
      (mfderiv (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap x.1 v.1)
      (mfderiv (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap x.1 w.1) +
      (euclideanMetric (E := Real)).inner x.2
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real) id x.2 v.2)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real) id x.2 w.2) =
    roundTwoSphereShrinkerMetric.inner x.1 v.1 w.1 +
      (euclideanMetric (E := Real)).inner x.2 v.2 w.2
  erw [scaleMetric_inner]
  erw [roundProjectiveQuotientMap_inner]
  erw [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
    roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2), mfderiv_id]
  norm_num
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderProjectiveQuotientMap_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderProjectiveQuotientMap_inner target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem cylinderAntipodalQuotientDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetricCross
      ((scaleMetric 2 (by norm_num)
        (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
        (euclideanMetric (E := Real))) cylinderAntipodalQuotientDiffeomorph =
      cylinderAntipodalQuotientMetric := by
  apply localPullMetric_injective_of_surjective cylinderAntipodalQuotientMap
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_surjective
  rw [localPullMetric_cylinderAntipodalQuotientMetric]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hchain :
      mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        (Prod.map realProjectivePlaneQuotientMap id) x =
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        cylinderAntipodalQuotientDiffeomorph (cylinderAntipodalQuotientMap x)).comp
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
          cylinderAntipodalQuotientMap x) :=
    mfderiv_comp x
      (cylinderAntipodalQuotientDiffeomorph.contMDiff.mdifferentiableAt (by simp))
      (cylinderAntipodalQuotientMap_isLocalDiffeomorph.contMDiff.mdifferentiableAt (by simp))
  have hv := DFunLike.congr_fun hchain v
  have hw := DFunLike.congr_fun hchain w
  rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner]
  have h := cylinderProjectiveQuotientMap_inner x v w
  rw [hv, hw] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_pullbackMetric ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientDiffeomorph_pullbackMetric

end DifferentialGeometry.Geometry

end

section
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

private theorem exists_diffeomorph_orbitQuotient
    : ∃ e : CylinderDiagonalQuotient ≃ₘ⟮
        (𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        DifferentialGeometry.Geometry.CylinderDiagonalQuotient, ∀ p,
      e (proj p) = DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap p := by
  obtain ⟨e, he⟩ := exists_homeomorph_orbitQuotient
  obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
    proj isLocalDiffeomorph_proj surjective_proj
    DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap
    DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph
    e he
  exact ⟨D, fun p => (congrFun hD (proj p)).trans (he p)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_diffeomorph_orbitQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_diffeomorph_orbitQuotient target :: scope.openDecls } }

theorem exists_diffeomorph_puncturedRealProjectiveThreeSpace :
    ∃ e : CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), 𝓡 3⟯
        PuncturedRealProjectiveThreeSpace,
      ∀ p : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real,
        e (proj p) =
          ⟨realProjectiveSpaceQuotientMap
            (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture p).1,
            (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture p).2⟩ := by
  obtain ⟨e, he⟩ := exists_diffeomorph_orbitQuotient
  refine ⟨e.trans DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph, ?_⟩
  intro p
  change DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph
    (e (proj p)) = _
  rw [he p]
  exact DifferentialGeometry.Geometry.cylinderDiagonalQuotientDiffeomorph_apply p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_diffeomorph_puncturedRealProjectiveThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_diffeomorph_puncturedRealProjectiveThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_diffeomorph_puncturedRealProjectiveThreeSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_diffeomorph_puncturedRealProjectiveThreeSpace

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

end

end
