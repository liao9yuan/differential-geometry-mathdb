import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Area
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Basic
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Gauss
import Submission.DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Frame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ENNReal _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem preimage_gBall
    (g : SmoothRiemannianMetric I M) (x : M) (R : Real) :
    (normalFrame (I := I) (E := E) g x) ⁻¹'
        gBall (I := I) g x R =
      ball (0 : E) R := by
  ext w
  simp only [_root_.Set.mem_preimage, gBall, _root_.Set.mem_ofPred_eq, _root_.Metric.mem_ball, dist_zero_right]
  rw [normalFrame_sqrt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.preimage_gBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.preimage_gBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.preimage_gBall ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.preimage_gBall

section Measure

variable [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expJacobian_normal_int
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (x : M) (K : Set E) :
    (∫⁻ v in K,
        ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E))) =
      ∫⁻ w in (normalFrame (I := I) (E := E) g x) ⁻¹' K,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x
              (normalFrame (I := I) (E := E) g x w))
            (fun i t =>
              intrinsicJacobi (I := I) g hEnorm x
                (normalFrame (I := I) (E := E) g x w)
                ((normalBasis (I := I) g x) i) t)
            1)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  classical
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    normalBasis (I := I) g x
  let L : E ≃L[Real] E := normalFrame (I := I) (E := E) g x
  let Dn : E → Real := fun v =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x v)
      (fun i t => intrinsicJacobi (I := I) g hEnorm x v (b' i) t) 1
  have hD (v : E) :
      ENNReal.ofReal |b.det b'| *
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v) =
        ENNReal.ofReal (Dn v) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg (b.det b'))]
    congr 1
    change |b.det b'| * expJacobianDensity (I := I) g hEnorm x v =
      curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm x v)
        (fun i t => intrinsicJacobi (I := I) g hEnorm x v (b' i) t) 1
    exact (jacobianDens_basis (I := I) g hEnorm x v b b').symm
  have hbasis :
      (∫⁻ v in K,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
    calc
      _ = ∫⁻ v in K,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂b.addHaar := by rfl
      _ = ∫⁻ v in K,
          ENNReal.ofReal |b.det b'| *
            ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂b'.addHaar := by
            rw [← Module.Basis.det_smul_addHaar b b',
              _root_.MeasureTheory.setLIntegral_smul_measure]
            exact
              (_root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
            apply _root_.MeasureTheory.lintegral_congr
            exact hD
  have hbmap :
      (stdOrthonormalBasis Real E).toBasis.map L.toLinearEquiv = b' := by
    ext i
    change normalFrame (I := I) (E := E) g x
        ((stdOrthonormalBasis Real E) i) =
      normalBasis (I := I) g x i
    exact normalFrame_basis (I := I) g x i
  have hmap :
      Measure.map L (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) = b'.addHaar := by
    calc
      _ = Measure.map L (stdOrthonormalBasis Real E).toBasis.addHaar := by
            rw [(stdOrthonormalBasis Real E).addHaar_eq_volume]
      _ = ((stdOrthonormalBasis Real E).toBasis.map
          L.toLinearEquiv).addHaar :=
            Module.Basis.map_addHaar _ _
      _ = b'.addHaar := congrArg Module.Basis.addHaar hbmap
  have hmp : _root_.MeasureTheory.MeasurePreserving L (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) b'.addHaar :=
    ⟨L.continuous.measurable, hmap⟩
  rw [hbasis]
  change (∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar) =
    ∫⁻ w in L ⁻¹' K, ENNReal.ofReal (Dn (L w)) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
  exact (hmp.setLIntegral_comp_preimage_emb
    L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun v => ENNReal.ofReal (Dn v)) K).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.expJacobian_normal_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.expJacobian_normal_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.expJacobian_normal_int ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.expJacobian_normal_int

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem framed_mul_le_area
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (x : M) {U : Set E} (hU : MeasurableSet U)
    {S : Set M} (hS : MeasurableSet S) {m : ENat}
    (hloc : IsLocalHomeomorphOn
      (intrinsicFramedExp (I := I) g hEnorm x) U)
    (hcount : ∀ y ∈ S, m ≤
      {w : E | w ∈ U ∧
        intrinsicFramedExp (I := I) g hEnorm x w = y}.encard) :
    m.toENNReal *
        riemannianVolumeMeasure (I := I) (M := M) g S
      ≤ ∫⁻ w in U,
          ENNReal.ofReal
            (curveDensity (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm x
                (normalFrame (I := I) (E := E) g x w))
              (fun i t =>
                intrinsicJacobi (I := I) g hEnorm x
                  (normalFrame (I := I) (E := E) g x w)
                  ((normalBasis (I := I) g x) i) t)
              1)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  classical
  let L : E ≃L[Real] E :=
    (normalFrame (I := I) (E := E) g x).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) x)
  have hL (w : E) :
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L w) =
        normalFrame (I := I) g x w := by
    change (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (normalFrame (I := I) g x w)) = normalFrame (I := I) g x w
    exact ContinuousLinearEquiv.symm_apply_apply _ _
  let K : Set E := L '' U
  have hK : MeasurableSet K := by
    exact
      L.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hU
  have hLloc :
      IsLocalHomeomorphOn (fun w : E => L w) U :=
    L.toHomeomorph.isLocalHomeomorph.isLocalHomeomorphOn.mono
      (Set.subset_univ U)
  have hcomp :
      IsLocalHomeomorphOn
        ((fun v : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)) ∘
          fun w : E => L w) U := by
    rw [show ((fun v : E =>
        expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ∘ fun w : E => L w) =
      intrinsicFramedExp (I := I) g hEnorm x by
        funext w
        change expMapIntrinsic (I := I) g hEnorm x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L w)) =
          intrinsicFramedExp (I := I) g hEnorm x w
        calc
          _ = expMapIntrinsic (I := I) g hEnorm x
              (normalFrame (I := I) g x w) :=
            congrArg (expMapIntrinsic (I := I) g hEnorm x) (hL w)
          _ = intrinsicFramedExp (I := I) g hEnorm x w :=
            (intrinsicFrame_apply (I := I) g hEnorm x w).symm]
    exact hloc
  have hraw :
      IsLocalHomeomorphOn
        (fun v : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)) K := by
    simpa only [K] using hcomp.of_comp_right hLloc
  have hcountRaw :
      ∀ y ∈ S, m ≤
        {v : E | v ∈ K ∧
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v) = y}.encard := by
    intro y hy
    let A : Set E := {w : E | w ∈ U ∧
      intrinsicFramedExp (I := I) g hEnorm x w = y}
    let B : Set E := {v : E | v ∈ K ∧
      expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v) = y}
    let emb : A ↪ B :=
      { toFun := fun w =>
          ⟨L w.1, ⟨⟨w.1, w.2.1, rfl⟩, by
            change expMapIntrinsic (I := I) g hEnorm x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L w.1)) = y
            calc
              _ = expMapIntrinsic (I := I) g hEnorm x
                  (normalFrame (I := I) g x w.1) :=
                congrArg (expMapIntrinsic (I := I) g hEnorm x) (hL w.1)
              _ = y := by simpa only [intrinsicFrame_apply] using w.2.2⟩⟩
        inj' := by
          intro w z hwz
          apply Subtype.ext
          apply L.injective
          exact congrArg Subtype.val hwz }
    exact
      (hcount y hy).trans (by
        simpa only [A, B] using emb.encard_le)
  have harea :=
    riemVol_mul_le_area (I := I) g hEnorm x hK hS
      hraw hcountRaw
  have hpre : L ⁻¹' K = U := by
    exact Set.preimage_image_eq U L.injective
  have hpreRaw : (normalFrame (I := I) (E := E) g x) ⁻¹' K = U := by
    change L ⁻¹' K = U
    exact hpre
  rw [expJacobian_normal_int (I := I) g hEnorm x K, hpreRaw] at harea
  simpa only [L] using harea

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.framed_mul_le_area then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.framed_mul_le_area"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.framed_mul_le_area ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.framed_mul_le_area

end Measure

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
