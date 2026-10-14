import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import Submission.DifferentialGeometry.Tensor.Coordinates.ModelBasis
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory _root_.Set _root_.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.ContDiff

private local instance euclideanMeasurableSpace (n : Nat) :
    MeasurableSpace (EuclideanSpace Real (Fin (n + 1))) := borel _

run_cmd do
  let target := ``Submission.euclideanMeasurableSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `euclideanMeasurableSpace target :: scope.openDecls } }
private local instance euclideanBorelSpace (n : Nat) :
    BorelSpace (EuclideanSpace Real (Fin (n + 1))) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.euclideanBorelSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `euclideanBorelSpace target :: scope.openDecls } }

namespace EuclideanSpace
open _root_.EuclideanSpace

open _root_.EuclideanSpace in
theorem measurePreserving_tail_prod_head (n : Nat) :
    _root_.MeasureTheory.MeasurePreserving
      (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i : Fin n => x i.succ), x 0))
      volume ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (Fin n → Real)).prod _root_.MeasureTheory.MeasureSpace.volume) := by
  have hsplit := _root_.MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Real) 0
  have hcoord : _root_.MeasureTheory.MeasurePreserving (EuclideanSpace.equiv (Fin (n + 1)) Real)
      volume (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (Fin (n + 1) → Real)) := by
    refine ⟨(EuclideanSpace.equiv (Fin (n + 1)) Real).continuous.measurable, ?_⟩
    rw [← (EuclideanSpace.basisFun (Fin (n + 1)) Real).addHaar_eq_volume,
      Module.Basis.map_addHaar]
    have hb : (EuclideanSpace.basisFun (Fin (n + 1)) Real).toBasis.map
        (EuclideanSpace.equiv (Fin (n + 1)) Real).toLinearEquiv =
        Pi.basisFun Real (Fin (n + 1)) := by
      apply Module.Basis.eq_of_apply_eq
      intro i
      ext j
      simp [Pi.single_apply]
    rw [hb, Module.Basis.addHaar_def, Module.Basis.parallelepiped_basisFun,
      _root_.MeasureTheory.addHaarMeasure_eq_volume_pi]
  have hswap := MeasureTheory.Measure.measurePreserving_swap
    (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure Real)) (ν := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (Fin n → Real)))
  convert hswap.comp (hsplit.comp hcoord) using 1
  funext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanSpace.measurePreserving_tail_prod_head then
    throwError "Refusing to shadow existing declaration EuclideanSpace.measurePreserving_tail_prod_head"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanSpace.measurePreserving_tail_prod_head ``Submission.EuclideanSpace.measurePreserving_tail_prod_head

open _root_.EuclideanSpace in
theorem map_tail_prod_head_volume (n : Nat) :
    Measure.map
      (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i : Fin n => x i.succ), x 0))
      volume = ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (Fin n → Real)).prod _root_.MeasureTheory.MeasureSpace.volume) :=
  (measurePreserving_tail_prod_head n).map_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanSpace.map_tail_prod_head_volume then
    throwError "Refusing to shadow existing declaration EuclideanSpace.map_tail_prod_head_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanSpace.map_tail_prod_head_volume ``Submission.EuclideanSpace.map_tail_prod_head_volume

end EuclideanSpace

namespace DifferentialGeometry.Analysis

private noncomputable def euclideanTailHead (n : Nat) :
    EuclideanSpace Real (Fin (n + 1)) ≃L[Real] ((Fin n → Real) × Real) :=
  (EuclideanSpace.equiv (Fin (n + 1)) Real).trans
    ((Fin.consEquivL Real (fun _ : Fin (n + 1) => Real)).symm.trans
      (ContinuousLinearEquiv.prodComm Real Real (Fin n → Real)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.euclideanTailHead
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.euclideanTailHead target :: scope.openDecls } }

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Integral.Measure

private local instance modelMeasurableSpace (V : Type*) [TopologicalSpace V] :
    MeasurableSpace V := borel V

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.modelMeasurableSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.modelMeasurableSpace target :: scope.openDecls } }
private local instance modelBorelSpace (V : Type*) [TopologicalSpace V] :
    BorelSpace V := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.modelBorelSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.modelBorelSpace target :: scope.openDecls } }

theorem modelHaar_eq_det_smul_volume
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    (b : OrthonormalBasis (Fin (Module.finrank Real V)) Real V) :
    modelHaar (E := V) = ENNReal.ofReal |(chartModelBasis V).det b.toBasis| •
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) := by
  rw [← b.addHaar_eq_volume]
  exact ((chartModelBasis V).det_smul_addHaar b.toBasis).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.modelHaar_eq_det_smul_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.modelHaar_eq_det_smul_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.modelHaar_eq_det_smul_volume ``Submission.DifferentialGeometry.Integral.Measure.modelHaar_eq_det_smul_volume

theorem modelHaar_addHaarScalarFactor_eq_abs_det
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    (b : OrthonormalBasis (Fin (Module.finrank Real V)) Real V) :
    (MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := V)) _root_.MeasureTheory.MeasureSpace.volume : Real) =
      |(chartModelBasis V).det b.toBasis| := by
  have h : modelHaar (E := V) =
      Real.toNNReal |(chartModelBasis V).det b.toBasis| • (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) :=
    modelHaar_eq_det_smul_volume b
  simp only [h, MeasureTheory.Measure.addHaarScalarFactor_smul,
    MeasureTheory.Measure.addHaarScalarFactor_self, smul_eq_mul, mul_one,
    Real.coe_toNNReal _ (abs_nonneg _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.modelHaar_addHaarScalarFactor_eq_abs_det then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.modelHaar_addHaarScalarFactor_eq_abs_det"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.modelHaar_addHaarScalarFactor_eq_abs_det ``Submission.DifferentialGeometry.Integral.Measure.modelHaar_addHaarScalarFactor_eq_abs_det

theorem modelHaarScalarFactor_mul_sqrt_det_toMatrix
    {V i : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [Fintype i] [DecidableEq i]
    (B : LinearMap.BilinForm Real V) (b : OrthonormalBasis i Real V) :
    (MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := V)) _root_.MeasureTheory.MeasureSpace.volume : Real) *
        Real.sqrt (LinearMap.BilinForm.toMatrix (chartModelBasis V) B).det =
      Real.sqrt (LinearMap.BilinForm.toMatrix b.toBasis B).det := by
  let e : i ≃ Fin (Module.finrank Real V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b.toBasis).symm
  have h := (B.sqrt_det_toMatrix_basis_change (chartModelBasis V) (b.reindex e).toBasis).symm
  rw [← modelHaar_addHaarScalarFactor_eq_abs_det (b.reindex e)] at h
  have hmatrix : LinearMap.BilinForm.toMatrix (b.reindex e).toBasis B =
      (LinearMap.BilinForm.toMatrix b.toBasis B).submatrix e.symm e.symm := by
    ext j k
    simp only [LinearMap.BilinForm.toMatrix_apply, OrthonormalBasis.reindex_toBasis,
      Module.Basis.reindex_apply, Matrix.submatrix_apply]
  rw [hmatrix, Matrix.det_submatrix_equiv_self] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_sqrt_det_toMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_sqrt_det_toMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_sqrt_det_toMatrix ``Submission.DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_sqrt_det_toMatrix

theorem modelHaarScalarFactor_mul_chartDensity
    {E i : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
    [Fintype i] [DecidableEq i]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (alpha x : M) (b : OrthonormalBasis i Real E) :
    (MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := E)) _root_.MeasureTheory.MeasureSpace.volume : Real) *
        chartDensity g alpha x =
      Real.sqrt (Matrix.of fun i j => g.inner x
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).symmL Real x (b i))
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).symmL Real x (b j))).det := by
  let L := (_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).symmL Real x
  let B := (g.inner x).toBilinForm.comp L.toLinearMap L.toLinearMap
  have h := modelHaarScalarFactor_mul_sqrt_det_toMatrix B b
  have hchart : LinearMap.BilinForm.toMatrix (chartModelBasis E) B =
      chartGramMatrix g alpha x := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, chartGramMatrix_apply]
    rfl
  rw [hchart] at h
  have horth : LinearMap.BilinForm.toMatrix b.toBasis B =
      Matrix.of (fun i j => g.inner x (L (b i)) (L (b j))) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [horth] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_chartDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_chartDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_chartDensity ``Submission.DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_chartDensity

section

private local instance euclideanIndexMeasurableSpace (i : Type*) :
    MeasurableSpace (EuclideanSpace Real i) := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.euclideanIndexMeasurableSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.euclideanIndexMeasurableSpace target :: scope.openDecls } }
private local instance euclideanIndexBorelSpace (i : Type*) :
    BorelSpace (EuclideanSpace Real i) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.euclideanIndexBorelSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.euclideanIndexBorelSpace target :: scope.openDecls } }

theorem modelHaarScalarFactor_mul_chartDensity_self_euclideanSpace
    {i : Type*} [Fintype i] [DecidableEq i]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real (EuclideanSpace Real i) H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    (MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real i)) _root_.MeasureTheory.MeasureSpace.volume : Real) * chartDensity g x x =
      Real.sqrt (Matrix.of fun j k => g.inner x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (EuclideanSpace.single j 1))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (EuclideanSpace.single k 1))).det := by
  have h := modelHaarScalarFactor_mul_chartDensity g x x (EuclideanSpace.basisFun i Real)
  rw [TangentBundle.symmL_trivializationAt (mem_chart_source H x),
    mfderivWithin_range_extChartAt_symm] at h
  convert h using 1
  congr 2
  ext j k
  simp only [Matrix.of_apply, EuclideanSpace.basisFun_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_chartDensity_self_euclideanSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_chartDensity_self_euclideanSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_chartDensity_self_euclideanSpace ``Submission.DifferentialGeometry.Integral.Measure.modelHaarScalarFactor_mul_chartDensity_self_euclideanSpace

end

theorem map_tail_prod_head_modelHaar (n : Nat) :
    MeasureTheory.Measure.map
      (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i : Fin n => x i.succ), x 0))
      (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) =
      MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) _root_.MeasureTheory.MeasureSpace.volume •
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (Fin n → Real)).prod _root_.MeasureTheory.MeasureSpace.volume) := by
  conv_lhs =>
    rw [(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).isAddLeftInvariant_eq_smul _root_.MeasureTheory.MeasureSpace.volume]
  rw [MeasureTheory.Measure.map_smul]
  congr 1
  exact EuclideanSpace.map_tail_prod_head_volume n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.map_tail_prod_head_modelHaar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.map_tail_prod_head_modelHaar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.map_tail_prod_head_modelHaar ``Submission.DifferentialGeometry.Integral.Measure.map_tail_prod_head_modelHaar

theorem map_tail_prod_head_modelHaar_restrict_half_space (n : Nat) (a : Real) :
    MeasureTheory.Measure.map
      (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i : Fin n => x i.succ), x 0))
      ((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict {x | a < x 0}) =
      MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) _root_.MeasureTheory.MeasureSpace.volume •
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (Fin n → Real)).prod (volume.restrict (_root_.Set.Ioi a))) := by
  let f : EuclideanSpace Real (Fin (n + 1)) → (Fin n → Real) × Real :=
    fun x => ((fun i => x i.succ), x 0)
  have hf : Measurable f :=
    ((DifferentialGeometry.Analysis.euclideanTailHead n).continuous.measurable)
  have hs : MeasurableSet (_root_.Set.univ ×ˢ _root_.Set.Ioi a : Set ((Fin n → Real) × Real)) :=
    (isOpen_univ.prod isOpen_Ioi).measurableSet
  have hpre : f ⁻¹' (_root_.Set.univ ×ˢ _root_.Set.Ioi a) = {x | a < x 0} := by
    ext x
    simp [f]
  rw [← hpre, ← MeasureTheory.Measure.restrict_map hf hs]
  rw [map_tail_prod_head_modelHaar, MeasureTheory.Measure.restrict_smul,
    ← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.map_tail_prod_head_modelHaar_restrict_half_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.map_tail_prod_head_modelHaar_restrict_half_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.map_tail_prod_head_modelHaar_restrict_half_space ``Submission.DifferentialGeometry.Integral.Measure.map_tail_prod_head_modelHaar_restrict_half_space

theorem integral_modelHaar_half_space_eq_integral_prod
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (n : Nat) (a : Real) (f : EuclideanSpace Real (Fin (n + 1)) → F) :
    ∫ x in {x | a < x 0}, f x ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) =
      (MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1))))) _root_.MeasureTheory.MeasureSpace.volume •
        ∫ p, f (WithLp.toLp 2 (Fin.cons p.2 p.1))
          ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (Fin n → Real)).prod (volume.restrict (_root_.Set.Ioi a))) := by
  let e := DifferentialGeometry.Analysis.euclideanTailHead n
  have hmap := e.toHomeomorph.isClosedEmbedding.integral_map
    (μ := (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict {x | a < x 0})
    (fun p => f (e.symm p))
  change (∫ p, f (e.symm p) ∂MeasureTheory.Measure.map
    (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i => x i.succ), x 0))
    ((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict {x | a < x 0})) =
      ∫ x in {x | a < x 0}, f (e.symm (e x))
        ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) at hmap
  simp only [e.symm_apply_apply] at hmap
  rw [map_tail_prod_head_modelHaar_restrict_half_space, _root_.MeasureTheory.integral_smul_nnreal_measure] at hmap
  exact hmap.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integral_modelHaar_half_space_eq_integral_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integral_modelHaar_half_space_eq_integral_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integral_modelHaar_half_space_eq_integral_prod ``Submission.DifferentialGeometry.Integral.Measure.integral_modelHaar_half_space_eq_integral_prod

end DifferentialGeometry.Integral.Measure
