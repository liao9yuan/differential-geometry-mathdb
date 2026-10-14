import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.VectorField.LieBracket

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section


namespace DifferentialGeometry.Tensor.Coordinates

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Filter
open scoped _root_.Topology _root_.Manifold _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


abbrev CoordinateIdx (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [hfinite : FiniteDimensional 𝕜 E] :=
  let _ := hfinite
  Fin (Module.finrank 𝕜 E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.CoordinateIdx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.CoordinateIdx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.CoordinateIdx ``Submission.DifferentialGeometry.Tensor.Coordinates.CoordinateIdx

structure LocalChartAt (x₀ : M) where
  chart : OpenPartialHomeomorph M H
  mem_source : x₀ ∈ chart.source
  mem_max : chart ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M
  triv : _root_.Bundle.Trivialization E (π E (TangentSpace I : M -> Type _))
  triv_mem : MemTrivializationAtlas triv
  triv_baseSet_eq : triv.baseSet = chart.source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt

namespace LocalChartAt


def source {x₀ : M} (C : LocalChartAt (I := I) x₀) : Set M :=
  C.chart.source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.source ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.source

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem source_open {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    IsOpen C.source :=
  C.chart.open_source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.source_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.source_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.source_open ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.source_open

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem triv_baseSet {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    C.triv.baseSet = C.source :=
  C.triv_baseSet_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.triv_baseSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.triv_baseSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.triv_baseSet ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.triv_baseSet


def default (x₀ : M) : LocalChartAt (I := I) x₀ where
  chart := chartAt H x₀
  mem_source := mem_chart_source H x₀
  mem_max := IsManifold.chart_mem_maximalAtlas (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  triv := _root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀
  triv_mem := inferInstance
  triv_baseSet_eq := by
    simp only [TangentBundle.trivializationAt_baseSet]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem default_mem (x₀ : M) :
    x₀ ∈ (LocalChartAt.default (I := I) x₀).source :=
  (LocalChartAt.default (I := I) x₀).mem_source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_mem ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_mem


def ext {x₀ : M} (C : LocalChartAt (I := I) x₀) : PartialEquiv M E :=
  C.chart.extend I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp]
theorem ext_source {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    C.ext.source = C.source := by
  simp [ext, source]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext_source ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext_source

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem mem_ext_source {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    x₀ ∈ C.ext.source := by
  simpa [ext_source, source] using C.mem_source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.mem_ext_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.mem_ext_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.mem_ext_source ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.mem_ext_source

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem default_ext (x₀ : M) :
    (LocalChartAt.default (I := I) x₀).ext = extChartAt I x₀ := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_ext ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_ext


def overlap {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) : Set M :=
  C.source ∩ D.source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.overlap ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.overlap

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem overlap_open {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    IsOpen (C.overlap D) :=
  C.source_open.inter D.source_open

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.overlap_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.overlap_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.overlap_open ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.overlap_open

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem mem_overlap {x₀ x₁ x : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    x ∈ C.overlap D ↔ x ∈ C.source ∧ x ∈ D.source := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.mem_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.mem_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.mem_overlap ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.mem_overlap


def change {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) : PartialEquiv E E :=
  ModelWithCorners.extendCoordChange (I := I) C.chart D.chart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem change_symm {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    (C.change D).symm = D.change C := by
  simpa [change] using
    (ModelWithCorners.extendCoordChange_symm (I := I) (e := C.chart) (e' := D.chart))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change_symm ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change_symm

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem change_smooth {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    ContDiffOn 𝕜 (∞ : WithTop ℕ∞) (C.change D) (C.change D).source := by
  simpa [change] using
    (ModelWithCorners.contDiffOn_extendCoordChange (I := I) C.mem_max D.mem_max)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change_smooth ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.change_smooth

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem ext_mem_change {x₀ x₁ x : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) (hx : x ∈ C.overlap D) :
    C.ext x ∈ (C.change D).source := by
  have hx' : x ∈ C.chart.source ∩ D.chart.source := by
    simpa [overlap, source] using hx
  have hmem : C.chart.extend I x ∈ C.chart.extend I '' (C.chart.source ∩ D.chart.source) :=
    ⟨x, hx', rfl⟩
  change C.chart.extend I x ∈
    (ModelWithCorners.extendCoordChange (I := I) C.chart D.chart).source
  rw [← OpenPartialHomeomorph.extend_image_source_inter (I := I)]
  exact hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext_mem_change then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext_mem_change"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext_mem_change ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.ext_mem_change

def vec {x₀ : M} (C : LocalChartAt (I := I) x₀) {x : M}
    (hx : x ∈ C.source) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    TangentSpace I x := by
  have hx_ext : x ∈ C.ext.source := by
    simpa [source] using hx
  have hleft : C.ext.symm (C.ext x) = x := C.ext.left_inv hx_ext
  exact hleft ▸
    ((mfderiv[Set.range I] C.ext.symm (C.ext x)) ((Module.finBasis 𝕜 E) i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.vec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.vec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.vec ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.vec

end LocalChartAt


abbrev coordinateTrivializationAt
    (x₀ : M) :
    Trivialization E (π E (TangentSpace I : M -> Type _)) :=
  _root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateTrivializationAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateTrivializationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateTrivializationAt ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateTrivializationAt

namespace LocalChartAt


abbrev defaultTriv (x₀ : M) :
    Trivialization E (π E (TangentSpace I : M -> Type _)) :=
  (LocalChartAt.default (I := I) x₀).triv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultTriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultTriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultTriv ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultTriv

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp]
theorem default_triv (x₀ : M) :
    LocalChartAt.defaultTriv (I := I) x₀ =
      coordinateTrivializationAt (I := I) x₀ := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_triv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_triv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_triv ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_triv

end LocalChartAt

def coordinateFrameAt (x₀ : M) :
    CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x :=
  (coordinateTrivializationAt (I := I) x₀).localFrame (Module.finBasis 𝕜 E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt


def coordinateFrameSet (x₀ : M) : Set M :=
  (coordinateTrivializationAt (I := I) x₀).baseSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem coordinateFrameSet_open (x₀ : M) :
    IsOpen (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).open_baseSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem coordinateFrameAt_mem (x₀ : M) :
    x₀ ∈ coordinateFrameSet (I := I) x₀ :=
  _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_isLocalFrame (x₀ : M) :
    IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).isLocalFrameOn_localFrame_baseSet
    I (∞ : WithTop ℕ∞) (Module.finBasis 𝕜 E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame

namespace LocalChartAt

structure Frame {x₀ : M} (C : LocalChartAt (I := I) x₀) where
  domain : Set M
  frame : CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x
  isLocalFrame : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame domain
  isOpen_domain : IsOpen domain
  mem_base : x₀ ∈ domain
  domain_subset_source : domain ⊆ C.source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame

namespace Frame


omit [CompleteSpace 𝕜] in
theorem mem_source {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain) :
    x ∈ C.source :=
  F.domain_subset_source hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.mem_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.mem_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.mem_source ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.mem_source


def basisAt {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame) {x : M}
    (hx : x ∈ F.domain) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x) :=
  F.isLocalFrame.toBasisAt hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.basisAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.basisAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.basisAt ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.basisAt

omit [CompleteSpace 𝕜] in
theorem basisAt_apply {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    F.basisAt hx i = F.frame i x := by
  simp [basisAt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.basisAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.basisAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.basisAt_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.basisAt_apply

end Frame

def toFrame {x₀ : M} (C : LocalChartAt (I := I) x₀) : C.Frame where
  domain := C.triv.baseSet
  frame := by
    haveI : MemTrivializationAtlas C.triv := C.triv_mem
    exact C.triv.localFrame (Module.finBasis 𝕜 E)
  isLocalFrame := by
    have : MemTrivializationAtlas C.triv := C.triv_mem
    exact C.triv.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (Module.finBasis 𝕜 E)
  isOpen_domain := C.triv.open_baseSet
  mem_base := by
    rw [C.triv_baseSet]
    exact C.mem_source
  domain_subset_source := by
    intro x hx
    rw [C.triv_baseSet] at hx
    exact hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.toFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.toFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.toFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.toFrame


def defaultFrame (x₀ : M) : (LocalChartAt.default (I := I) x₀).Frame where
  domain := coordinateFrameSet (I := I) x₀
  frame := coordinateFrameAt (I := I) x₀
  isLocalFrame := coordinateFrameAt_isLocalFrame (I := I) x₀
  isOpen_domain := coordinateFrameSet_open (I := I) x₀
  mem_base := coordinateFrameAt_mem (I := I) x₀
  domain_subset_source := by
    intro x hx
    have hx_triv : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      change x ∈ coordinateFrameSet (I := I) x₀
      exact hx
    rw [TangentBundle.trivializationAt_baseSet] at hx_triv
    exact hx_triv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame

omit [CompleteSpace 𝕜] in
theorem defaultFrame_domain (x₀ : M) :
    (LocalChartAt.defaultFrame (I := I) x₀).domain =
      coordinateFrameSet (I := I) x₀ := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame_domain ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame_domain

omit [CompleteSpace 𝕜] in
theorem defaultFrame_frame (x₀ : M) :
    (LocalChartAt.defaultFrame (I := I) x₀).frame =
      coordinateFrameAt (I := I) x₀ := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame_frame ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.defaultFrame_frame

end LocalChartAt


omit [CompleteSpace 𝕜] in
lemma coordinateFrameAt_isLocalFrame_one (x₀ : M) :
    IsLocalFrameOn I E (1 : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).isLocalFrameOn_localFrame_baseSet
    I (1 : WithTop ℕ∞) (Module.finBasis 𝕜 E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one


omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_mdifferentiableAt (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    MDiffAt (T% (coordinateFrameAt (I := I) x₀ i)) x₀ := by
  exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
    (coordinateFrameSet_open (I := I) x₀)
    (coordinateFrameAt_mem (I := I) x₀) i).mdifferentiableAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mdifferentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mdifferentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mdifferentiableAt ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mdifferentiableAt


def coordinateFrameAtBasis (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x) :=
  (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtBasis ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtBasis

omit [CompleteSpace 𝕜] in
@[simp]
theorem coordinateFrameAt_basis_apply (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAtBasis (I := I) x₀ hx i =
      coordinateFrameAt (I := I) x₀ i x := by
  simp [coordinateFrameAtBasis]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply


def coordinateFrameAtToBasis (x₀ : M) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x₀) :=
  coordinateFrameAtBasis (I := I) x₀ (coordinateFrameAt_mem (I := I) x₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis

omit [CompleteSpace 𝕜] in
@[simp]
theorem coordinateFrameAt_toBasis_apply (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAtToBasis (I := I) x₀ i =
      coordinateFrameAt (I := I) x₀ i x₀ := by
  simp [coordinateFrameAtToBasis]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_coeff_eq_toBasis_coord
    (x₀ : M) (Z : TangentSpace I x₀) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j x₀ Z =
      (coordinateFrameAtToBasis (I := I) x₀).coord j Z := by
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt
          (coordinateFrameAt_mem (I := I) x₀) =
        coordinateFrameAtToBasis (I := I) x₀ := by
    ext k
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [coordinateFrameAt_toBasis_apply]
  unfold IsLocalFrameOn.coeff
  rw [dif_pos (coordinateFrameAt_mem (I := I) x₀)]
  rw [hbasis]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_coeff_eq_toBasis_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_coeff_eq_toBasis_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_coeff_eq_toBasis_coord ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_coeff_eq_toBasis_coord

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_apply_of_mem {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAt (I := I) x₀ i x =
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
        ((Module.finBasis 𝕜 E) i) := by
  have hx_source : x ∈ (chartAt H x₀).source := by
    have hx_triv : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      change x ∈ coordinateFrameSet (I := I) x₀
      exact hx
    rw [TangentBundle.trivializationAt_baseSet] at hx_triv
    exact hx_triv
  have hx_triv :
      x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    change x ∈ coordinateFrameSet (I := I) x₀
    exact hx
  change (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).localFrame
      (Module.finBasis 𝕜 E) i x =
    (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
      ((Module.finBasis 𝕜 E) i)
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀)
    (b := Module.finBasis 𝕜 E) (i := i) hx_triv]
  rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply,
    Trivialization.linearEquivAt_symm_apply]
  rw [← Trivialization.symmL_apply (R := 𝕜)
    (_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀) hx_triv]
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_source]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_apply_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_apply_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_apply_of_mem ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_apply_of_mem

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem LocalChartAt.default_source (x₀ : M) :
    (LocalChartAt.default (I := I) x₀).source =
      coordinateFrameSet (I := I) x₀ := by
  simp only [LocalChartAt.source, LocalChartAt.default, coordinateFrameSet,
    coordinateTrivializationAt, TangentBundle.trivializationAt_baseSet]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_source ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.default_source

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_basis_triv
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt
        𝕜 x ((coordinateFrameAtBasis (I := I) x₀ hx) i) =
      (Module.finBasis 𝕜 E) i := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hxE : x ∈ e.baseSet := by
    change x ∈ coordinateFrameSet (I := I) x₀
    exact hx
  have hx_source : x ∈ (chartAt H x₀).source := by
    have hx_triv : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      change x ∈ coordinateFrameSet (I := I) x₀
      exact hx
    rw [TangentBundle.trivializationAt_baseSet] at hx_triv
    exact hx_triv
  have hframe :
      (coordinateFrameAtBasis (I := I) x₀ hx) i =
        e.symmL 𝕜 x ((Module.finBasis 𝕜 E) i) := by
    rw [coordinateFrameAt_basis_apply]
    rw [coordinateFrameAt_apply_of_mem (I := I) hx i]
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_source]
    rfl
  rw [hframe]
  exact e.continuousLinearMapAt_symmL (R := 𝕜) hxE ((Module.finBasis 𝕜 E) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_triv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_triv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_triv ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_triv

omit [CompleteSpace 𝕜] in
theorem basisRepr_eq_triv
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (v : TangentSpace I x) :
    (coordinateFrameAtBasis (I := I) x₀ hx).repr v =
      (Module.finBasis 𝕜 E).repr
        ((coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt 𝕜 x v) := by
  classical
  let b := coordinateFrameAtBasis (I := I) x₀ hx
  let e := Module.finBasis 𝕜 E
  let L := (coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt 𝕜 x
  have hLbasis : ∀ i, L (b i) = e i := by
    intro i
    exact coordinateFrameAt_basis_triv (I := I) x₀ hx i
  have hLv : L v = ∑ i, (b.repr v i) • e i := by
    calc
      L v = L (∑ i, (b.repr v i) • b i) := by
          exact congrArg L (b.sum_repr v).symm
      _ = ∑ i, L ((b.repr v i) • b i) := by
          rw [map_sum]
      _ = ∑ i, (b.repr v i) • L (b i) := by
          simp
      _ = ∑ i, (b.repr v i) • e i := by
          simp [hLbasis]
  rw [hLv]
  ext i
  exact (congrFun (e.repr_sum_self (fun i => b.repr v i)) i).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.basisRepr_eq_triv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.basisRepr_eq_triv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.basisRepr_eq_triv ``Submission.DifferentialGeometry.Tensor.Coordinates.basisRepr_eq_triv


omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_toBasis_eq_finBasis (x₀ : M) :
    coordinateFrameAtToBasis (I := I) x₀ = Module.finBasis 𝕜 E := by
  ext i
  rw [coordinateFrameAt_toBasis_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) (coordinateFrameAt_mem (I := I) x₀) i]
  rw [mfderivWithin_range_extChartAt_symm]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_eq_finBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_eq_finBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_eq_finBasis ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_eq_finBasis

def normalCoordLinearEquiv (x : M) : TangentSpace I x ≃L[𝕜] E :=
  ContinuousLinearEquiv.refl 𝕜 E

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalCoordLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalCoordLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalCoordLinearEquiv ``Submission.DifferentialGeometry.Tensor.Coordinates.normalCoordLinearEquiv


def normalCoord (x : M) (v : TangentSpace I x) : E :=
  normalCoordLinearEquiv (I := I) x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalCoord ``Submission.DifferentialGeometry.Tensor.Coordinates.normalCoord

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalCoord_zero (x : M) :
    normalCoord (I := I) x (0 : TangentSpace I x) = 0 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalCoord_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalCoord_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalCoord_zero ``Submission.DifferentialGeometry.Tensor.Coordinates.normalCoord_zero

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
theorem normalCoord_injective (x : M) :
    Function.Injective (normalCoord (I := I) x) :=
  (normalCoordLinearEquiv (I := I) x).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalCoord_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalCoord_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalCoord_injective ``Submission.DifferentialGeometry.Tensor.Coordinates.normalCoord_injective

def normalHCoord (x : M) (v : TangentSpace I x) : H :=
  I.symm (normalCoord (I := I) x v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalHCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalHCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalHCoord ``Submission.DifferentialGeometry.Tensor.Coordinates.normalHCoord

def normalHCoordHomeomorph [I.Boundaryless] (x : M) :
    TangentSpace I x ≃ₜ H :=
  (normalCoordLinearEquiv (I := I) x).toHomeomorph.trans I.toHomeomorph.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalHCoordHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalHCoordHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalHCoordHomeomorph ``Submission.DifferentialGeometry.Tensor.Coordinates.normalHCoordHomeomorph

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalHCoordHomeomorph_apply [I.Boundaryless]
    (x : M) (v : TangentSpace I x) :
    normalHCoordHomeomorph (I := I) x v = normalHCoord (I := I) x v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalHCoordHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalHCoordHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalHCoordHomeomorph_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.normalHCoordHomeomorph_apply

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem model_normalHCoord [I.Boundaryless]
    (x : M) (v : TangentSpace I x) :
    I (normalHCoord (I := I) x v) = normalCoord (I := I) x v := by
  simpa [normalHCoord] using
    I.toHomeomorph.right_inv (normalCoord (I := I) x v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.model_normalHCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.model_normalHCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.model_normalHCoord ``Submission.DifferentialGeometry.Tensor.Coordinates.model_normalHCoord

def modelSymmDiffeomorph [I.Boundaryless] :
    E ≃ₘ^(∞ : WithTop ℕ∞)⟮𝓘(𝕜, E), I⟯ H where
  toEquiv := I.toHomeomorph.symm.toEquiv
  contMDiff_toFun := by
    rw [← contMDiffOn_univ]
    have h := I.contMDiffOn_symm (n := (∞ : WithTop ℕ∞))
    rw [ModelWithCorners.range_eq_univ (I := I)] at h
    exact h.congr fun _ _ => rfl
  contMDiff_invFun := I.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.modelSymmDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.modelSymmDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.modelSymmDiffeomorph ``Submission.DifferentialGeometry.Tensor.Coordinates.modelSymmDiffeomorph

def normalHCoordDiffeomorph [I.Boundaryless] (x : M) :
    TangentSpace I x ≃ₘ^(∞ : WithTop ℕ∞)⟮𝓘(𝕜, TangentSpace I x), I⟯ H :=
  (normalCoordLinearEquiv (I := I) x).toDiffeomorph.trans
    (modelSymmDiffeomorph (I := I))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph ``Submission.DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalHCoordDiffeomorph_apply [I.Boundaryless]
    (x : M) (v : TangentSpace I x) :
    normalHCoordDiffeomorph (I := I) x v = normalHCoord (I := I) x v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph_apply

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalHCoordDiffeomorph_toHomeomorph [I.Boundaryless] (x : M) :
    (normalHCoordDiffeomorph (I := I) x).toHomeomorph =
      normalHCoordHomeomorph (I := I) x := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph_toHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph_toHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph_toHomeomorph ``Submission.DifferentialGeometry.Tensor.Coordinates.normalHCoordDiffeomorph_toHomeomorph

omit [CompleteSpace 𝕜] in
theorem coordCoeff_eq_chart {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (v : TangentSpace I x) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i x v =
      (Module.finBasis 𝕜 E).repr
        ((mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x) v) i := by
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx =
        coordinateFrameAtBasis (I := I) x₀ hx := by
    ext j
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [coordinateFrameAt_basis_apply]
  have hcoeff :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i x v =
        (coordinateFrameAtBasis (I := I) x₀ hx).repr v i := by
    unfold IsLocalFrameOn.coeff
    rw [dif_pos hx]
    rw [hbasis]
    rfl
  have hx_chart : x ∈ (chartAt H x₀).source := by
    have hx_triv : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      change x ∈ coordinateFrameSet (I := I) x₀
      exact hx
    rw [TangentBundle.trivializationAt_baseSet] at hx_triv
    exact hx_triv
  rw [hcoeff]
  rw [basisRepr_eq_triv (I := I) x₀ hx v]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I) (𝕜 := 𝕜) (x₀ := x₀) (x := x) hx_chart]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordCoeff_eq_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordCoeff_eq_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordCoeff_eq_chart ``Submission.DifferentialGeometry.Tensor.Coordinates.coordCoeff_eq_chart

omit [CompleteSpace 𝕜] in
private theorem coordinateFrame_pullback_eq_const (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (coordinateFrameAt (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        fun _ : E => (Module.finBasis 𝕜 E i : E) := by
  have : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  simp only [VectorField.mpullbackWithin_apply]
  have hy_source : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
    change (extChartAt I x₀).symm y ∈
      (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy_source
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base i]
  rw [(extChartAt I x₀).right_inv hy]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self
    (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy)
    ((Module.finBasis 𝕜 E) i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrame_pullback_eq_const
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.coordinateFrame_pullback_eq_const target :: scope.openDecls } }

omit [CompleteSpace 𝕜] in
private theorem coordinateFrame_pullback_eq_const_of_mem {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (coordinateFrameAt (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x)]
        fun _ : E => (Module.finBasis 𝕜 E i : E) := by
  have : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hx_source : x ∈ (extChartAt I x₀).source := by
    have hx_chart : x ∈ (chartAt H x₀).source := by
      have hx_triv : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
        change x ∈ coordinateFrameSet (I := I) x₀
        exact hx
      rw [TangentBundle.trivializationAt_baseSet] at hx_triv
      exact hx_triv
    rw [extChartAt_source]
    exact hx_chart
  filter_upwards [extChartAt_target_mem_nhdsWithin' (I := I) hx_source] with y hy
  simp only [VectorField.mpullbackWithin_apply]
  have hy_source : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
    change (extChartAt I x₀).symm y ∈
      (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy_source
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base i]
  rw [(extChartAt I x₀).right_inv hy]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self
    (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy)
    ((Module.finBasis 𝕜 E) i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrame_pullback_eq_const_of_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.coordinateFrame_pullback_eq_const_of_mem target :: scope.openDecls } }

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
private theorem lieBracketWithin_const_const {s : Set E} {x v w : E} :
    VectorField.lieBracketWithin 𝕜 (fun _ : E => v) (fun _ : E => w) s x = 0 := by
  simp [VectorField.lieBracketWithin]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.lieBracketWithin_const_const
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.lieBracketWithin_const_const target :: scope.openDecls } }

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_bracket_zero (x₀ : M) (i j : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mlieBracket I
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ j) x₀ = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  have hleft :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (coordinateFrameAt (I := I) x₀ i) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => (Module.finBasis 𝕜 E i : E) := by
    simpa using coordinateFrame_pullback_eq_const (I := I) x₀ i
  have hright :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (coordinateFrameAt (I := I) x₀ j) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => (Module.finBasis 𝕜 E j : E) := by
    simpa using coordinateFrame_pullback_eq_const (I := I) x₀ j
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright (by simp)]
  rw [lieBracketWithin_const_const]
  exact ContinuousLinearMap.map_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_bracket_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_bracket_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_bracket_zero ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_bracket_zero

theorem coordinateFrameAt_bracket_zero_of_mem [IsRCLikeNormedField 𝕜] {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mlieBracket I
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ j) x = 0 := by
  have : IsManifold I (minSmoothness 𝕜 2) M :=
    by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact IsManifold.of_le (I := I) (M := M) (n := ∞) (by
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let V : (x : M) → TangentSpace I x := coordinateFrameAt (I := I) x₀ i
  let W : (x : M) → TangentSpace I x := coordinateFrameAt (I := I) x₀ j
  let z : E := extChartAt I x₀ x
  let f : E → M := (extChartAt I x₀).symm
  have hx_source : x ∈ (extChartAt I x₀).source := by
    have hx_chart : x ∈ (chartAt H x₀).source := by
      have hx_triv : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
        change x ∈ coordinateFrameSet (I := I) x₀
        exact hx
      rw [TangentBundle.trivializationAt_baseSet] at hx_triv
      exact hx_triv
    rw [extChartAt_source]
    exact hx_chart
  have hz_target : z ∈ (extChartAt I x₀).target := by
    exact (extChartAt I x₀).map_source hx_source
  have hz_range : z ∈ Set.range I :=
    extChartAt_target_subset_range x₀ hz_target
  have hfz : f z = x := by
    exact (extChartAt I x₀).left_inv hx_source
  have hVdiff : MDiffAt[Set.univ] (T% V) (f z) := by
    rw [hfz]
    exact (((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀) hx i).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
  have hWdiff : MDiffAt[Set.univ] (T% W) (f z) := by
    rw [hfz]
    exact (((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀) hx j).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
  have hf :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞) f (Set.range I) z :=
    contMDiffWithinAt_extChartAt_symm_range (I := I) (x := x₀) hz_target
  have hpb :=
    VectorField.mpullbackWithin_mlieBracketWithin
      (I := 𝓘(𝕜, E)) (I' := I) (n := (∞ : WithTop ℕ∞))
      (f := f) (V := V) (W := W) (x₀ := z)
      (s := Set.range I) (t := Set.univ)
      hVdiff hWdiff I.uniqueMDiffOn hf hz_range
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
      (by simp only [Set.preimage_univ]; exact Filter.univ_mem)
      (by
        simpa [z] using I.range_subset_closure_interior hz_range)
  have hleft :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I f V (Set.range I)
        =ᶠ[𝓝[Set.range I] z]
          fun _ : E => (Module.finBasis 𝕜 E i : E) := by
    simpa [f, V, z] using coordinateFrame_pullback_eq_const_of_mem (I := I) hx i
  have hright :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I f W (Set.range I)
        =ᶠ[𝓝[Set.range I] z]
          fun _ : E => (Module.finBasis 𝕜 E j : E) := by
    simpa [f, W, z] using coordinateFrame_pullback_eq_const_of_mem (I := I) hx j
  have hrhs :
      VectorField.mlieBracketWithin 𝓘(𝕜, E)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I f V (Set.range I))
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I f W (Set.range I))
          (Set.range I) z = 0 := by
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright hz_range]
    rw [lieBracketWithin_const_const]
    rfl
  rw [hrhs] at hpb
  rw [VectorField.mlieBracketWithin_univ] at hpb
  simp only [VectorField.mpullbackWithin_apply] at hpb
  have hInv :
      (mfderiv[Set.range I] f z).IsInvertible := by
    simpa [f, z] using isInvertible_mfderivWithin_extChartAt_symm (I := I) hz_target
  have hzero := congrArg (fun v => (mfderiv[Set.range I] f z) v) hpb
  change VectorField.mlieBracket I V W x = 0
  rw [← hfz]
  simpa [ContinuousLinearMap.IsInvertible.self_apply_inverse hInv] using hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_bracket_zero_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_bracket_zero_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_bracket_zero_of_mem ``Submission.DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_bracket_zero_of_mem


structure CoordinateFrameAt (x₀ : M) where
  domain : Set M
  frame : CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x
  isLocalFrame : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame domain
  isOpen_domain : IsOpen domain
  mem_base : x₀ ∈ domain
  bracket_zero : ∀ i j : CoordinateIdx (𝕜 := 𝕜) E,
    VectorField.mlieBracket I (frame i) (frame j) x₀ = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.CoordinateFrameAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.CoordinateFrameAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.CoordinateFrameAt ``Submission.DifferentialGeometry.Tensor.Coordinates.CoordinateFrameAt


def canonicalCoordinateFrameAt (x₀ : M) : CoordinateFrameAt (I := I) x₀ where
  domain := coordinateFrameSet (I := I) x₀
  frame := coordinateFrameAt (I := I) x₀
  isLocalFrame := coordinateFrameAt_isLocalFrame (I := I) x₀
  isOpen_domain := coordinateFrameSet_open (I := I) x₀
  mem_base := coordinateFrameAt_mem (I := I) x₀
  bracket_zero := coordinateFrameAt_bracket_zero (I := I) x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.canonicalCoordinateFrameAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.canonicalCoordinateFrameAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.canonicalCoordinateFrameAt ``Submission.DifferentialGeometry.Tensor.Coordinates.canonicalCoordinateFrameAt

namespace LocalChartAt
namespace Frame


def comp0S {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {s : ℕ} {x : M} (hx : x ∈ F.domain)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  component0S (I := I) (F.basisAt hx) A slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.comp0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.comp0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.comp0S ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.comp0S

omit [CompleteSpace 𝕜] in
theorem comp0S_apply {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {s : ℕ} {x : M} (hx : x ∈ F.domain)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    F.comp0S hx A slots =
      A (fun a => F.basisAt hx (slots a)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.comp0S_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.comp0S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.comp0S_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.comp0S_apply


def compRS {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {r s : ℕ} {x : M} (hx : x ∈ F.domain)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  componentRSField (I := I) (F.basisAt hx) T upper lower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.compRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.compRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.compRS ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.compRS

theorem compRS_apply {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {r s : ℕ} {x : M} (hx : x ∈ F.domain)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    F.compRS hx T upper lower =
      componentRSField (I := I) (F.basisAt hx) T upper lower :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.compRS_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.compRS_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.compRS_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.compRS_apply

end Frame
end LocalChartAt


def coordComponent0SAt {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  component0S (I := I) (coordinateFrameAtToBasis (I := I) x₀) A slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt ``Submission.DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt

omit [CompleteSpace 𝕜] in
@[simp]
theorem coordComponent0SAt_apply {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I) A slots =
      A (fun a => coordinateFrameAtToBasis (I := I) x₀ (slots a)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_apply


def coordComponentRSAt {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  componentRSField (I := I) (coordinateFrameAtToBasis (I := I) x₀) T upper lower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt ``Submission.DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt

@[simp]
theorem coordComponentRSAt_apply {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I) T upper lower =
      componentRSField (I := I) (coordinateFrameAtToBasis (I := I) x₀) T upper lower :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt_apply

omit [CompleteSpace 𝕜] in
theorem coordComponent0SAt_congr_slots {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    {slots slots' : Fin s -> CoordinateIdx (𝕜 := 𝕜) E}
    (h : slots = slots') :
    coordComponent0SAt (I := I) A slots = coordComponent0SAt (I := I) A slots' := by
  rw [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_congr_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_congr_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_congr_slots ``Submission.DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_congr_slots

theorem coordComponentRSAt_congr_slots {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    {upper upper' : Fin r -> CoordinateIdx (𝕜 := 𝕜) E}
    {lower lower' : Fin s -> CoordinateIdx (𝕜 := 𝕜) E}
    (hu : upper = upper') (hl : lower = lower') :
    coordComponentRSAt (I := I) T upper lower =
      coordComponentRSAt (I := I) T upper' lower' := by
  rw [hu, hl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt_congr_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt_congr_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt_congr_slots ``Submission.DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt_congr_slots

theorem coordExt0SAt {s : ℕ} {x₀ : M}
    {A B : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀}
    (h : ∀ slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E,
      coordComponent0SAt (I := I) A slots = coordComponent0SAt (I := I) B slots) :
    A = B :=
  ext0S_basis (I := I) (coordinateFrameAtToBasis (I := I) x₀) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordExt0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordExt0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordExt0SAt ``Submission.DifferentialGeometry.Tensor.Coordinates.coordExt0SAt

theorem coordExtRSAt {r s : ℕ} {x₀ : M}
    {A B : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀}
    (h : ∀ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
         ∀ lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E,
      coordComponentRSAt (I := I) A upper lower =
        coordComponentRSAt (I := I) B upper lower) :
    A = B :=
  extRS_basis_field (I := I) (coordinateFrameAtToBasis (I := I) x₀) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordExtRSAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordExtRSAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordExtRSAt ``Submission.DifferentialGeometry.Tensor.Coordinates.coordExtRSAt

namespace LocalChartAt
namespace Frame

omit [CompleteSpace 𝕜] in
theorem default_comp0S {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (LocalChartAt.defaultFrame (I := I) x₀).comp0S
        (LocalChartAt.defaultFrame (I := I) x₀).mem_base A slots =
      coordComponent0SAt (I := I) A slots := by
  simp [LocalChartAt.Frame.comp0S, LocalChartAt.Frame.basisAt,
    LocalChartAt.defaultFrame, coordComponent0SAt, coordinateFrameAtToBasis,
    coordinateFrameAtBasis]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.default_comp0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.default_comp0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.default_comp0S ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.default_comp0S

theorem default_compRS {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (LocalChartAt.defaultFrame (I := I) x₀).compRS
        (LocalChartAt.defaultFrame (I := I) x₀).mem_base T upper lower =
      coordComponentRSAt (I := I) T upper lower := by
  simp [LocalChartAt.Frame.compRS, LocalChartAt.Frame.basisAt,
    LocalChartAt.defaultFrame, coordComponentRSAt, coordinateFrameAtToBasis,
    coordinateFrameAtBasis]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.default_compRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.default_compRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.default_compRS ``Submission.DifferentialGeometry.Tensor.Coordinates.LocalChartAt.Frame.default_compRS

end Frame
end LocalChartAt

end DifferentialGeometry.Tensor.Coordinates
