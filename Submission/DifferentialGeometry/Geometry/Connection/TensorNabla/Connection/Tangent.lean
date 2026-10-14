import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Smooth
import Submission.DifferentialGeometry.Bundle.Section
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.VectorField _root_.Filter
    DifferentialGeometry.Tensor0SBundle Function
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section TangentCovariantDerivative

variable [IsManifold I 1 M]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem covariantDeriv_vectorField_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, covariantDerivVectorField (I := I) cov (fun q => X q) (fun q => Y q) p⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) := by
  refine (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply
    (𝕜 := 𝕜) (I := I) (M := M) cov hcov X Y).congr ?_
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.covariantDeriv_vectorField_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.covariantDeriv_vectorField_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.covariantDeriv_vectorField_contMDiff ``Submission.DifferentialGeometry.TensorLieDeriv.covariantDeriv_vectorField_contMDiff

noncomputable def covSection
    [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) where
  toFun := fun p : M => (cov (fun q : M => Y q) p) (X p)
  contMDiff_toFun := by
    simpa [covariantDerivVectorField] using
      covariantDeriv_vectorField_contMDiff (I := I) cov hcov X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.covSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.covSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.covSection ``Submission.DifferentialGeometry.TensorLieDeriv.covSection

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] theorem covSection_apply
    [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (p : M) :
    covSection (I := I) cov hcov X Y p = (cov (fun q : M => Y q) p) (X p) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.covSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.covSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.covSection_apply ``Submission.DifferentialGeometry.TensorLieDeriv.covSection_apply

noncomputable def tangentFieldModelInChart (x₀ : M)
    (V : (x : M) → TangentSpace I x) (y : E) : E :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt 𝕜
    ((extChartAt I x₀).symm y) (V ((extChartAt I x₀).symm y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tangentFieldModelInChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tangentFieldModelInChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tangentFieldModelInChart ``Submission.DifferentialGeometry.TensorLieDeriv.tangentFieldModelInChart

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem tangentFieldModelInChart_tangentConstInChart_apply_of_mem
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) (v : E) :
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) y = v := by
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀
  have hp_source : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hy
  have hp_base : (extChartAt I x₀).symm y ∈ e.baseSet := by
    simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
  unfold tangentFieldModelInChart tangentConstInChart
  exact e.continuousLinearMapAt_symmL (R := 𝕜) hp_base v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tangentFieldModelInChart_tangentConstInChart_apply_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tangentFieldModelInChart_tangentConstInChart_apply_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tangentFieldModelInChart_tangentConstInChart_apply_of_mem ``Submission.DifferentialGeometry.TensorLieDeriv.tangentFieldModelInChart_tangentConstInChart_apply_of_mem

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem tangentConstInChart_self_continuousLinearMapAt
    (x : M) (v : TangentSpace I x) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt
          𝕜 x v) x =
      v := by
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  rw [tangentConstInChart_apply]
  exact e.symmL_continuousLinearMapAt (R := 𝕜) hx v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tangentConstInChart_self_continuousLinearMapAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tangentConstInChart_self_continuousLinearMapAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tangentConstInChart_self_continuousLinearMapAt ``Submission.DifferentialGeometry.TensorLieDeriv.tangentConstInChart_self_continuousLinearMapAt

omit [CompleteSpace 𝕜] in
theorem tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem
    (x₀ : M) (V : (x : M) → TangentSpace I x) {p₀ : M}
    (hp₀ : p₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet) :
    V =ᶠ[𝓝 p₀]
      fun p : M =>
        ∑ i : Fin (Module.finrank 𝕜 E),
          (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p)) •
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) i) p := by
  classical
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis 𝕜 E
  filter_upwards [e.open_baseSet.mem_nhds hp₀] with p hp
  have hp_source : p ∈ (extChartAt I x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp
  have hsymm :
      e.symmL 𝕜 p (e.continuousLinearMapAt 𝕜 p (V p)) = V p :=
    e.symmL_continuousLinearMapAt (R := 𝕜) hp (V p)
  calc
    V p = e.symmL 𝕜 p (e.continuousLinearMapAt 𝕜 p (V p)) := hsymm.symm
    _ = e.symmL 𝕜 p
          (∑ i : Fin (Module.finrank 𝕜 E),
            b.coord i (e.continuousLinearMapAt 𝕜 p (V p)) • b i) := by
          congr 1
          exact (b.sum_repr (e.continuousLinearMapAt 𝕜 p (V p))).symm
    _ = ∑ i : Fin (Module.finrank 𝕜 E),
          b.coord i (e.continuousLinearMapAt 𝕜 p (V p)) • e.symmL 𝕜 p (b i) := by
          rw [map_sum]
          congr
          ext i
          rw [map_smul]
    _ = ∑ i : Fin (Module.finrank 𝕜 E),
          b.coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p)) •
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) p := by
          have hleft : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
            (extChartAt I x₀).left_inv hp_source
          have hmodel :
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                  (extChartAt I x₀ p) =
                e.continuousLinearMapAt 𝕜 p (V p) := by
            unfold tangentFieldModelInChart
            rw [hleft]
          congr
          ext i
          rw [tangentConstInChart_apply]
          rw [hmodel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem ``Submission.DifferentialGeometry.TensorLieDeriv.tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem

omit [CompleteSpace 𝕜] in
theorem tangentField_eq_sum_modelCoord_tangentConst_eventually
    (x₀ : M) (V : (x : M) → TangentSpace I x) :
    V =ᶠ[𝓝 x₀]
      fun p : M =>
        ∑ i : Fin (Module.finrank 𝕜 E),
          (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p)) •
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) i) p := by
  exact tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem
    (𝕜 := 𝕜) (I := I) x₀ V (FiberBundle.mem_baseSet_trivializationAt' x₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tangentField_eq_sum_modelCoord_tangentConst_eventually then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tangentField_eq_sum_modelCoord_tangentConst_eventually"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tangentField_eq_sum_modelCoord_tangentConst_eventually ``Submission.DifferentialGeometry.TensorLieDeriv.tangentField_eq_sum_modelCoord_tangentConst_eventually

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
omit [IsManifold I n M] in
lemma tangentConstInChart_contMDiffOn_baseSet (x₀ : M) (v : E)
    [IsManifold I (n + 1) M] :
    CMDiff[(_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet] n
      (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v :
        (p : M) → TangentSpace I p)) := by
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I) x₀
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  rw [e.contMDiffOn_section_baseSet_iff]
  refine (contMDiffOn_const (c := v)).congr ?_
  intro y hy
  have hcoe : ⇑(e.linearMapAt 𝕜 y) = fun z => (e ⟨y, z⟩).2 :=
    e.coe_linearMapAt_of_mem (R := 𝕜) hy
  simpa [e, tangentConstInChart, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
    (e.continuousLinearMapAt_symmL (R := 𝕜) hy v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet ``Submission.DifferentialGeometry.TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet

end TangentCovariantDerivative

end

end TensorLieDeriv

end DifferentialGeometry
namespace CovariantDerivative
open _root_.CovariantDerivative
open _root_.Submission.DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

open _root_.CovariantDerivative in
theorem smoothSections_cov_contMDiffAt_one
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [hM2 : IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivativeLocally cov (1 : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (fun q : M => Y q) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) x := by
  rcases hM2 with ⟨⟩
  let : IsManifold I 2 M := IsManifold.mk
  have : IsManifold I ((1 : WithTop ℕ∞) + 1) M := by
    have h : ((1 : WithTop ℕ∞) + 1) = (2 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 2 M)
  have hY :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) ((1 : WithTop ℕ∞) + 1)
        (fun p : M =>
          (⟨p, Y p⟩ : _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _))) Set.univ :=
    (Y.contMDiff.of_le
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)).contMDiffOn
  have hcovY :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (fun q : M => Y q) p⟩ :
            _root_.Bundle.TotalSpace (E →L[𝕜] E)
              (fun p : M =>
                TangentSpace I p →L[𝕜] TangentSpace I p))) Set.univ :=
    (hcov isOpen_univ).contMDiff hY
  have hX :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, X p⟩ : _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _))) Set.univ :=
    (X.contMDiff.of_le
      (by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)).contMDiffOn
  exact (hcovY.clm_bundle_apply hX).contMDiffAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.smoothSections_cov_contMDiffAt_one then
    throwError "Refusing to shadow existing declaration CovariantDerivative.smoothSections_cov_contMDiffAt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.smoothSections_cov_contMDiffAt_one ``Submission.CovariantDerivative.smoothSections_cov_contMDiffAt_one

open _root_.CovariantDerivative in
theorem tangentConst_cov_mdiffAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivativeLocally cov (1 : WithTop ℕ∞))
    {x : M} (v w : TangentSpace I x) :
    MDiffAt
      (T% (fun p : M =>
        (cov (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x w)) p)
          ((TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x v)) p))) x := by
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x
  let vModel : E := e.continuousLinearMapAt 𝕜 x v
  let wModel : E := e.continuousLinearMapAt 𝕜 x w
  change MDiffAt
    (T% (fun p : M =>
      (cov (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x wModel) p)
        ((TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x vModel) p))) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have : IsManifold I ((1 : WithTop ℕ∞) + 1) M := by
    have h : ((1 : WithTop ℕ∞) + 1) = (2 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 2 M)
  have : IsManifold I (((1 : WithTop ℕ∞) + 1) + 1) M := by
    have h : (((1 : WithTop ℕ∞) + 1) + 1) = (3 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 3 M)
  have hw :
      CMDiff[e.baseSet] ((1 : WithTop ℕ∞) + 1)
        (T% (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x wModel :
          (p : M) → TangentSpace I p)) := by
    simpa [e] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := 𝕜) (I := I) (M := M)
        (n := (1 : WithTop ℕ∞) + 1) x wModel)
  have hcovw :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x wModel) p⟩ :
            _root_.Bundle.TotalSpace (E →L[𝕜] E)
              (fun p : M =>
                TangentSpace I p →L[𝕜] TangentSpace I p)))
        e.baseSet := by
    exact (hcov e.open_baseSet).contMDiff hw
  have hv :
      CMDiff[e.baseSet] (1 : WithTop ℕ∞)
        (T% (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x vModel :
          (p : M) → TangentSpace I p)) := by
    simpa [e] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := 𝕜) (I := I) (M := M)
        (n := (1 : WithTop ℕ∞)) x vModel)
  have h_on :
      CMDiff[e.baseSet] (1 : WithTop ℕ∞)
        (T% (fun p : M =>
          (cov (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x wModel) p)
            ((TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x vModel) p))) := by
    simpa [e] using hcovw.clm_bundle_apply hv
  exact ((h_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.tangentConst_cov_mdiffAt then
    throwError "Refusing to shadow existing declaration CovariantDerivative.tangentConst_cov_mdiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.tangentConst_cov_mdiffAt ``Submission.CovariantDerivative.tangentConst_cov_mdiffAt

end CovariantDerivative
