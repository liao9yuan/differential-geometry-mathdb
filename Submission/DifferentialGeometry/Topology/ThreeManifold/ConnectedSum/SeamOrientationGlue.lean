import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssemblyReduction
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamTransition
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientationPrelude
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientationTopology
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.TopologicalSpace _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace OrientationAssembly
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.ConnectedSumQuotient
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Topology.OrientationAssembly

universe u v

variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}

variable (c : OrientedBallChart M) (d : OrientedBallChart N)
  (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)

variable [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
variable [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]

section OrientationIndexBridge

variable {ι : Type*}
variable {R M₁ M₂ M₃ : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
variable [AddCommGroup M₃] [Module R M₃]

theorem orientation_map_map_trans (e : M₁ ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃)
    (o : Orientation R M₁ ι) :
    Orientation.map ι f (Orientation.map ι e o) = Orientation.map ι (e.trans f) o := by
  induction o using Module.Ray.ind R with
  | h v hv =>
    have hfun2 : AlternatingMap.compLinearMap
          (AlternatingMap.compLinearMap v (e.symm : M₂ →ₗ[R] M₁)) (f.symm : M₃ →ₗ[R] M₂) =
        AlternatingMap.compLinearMap v (((e.trans f).symm : M₃ →ₗ[R] M₁)) := by
      rw [LinearEquiv.trans_symm]
      ext g
      change v (fun i => e.symm (f.symm (g i))) = v (fun i => e.symm (f.symm (g i)))
      rfl
    simp only [Orientation.map_apply, hfun2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.orientation_map_map_trans then
    throwError "Refusing to shadow existing declaration OrientationAssembly.orientation_map_map_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.orientation_map_map_trans ``Submission.OrientationAssembly.orientation_map_map_trans

theorem orientation_map_symm_map_self (e : M₁ ≃ₗ[R] M₂) (o : Orientation R M₂ ι) :
    Orientation.map ι e (Orientation.map ι e.symm o) = o := by
  rw [orientation_map_map_trans e.symm e o]
  have h : e.symm.trans e = LinearEquiv.refl R M₂ := LinearEquiv.ext (fun v => e.apply_symm_apply v)
  rw [h, Orientation.map_refl]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.orientation_map_symm_map_self then
    throwError "Refusing to shadow existing declaration OrientationAssembly.orientation_map_symm_map_self"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.orientation_map_symm_map_self ``Submission.OrientationAssembly.orientation_map_symm_map_self

end OrientationIndexBridge

section OrientationReindexBridge

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

omit [PartialOrder R] [IsStrictOrderedRing R] in
theorem alternatingMap_domDomCongr_compLinearMap {ι ι' : Type*} (e : ι ≃ ι')
    (f : M ≃ₗ[R] N) (v : M [⋀^ι]→ₗ[R] R) :
    AlternatingMap.domDomCongr e (v.compLinearMap (f.symm : N →ₗ[R] M)) =
      AlternatingMap.compLinearMap (AlternatingMap.domDomCongr e v) (f.symm : N →ₗ[R] M) := by
  ext g
  change v (fun i => f.symm (g (e i))) = v (fun i => f.symm (g (e i)))
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.alternatingMap_domDomCongr_compLinearMap then
    throwError "Refusing to shadow existing declaration OrientationAssembly.alternatingMap_domDomCongr_compLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.alternatingMap_domDomCongr_compLinearMap ``Submission.OrientationAssembly.alternatingMap_domDomCongr_compLinearMap

theorem orientation_reindex_map_comm {ι ι' : Type*} (e : ι ≃ ι') (f : M ≃ₗ[R] N)
    (o : Orientation R M ι) :
    Orientation.reindex R N e (Orientation.map ι f o) =
      Orientation.map ι' f (Orientation.reindex R M e o) := by
  induction o using Module.Ray.ind R with
  | h v hv =>
    have hfun : AlternatingMap.domDomCongr e (v.compLinearMap (f.symm : N →ₗ[R] M)) =
        AlternatingMap.compLinearMap (AlternatingMap.domDomCongr e v) (f.symm : N →ₗ[R] M) :=
      alternatingMap_domDomCongr_compLinearMap e f v
    simp only [Orientation.map_apply, Orientation.reindex_apply, hfun]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.orientation_reindex_map_comm then
    throwError "Refusing to shadow existing declaration OrientationAssembly.orientation_reindex_map_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.orientation_reindex_map_comm ``Submission.OrientationAssembly.orientation_reindex_map_comm

end OrientationReindexBridge
abbrev AtlasLeft (c : OrientedBallChart M) (d : OrientedBallChart N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] : Prop :=
  ∀ (f : OpenPartialHomeomorph M.Carrier csModel), f ∈ atlas csModel M.Carrier →
    (leftChart c.toBallChart d.toBallChart aD.toHomeomorph hn3 f).symm ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.AtlasLeft then
    throwError "Refusing to shadow existing declaration OrientationAssembly.AtlasLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.AtlasLeft ``Submission.OrientationAssembly.AtlasLeft

abbrev AtlasRight (c : OrientedBallChart M) (d : OrientedBallChart N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] : Prop :=
  ∀ (g : OpenPartialHomeomorph N.Carrier csModel), g ∈ atlas csModel N.Carrier →
    (rightChart c.toBallChart d.toBallChart aD.toHomeomorph hn3 g).symm ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.AtlasRight then
    throwError "Refusing to shadow existing declaration OrientationAssembly.AtlasRight"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.AtlasRight ``Submission.OrientationAssembly.AtlasRight


def csIdx : Fin 3 ≃ Fin (Module.finrank ℝ csModel) := finCongr (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.csIdx then
    throwError "Refusing to shadow existing declaration OrientationAssembly.csIdx"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.csIdx ``Submission.OrientationAssembly.csIdx

def stdOrientation (x : csModel) :
    Orientation ℝ (TangentSpace 𝓘(ℝ, csModel) x) (Fin 3) :=
  ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
    (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.stdOrientation then
    throwError "Refusing to shadow existing declaration OrientationAssembly.stdOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.stdOrientation ``Submission.OrientationAssembly.stdOrientation

theorem stdOrientation_eq (x y : csModel) : stdOrientation x = stdOrientation y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.stdOrientation_eq then
    throwError "Refusing to shadow existing declaration OrientationAssembly.stdOrientation_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.stdOrientation_eq ``Submission.OrientationAssembly.stdOrientation_eq

def stdOrientationModel : Orientation ℝ csModel (Fin (Module.finrank ℝ csModel)) :=
  Orientation.reindex ℝ csModel csIdx (stdOrientation 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.stdOrientationModel then
    throwError "Refusing to shadow existing declaration OrientationAssembly.stdOrientationModel"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.stdOrientationModel ``Submission.OrientationAssembly.stdOrientationModel

theorem stdOrientationModel_eq_reindex (x : csModel) :
    stdOrientationModel = Orientation.reindex ℝ csModel csIdx (stdOrientation x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.stdOrientationModel_eq_reindex then
    throwError "Refusing to shadow existing declaration OrientationAssembly.stdOrientationModel_eq_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.stdOrientationModel_eq_reindex ``Submission.OrientationAssembly.stdOrientationModel_eq_reindex
theorem isOpen_range_interiorLeft' (hLq : AtlasLeft c d aD) :
    IsOpen (Set.range (interiorLeft c.toBallChart d.toBallChart aD)) :=
  (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).isOpen_range

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.isOpen_range_interiorLeft' then
    throwError "Refusing to shadow existing declaration OrientationAssembly.isOpen_range_interiorLeft'"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.isOpen_range_interiorLeft' ``Submission.OrientationAssembly.isOpen_range_interiorLeft'

theorem isOpen_range_interiorRight' (hRq : AtlasRight c d aD) :
    IsOpen (Set.range (interiorRight c.toBallChart d.toBallChart aD)) :=
  (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).isOpen_range

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.isOpen_range_interiorRight' then
    throwError "Refusing to shadow existing declaration OrientationAssembly.isOpen_range_interiorRight'"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.isOpen_range_interiorRight' ``Submission.OrientationAssembly.isOpen_range_interiorRight'

def qL (hLq : AtlasLeft c d aD) :
    TopologicalSpace.Opens (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  ⟨Set.range (interiorLeft c.toBallChart d.toBallChart aD),
    isOpen_range_interiorLeft' c d aD hLq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.qL then
    throwError "Refusing to shadow existing declaration OrientationAssembly.qL"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.qL ``Submission.OrientationAssembly.qL

def qR (hRq : AtlasRight c d aD) :
    TopologicalSpace.Opens (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  ⟨Set.range (interiorRight c.toBallChart d.toBallChart aD),
    isOpen_range_interiorRight' c d aD hRq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.qR then
    throwError "Refusing to shadow existing declaration OrientationAssembly.qR"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.qR ``Submission.OrientationAssembly.qR

def qS : TopologicalSpace.Opens (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  ⟨(seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source,
    (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).open_source⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.qS then
    throwError "Refusing to shadow existing declaration OrientationAssembly.qS"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.qS ``Submission.OrientationAssembly.qS

def gL (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) : c.toBallChart.interior :=
  Classical.choose x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.gL then
    throwError "Refusing to shadow existing declaration OrientationAssembly.gL"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.gL ``Submission.OrientationAssembly.gL

theorem gL_spec (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  Classical.choose_spec x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.gL_spec then
    throwError "Refusing to shadow existing declaration OrientationAssembly.gL_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.gL_spec ``Submission.OrientationAssembly.gL_spec

def gR (hRq : AtlasRight c d aD) (x : qR c d aD hRq) : d.toBallChart.interior :=
  Classical.choose x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.gR then
    throwError "Refusing to shadow existing declaration OrientationAssembly.gR"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.gR ``Submission.OrientationAssembly.gR

theorem gR_spec (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  Classical.choose_spec x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.gR_spec then
    throwError "Refusing to shadow existing declaration OrientationAssembly.gR_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.gR_spec ``Submission.OrientationAssembly.gR_spec

theorem gL_apply (hLq : AtlasLeft c d aD) (u : c.toBallChart.interior) :
    gL c d aD hLq ⟨interiorLeft c.toBallChart d.toBallChart aD u, ⟨u, rfl⟩⟩ = u :=
  interiorLeft_injective c.toBallChart d.toBallChart aD
    (by rw [gL_spec])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.gL_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.gL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.gL_apply ``Submission.OrientationAssembly.gL_apply

theorem gR_apply (hRq : AtlasRight c d aD) (v : d.toBallChart.interior) :
    gR c d aD hRq ⟨interiorRight c.toBallChart d.toBallChart aD v, ⟨v, rfl⟩⟩ = v :=
  interiorRight_injective c.toBallChart d.toBallChart aD
    (by rw [gR_spec])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.gR_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.gR_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.gR_apply ``Submission.OrientationAssembly.gR_apply

theorem gL_eventuallyEq_localInverse (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    gL c d aD hLq =ᶠ[𝓝 x]
      (fun y : qL c d aD hLq =>
        (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq
          (gL c d aD hLq x)).localInverse ↑y) := by
  let hf := interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq (gL c d aD hLq x)
  have hx : interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gL_spec c d aD hLq x
  have hmem : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)
      ∈ hf.localInverse.source := by
    rw [← hx]
    exact hf.localInverse_mem_source
  refine Filter.eventuallyEq_of_mem
    ((continuous_subtype_val
      (X := ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)).continuousAt.preimage_mem_nhds
      (hf.localInverse.open_source.mem_nhds hmem)) ?_
  intro y hy
  have h1 : interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq y)
      = (y : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gL_spec c d aD hLq y
  have h2 : interiorLeft c.toBallChart d.toBallChart aD (hf.localInverse ↑y)
      = (y : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    hf.localInverse_right_inv hy
  exact interiorLeft_injective c.toBallChart d.toBallChart aD (h1.trans h2.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.gL_eventuallyEq_localInverse then
    throwError "Refusing to shadow existing declaration OrientationAssembly.gL_eventuallyEq_localInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.gL_eventuallyEq_localInverse ``Submission.OrientationAssembly.gL_eventuallyEq_localInverse

theorem gR_eventuallyEq_localInverse (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    gR c d aD hRq =ᶠ[𝓝 x]
      (fun y : qR c d aD hRq =>
        (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq
          (gR c d aD hRq x)).localInverse ↑y) := by
  let hf := interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq (gR c d aD hRq x)
  have hx : interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gR_spec c d aD hRq x
  have hmem : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)
      ∈ hf.localInverse.source := by
    rw [← hx]
    exact hf.localInverse_mem_source
  refine Filter.eventuallyEq_of_mem
    ((continuous_subtype_val
      (X := ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)).continuousAt.preimage_mem_nhds
      (hf.localInverse.open_source.mem_nhds hmem)) ?_
  intro y hy
  have h1 : interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq y)
      = (y : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gR_spec c d aD hRq y
  have h2 : interiorRight c.toBallChart d.toBallChart aD (hf.localInverse ↑y)
      = (y : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    hf.localInverse_right_inv hy
  exact interiorRight_injective c.toBallChart d.toBallChart aD (h1.trans h2.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.gR_eventuallyEq_localInverse then
    throwError "Refusing to shadow existing declaration OrientationAssembly.gR_eventuallyEq_localInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.gR_eventuallyEq_localInverse ``Submission.OrientationAssembly.gR_eventuallyEq_localInverse

theorem contMDiffAt_gL (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (gL c d aD hLq) x := by
  have hx : interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gL_spec c d aD hLq x
  have hfinv : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq
        (gL c d aD hLq x)).localInverse
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    hx ▸ (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq
      (gL c d aD hLq x)).localInverse_contMDiffAt
  refine (hfinv.comp x contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq ?_
  exact gL_eventuallyEq_localInverse c d aD hLq x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.contMDiffAt_gL then
    throwError "Refusing to shadow existing declaration OrientationAssembly.contMDiffAt_gL"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.contMDiffAt_gL ``Submission.OrientationAssembly.contMDiffAt_gL

theorem contMDiff_gL (hLq : AtlasLeft c d aD) : ContMDiff (𝓡 3) (𝓡 3) ∞ (gL c d aD hLq) :=
  fun x => contMDiffAt_gL c d aD hLq x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.contMDiff_gL then
    throwError "Refusing to shadow existing declaration OrientationAssembly.contMDiff_gL"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.contMDiff_gL ``Submission.OrientationAssembly.contMDiff_gL

theorem contMDiffAt_gR (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (gR c d aD hRq) x := by
  have hx : interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gR_spec c d aD hRq x
  have hfinv : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq
        (gR c d aD hRq x)).localInverse
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    hx ▸ (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq
      (gR c d aD hRq x)).localInverse_contMDiffAt
  refine (hfinv.comp x contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq ?_
  exact gR_eventuallyEq_localInverse c d aD hRq x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.contMDiffAt_gR then
    throwError "Refusing to shadow existing declaration OrientationAssembly.contMDiffAt_gR"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.contMDiffAt_gR ``Submission.OrientationAssembly.contMDiffAt_gR

theorem contMDiff_gR (hRq : AtlasRight c d aD) : ContMDiff (𝓡 3) (𝓡 3) ∞ (gR c d aD hRq) :=
  fun x => contMDiffAt_gR c d aD hRq x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.contMDiff_gR then
    throwError "Refusing to shadow existing declaration OrientationAssembly.contMDiff_gR"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.contMDiff_gR ``Submission.OrientationAssembly.contMDiff_gR


section ChainRules

theorem mfderiv_IL_comp_gL (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x)).comp
      (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x) = ContinuousLinearMap.id ℝ csModel := by
  have hdiffIL : MDifferentiableAt (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
      (gL c d aD hLq x) :=
    ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq)
      (gL c d aD hLq x)).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hdiffgL : MDifferentiableAt (𝓡 3) (𝓡 3) (gL c d aD hLq) x :=
    (contMDiffAt_gL c d aD hLq x).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := x) (f := (gL c d aD hLq))
    (g := (interiorLeft c.toBallChart d.toBallChart aD)) hdiffIL hdiffgL
  have heq : (interiorLeft c.toBallChart d.toBallChart aD ∘ gL c d aD hLq) =
      (Subtype.val : qL c d aD hLq →
        ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) := by
    funext y
    exact gL_spec c d aD hLq y
  rw [heq, DifferentialGeometry.mfderiv_subtype_val] at hcomp
  exact hcomp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_IL_comp_gL then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_IL_comp_gL"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_IL_comp_gL ``Submission.OrientationAssembly.mfderiv_IL_comp_gL

theorem mfderiv_IR_comp_gR (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x)).comp
      (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x) = ContinuousLinearMap.id ℝ csModel := by
  have hdiffIR : MDifferentiableAt (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
      (gR c d aD hRq x) :=
    ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq)
      (gR c d aD hRq x)).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hdiffgR : MDifferentiableAt (𝓡 3) (𝓡 3) (gR c d aD hRq) x :=
    (contMDiffAt_gR c d aD hRq x).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := x) (f := (gR c d aD hRq))
    (g := (interiorRight c.toBallChart d.toBallChart aD)) hdiffIR hdiffgR
  have heq : (interiorRight c.toBallChart d.toBallChart aD ∘ gR c d aD hRq) =
      (Subtype.val : qR c d aD hRq →
        ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) := by
    funext y
    exact gR_spec c d aD hRq y
  rw [heq, DifferentialGeometry.mfderiv_subtype_val] at hcomp
  exact hcomp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_IR_comp_gR then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_IR_comp_gR"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_IR_comp_gR ``Submission.OrientationAssembly.mfderiv_IR_comp_gR

def leftDifferential (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    TangentSpace (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)) ≃L[ℝ]
      TangentSpace (𝓡 3) (gL c d aD hLq x) where
  toFun := mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x
  invFun := mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x)
  left_inv := by
    intro v
    exact DFunLike.congr_fun (mfderiv_IL_comp_gL c d aD hLq x) v
  right_inv := by
    intro w
    have hAB := mfderiv_IL_comp_gL c d aD hLq x
    have hinj : Function.Injective
        (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x)) := by
      have h := (((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq)
        (gL c d aD hLq x)).mfderivToContinuousLinearEquiv
        (show (∞ : ℕ∞ω) ≠ 0 by simp)).injective
      exact h
    exact hinj (DFunLike.congr_fun hAB _)
  map_add' := (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x).map_add
  map_smul' := (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x).map_smul
  continuous_toFun := (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x).cont
  continuous_invFun :=
    (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
      (gL c d aD hLq x)).cont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.leftDifferential then
    throwError "Refusing to shadow existing declaration OrientationAssembly.leftDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.leftDifferential ``Submission.OrientationAssembly.leftDifferential

theorem mfderiv_gL_eq_leftDifferential (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x
      = (leftDifferential c d aD hLq x).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_gL_eq_leftDifferential then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_gL_eq_leftDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_gL_eq_leftDifferential ``Submission.OrientationAssembly.mfderiv_gL_eq_leftDifferential

theorem bijective_mfderiv_gL (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x) := by
  rw [mfderiv_gL_eq_leftDifferential c d aD hLq x]
  exact (leftDifferential c d aD hLq x).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.bijective_mfderiv_gL then
    throwError "Refusing to shadow existing declaration OrientationAssembly.bijective_mfderiv_gL"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.bijective_mfderiv_gL ``Submission.OrientationAssembly.bijective_mfderiv_gL

def rightDifferential (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    TangentSpace (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)) ≃L[ℝ]
      TangentSpace (𝓡 3) (gR c d aD hRq x) where
  toFun := mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x
  invFun := mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x)
  left_inv := by
    intro v
    exact DFunLike.congr_fun (mfderiv_IR_comp_gR c d aD hRq x) v
  right_inv := by
    intro w
    have hAB := mfderiv_IR_comp_gR c d aD hRq x
    have hinj : Function.Injective
        (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x)) := by
      have h := (((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq)
        (gR c d aD hRq x)).mfderivToContinuousLinearEquiv
        (show (∞ : ℕ∞ω) ≠ 0 by simp)).injective
      exact h
    exact hinj (DFunLike.congr_fun hAB _)
  map_add' := (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x).map_add
  map_smul' := (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x).map_smul
  continuous_toFun := (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x).cont
  continuous_invFun :=
    (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
      (gR c d aD hRq x)).cont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.rightDifferential then
    throwError "Refusing to shadow existing declaration OrientationAssembly.rightDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.rightDifferential ``Submission.OrientationAssembly.rightDifferential

theorem mfderiv_gR_eq_rightDifferential (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x
      = (rightDifferential c d aD hRq x).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_gR_eq_rightDifferential then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_gR_eq_rightDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_gR_eq_rightDifferential ``Submission.OrientationAssembly.mfderiv_gR_eq_rightDifferential

theorem bijective_mfderiv_gR (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x) := by
  rw [mfderiv_gR_eq_rightDifferential c d aD hRq x]
  exact (rightDifferential c d aD hRq x).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.bijective_mfderiv_gR then
    throwError "Refusing to shadow existing declaration OrientationAssembly.bijective_mfderiv_gR"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.bijective_mfderiv_gR ``Submission.OrientationAssembly.bijective_mfderiv_gR

end ChainRules

section Pieces

theorem finrank_csModel : Module.finrank ℝ csModel = 3 := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.finrank_csModel then
    throwError "Refusing to shadow existing declaration OrientationAssembly.finrank_csModel"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.finrank_csModel ``Submission.OrientationAssembly.finrank_csModel

def chartPartialDiffeomorph
    (e : OpenPartialHomeomorph (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) csModel)
    (he : e ∈ atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    PartialDiffeomorph (𝓡 3) (𝓡 3)
      (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) csModel ∞ where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.chartPartialDiffeomorph then
    throwError "Refusing to shadow existing declaration OrientationAssembly.chartPartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.chartPartialDiffeomorph ``Submission.OrientationAssembly.chartPartialDiffeomorph

def reindexManifoldOrientation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H M' : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] {n m : ℕ} (e : Fin n ≃ Fin m)
    (o : DifferentialGeometry.ManifoldOrientation I M' n) :
    DifferentialGeometry.ManifoldOrientation I M' m where
  dimension_eq := o.dimension_eq.trans (by simpa using Fintype.card_congr e)
  orientation x := Orientation.reindex ℝ E e (o.orientation x)
  locally_constant p x hx := by
    obtain ⟨U, hUo, hxU, hU, h⟩ := o.locally_constant p x hx
    refine ⟨U, hUo, hxU, hU, fun y hy => ?_⟩
    have h1 := orientation_reindex_map_comm (R := ℝ) (M := TangentSpace I y) (N := E) e
      (DifferentialGeometry.tangentChartEquiv I M' p y (hU hy)) (o.orientation y)
    have h2 := orientation_reindex_map_comm (R := ℝ) (M := TangentSpace I x) (N := E) e
      (DifferentialGeometry.tangentChartEquiv I M' p x hx) (o.orientation x)
    exact h1.symm.trans ((congrArg (Orientation.reindex ℝ E e) (h y hy)).trans h2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.reindexManifoldOrientation then
    throwError "Refusing to shadow existing declaration OrientationAssembly.reindexManifoldOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.reindexManifoldOrientation ``Submission.OrientationAssembly.reindexManifoldOrientation

def orientationFinrank (M : ClosedOrientedManifold.{u} 3) :
    DifferentialGeometry.ManifoldOrientation (𝓡 3) M.Carrier (Module.finrank ℝ csModel) :=
  reindexManifoldOrientation (𝓡 3) csIdx M.orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.orientationFinrank then
    throwError "Refusing to shadow existing declaration OrientationAssembly.orientationFinrank"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.orientationFinrank ``Submission.OrientationAssembly.orientationFinrank

theorem orientationFinrank_orientation (M : ClosedOrientedManifold.{u} 3) (x : M.Carrier) :
    (orientationFinrank M).orientation x
      = Orientation.reindex ℝ csModel csIdx (M.orientation.orientation x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.orientationFinrank_orientation then
    throwError "Refusing to shadow existing declaration OrientationAssembly.orientationFinrank_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.orientationFinrank_orientation ``Submission.OrientationAssembly.orientationFinrank_orientation

def oMrestrict : SmoothOrientation (𝓡 3) c.toBallChart.interior :=
  restrictSmoothOrientation (𝓡 3) c.toBallChart.interior
    (smoothOrientationOfManifoldOrientation (𝓡 3) (orientationFinrank M))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.oMrestrict then
    throwError "Refusing to shadow existing declaration OrientationAssembly.oMrestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.oMrestrict ``Submission.OrientationAssembly.oMrestrict

theorem oMrestrict_apply (u : c.toBallChart.interior) :
    (oMrestrict c).val u
      = Orientation.reindex ℝ csModel csIdx (M.orientation.orientation u) := by
  unfold oMrestrict restrictSmoothOrientation smoothOrientationOfManifoldOrientation
    orientationFinrank reindexManifoldOrientation
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.oMrestrict_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.oMrestrict_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.oMrestrict_apply ``Submission.OrientationAssembly.oMrestrict_apply

def oNrestrict : SmoothOrientation (𝓡 3) d.toBallChart.interior :=
  restrictSmoothOrientation (𝓡 3) d.toBallChart.interior
    (smoothOrientationOfManifoldOrientation (𝓡 3) (orientationFinrank N))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.oNrestrict then
    throwError "Refusing to shadow existing declaration OrientationAssembly.oNrestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.oNrestrict ``Submission.OrientationAssembly.oNrestrict

theorem oNrestrict_apply (v : d.toBallChart.interior) :
    (oNrestrict d).val v
      = Orientation.reindex ℝ csModel csIdx (N.orientation.orientation v) := by
  unfold oNrestrict restrictSmoothOrientation smoothOrientationOfManifoldOrientation
    orientationFinrank reindexManifoldOrientation
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.oNrestrict_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.oNrestrict_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.oNrestrict_apply ``Submission.OrientationAssembly.oNrestrict_apply

def SO_L (hLq : AtlasLeft c d aD) : SmoothOrientation (𝓡 3) (qL c d aD hLq) :=
  pullbackSmoothOrientation (𝓡 3) (𝓡 3) (gL c d aD hLq)
    (contMDiff_gL c d aD hLq) (bijective_mfderiv_gL c d aD hLq) (oMrestrict c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_L then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_L"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_L ``Submission.OrientationAssembly.SO_L

def SO_R (hRq : AtlasRight c d aD) : SmoothOrientation (𝓡 3) (qR c d aD hRq) :=
  pullbackSmoothOrientation (𝓡 3) (𝓡 3) (gR c d aD hRq)
    (contMDiff_gR c d aD hRq) (bijective_mfderiv_gR c d aD hRq) (oNrestrict d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_R then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_R"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_R ``Submission.OrientationAssembly.SO_R

def seamChartFun : qS c d aD → csModel :=
  fun x => seamChartX c.toBallChart d.toBallChart aD.toHomeomorph x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seamChartFun then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seamChartFun"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seamChartFun ``Submission.OrientationAssembly.seamChartFun

theorem contMDiff_seamChartFun (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (seamChartFun c d aD) := by
  intro x
  have hcont : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hS)
  have hx : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := x.2
  exact (contMDiffAt_subtype_iff (U := qS c d aD) (f :=
    (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)) (x := x)).mpr
    (hcont.contMDiffAt ((seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).open_source.mem_nhds hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.contMDiff_seamChartFun then
    throwError "Refusing to shadow existing declaration OrientationAssembly.contMDiff_seamChartFun"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.contMDiff_seamChartFun ``Submission.OrientationAssembly.contMDiff_seamChartFun

theorem mfderiv_seamChartFun (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qS c d aD) : mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD) x =
      mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
        (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) := by
  have hmd : MDifferentiableAt (𝓡 3) (𝓡 3)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (chartPartialDiffeomorph c d aD (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) hS)
      x.2).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := x) (f := (Subtype.val : qS c d aD →
      ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (g := (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)) hmd
    (contMDiff_subtype_val.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp))
  apply ContinuousLinearMap.ext
  intro v
  have h2 := DFunLike.congr_fun hcomp v
  change (mfderiv (𝓡 3) (𝓡 3)
      ((seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) ∘
        (Subtype.val : qS c d aD →
          ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) x) v =
    (mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) v
  simpa [DifferentialGeometry.mfderiv_subtype_val_apply] using h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_seamChartFun then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_seamChartFun"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_seamChartFun ``Submission.OrientationAssembly.mfderiv_seamChartFun

theorem bijective_mfderiv_seamChartFun (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qS c d aD) : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD) x) := by
  rw [mfderiv_seamChartFun c d aD hS x]
  have hb := ((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (chartPartialDiffeomorph c d aD (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) hS)
      x.2).mfderivToContinuousLinearEquiv (show (∞ : ℕ∞ω) ≠ 0 by simp)).bijective
  exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.bijective_mfderiv_seamChartFun then
    throwError "Refusing to shadow existing declaration OrientationAssembly.bijective_mfderiv_seamChartFun"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.bijective_mfderiv_seamChartFun ``Submission.OrientationAssembly.bijective_mfderiv_seamChartFun

def SO_S (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    SmoothOrientation (𝓡 3) (qS c d aD) :=
  pullbackSmoothOrientation (𝓡 3) 𝓘(ℝ, csModel) (seamChartFun c d aD)
    (contMDiff_seamChartFun c d aD hS) (bijective_mfderiv_seamChartFun c d aD hS)
    (euclideanSmoothOrientation csModel stdOrientationModel)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_S then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_S"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_S ``Submission.OrientationAssembly.SO_S

end Pieces

section CoordinateDetection

theorem boundaryMap_mem_chart_closedBall' (z : csSphere) :
    ((c.toBallChart.boundaryMap z : c.toBallChart.Punctured) : M.Carrier) ∈
      c.toBallChart.chart '' Metric.closedBall (0 : csModel) 1 :=
  ⟨(z : csModel), by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (norm_coe_sphere z), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.boundaryMap_mem_chart_closedBall' then
    throwError "Refusing to shadow existing declaration OrientationAssembly.boundaryMap_mem_chart_closedBall'"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.boundaryMap_mem_chart_closedBall' ``Submission.OrientationAssembly.boundaryMap_mem_chart_closedBall'

theorem interiorToPunctured_not_mem_chart_closedBall' (u : c.toBallChart.interior) :
    ((c.toBallChart.interiorToPunctured u : c.toBallChart.Punctured) : M.Carrier) ∉
      c.toBallChart.chart '' Metric.closedBall (0 : csModel) 1 :=
  u.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.interiorToPunctured_not_mem_chart_closedBall' then
    throwError "Refusing to shadow existing declaration OrientationAssembly.interiorToPunctured_not_mem_chart_closedBall'"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.interiorToPunctured_not_mem_chart_closedBall' ``Submission.OrientationAssembly.interiorToPunctured_not_mem_chart_closedBall'

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem mem_qS_iff (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :
    x ∈ qS c d aD ↔
      x ∈ (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mem_qS_iff then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mem_qS_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mem_qS_iff ``Submission.OrientationAssembly.mem_qS_iff

theorem interiorLeft_ne_inr (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) (q : d.toBallChart.Punctured) :
    interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x) ≠
      inr c.toBallChart d.toBallChart aD.toHomeomorph q := by
  intro h
  obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart aD.toHomeomorph
    (c.toBallChart.interiorToPunctured (gL c d aD hLq x)) q).mp h
  exact interiorToPunctured_not_mem_chart_closedBall' c (gL c d aD hLq x)
    (hz ▸ boundaryMap_mem_chart_closedBall' c z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.interiorLeft_ne_inr then
    throwError "Refusing to shadow existing declaration OrientationAssembly.interiorLeft_ne_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.interiorLeft_ne_inr ``Submission.OrientationAssembly.interiorLeft_ne_inr

theorem exists_left_coordinate (hLq : AtlasLeft c d aD) (x : qL c d aD hLq)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    ∃ w : csModel, w ∈ SeamShell ∧ 1 < ‖w‖ ∧
      ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w ∧
      seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
        (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) = w := by
  rw [mem_qS_iff] at hSp
  rw [seamChartX_source c.toBallChart d.toBallChart aD.toHomeomorph] at hSp
  obtain ⟨⟨w, hw⟩, hwmap⟩ := hSp
  have hnotlt : ¬ ‖w‖ < 1 := by
    intro hlt
    have h2 := seamMap_eq_inr_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw hlt
    exact interiorLeft_ne_inr c d aD hLq x _
      ((gL_spec c d aD hLq x).trans (hwmap.symm.trans h2))
  have h1 : 1 ≤ ‖w‖ := le_of_not_gt hnotlt
  have hseam : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) = w := by
    rw [show (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) =
        seamMap c.toBallChart d.toBallChart aD.toHomeomorph ⟨w, hw⟩ from hwmap.symm,
      seamMap_eq_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw h1]
    exact seamChartX_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw h1
  have hdeep : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w := by
    have hkey : c.toBallChart.interiorToPunctured (gL c d aD hLq x) =
        puncturedOfCoord c.toBallChart w hw h1 :=
      inl_injective c.toBallChart d.toBallChart aD.toHomeomorph (by
        calc inl c.toBallChart d.toBallChart aD.toHomeomorph
              (c.toBallChart.interiorToPunctured (gL c d aD hLq x))
            = interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x) := rfl
          _ = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
              gL_spec c d aD hLq x
          _ = seamMap c.toBallChart d.toBallChart aD.toHomeomorph ⟨w, hw⟩ := hwmap.symm
          _ = inl c.toBallChart d.toBallChart aD.toHomeomorph
                (puncturedOfCoord c.toBallChart w hw h1) :=
              seamMap_eq_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw h1)
    calc ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier)
        = ((c.toBallChart.interiorToPunctured (gL c d aD hLq x) : c.toBallChart.Punctured) :
            M.Carrier) := rfl
      _ = ((puncturedOfCoord c.toBallChart w hw h1 : c.toBallChart.Punctured) : M.Carrier) := by
            rw [hkey]
      _ = c.toBallChart.chart w := puncturedOfCoord_val c.toBallChart w hw h1
  have hwpos : 1 < ‖w‖ := by
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      refine (gL c d aD hLq x).2 ?_
      refine ⟨w, ?_, hdeep.symm⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq h.symm
  exact ⟨w, hw, hwpos, hdeep, hseam⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.exists_left_coordinate then
    throwError "Refusing to shadow existing declaration OrientationAssembly.exists_left_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.exists_left_coordinate ``Submission.OrientationAssembly.exists_left_coordinate

end CoordinateDetection

section LeftAgreement

variable (hLq : AtlasLeft c d aD)

theorem chart_source_of_mem_SeamShell (w : csModel) (hw : w ∈ SeamShell) :
    w ∈ c.toBallChart.chart.source := by
  apply c.toBallChart.closedBall_subset_source
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith [hw.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.chart_source_of_mem_SeamShell then
    throwError "Refusing to shadow existing declaration OrientationAssembly.chart_source_of_mem_SeamShell"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.chart_source_of_mem_SeamShell ``Submission.OrientationAssembly.chart_source_of_mem_SeamShell

theorem chart_target_of_coord (u : c.toBallChart.interior) (w : csModel)
    (hw : w ∈ SeamShell) (hu : (u : M.Carrier) = c.toBallChart.chart w) :
    (u : M.Carrier) ∈ c.toBallChart.chart.target := by
  rw [hu]
  exact c.toBallChart.chart.map_source (chart_source_of_mem_SeamShell c w hw)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.chart_target_of_coord then
    throwError "Refusing to shadow existing declaration OrientationAssembly.chart_target_of_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.chart_target_of_coord ``Submission.OrientationAssembly.chart_target_of_coord

theorem chart_symm_eq_of_coord (u : c.toBallChart.interior) (w : csModel)
    (hw : w ∈ SeamShell) (hu : (u : M.Carrier) = c.toBallChart.chart w) :
    c.toBallChart.chart.symm (u : M.Carrier) = w := by
  rw [hu]
  exact c.toBallChart.chart.left_inv (chart_source_of_mem_SeamShell c w hw)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.chart_symm_eq_of_coord then
    throwError "Refusing to shadow existing declaration OrientationAssembly.chart_symm_eq_of_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.chart_symm_eq_of_coord ``Submission.OrientationAssembly.chart_symm_eq_of_coord


theorem mdifferentiableAt_chartSymm (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    MDifferentiableAt (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
      (c.toBallChart.chart w) :=
  (c.toBallChart.chart.contMDiffOn_invFun.contMDiffAt
    (c.toBallChart.chart.open_target.mem_nhds (c.toBallChart.chart.map_source hw))).mdifferentiableAt
    (show (∞ : ℕ∞ω) ≠ 0 by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mdifferentiableAt_chartSymm then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mdifferentiableAt_chartSymm"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mdifferentiableAt_chartSymm ``Submission.OrientationAssembly.mdifferentiableAt_chartSymm

theorem mdifferentiableAt_chart (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    MDifferentiableAt (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w :=
  (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c.toBallChart.chart hw).mdifferentiableAt
    (show (∞ : ℕ∞ω) ≠ 0 by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mdifferentiableAt_chart then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mdifferentiableAt_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mdifferentiableAt_chart ``Submission.OrientationAssembly.mdifferentiableAt_chart

theorem mfderiv_chartSymm_comp_chart (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w)).comp
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w)
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) w) := by
  have hev : ((c.toBallChart.chart.symm : M.Carrier → csModel)) ∘
      ((c.toBallChart.chart : csModel → M.Carrier)) =ᶠ[𝓝 w] id :=
    Filter.eventuallyEq_of_mem (c.toBallChart.chart.open_source.mem_nhds hw)
      (fun y hy => c.toBallChart.chart.left_inv hy)
  have hcomp := mfderiv_comp (x := w) (f := ((c.toBallChart.chart : csModel → M.Carrier)))
    (g := ((c.toBallChart.chart.symm : M.Carrier → csModel)))
    (mdifferentiableAt_chartSymm c w hw) (mdifferentiableAt_chart c w hw)
  rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_id] at hcomp
  exact hcomp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_chartSymm_comp_chart then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_chartSymm_comp_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_chartSymm_comp_chart ``Submission.OrientationAssembly.mfderiv_chartSymm_comp_chart

theorem chart_symm_chart_apply (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    (c.toBallChart.chart.symm.toPartialEquiv) (c.toBallChart.chart.toPartialEquiv w) = w :=
  c.toBallChart.chart.left_inv hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.chart_symm_chart_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.chart_symm_chart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.chart_symm_chart_apply ``Submission.OrientationAssembly.chart_symm_chart_apply

theorem mfderiv_chart_comp_chartSymm (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w).comp
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w))
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) (c.toBallChart.chart w)) := by
  have hev : ((c.toBallChart.chart : csModel → M.Carrier)) ∘
      ((c.toBallChart.chart.symm : M.Carrier → csModel)) =ᶠ[𝓝 (c.toBallChart.chart w)] id :=
    Filter.eventuallyEq_of_mem
      (c.toBallChart.chart.open_target.mem_nhds (c.toBallChart.chart.map_source hw))
      (fun y hy => c.toBallChart.chart.right_inv hy)
  have hmem : c.toBallChart.chart.symm (c.toBallChart.chart w) ∈ c.toBallChart.chart.source :=
    c.toBallChart.chart.map_target (c.toBallChart.chart.map_source hw)
  have hmd1' : MDifferentiableAt (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier))
      (c.toBallChart.chart.symm (c.toBallChart.chart w)) :=
    (c.toBallChart.chart.contMDiffOn_toFun.contMDiffAt
      (c.toBallChart.chart.open_source.mem_nhds hmem)).mdifferentiableAt
      (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := c.toBallChart.chart w)
    (f := ((c.toBallChart.chart.symm : M.Carrier → csModel)))
    (g := ((c.toBallChart.chart : csModel → M.Carrier))) hmd1' (mdifferentiableAt_chartSymm c w hw)
  rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_id] at hcomp
  rw [chart_symm_chart_apply c w hw] at hcomp
  exact hcomp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_chart_comp_chartSymm then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_chart_comp_chartSymm"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_chart_comp_chartSymm ``Submission.OrientationAssembly.mfderiv_chart_comp_chartSymm


def chartSymmEquiv (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    TangentSpace (𝓡 3) (c.toBallChart.chart w) ≃L[ℝ] TangentSpace (𝓡 3) w where
  toFun := mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
    (c.toBallChart.chart w)
  invFun := mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w
  left_inv := by
    intro v
    exact DFunLike.congr_fun (mfderiv_chart_comp_chartSymm c w hw) v
  right_inv := by
    intro v
    exact DFunLike.congr_fun (mfderiv_chartSymm_comp_chart c w hw) v
  map_add' := (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
    (c.toBallChart.chart w)).map_add
  map_smul' := (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
    (c.toBallChart.chart w)).map_smul
  continuous_toFun := (mfderiv (𝓡 3) (𝓡 3)
    ((c.toBallChart.chart.symm : M.Carrier → csModel)) (c.toBallChart.chart w)).cont
  continuous_invFun := (mfderiv (𝓡 3) (𝓡 3)
    ((c.toBallChart.chart : csModel → M.Carrier)) w).cont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.chartSymmEquiv then
    throwError "Refusing to shadow existing declaration OrientationAssembly.chartSymmEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.chartSymmEquiv ``Submission.OrientationAssembly.chartSymmEquiv

theorem seam_interiorLeft_eventuallyEq (x : qL c d aD hLq) (w : csModel)
    (hw : w ∈ SeamShell) (h1w : 1 < ‖w‖) (h2w : ‖w‖ < 3 / 2)
    (hu : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w) :
    (fun z : c.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorLeft c.toBallChart d.toBallChart aD z)) =ᶠ[𝓝 (gL c d aD hLq x)]
      (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier)) := by
  have hwsrc : w ∈ c.toBallChart.chart.source := chart_source_of_mem_SeamShell c w hw
  have hmemT : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) ∈
      c.toBallChart.chart.target := by
    rw [hu]
    exact c.toBallChart.chart.map_source hwsrc
  have hcontSymm : ContinuousAt
      (fun z : M.Carrier => c.toBallChart.chart.symm z)
      ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) :=
    (c.toBallChart.chart.symm.contMDiffOn_toFun.contMDiffAt
      (c.toBallChart.chart.symm.open_source.mem_nhds hmemT)).continuousAt
  have hcont : ContinuousAt
      (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier))
      (gL c d aD hLq x) :=
    hcontSymm.comp (continuous_subtype_val.continuousAt (x := gL c d aD hLq x))
  have hnhds1 : (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier)) ⁻¹'
      {y : csModel | 1 < ‖y‖ ∧ ‖y‖ < 3 / 2} ∈ 𝓝 (gL c d aD hLq x) := by
    apply hcont.preimage_mem_nhds
    refine ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨?_, ?_⟩
    · rw [hu, chart_symm_chart_apply c w hwsrc]; exact h1w
    · rw [hu, chart_symm_chart_apply c w hwsrc]; exact h2w
  have hnhds2 : {z : c.toBallChart.interior | (z : M.Carrier) ∈ c.toBallChart.chart.target}
      ∈ 𝓝 (gL c d aD hLq x) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (c.toBallChart.chart.open_target.mem_nhds hmemT)
  filter_upwards [hnhds1, hnhds2] with z hz hzT
  have hzsrc : c.toBallChart.chart.symm (z : M.Carrier) ∈ c.toBallChart.chart.source :=
    c.toBallChart.chart.map_target hzT
  have hzchart : c.toBallChart.chart (c.toBallChart.chart.symm (z : M.Carrier)) =
      (z : M.Carrier) :=
    c.toBallChart.chart.right_inv hzT
  have hy1 : 1 ≤ ‖c.toBallChart.chart.symm (z : M.Carrier)‖ := le_of_lt hz.1
  have hyShell : c.toBallChart.chart.symm (z : M.Carrier) ∈ SeamShell :=
    ⟨by linarith [hz.1], hz.2⟩
  have hkey : puncturedOfCoord c.toBallChart (c.toBallChart.chart.symm (z : M.Carrier))
      hyShell hy1 = c.toBallChart.interiorToPunctured z := by
    apply Subtype.ext
    rw [puncturedOfCoord_val, BallChart.interiorToPunctured_val, hzchart]
  calc seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
        (interiorLeft c.toBallChart d.toBallChart aD z)
      = seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (inl c.toBallChart d.toBallChart aD.toHomeomorph
            (puncturedOfCoord c.toBallChart (c.toBallChart.chart.symm (z : M.Carrier))
              hyShell hy1)) := by
          rw [show interiorLeft c.toBallChart d.toBallChart aD z =
              inl c.toBallChart d.toBallChart aD.toHomeomorph
                (c.toBallChart.interiorToPunctured z) from rfl, ← hkey]
    _ = c.toBallChart.chart.symm (z : M.Carrier) :=
        seamChartX_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph _
          hyShell hy1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seam_interiorLeft_eventuallyEq then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seam_interiorLeft_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seam_interiorLeft_eventuallyEq ``Submission.OrientationAssembly.seam_interiorLeft_eventuallyEq

end LeftAgreement

section SeamDifferential

theorem mdifferentiableAt_seamChartX_of_atlas
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)
    (hx : x ∈ (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source) :
    MDifferentiableAt (𝓡 3) (𝓡 3)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) x :=
  (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
    (chartPartialDiffeomorph c d aD
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) hS) hx).mdifferentiableAt
    (show (∞ : ℕ∞ω) ≠ 0 by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mdifferentiableAt_seamChartX_of_atlas then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mdifferentiableAt_seamChartX_of_atlas"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mdifferentiableAt_seamChartX_of_atlas ``Submission.OrientationAssembly.mdifferentiableAt_seamChartX_of_atlas

theorem seam_interiorLeft_chain (hLq : AtlasLeft c d aD)
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qL c d aD hLq) (w : csModel) (hw : w ∈ SeamShell) (h1w : 1 < ‖w‖)
    (hu : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩).comp
      (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
        (gL c d aD hLq x))
    = mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w) := by
  have hxsrc : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := hSp
  have hSx : MDifferentiableAt (𝓡 3) (𝓡 3)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)) := by
    rw [gL_spec c d aD hLq x]
    exact mdifferentiableAt_seamChartX_of_atlas c d aD hS _ hxsrc
  have hIL : MDifferentiableAt (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
      (gL c d aD hLq x) :=
    ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq)
      (gL c d aD hLq x)).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := gL c d aD hLq x)
    (f := (interiorLeft c.toBallChart d.toBallChart aD))
    (g := (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)) hSx hIL
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : c.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorLeft c.toBallChart d.toBallChart aD z)) (gL c d aD hLq x) =
      (mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
          (interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x))).comp
        (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
          (gL c d aD hLq x)) := hcomp
  have hev' : (fun z : c.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorLeft c.toBallChart d.toBallChart aD z)) =ᶠ[𝓝 (gL c d aD hLq x)]
      (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier)) :=
    seam_interiorLeft_eventuallyEq c d aD hLq x w hw h1w hw.2 hu
  have hsub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : c.toBallChart.interior → M.Carrier) (gL c d aD hLq x) :=
    contMDiff_subtype_val.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcs : MDifferentiableAt (𝓡 3) (𝓡 3)
      ((c.toBallChart.chart.symm : M.Carrier → csModel))
      ((Subtype.val : c.toBallChart.interior → M.Carrier) (gL c d aD hLq x)) := by
    rw [hu]
    exact mdifferentiableAt_chartSymm c w (chart_source_of_mem_SeamShell c w hw)
  have hA : mfderiv (𝓡 3) (𝓡 3)
      (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier))
      (gL c d aD hLq x) =
      mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w) := by
    rw [show (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier)) =
        ((c.toBallChart.chart.symm : M.Carrier → csModel) ∘
          (Subtype.val : c.toBallChart.interior → M.Carrier)) from rfl]
    rw [mfderiv_comp (x := gL c d aD hLq x)
      (f := (Subtype.val : c.toBallChart.interior → M.Carrier))
      (g := (c.toBallChart.chart.symm : M.Carrier → csModel)) hcs hsub]
    rw [hu]
    apply ContinuousLinearMap.ext
    intro v
    change (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
          (c.toBallChart.chart w))
        ((mfderiv (𝓡 3) (𝓡 3) (Subtype.val : c.toBallChart.interior → M.Carrier)
          (gL c d aD hLq x)) v) =
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w)) v
    rw [DifferentialGeometry.mfderiv_subtype_val_apply]
  have hSfun : mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)) =
      mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩ := by
    rw [gL_spec c d aD hLq x,
      ← mfderiv_seamChartFun c d aD hS
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩]
  rw [← hSfun]
  exact hcomp'.symm.trans (hev'.mfderiv_eq.trans hA)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seam_interiorLeft_chain then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seam_interiorLeft_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seam_interiorLeft_chain ``Submission.OrientationAssembly.seam_interiorLeft_chain

end SeamDifferential

section Differentials

variable (hLq : AtlasLeft c d aD)
variable (hRq : AtlasRight c d aD)
variable (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
  atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))

def seamDifferential (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (y : qS c d aD) : csModel ≃L[ℝ] csModel :=
  DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective (𝓡 3) 𝓘(ℝ, csModel)
    (seamChartFun c d aD) (bijective_mfderiv_seamChartFun c d aD hS) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seamDifferential then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seamDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seamDifferential ``Submission.OrientationAssembly.seamDifferential

theorem seamDifferential_apply (y : qS c d aD) (v : csModel) :
    seamDifferential c d aD hS y v =
      mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD) y v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seamDifferential_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seamDifferential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seamDifferential_apply ``Submission.OrientationAssembly.seamDifferential_apply

theorem SO_S_apply (y : qS c d aD) :
    (SO_S c d aD hS).val y =
      tangentOrientationEquiv (seamDifferential c d aD hS y).symm.toLinearEquiv
        stdOrientationModel := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_S_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_S_apply ``Submission.OrientationAssembly.SO_S_apply

theorem SO_S_apply_map (y : qS c d aD) :
    (SO_S c d aD hS).val y =
      Orientation.map (Fin (Module.finrank ℝ csModel))
        (seamDifferential c d aD hS y).symm.toLinearEquiv stdOrientationModel := by
  rw [SO_S_apply, tangentOrientationEquiv_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_S_apply_map then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_S_apply_map"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_S_apply_map ``Submission.OrientationAssembly.SO_S_apply_map

def leftDifferentialEquiv (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    csModel ≃L[ℝ] csModel :=
  DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective (𝓡 3) (𝓡 3)
    (gL c d aD hLq) (bijective_mfderiv_gL c d aD hLq) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.leftDifferentialEquiv then
    throwError "Refusing to shadow existing declaration OrientationAssembly.leftDifferentialEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.leftDifferentialEquiv ``Submission.OrientationAssembly.leftDifferentialEquiv

theorem leftDifferentialEquiv_apply (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) (v : csModel) :
    leftDifferentialEquiv c d aD hLq x v =
      mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.leftDifferentialEquiv_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.leftDifferentialEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.leftDifferentialEquiv_apply ``Submission.OrientationAssembly.leftDifferentialEquiv_apply

theorem leftDifferentialEquiv_eq (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    leftDifferentialEquiv c d aD hLq x = leftDifferential c d aD hLq x := by
  apply ContinuousLinearEquiv.ext
  funext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.leftDifferentialEquiv_eq then
    throwError "Refusing to shadow existing declaration OrientationAssembly.leftDifferentialEquiv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.leftDifferentialEquiv_eq ``Submission.OrientationAssembly.leftDifferentialEquiv_eq

theorem leftDifferential_symm_apply (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) (v : csModel) :
    (leftDifferential c d aD hLq x).symm v =
      mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x) v :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.leftDifferential_symm_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.leftDifferential_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.leftDifferential_symm_apply ``Submission.OrientationAssembly.leftDifferential_symm_apply

theorem SO_L_apply (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    (SO_L c d aD hLq).val x =
      tangentOrientationEquiv (leftDifferentialEquiv c d aD hLq x).symm.toLinearEquiv
        ((oMrestrict c).val (gL c d aD hLq x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_L_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_L_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_L_apply ``Submission.OrientationAssembly.SO_L_apply

theorem SO_L_apply_map (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    (SO_L c d aD hLq).val x =
      Orientation.map (Fin (Module.finrank ℝ csModel))
        (leftDifferentialEquiv c d aD hLq x).symm.toLinearEquiv
        (Orientation.reindex ℝ csModel csIdx
          (M.orientation.orientation (gL c d aD hLq x))) := by
  rw [SO_L_apply, oMrestrict_apply, tangentOrientationEquiv_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_L_apply_map then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_L_apply_map"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_L_apply_map ``Submission.OrientationAssembly.SO_L_apply_map

def rightDifferentialEquiv (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    csModel ≃L[ℝ] csModel :=
  DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective (𝓡 3) (𝓡 3)
    (gR c d aD hRq) (bijective_mfderiv_gR c d aD hRq) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.rightDifferentialEquiv then
    throwError "Refusing to shadow existing declaration OrientationAssembly.rightDifferentialEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.rightDifferentialEquiv ``Submission.OrientationAssembly.rightDifferentialEquiv

theorem rightDifferentialEquiv_eq (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    rightDifferentialEquiv c d aD hRq x = rightDifferential c d aD hRq x := by
  apply ContinuousLinearEquiv.ext
  funext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.rightDifferentialEquiv_eq then
    throwError "Refusing to shadow existing declaration OrientationAssembly.rightDifferentialEquiv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.rightDifferentialEquiv_eq ``Submission.OrientationAssembly.rightDifferentialEquiv_eq

theorem rightDifferential_symm_apply (hRq : AtlasRight c d aD) (x : qR c d aD hRq) (v : csModel) :
    (rightDifferential c d aD hRq x).symm v =
      mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x) v :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.rightDifferential_symm_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.rightDifferential_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.rightDifferential_symm_apply ``Submission.OrientationAssembly.rightDifferential_symm_apply

theorem SO_R_apply (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    (SO_R c d aD hRq).val x =
      tangentOrientationEquiv (rightDifferentialEquiv c d aD hRq x).symm.toLinearEquiv
        ((oNrestrict d).val (gR c d aD hRq x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_R_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_R_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_R_apply ``Submission.OrientationAssembly.SO_R_apply

theorem SO_R_apply_map (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    (SO_R c d aD hRq).val x =
      Orientation.map (Fin (Module.finrank ℝ csModel))
        (rightDifferentialEquiv c d aD hRq x).symm.toLinearEquiv
        (Orientation.reindex ℝ csModel csIdx
          (N.orientation.orientation (gR c d aD hRq x))) := by
  rw [SO_R_apply, oNrestrict_apply, tangentOrientationEquiv_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_R_apply_map then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_R_apply_map"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_R_apply_map ``Submission.OrientationAssembly.SO_R_apply_map

end Differentials

section LeftAgreement

theorem chartTangentEquiv_apply (c : OrientedBallChart M) {x : csModel} (hx : x ∈ c.chart.source)
    (v : csModel) : chartTangentEquiv c hx v = mfderiv (𝓡 3) (𝓡 3) (c.chart : csModel →
      M.Carrier) x v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.chartTangentEquiv_apply then
    throwError "Refusing to shadow existing declaration OrientationAssembly.chartTangentEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.chartTangentEquiv_apply ``Submission.OrientationAssembly.chartTangentEquiv_apply

theorem orientation_eq_map_chartTangentEquiv (c : OrientedBallChart M) {x : csModel}
    (hx : x ∈ c.chart.source) :
    M.orientation.orientation (c.chart x) =
      Orientation.map (Fin 3) (chartTangentEquiv c hx).toLinearEquiv (stdOrientation x) := by
  have h := congrArg (Orientation.map (Fin 3) (chartTangentEquiv c hx).toLinearEquiv)
    (orientation_map_chartTangentEquiv_symm c hx)
  rw [orientation_map_symm_map_self (chartTangentEquiv c hx).toLinearEquiv
    (M.orientation.orientation (c.chart x))] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.orientation_eq_map_chartTangentEquiv then
    throwError "Refusing to shadow existing declaration OrientationAssembly.orientation_eq_map_chartTangentEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.orientation_eq_map_chartTangentEquiv ``Submission.OrientationAssembly.orientation_eq_map_chartTangentEquiv

theorem seamDifferential_symm_eq (hLq : AtlasLeft c d aD)
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qL c d aD hLq) (w : csModel) (hw : w ∈ SeamShell) (h1w : 1 < ‖w‖)
    (hu : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩).symm.toLinearEquiv
      = (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv.trans
          (leftDifferential c d aD hLq x).symm.toLinearEquiv := by
  have hchain := seam_interiorLeft_chain c d aD hLq hS x w hw h1w hu hSp
  apply LinearEquiv.ext
  intro v
  change (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
      d.toBallChart aD.toHomeomorph), hSp⟩).symm v =
    (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x))
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w v)
  refine (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
    d.toBallChart aD.toHomeomorph), hSp⟩).toLinearEquiv.injective ?_
  erw [show (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩)
      ((seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩).symm v) = v from
    LinearEquiv.apply_symm_apply _ v]
  change v = ((mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
      ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩).comp
    (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x)))
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w v)
  erw [DFunLike.congr_fun hchain (mfderiv (𝓡 3) (𝓡 3)
    ((c.toBallChart.chart : csModel → M.Carrier)) w v)]
  exact ((chartSymmEquiv c w (chart_source_of_mem_SeamShell c w hw)).right_inv v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seamDifferential_symm_eq then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seamDifferential_symm_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seamDifferential_symm_eq ``Submission.OrientationAssembly.seamDifferential_symm_eq

theorem SO_L_eq_SO_S (hLq : AtlasLeft c d aD)
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qL c d aD hLq)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (SO_L c d aD hLq).val x =
      (SO_S c d aD hS).val ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩ := by
  obtain ⟨w, hw, h1w, hdeep, -⟩ := exists_left_coordinate c d aD hLq x hSp
  have hchain := seamDifferential_symm_eq c d aD hLq hS x w hw h1w hdeep hSp
  have hchart : M.orientation.orientation
      ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) =
      Orientation.map (Fin 3)
        (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv
        (stdOrientation w) := by
    rw [hdeep]
    exact orientation_eq_map_chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)
  rw [SO_L_apply_map, SO_S_apply_map, hchain]
  erw [← orientation_map_map_trans (R := ℝ)
    (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv
    (leftDifferential c d aD hLq x).symm.toLinearEquiv stdOrientationModel]
  erw [leftDifferentialEquiv_eq]
  erw [hchart]
  erw [show Orientation.reindex ℝ csModel csIdx
        (Orientation.map (Fin 3)
          (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv
          (stdOrientation w)) =
      Orientation.map (Fin (Module.finrank ℝ csModel))
        (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv
        (Orientation.reindex ℝ csModel csIdx (stdOrientation w)) from
    orientation_reindex_map_comm csIdx
      (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv (stdOrientation w)]
  erw [← stdOrientationModel_eq_reindex w]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_L_eq_SO_S then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_L_eq_SO_S"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_L_eq_SO_S ``Submission.OrientationAssembly.SO_L_eq_SO_S

end LeftAgreement

section RightCoordinate

variable (hRq : AtlasRight c d aD)

theorem inl_ne_interiorRight (p : c.toBallChart.Punctured) (x : qR c d aD hRq) :
    inl c.toBallChart d.toBallChart aD.toHomeomorph p ≠
      interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x) := by
  intro h
  obtain ⟨z, -, hz⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart aD.toHomeomorph p
    (d.toBallChart.interiorToPunctured (gR c d aD hRq x))).mp h
  have h1 : ((d.toBallChart.boundaryMap (aD.toHomeomorph z) : d.toBallChart.Punctured) :
      N.Carrier) = ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) := by
    rw [← BallChart.interiorToPunctured_val (c := d.toBallChart) (gR c d aD hRq x), ← hz]
  exact interiorToPunctured_not_mem_chart_closedBall' d (gR c d aD hRq x)
    (h1 ▸ boundaryMap_mem_chart_closedBall' d (aD.toHomeomorph z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.inl_ne_interiorRight then
    throwError "Refusing to shadow existing declaration OrientationAssembly.inl_ne_interiorRight"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.inl_ne_interiorRight ``Submission.OrientationAssembly.inl_ne_interiorRight

theorem exists_right_coordinate (x : qR c d aD hRq)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD)
    (hT : 1 / 2 < ‖seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)‖) :
    ∃ y : csModel, y ∈ SeamShell ∧ 1 < ‖y‖ ∧
      ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y ∧
      seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
        (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) =
        reflectMapInv aD.toHomeomorph y := by
  rw [mem_qS_iff] at hSp
  rw [seamChartX_source c.toBallChart d.toBallChart aD.toHomeomorph] at hSp
  obtain ⟨⟨w, hw⟩, hwmap⟩ := hSp
  have hnotle : ¬ 1 ≤ ‖w‖ := by
    intro h1
    refine inl_ne_interiorRight c d aD hRq (puncturedOfCoord c.toBallChart w hw h1) x ?_
    rw [← seamMap_eq_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw h1,
      hwmap, ← gR_spec c d aD hRq x]
  have hlt : ‖w‖ < 1 := not_le.mp hnotle
  have hkey : puncturedOfCoord d.toBallChart (reflectMap aD.toHomeomorph w)
      (reflectMap_mem_SeamShell aD.toHomeomorph w hw)
      (one_le_norm_reflectMap aD.toHomeomorph w hlt)
      = d.toBallChart.interiorToPunctured (gR c d aD hRq x) :=
    inr_injective c.toBallChart d.toBallChart aD.toHomeomorph (by
      show inr c.toBallChart d.toBallChart aD.toHomeomorph (puncturedOfCoord d.toBallChart
          (reflectMap aD.toHomeomorph w) (reflectMap_mem_SeamShell aD.toHomeomorph w hw)
          (one_le_norm_reflectMap aD.toHomeomorph w hlt)) =
        inr c.toBallChart d.toBallChart aD.toHomeomorph
          (d.toBallChart.interiorToPunctured (gR c d aD hRq x))
      rw [← seamMap_eq_inr_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw hlt,
        hwmap]
      exact (gR_spec c d aD hRq x).symm)
  have hy_eq : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) =
      d.toBallChart.chart (reflectMap aD.toHomeomorph w) := by
    rw [← BallChart.interiorToPunctured_val (c := d.toBallChart) (gR c d aD hRq x), ← hkey]
    rfl
  have hwnorm : ‖w‖ = ‖seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)‖ := by
    rw [← hwmap, seamChartX_apply_seamMap]
  have hnormy : ‖reflectMap aD.toHomeomorph w‖ = 2 - ‖w‖ :=
    norm_reflectMap (a := aD.toHomeomorph) (x := w) (by linarith [hw.2])
  refine ⟨reflectMap aD.toHomeomorph w, reflectMap_mem_SeamShell aD.toHomeomorph w hw, ?_, hy_eq, ?_⟩
  · rw [hnormy]; linarith
  · rw [← hwmap, seamChartX_apply_seamMap]
    change (w : csModel) = reflectMapInv aD.toHomeomorph (reflectMap aD.toHomeomorph w)
    exact (reflectMapInv_reflectMap aD.toHomeomorph ⟨w, hw⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.exists_right_coordinate then
    throwError "Refusing to shadow existing declaration OrientationAssembly.exists_right_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.exists_right_coordinate ``Submission.OrientationAssembly.exists_right_coordinate

end RightCoordinate

section RightTransition

variable (hRq : AtlasRight c d aD)

theorem seam_interiorRight_eventuallyEq (x : qR c d aD hRq) (y : csModel)
    (hy : y ∈ SeamShell) (h1y : 1 < ‖y‖)
    (hu : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y) :
    (fun z : d.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorRight c.toBallChart d.toBallChart aD z)) =ᶠ[𝓝 (gR c d aD hRq x)]
      (fun z : d.toBallChart.interior =>
        rightSeamTransition c.toBallChart d.toBallChart aD.toHomeomorph
          (d.toBallChart.chart.symm (z : N.Carrier))) := by
  have hysrc : y ∈ d.toBallChart.chart.source := chart_source_of_mem_SeamShell d y hy
  have hmemT : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) ∈
      d.toBallChart.chart.target := by
    rw [hu]
    exact d.toBallChart.chart.map_source hysrc
  have hcont : ContinuousAt
      (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
      (gR c d aD hRq x) :=
    ((d.toBallChart.chart.symm.contMDiffOn_toFun.contMDiffAt
      (d.toBallChart.chart.symm.open_source.mem_nhds hmemT)).continuousAt).comp
      (continuous_subtype_val.continuousAt (x := gR c d aD hRq x))
  have hsymm : d.toBallChart.chart.symm
      ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = y := by
    rw [hu]
    exact d.toBallChart.chart.left_inv hysrc
  have hnhds1 : (fun z : d.toBallChart.interior =>
      d.toBallChart.chart.symm (z : N.Carrier)) ⁻¹'
      {y' : csModel | y' ∈ SeamShell ∧ 1 ≤ ‖y'‖} ∈ 𝓝 (gR c d aD hRq x) := by
    have hbase : {y' : csModel | y' ∈ SeamShell ∧ 1 < ‖y'‖} ∈
        𝓝 (d.toBallChart.chart.symm
          ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier)) := by
      rw [hsymm]
      exact (isOpen_seamShell.inter (isOpen_lt continuous_const continuous_norm)).mem_nhds
        ⟨hy, h1y⟩
    refine hcont.preimage_mem_nhds (Filter.mem_of_superset hbase ?_)
    intro y' hy'
    exact ⟨hy'.1, le_of_lt hy'.2⟩
  have hnhds2 : {z : d.toBallChart.interior |
      (z : N.Carrier) ∈ d.toBallChart.chart.target} ∈ 𝓝 (gR c d aD hRq x) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (d.toBallChart.chart.open_target.mem_nhds hmemT)
  filter_upwards [hnhds1, hnhds2] with z hz hzT
  obtain ⟨hzShell, hz1⟩ := hz
  have hzchart : d.toBallChart.chart (d.toBallChart.chart.symm (z : N.Carrier)) =
      (z : N.Carrier) :=
    d.toBallChart.chart.right_inv hzT
  have hkey : puncturedOfCoord d.toBallChart (d.toBallChart.chart.symm (z : N.Carrier))
      hzShell hz1 = d.toBallChart.interiorToPunctured z := by
    apply Subtype.ext
    rw [puncturedOfCoord_val, BallChart.interiorToPunctured_val, hzchart]
  rw [rightSeamTransition, dif_pos ⟨hzShell, hz1⟩]
  congr 1
  rw [show interiorRight c.toBallChart d.toBallChart aD z =
      inr c.toBallChart d.toBallChart aD.toHomeomorph (d.toBallChart.interiorToPunctured z)
      from rfl, hkey]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seam_interiorRight_eventuallyEq then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seam_interiorRight_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seam_interiorRight_eventuallyEq ``Submission.OrientationAssembly.seam_interiorRight_eventuallyEq

end RightTransition

section RightChain

variable (hRq : AtlasRight c d aD)

theorem mdifferentiableAt_reflectMapInv {y : csModel} (hy : y ≠ 0) :
    MDifferentiableAt (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y := by
  rw [reflectMapInv_eq_reflectMap_symm aD]
  exact mdifferentiableAt_iff_differentiableAt.mpr
    (hasFDerivAt_reflectMap aD.symm hy).differentiableAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mdifferentiableAt_reflectMapInv then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mdifferentiableAt_reflectMapInv"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mdifferentiableAt_reflectMapInv ``Submission.OrientationAssembly.mdifferentiableAt_reflectMapInv

theorem mfderiv_chartSymm_subtype (v : d.toBallChart.interior) (y : csModel)
    (hy : y ∈ d.toBallChart.chart.source)
    (hu : ((v : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y) :
    mfderiv (𝓡 3) (𝓡 3)
        (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier)) v
      = mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
          ((v : d.toBallChart.interior) : N.Carrier) := by
  have hsub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : d.toBallChart.interior → N.Carrier) v :=
    contMDiff_subtype_val.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hchart : MDifferentiableAt (𝓡 3) (𝓡 3)
      ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((Subtype.val : d.toBallChart.interior → N.Carrier) v) := by
    rw [hu]
    exact mdifferentiableAt_chartSymm d y hy
  have hcomp := mfderiv_comp (x := v) (f := (Subtype.val : d.toBallChart.interior → N.Carrier))
    (g := ((d.toBallChart.chart.symm : N.Carrier → csModel))) hchart hsub
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier)) v =
      (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
        ((Subtype.val : d.toBallChart.interior → N.Carrier) v)).comp
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : d.toBallChart.interior → N.Carrier) v) := hcomp
  rw [hcomp']
  apply ContinuousLinearMap.ext
  intro w
  change (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((v : d.toBallChart.interior) : N.Carrier))
    ((mfderiv (𝓡 3) (𝓡 3) (Subtype.val : d.toBallChart.interior → N.Carrier) v) w) =
    (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((v : d.toBallChart.interior) : N.Carrier)) w
  rw [DifferentialGeometry.mfderiv_subtype_val_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_chartSymm_subtype then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_chartSymm_subtype"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_chartSymm_subtype ``Submission.OrientationAssembly.mfderiv_chartSymm_subtype

end RightChain

section RightChainRule

variable (hRq : AtlasRight c d aD)

theorem seam_interiorRight_chain
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qR c d aD hRq) (y : csModel) (hy : y ∈ SeamShell) (h1y : 1 < ‖y‖)
    (hu : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩).comp
      (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x))
    = (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y).comp
        (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
          ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier)) := by
  have hysrc : y ∈ d.toBallChart.chart.source := chart_source_of_mem_SeamShell d y hy
  have hyne : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1y
    linarith
  have hyT : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) ∈
      d.toBallChart.chart.target := by
    rw [hu]
    exact d.toBallChart.chart.map_source hysrc
  have hxsrc : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := hSp
  have hSx : MDifferentiableAt (𝓡 3) (𝓡 3)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)) := by
    rw [gR_spec c d aD hRq x]
    exact mdifferentiableAt_seamChartX_of_atlas c d aD hS _ hxsrc
  have hIR : MDifferentiableAt (𝓡 3) (𝓡 3)
      (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x) :=
    ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq)
      (gR c d aD hRq x)).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := gR c d aD hRq x)
    (f := (interiorRight c.toBallChart d.toBallChart aD))
    (g := (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)) hSx hIR
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : d.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorRight c.toBallChart d.toBallChart aD z)) (gR c d aD hRq x) =
      (mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
          (interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x))).comp
        (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
          (gR c d aD hRq x)) := hcomp
  have hev' : (fun z : d.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorRight c.toBallChart d.toBallChart aD z)) =ᶠ[𝓝 (gR c d aD hRq x)]
      (fun z : d.toBallChart.interior =>
        rightSeamTransition c.toBallChart d.toBallChart aD.toHomeomorph
          (d.toBallChart.chart.symm (z : N.Carrier))) :=
    seam_interiorRight_eventuallyEq c d aD hRq x y hy h1y hu
  have hcontSymm : Filter.Tendsto
      (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
      (𝓝 (gR c d aD hRq x)) (𝓝 y) := by
    have hsymm : d.toBallChart.chart.symm
        ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = y := by
      rw [hu]
      exact d.toBallChart.chart.left_inv hysrc
    have hcont : ContinuousAt
        (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
        (gR c d aD hRq x) :=
      ((d.toBallChart.chart.symm.contMDiffOn_toFun.contMDiffAt
        (d.toBallChart.chart.symm.open_source.mem_nhds hyT)).continuousAt).comp
        (continuous_subtype_val.continuousAt (x := gR c d aD hRq x))
    rw [← hsymm]
    exact hcont
  have hevT : (fun z : d.toBallChart.interior =>
        rightSeamTransition c.toBallChart d.toBallChart aD.toHomeomorph
          (d.toBallChart.chart.symm (z : N.Carrier))) =ᶠ[𝓝 (gR c d aD hRq x)]
      (fun z : d.toBallChart.interior =>
        reflectMapInv aD.toHomeomorph (d.toBallChart.chart.symm (z : N.Carrier))) :=
    (rightSeamTransition_eventuallyEq c.toBallChart d.toBallChart aD.toHomeomorph y hy h1y)
      |>.comp_tendsto hcontSymm
  have hsubM : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : d.toBallChart.interior → N.Carrier) (gR c d aD hRq x) :=
    contMDiff_subtype_val.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hsymmM : MDifferentiableAt (𝓡 3) (𝓡 3)
      ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((Subtype.val : d.toBallChart.interior → N.Carrier) (gR c d aD hRq x)) := by
    rw [hu]
    exact mdifferentiableAt_chartSymm d y hysrc
  have hsymmFun : MDifferentiableAt (𝓡 3) (𝓡 3)
      (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
      (gR c d aD hRq x) := hsymmM.comp (gR c d aD hRq x) hsubM
  have hrefl : MDifferentiableAt (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y :=
    mdifferentiableAt_reflectMapInv (aD := aD) hyne
  have hA : mfderiv (𝓡 3) (𝓡 3)
      (fun z : d.toBallChart.interior =>
        reflectMapInv aD.toHomeomorph (d.toBallChart.chart.symm (z : N.Carrier)))
      (gR c d aD hRq x) =
      (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y).comp
        (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
          ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier)) := by
    have hval : d.toBallChart.chart.symm
        ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = y := by
      rw [hu]
      exact d.toBallChart.chart.left_inv hysrc
    have hrefl' : MDifferentiableAt (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph)
        (d.toBallChart.chart.symm ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier)) :=
      hval.symm ▸ hrefl
    have hcomp2 := mfderiv_comp (x := gR c d aD hRq x)
      (f := (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier)))
      (g := (reflectMapInv aD.toHomeomorph)) hrefl' hsymmFun
    have hcomp3 : mfderiv (𝓡 3) (𝓡 3)
        (fun z : d.toBallChart.interior => reflectMapInv aD.toHomeomorph
          (d.toBallChart.chart.symm (z : N.Carrier))) (gR c d aD hRq x) =
        (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph)
            (d.toBallChart.chart.symm ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier))).comp
          (mfderiv (𝓡 3) (𝓡 3)
            (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
            (gR c d aD hRq x)) := hcomp2
    rw [hval] at hcomp3
    rw [mfderiv_chartSymm_subtype (d := d) (gR c d aD hRq x) y hysrc hu] at hcomp3
    exact hcomp3
  have hSfun : mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)) =
      mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩ := by
    rw [gR_spec c d aD hRq x,
      ← mfderiv_seamChartFun c d aD hS
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩]
  rw [← hSfun]
  exact hcomp'.symm.trans ((hev'.mfderiv_eq.trans hevT.mfderiv_eq).trans hA)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seam_interiorRight_chain then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seam_interiorRight_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seam_interiorRight_chain ``Submission.OrientationAssembly.seam_interiorRight_chain

end RightChainRule

section ReflectDifferential

theorem mdifferentiableAt_reflectMap' {y : csModel} (hy : y ≠ 0) :
    MDifferentiableAt (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph) y :=
  mdifferentiableAt_iff_differentiableAt.mpr (hasFDerivAt_reflectMap aD hy).differentiableAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mdifferentiableAt_reflectMap' then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mdifferentiableAt_reflectMap'"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mdifferentiableAt_reflectMap' ``Submission.OrientationAssembly.mdifferentiableAt_reflectMap'

theorem reflectMapInv_comp_reflectMap_eventuallyEq {y : csModel} (hy : y ∈ SeamShell) :
    (fun z : csModel => reflectMapInv aD.toHomeomorph (reflectMap aD.toHomeomorph z))
      =ᶠ[𝓝 y] id := by
  refine Filter.eventually_of_mem (isOpen_seamShell.mem_nhds hy) ?_
  intro z hz
  exact reflectMapInv_reflectMap aD.toHomeomorph ⟨z, hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.reflectMapInv_comp_reflectMap_eventuallyEq then
    throwError "Refusing to shadow existing declaration OrientationAssembly.reflectMapInv_comp_reflectMap_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.reflectMapInv_comp_reflectMap_eventuallyEq ``Submission.OrientationAssembly.reflectMapInv_comp_reflectMap_eventuallyEq

theorem reflectMap_comp_reflectMapInv_eventuallyEq {y : csModel} (hy : y ∈ SeamShell) :
    (fun z : csModel => reflectMap aD.toHomeomorph (reflectMapInv aD.toHomeomorph z))
      =ᶠ[𝓝 y] id := by
  refine Filter.eventually_of_mem (isOpen_seamShell.mem_nhds hy) ?_
  intro z hz
  exact reflectMap_reflectMapInv aD.toHomeomorph ⟨z, hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.reflectMap_comp_reflectMapInv_eventuallyEq then
    throwError "Refusing to shadow existing declaration OrientationAssembly.reflectMap_comp_reflectMapInv_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.reflectMap_comp_reflectMapInv_eventuallyEq ``Submission.OrientationAssembly.reflectMap_comp_reflectMapInv_eventuallyEq

theorem mfderiv_reflectMap_comp_reflectMapInv {y : csModel} (hy : y ∈ SeamShell) :
    (mfderiv (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)).comp
      (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y)
      = ContinuousLinearMap.id ℝ csModel := by
  have hyne : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith [hy.1]))
  have hinvne : reflectMapInv aD.toHomeomorph y ≠ 0 := by
    intro h
    have hnorm := norm_reflectMapInv (a := aD.toHomeomorph) (x := y) (by linarith [hy.2])
    rw [h, norm_zero] at hnorm
    linarith [hy.2]
  have hcomp := mfderiv_comp (x := y) (f := (reflectMapInv aD.toHomeomorph))
    (g := (reflectMap aD.toHomeomorph))
    (mdifferentiableAt_reflectMap' (aD := aD) (y := reflectMapInv aD.toHomeomorph y) hinvne)
    (mdifferentiableAt_reflectMapInv (aD := aD) (y := y) hyne)
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : csModel => reflectMap aD.toHomeomorph (reflectMapInv aD.toHomeomorph z)) y =
      (mfderiv (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)).comp
        (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y) := hcomp
  rw [Filter.EventuallyEq.mfderiv_eq (reflectMap_comp_reflectMapInv_eventuallyEq (aD := aD) hy),
    mfderiv_id] at hcomp'
  exact hcomp'.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_reflectMap_comp_reflectMapInv then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_reflectMap_comp_reflectMapInv"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_reflectMap_comp_reflectMapInv ``Submission.OrientationAssembly.mfderiv_reflectMap_comp_reflectMapInv

theorem mfderiv_reflectMapInv_comp_reflectMap {y : csModel} (hy : y ∈ SeamShell) :
    (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y).comp
      (mfderiv (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y))
      = ContinuousLinearMap.id ℝ csModel := by
  have hyne : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith [hy.1]))
  have hinvne : reflectMapInv aD.toHomeomorph y ≠ 0 := by
    intro h
    have hnorm := norm_reflectMapInv (a := aD.toHomeomorph) (x := y) (by linarith [hy.2])
    rw [h, norm_zero] at hnorm
    linarith [hy.2]
  have hmem : reflectMapInv aD.toHomeomorph y ∈ SeamShell :=
    reflectMapInv_mem_SeamShell aD.toHomeomorph y hy
  have hcomp := mfderiv_comp (x := reflectMapInv aD.toHomeomorph y)
    (f := (reflectMap aD.toHomeomorph)) (g := (reflectMapInv aD.toHomeomorph))
    (mdifferentiableAt_reflectMapInv (aD := aD)
      (y := reflectMap aD.toHomeomorph (reflectMapInv aD.toHomeomorph y)) (by
        rw [reflectMap_reflectMapInv aD.toHomeomorph ⟨y, hy⟩]
        exact hyne))
    (mdifferentiableAt_reflectMap' (aD := aD) (y := reflectMapInv aD.toHomeomorph y) hinvne)
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : csModel => reflectMapInv aD.toHomeomorph (reflectMap aD.toHomeomorph z))
      (reflectMapInv aD.toHomeomorph y) =
      (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph)
        (reflectMap aD.toHomeomorph (reflectMapInv aD.toHomeomorph y))).comp
        (mfderiv (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph)
          (reflectMapInv aD.toHomeomorph y)) := hcomp
  rw [Filter.EventuallyEq.mfderiv_eq (reflectMapInv_comp_reflectMap_eventuallyEq (aD := aD) hmem),
    mfderiv_id, reflectMap_reflectMapInv aD.toHomeomorph ⟨y, hy⟩] at hcomp'
  exact hcomp'.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mfderiv_reflectMapInv_comp_reflectMap then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mfderiv_reflectMapInv_comp_reflectMap"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mfderiv_reflectMapInv_comp_reflectMap ``Submission.OrientationAssembly.mfderiv_reflectMapInv_comp_reflectMap

theorem fderiv_reflectMap_comp_reflectMapInv {y : csModel} (hy : y ∈ SeamShell) :
    (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)).comp
      (fderiv ℝ (reflectMapInv aD.toHomeomorph) y)
      = ContinuousLinearMap.id ℝ csModel := by
  have h := mfderiv_reflectMap_comp_reflectMapInv (aD := aD) hy
  rwa [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.fderiv_reflectMap_comp_reflectMapInv then
    throwError "Refusing to shadow existing declaration OrientationAssembly.fderiv_reflectMap_comp_reflectMapInv"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.fderiv_reflectMap_comp_reflectMapInv ``Submission.OrientationAssembly.fderiv_reflectMap_comp_reflectMapInv

theorem fderiv_reflectMapInv_comp_reflectMap {y : csModel} (hy : y ∈ SeamShell) :
    (fderiv ℝ (reflectMapInv aD.toHomeomorph) y).comp
      (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y))
      = ContinuousLinearMap.id ℝ csModel := by
  have h := mfderiv_reflectMapInv_comp_reflectMap (aD := aD) hy
  rwa [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.fderiv_reflectMapInv_comp_reflectMap then
    throwError "Refusing to shadow existing declaration OrientationAssembly.fderiv_reflectMapInv_comp_reflectMap"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.fderiv_reflectMapInv_comp_reflectMap ``Submission.OrientationAssembly.fderiv_reflectMapInv_comp_reflectMap

end ReflectDifferential

section ReflectDifferentialEquiv

def reflectDifferential {y : csModel} (hy : y ∈ SeamShell) :
    csModel ≃L[ℝ] csModel where
  toFun := fderiv ℝ (reflectMapInv aD.toHomeomorph) y
  invFun := fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)
  left_inv := fun v =>
    DFunLike.congr_fun (fderiv_reflectMap_comp_reflectMapInv (aD := aD) hy) v
  right_inv := fun v =>
    DFunLike.congr_fun (fderiv_reflectMapInv_comp_reflectMap (aD := aD) hy) v
  map_add' := (fderiv ℝ (reflectMapInv aD.toHomeomorph) y).map_add
  map_smul' := (fderiv ℝ (reflectMapInv aD.toHomeomorph) y).map_smul
  continuous_toFun := (fderiv ℝ (reflectMapInv aD.toHomeomorph) y).cont
  continuous_invFun :=
    (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)).cont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.reflectDifferential then
    throwError "Refusing to shadow existing declaration OrientationAssembly.reflectDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.reflectDifferential ``Submission.OrientationAssembly.reflectDifferential

theorem reflectDifferential_toLinearMap_eq {y : csModel} (hy : y ∈ SeamShell) :
    ((reflectDifferential (aD := aD) hy).toLinearEquiv : csModel →ₗ[ℝ] csModel)
      = fderiv ℝ (reflectMapInv aD.toHomeomorph) y :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.reflectDifferential_toLinearMap_eq then
    throwError "Refusing to shadow existing declaration OrientationAssembly.reflectDifferential_toLinearMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.reflectDifferential_toLinearMap_eq ``Submission.OrientationAssembly.reflectDifferential_toLinearMap_eq


theorem det_reflectDifferential_pos
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite)
    {y : csModel} (hy : y ∈ SeamShell) :
    0 < LinearMap.det ((reflectDifferential (aD := aD) hy).toLinearEquiv :
      csModel →ₗ[ℝ] csModel) := by
  rw [reflectDifferential_toLinearMap_eq (aD := aD) hy]
  exact det_fderiv_reflectMapInv_pos aD ha (by linarith [hy.1]) (by linarith [hy.2])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.det_reflectDifferential_pos then
    throwError "Refusing to shadow existing declaration OrientationAssembly.det_reflectDifferential_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.det_reflectDifferential_pos ``Submission.OrientationAssembly.det_reflectDifferential_pos

theorem map_reflectDifferential_stdOrientationModel
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite)
    {y : csModel} (hy : y ∈ SeamShell) :
    Orientation.map (Fin (Module.finrank ℝ csModel)) (reflectDifferential (aD := aD) hy).toLinearEquiv
      stdOrientationModel = stdOrientationModel :=
  (Orientation.map_eq_iff_det_pos stdOrientationModel
    (reflectDifferential (aD := aD) hy).toLinearEquiv (Fintype.card_fin _)).2
    (det_reflectDifferential_pos (aD := aD) ha hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.map_reflectDifferential_stdOrientationModel then
    throwError "Refusing to shadow existing declaration OrientationAssembly.map_reflectDifferential_stdOrientationModel"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.map_reflectDifferential_stdOrientationModel ``Submission.OrientationAssembly.map_reflectDifferential_stdOrientationModel

theorem map_reflectDifferential_symm_stdOrientationModel
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite)
    {y : csModel} (hy : y ∈ SeamShell) :
    Orientation.map (Fin (Module.finrank ℝ csModel))
      (reflectDifferential (aD := aD) hy).symm.toLinearEquiv stdOrientationModel
      = stdOrientationModel := by
  have h := congrArg (Orientation.map (Fin (Module.finrank ℝ csModel))
    (reflectDifferential (aD := aD) hy).symm.toLinearEquiv)
    (map_reflectDifferential_stdOrientationModel (aD := aD) ha hy)
  rw [orientation_map_map_trans (R := ℝ)
      (reflectDifferential (aD := aD) hy).toLinearEquiv
      (reflectDifferential (aD := aD) hy).symm.toLinearEquiv stdOrientationModel] at h
  have hcomp : (reflectDifferential (aD := aD) hy).toLinearEquiv.trans
      (reflectDifferential (aD := aD) hy).symm.toLinearEquiv = LinearEquiv.refl ℝ csModel :=
    LinearEquiv.ext (fun v => (reflectDifferential (aD := aD) hy).symm_apply_apply v)
  rw [hcomp, Orientation.map_refl] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.map_reflectDifferential_symm_stdOrientationModel then
    throwError "Refusing to shadow existing declaration OrientationAssembly.map_reflectDifferential_symm_stdOrientationModel"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.map_reflectDifferential_symm_stdOrientationModel ``Submission.OrientationAssembly.map_reflectDifferential_symm_stdOrientationModel

end ReflectDifferentialEquiv

section RightAgreement

variable (hRq : AtlasRight c d aD)


theorem chartTangentEquiv_eq_chartSymmEquiv_symm (y : csModel)
    (hy : y ∈ d.toBallChart.chart.source) :
    (chartTangentEquiv d hy).toLinearEquiv
      = (chartSymmEquiv d y hy).symm.toLinearEquiv := by
  apply LinearEquiv.ext
  intro v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.chartTangentEquiv_eq_chartSymmEquiv_symm then
    throwError "Refusing to shadow existing declaration OrientationAssembly.chartTangentEquiv_eq_chartSymmEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.chartTangentEquiv_eq_chartSymmEquiv_symm ``Submission.OrientationAssembly.chartTangentEquiv_eq_chartSymmEquiv_symm

end RightAgreement

section HalfBound

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem half_lt_norm_seamChartX_of_mem_qS (p : ConnectedSumQuotient c.toBallChart
    d.toBallChart aD.toHomeomorph) (hp : p ∈ qS c d aD) :
    1 / 2 < ‖seamChartX c.toBallChart d.toBallChart aD.toHomeomorph p‖ := by
  rw [mem_qS_iff] at hp
  rw [seamChartX_source c.toBallChart d.toBallChart aD.toHomeomorph] at hp
  obtain ⟨⟨w, hw⟩, hwmap⟩ := hp
  rw [← hwmap, seamChartX_apply_seamMap]
  exact hw.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.half_lt_norm_seamChartX_of_mem_qS then
    throwError "Refusing to shadow existing declaration OrientationAssembly.half_lt_norm_seamChartX_of_mem_qS"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.half_lt_norm_seamChartX_of_mem_qS ``Submission.OrientationAssembly.half_lt_norm_seamChartX_of_mem_qS

end HalfBound

section RightOrientation

variable (hRq : AtlasRight c d aD)

theorem seamDifferential_symm_eq_right
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qR c d aD hRq) (y : csModel) (hy : y ∈ SeamShell) (h1y : 1 < ‖y‖)
    (hdeep : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩).symm.toLinearEquiv
      = (reflectDifferential (aD := aD) hy).symm.toLinearEquiv.trans
          ((chartTangentEquiv d (chart_source_of_mem_SeamShell d y hy)).toLinearEquiv.trans
            (rightDifferential c d aD hRq x).symm.toLinearEquiv) := by
  have hysrc : y ∈ d.toBallChart.chart.source := chart_source_of_mem_SeamShell d y hy
  have hchain := seam_interiorRight_chain c d aD hRq hS x y hy h1y hdeep hSp
  apply LinearEquiv.ext
  intro w
  change (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
      d.toBallChart aD.toHomeomorph), hSp⟩).symm w =
    (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x))
      ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
        ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w))
  refine (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
    d.toBallChart aD.toHomeomorph), hSp⟩).toLinearEquiv.injective ?_
  erw [show (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩)
      ((seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩).symm w) = w from
    LinearEquiv.apply_symm_apply _ w]
  change w = (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
      ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩)
    ((mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x))
      ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
        ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w)))
  have hz : (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier))
      ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
        ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w))
      = (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w := by
    have h1 : (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
        (d.toBallChart.chart y))
        ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
          ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w))
        = (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w :=
      DFunLike.congr_fun (mfderiv_chartSymm_comp_chart d y hysrc) _
    exact hdeep.symm ▸ h1
  rw [show (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩)
      ((mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
        (gR c d aD hRq x))
        ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
          ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w)))
      = (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y)
        ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
          ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier))
          ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
            ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w)))
      from DFunLike.congr_fun hchain _]
  rw [hz, mfderiv_eq_fderiv]
  exact ((ContinuousLinearEquiv.apply_symm_apply (reflectDifferential (aD := aD) hy) w)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seamDifferential_symm_eq_right then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seamDifferential_symm_eq_right"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seamDifferential_symm_eq_right ``Submission.OrientationAssembly.seamDifferential_symm_eq_right

theorem SO_R_eq_SO_S
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite)
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qR c d aD hRq)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (SO_R c d aD hRq).val x =
      (SO_S c d aD hS).val ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩ := by
  obtain ⟨y, hy, h1y, hdeep, -⟩ := exists_right_coordinate c d aD hRq x hSp
    (half_lt_norm_seamChartX_of_mem_qS c d aD _ hSp)
  have hysrc : y ∈ d.toBallChart.chart.source := chart_source_of_mem_SeamShell d y hy
  have hchain := seamDifferential_symm_eq_right c d aD hRq hS x y hy h1y hdeep hSp
  have hchart : N.orientation.orientation
      ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) =
      Orientation.map (Fin 3) (chartTangentEquiv d hysrc).toLinearEquiv (stdOrientation y) := by
    rw [hdeep]
    exact orientation_eq_map_chartTangentEquiv d hysrc
  rw [SO_R_apply_map, SO_S_apply_map, hchain, rightDifferentialEquiv_eq]
  erw [← orientation_map_map_trans (R := ℝ)
    (reflectDifferential (aD := aD) hy).symm.toLinearEquiv
    ((chartTangentEquiv d hysrc).toLinearEquiv.trans
      (rightDifferential c d aD hRq x).symm.toLinearEquiv) stdOrientationModel]
  rw [map_reflectDifferential_symm_stdOrientationModel (aD := aD) ha hy]
  erw [← orientation_map_map_trans (R := ℝ) (chartTangentEquiv d hysrc).toLinearEquiv
    (rightDifferential c d aD hRq x).symm.toLinearEquiv stdOrientationModel]
  rw [hchart]
  rw [show Orientation.reindex ℝ csModel csIdx
        (Orientation.map (Fin 3) (chartTangentEquiv d hysrc).toLinearEquiv (stdOrientation y)) =
      Orientation.map (Fin (Module.finrank ℝ csModel)) (chartTangentEquiv d hysrc).toLinearEquiv
        (Orientation.reindex ℝ csModel csIdx (stdOrientation y)) from
    orientation_reindex_map_comm csIdx (chartTangentEquiv d hysrc).toLinearEquiv (stdOrientation y)]
  rw [← stdOrientationModel_eq_reindex y]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.SO_R_eq_SO_S then
    throwError "Refusing to shadow existing declaration OrientationAssembly.SO_R_eq_SO_S"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.SO_R_eq_SO_S ``Submission.OrientationAssembly.SO_R_eq_SO_S

end RightOrientation

section IndexReindex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem reindex_symm_reindex {ι ι' : Type*} (e : ι ≃ ι') (o : Orientation ℝ E ι) :
    Orientation.reindex ℝ E e.symm (Orientation.reindex ℝ E e o) = o := by
  rw [← Orientation.reindex_symm]
  exact (Orientation.reindex ℝ E e).symm_apply_apply o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.reindex_symm_reindex then
    throwError "Refusing to shadow existing declaration OrientationAssembly.reindex_symm_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.reindex_symm_reindex ``Submission.OrientationAssembly.reindex_symm_reindex

omit [FiniteDimensional ℝ E] in
theorem reindex_symm_map_reindex {ι ι' : Type*} (e : ι ≃ ι') (f : E ≃ₗ[ℝ] E)
    (o : Orientation ℝ E ι) :
    Orientation.reindex ℝ E e.symm
        (Orientation.map ι' f (Orientation.reindex ℝ E e o)) =
      Orientation.map ι f o := by
  rw [orientation_reindex_map_comm (R := ℝ) (e := e.symm) f (Orientation.reindex ℝ E e o)]
  rw [reindex_symm_reindex e o]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.reindex_symm_map_reindex then
    throwError "Refusing to shadow existing declaration OrientationAssembly.reindex_symm_map_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.reindex_symm_map_reindex ``Submission.OrientationAssembly.reindex_symm_map_reindex

end IndexReindex

section Assembly

variable (hLq : AtlasLeft c d aD) (hRq : AtlasRight c d aD)
variable (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
  atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
include hLq hRq hS

omit hS in
theorem mem_qS_of_not_mem_qL_qR
    (p : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)
    (hL : p ∉ qL c d aD hLq) (hR : p ∉ qR c d aD hRq) : p ∈ qS c d aD := by
  have h := range_interior_left_right_union_seamChartX_source c d aD
  have hmem : p ∈ Set.range (interiorLeft c.toBallChart d.toBallChart aD) ∪
      Set.range (interiorRight c.toBallChart d.toBallChart aD) ∪
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := by
    rw [h]
    exact Set.mem_univ p
  rcases hmem with (h1 | h2) | h3
  · exact absurd h1 hL
  · exact absurd h2 hR
  · exact h3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mem_qS_of_not_mem_qL_qR then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mem_qS_of_not_mem_qL_qR"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mem_qS_of_not_mem_qL_qR ``Submission.OrientationAssembly.mem_qS_of_not_mem_qL_qR

theorem exists_manifoldOrientation_of_pieces
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite) :
    ∃ O : DifferentialGeometry.ManifoldOrientation (𝓡 3)
        (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) 3,
      (∀ x : c.toBallChart.interior, Orientation.map (Fin 3)
          ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv (M.orientation.orientation x)
        = O.orientation (interiorLeft c.toBallChart d.toBallChart aD x)) ∧
      (∀ x : d.toBallChart.interior, Orientation.map (Fin 3)
          ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv (N.orientation.orientation x)
        = O.orientation (interiorRight c.toBallChart d.toBallChart aD x)) := by
  classical
  let U : Option Bool → TopologicalSpace.Opens
      (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) := fun i =>
    match i with
    | none => qL c d aD hLq
    | some _root_.Bool.false => qR c d aD hRq
    | some _root_.Bool.true => qS c d aD
  let piece : (i : Option Bool) → SmoothOrientation (𝓡 3) (U i) := fun i =>
    match i with
    | none => SO_L c d aD hLq
    | some _root_.Bool.false => SO_R c d aD hRq
    | some _root_.Bool.true => SO_S c d aD hS
  have hcover : ∀ p : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph,
      ∃ i, p ∈ U i := by
    intro p
    by_cases hL : p ∈ qL c d aD hLq
    · exact ⟨none, hL⟩
    · by_cases hR : p ∈ qR c d aD hRq
      · exact ⟨some _root_.Bool.false, hR⟩
      · exact ⟨some _root_.Bool.true, mem_qS_of_not_mem_qL_qR c d aD hLq hRq p hL hR⟩
  have heq : ∀ (i j : Option Bool) (p : ConnectedSumQuotient c.toBallChart d.toBallChart
        aD.toHomeomorph) (hi : p ∈ U i) (hj : p ∈ U j),
      (piece i).val ⟨p, hi⟩ = (piece j).val ⟨p, hj⟩ := by
    intro i j p hi hj
    rcases i with _ | (b | b) <;> rcases j with _ | (b' | b')
    · rfl
    · exact absurd hj (Set.disjoint_left.mp
        (range_interiorLeft_disjoint_range_interiorRight c d aD) hi)
    · exact SO_L_eq_SO_S c d aD hLq hS ⟨p, hi⟩ hj
    · exact absurd hi (Set.disjoint_left.mp
        (range_interiorLeft_disjoint_range_interiorRight c d aD) hj)
    · rfl
    · exact SO_R_eq_SO_S c d aD hRq ha hS ⟨p, hi⟩ hj
    · exact (SO_L_eq_SO_S c d aD hLq hS ⟨p, hj⟩ hi).symm
    · exact (SO_R_eq_SO_S c d aD hRq ha hS ⟨p, hj⟩ hi).symm
    · rfl
  let SO : SmoothOrientation (𝓡 3)
      (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    glueSmoothOrientations (𝓡 3) U piece hcover heq
  obtain ⟨O', hO'⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3) SO
  refine ⟨reindexManifoldOrientation (𝓡 3) csIdx.symm O', ?_, ?_⟩
  · intro x
    have hSO : SO.val (interiorLeft c.toBallChart d.toBallChart aD x)
        = (SO_L c d aD hLq).val
            ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩ :=
      glueSmoothOrientations_apply (𝓡 3) U piece hcover heq _root_.Option.none
        ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩
    have hgL : gL c d aD hLq
        ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩ = x := gL_apply c d aD hLq x
    have hval : (SO_L c d aD hLq).val
        ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩
        = Orientation.map (Fin (Module.finrank ℝ csModel))
            (leftDifferential c d aD hLq
              ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩).symm.toLinearEquiv
            (Orientation.reindex ℝ csModel csIdx (M.orientation.orientation x)) := by
      rw [SO_L_apply_map, hgL, leftDifferentialEquiv_eq]
      rfl
    have hleft : (leftDifferential c d aD hLq
          ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩).symm.toLinearEquiv
        = ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv := by
      apply LinearEquiv.ext
      intro v
      change (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
          (gL c d aD hLq ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩)) v
        = (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) x) v
      rw [hgL]
    change Orientation.map (Fin 3)
        ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv (M.orientation.orientation x)
      = Orientation.reindex ℝ csModel csIdx.symm
          (O'.orientation (interiorLeft c.toBallChart d.toBallChart aD x))
    rw [hO']
    rw [hSO]
    rw [hval]
    rw [hleft]
    exact (reindex_symm_map_reindex (E := csModel) csIdx
      ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).mfderivToContinuousLinearEquiv
        (by simp) x).toLinearEquiv (M.orientation.orientation x)).symm
  · intro x
    have hSO : SO.val (interiorRight c.toBallChart d.toBallChart aD x)
        = (SO_R c d aD hRq).val
            ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩ :=
      glueSmoothOrientations_apply (𝓡 3) U piece hcover heq (_root_.Option.some _root_.Bool.false)
        ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩
    have hgR : gR c d aD hRq
        ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩ = x := gR_apply c d aD hRq x
    have hval : (SO_R c d aD hRq).val
        ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩
        = Orientation.map (Fin (Module.finrank ℝ csModel))
            (rightDifferential c d aD hRq
              ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩).symm.toLinearEquiv
            (Orientation.reindex ℝ csModel csIdx (N.orientation.orientation x)) := by
      rw [SO_R_apply_map, hgR, rightDifferentialEquiv_eq]
      rfl
    have hright : (rightDifferential c d aD hRq
          ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩).symm.toLinearEquiv
        = ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv := by
      apply LinearEquiv.ext
      intro v
      change (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
          (gR c d aD hRq ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩)) v
        = (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) x) v
      rw [hgR]
    change Orientation.map (Fin 3)
        ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv (N.orientation.orientation x)
      = Orientation.reindex ℝ csModel csIdx.symm
          (O'.orientation (interiorRight c.toBallChart d.toBallChart aD x))
    rw [hO']
    rw [hSO]
    rw [hval]
    rw [hright]
    exact (reindex_symm_map_reindex (E := csModel) csIdx
      ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).mfderivToContinuousLinearEquiv
        (by simp) x).toLinearEquiv (N.orientation.orientation x)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.exists_manifoldOrientation_of_pieces then
    throwError "Refusing to shadow existing declaration OrientationAssembly.exists_manifoldOrientation_of_pieces"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.exists_manifoldOrientation_of_pieces ``Submission.OrientationAssembly.exists_manifoldOrientation_of_pieces

end Assembly

theorem exists_smooth_connected_sum_of_orientation_data
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    Nonempty (SmoothConnectedSum c d a) := by
  refine AssemblyReduction.exists_smooth_connected_sum_of_orientation c d a ?_
  let _ := csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ := csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph (contDiffOn_reflectMap a.1)
    (contDiffOn_reflectMapInv a.1)
  exact exists_manifoldOrientation_of_pieces (M := M.toClosedOrientedManifold)
    (N := N.toClosedOrientedManifold) c d a.1
    (fun f hf => mem_atlas_leftChart c.toBallChart d.toBallChart a.1.toHomeomorph f hf)
    (fun g hg => mem_atlas_rightChart c.toBallChart d.toBallChart a.1.toHomeomorph g hg)
    (mem_atlas_seamChartX c.toBallChart d.toBallChart a.1.toHomeomorph) a.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.exists_smooth_connected_sum_of_orientation_data then
    throwError "Refusing to shadow existing declaration OrientationAssembly.exists_smooth_connected_sum_of_orientation_data"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.exists_smooth_connected_sum_of_orientation_data ``Submission.OrientationAssembly.exists_smooth_connected_sum_of_orientation_data


end OrientationAssembly
