import Submission.DifferentialGeometry.Geometry.Metric.ExteriorPower
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.BigOperators _root_.RealInnerProductSpace _root_.ContDiff

namespace exteriorPower
open _root_.exteriorPower

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

open _root_.exteriorPower in
theorem contDiff_ιMulti (k : ℕ) (n : ℕ∞ω) :
    ContDiff ℝ n (_root_.exteriorPower.ιMulti ℝ k (M := E)) := by
  let b := stdOrthonormalBasis ℝ (⋀[ℝ]^k E)
  have h (v : Fin k → E) :
      (∑ i, musicalEquiv k (b i) v • b i) = _root_.exteriorPower.ιMulti ℝ k v := by
    simpa only [musicalEquiv_apply] using b.sum_repr' (_root_.exteriorPower.ιMulti ℝ k v)
  have hs : ContDiff ℝ n (fun v : Fin k → E => ∑ i, musicalEquiv k (b i) v • b i) :=
    ContDiff.sum fun i _ =>
      (musicalEquiv k (b i)).toContinuousMultilinearMap.contDiff.smul contDiff_const
  convert hs using 1
  exact (funext h).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.contDiff_ιMulti then
    throwError "Refusing to shadow existing declaration exteriorPower.contDiff_ιMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.contDiff_ιMulti ``Submission.exteriorPower.contDiff_ιMulti

open _root_.exteriorPower in
def mapContinuousLinearMap (k : ℕ) (f : E →L[ℝ] F) : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k F :=
  (_root_.exteriorPower.map k f.toLinearMap).toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearMap then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearMap ``Submission.exteriorPower.mapContinuousLinearMap

open _root_.exteriorPower in
@[simp]
theorem mapContinuousLinearMap_apply (k : ℕ) (f : E →L[ℝ] F) (u : ⋀[ℝ]^k E) :
    mapContinuousLinearMap k f u = _root_.exteriorPower.map k f.toLinearMap u := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearMap_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearMap_apply ``Submission.exteriorPower.mapContinuousLinearMap_apply

open _root_.exteriorPower in
theorem mapContinuousLinearMap_ιMulti (k : ℕ) (f : E →L[ℝ] F) (v : Fin k → E) :
    mapContinuousLinearMap k f (_root_.exteriorPower.ιMulti ℝ k v) = _root_.exteriorPower.ιMulti ℝ k (fun i => f (v i)) :=
  _root_.exteriorPower.map_apply_ιMulti f.toLinearMap v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearMap_ιMulti then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearMap_ιMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearMap_ιMulti ``Submission.exteriorPower.mapContinuousLinearMap_ιMulti

open _root_.exteriorPower in
@[simp]
theorem mapContinuousLinearMap_id (k : ℕ) :
    mapContinuousLinearMap k (ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ (⋀[ℝ]^k E) := by
  apply ContinuousLinearMap.ext
  intro u
  change _root_.exteriorPower.map k (LinearMap.id : E →ₗ[ℝ] E) u = u
  rw [_root_.exteriorPower.map_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearMap_id then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearMap_id ``Submission.exteriorPower.mapContinuousLinearMap_id

open _root_.exteriorPower in
theorem mapContinuousLinearMap_comp {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (k : ℕ) (f : E →L[ℝ] F) (g : F →L[ℝ] G) :
    mapContinuousLinearMap k (g.comp f) =
      (mapContinuousLinearMap k g).comp (mapContinuousLinearMap k f) := by
  apply ContinuousLinearMap.ext
  intro u
  change _root_.exteriorPower.map k (g.toLinearMap.comp f.toLinearMap) u =
    _root_.exteriorPower.map k g.toLinearMap (_root_.exteriorPower.map k f.toLinearMap u)
  rw [_root_.exteriorPower.map_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearMap_comp then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearMap_comp ``Submission.exteriorPower.mapContinuousLinearMap_comp

open _root_.exteriorPower in
theorem mapContinuousLinearMap_smul (k : ℕ) (c : ℝ) (f : E →L[ℝ] F) :
    mapContinuousLinearMap k (c • f) = c ^ k • mapContinuousLinearMap k f := by
  apply ContinuousLinearMap.coe_injective
  change _root_.exteriorPower.map k (c • f).toLinearMap = c ^ k • _root_.exteriorPower.map k f.toLinearMap
  apply _root_.exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply, _root_.exteriorPower.map_apply_ιMulti]
  change _root_.exteriorPower.ιMulti ℝ k (fun i => c • f (v i)) = c ^ k • _root_.exteriorPower.ιMulti ℝ k (fun i => f (v i))
  rw [(_root_.exteriorPower.ιMulti ℝ k).map_smul_univ]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearMap_smul then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearMap_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearMap_smul ``Submission.exteriorPower.mapContinuousLinearMap_smul

open _root_.exteriorPower in
theorem contDiff_mapContinuousLinearMap (k : ℕ) (n : ℕ∞ω) :
    ContDiff ℝ n (mapContinuousLinearMap (E := E) (F := F) k) := by
  rw [contDiff_clm_apply_iff]
  intro u
  have hu : u ∈ Submodule.span ℝ (Set.range (_root_.exteriorPower.ιMulti ℝ k (M := E))) := by
    rw [_root_.exteriorPower.ιMulti_span]
    trivial
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨v, rfl⟩ := hu
    simp_rw [mapContinuousLinearMap_ιMulti]
    exact (contDiff_ιMulti k n).comp
      (contDiff_pi.mpr fun i => contDiff_id.clm_apply contDiff_const)
  | zero =>
    simp only [map_zero]
    exact contDiff_const
  | add u v _ _ hu hv =>
    simp only [map_add]
    exact hu.add hv
  | smul c u _ hu =>
    simp only [map_smul]
    exact (contDiff_const (c := c)).smul hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.contDiff_mapContinuousLinearMap then
    throwError "Refusing to shadow existing declaration exteriorPower.contDiff_mapContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.contDiff_mapContinuousLinearMap ``Submission.exteriorPower.contDiff_mapContinuousLinearMap

open _root_.exteriorPower in
theorem contDiff_mapContinuousLinearMap_apply (k : ℕ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : (E →L[ℝ] F) × (⋀[ℝ]^k E) =>
      mapContinuousLinearMap k p.1 p.2) :=
  ((contDiff_mapContinuousLinearMap k n).comp contDiff_fst).clm_apply contDiff_snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.contDiff_mapContinuousLinearMap_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.contDiff_mapContinuousLinearMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.contDiff_mapContinuousLinearMap_apply ``Submission.exteriorPower.contDiff_mapContinuousLinearMap_apply

open _root_.exteriorPower in
def mapContinuousLinearEquiv (k : ℕ) (φ : E ≃L[ℝ] F) : (⋀[ℝ]^k E) ≃L[ℝ] ⋀[ℝ]^k F :=
  ContinuousLinearEquiv.equivOfInverse (mapContinuousLinearMap k φ.toContinuousLinearMap)
    (mapContinuousLinearMap k φ.symm.toContinuousLinearMap)
    (by
      intro u
      change _root_.exteriorPower.map k φ.symm.toLinearEquiv.toLinearMap (_root_.exteriorPower.map k φ.toLinearEquiv.toLinearMap u) = u
      rw [← LinearMap.comp_apply, ← _root_.exteriorPower.map_comp]
      have h : φ.symm.toLinearEquiv.toLinearMap.comp φ.toLinearEquiv.toLinearMap = LinearMap.id := by
        ext v
        exact φ.symm_apply_apply v
      rw [h, _root_.exteriorPower.map_id]
      rfl)
    (by
      intro u
      change _root_.exteriorPower.map k φ.toLinearEquiv.toLinearMap (_root_.exteriorPower.map k φ.symm.toLinearEquiv.toLinearMap u) = u
      rw [← LinearMap.comp_apply, ← _root_.exteriorPower.map_comp]
      have h : φ.toLinearEquiv.toLinearMap.comp φ.symm.toLinearEquiv.toLinearMap = LinearMap.id := by
        ext v
        exact φ.apply_symm_apply v
      rw [h, _root_.exteriorPower.map_id]
      rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearEquiv ``Submission.exteriorPower.mapContinuousLinearEquiv

open _root_.exteriorPower in
@[simp]
theorem mapContinuousLinearEquiv_apply (k : ℕ) (φ : E ≃L[ℝ] F) (u : ⋀[ℝ]^k E) :
    mapContinuousLinearEquiv k φ u = _root_.exteriorPower.map k φ.toLinearEquiv.toLinearMap u := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearEquiv_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearEquiv_apply ``Submission.exteriorPower.mapContinuousLinearEquiv_apply

open _root_.exteriorPower in
@[simp]
theorem mapContinuousLinearEquiv_symm_apply (k : ℕ) (φ : E ≃L[ℝ] F) (u : ⋀[ℝ]^k F) :
    (mapContinuousLinearEquiv k φ).symm u = _root_.exteriorPower.map k φ.symm.toLinearEquiv.toLinearMap u := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearEquiv_symm_apply ``Submission.exteriorPower.mapContinuousLinearEquiv_symm_apply

open _root_.exteriorPower in
@[simp]
theorem mapContinuousLinearEquiv_toContinuousLinearMap (k : ℕ) (φ : E ≃L[ℝ] F) :
    (mapContinuousLinearEquiv k φ).toContinuousLinearMap =
      mapContinuousLinearMap k φ.toContinuousLinearMap := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearEquiv_toContinuousLinearMap then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearEquiv_toContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearEquiv_toContinuousLinearMap ``Submission.exteriorPower.mapContinuousLinearEquiv_toContinuousLinearMap

open _root_.exteriorPower in
@[simp]
theorem mapContinuousLinearEquiv_symm (k : ℕ) (φ : E ≃L[ℝ] F) :
    (mapContinuousLinearEquiv k φ).symm = mapContinuousLinearEquiv k φ.symm := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapContinuousLinearEquiv_symm then
    throwError "Refusing to shadow existing declaration exteriorPower.mapContinuousLinearEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapContinuousLinearEquiv_symm ``Submission.exteriorPower.mapContinuousLinearEquiv_symm

open _root_.exteriorPower in
def mapLinearIsometryEquiv (k : ℕ) (φ : E ≃ₗᵢ[ℝ] F) : (⋀[ℝ]^k E) ≃ₗᵢ[ℝ] ⋀[ℝ]^k F where
  toLinearEquiv := (mapContinuousLinearEquiv k φ.toContinuousLinearEquiv).toLinearEquiv
  norm_map' := (LinearMap.norm_map_iff_inner_map_map
    (_root_.exteriorPower.map k φ.toLinearIsometry.toLinearMap)).mpr (inner_map_linearIsometry k φ.toLinearIsometry)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapLinearIsometryEquiv then
    throwError "Refusing to shadow existing declaration exteriorPower.mapLinearIsometryEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapLinearIsometryEquiv ``Submission.exteriorPower.mapLinearIsometryEquiv

open _root_.exteriorPower in
@[simp]
theorem mapLinearIsometryEquiv_toContinuousLinearEquiv (k : ℕ) (φ : E ≃ₗᵢ[ℝ] F) :
    (mapLinearIsometryEquiv k φ).toContinuousLinearEquiv =
      mapContinuousLinearEquiv k φ.toContinuousLinearEquiv := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapLinearIsometryEquiv_toContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration exteriorPower.mapLinearIsometryEquiv_toContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapLinearIsometryEquiv_toContinuousLinearEquiv ``Submission.exteriorPower.mapLinearIsometryEquiv_toContinuousLinearEquiv

open _root_.exteriorPower in
@[simp]
theorem mapLinearIsometryEquiv_apply (k : ℕ) (φ : E ≃ₗᵢ[ℝ] F) (u : ⋀[ℝ]^k E) :
    mapLinearIsometryEquiv k φ u = _root_.exteriorPower.map k φ.toLinearIsometry.toLinearMap u := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.mapLinearIsometryEquiv_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.mapLinearIsometryEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.mapLinearIsometryEquiv_apply ``Submission.exteriorPower.mapLinearIsometryEquiv_apply

end exteriorPower
