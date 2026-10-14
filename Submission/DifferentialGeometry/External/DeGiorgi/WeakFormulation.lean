-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation.WeightedEstimates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Weak Formulation

This module re-exports the bilinear-form, solution-interface, smooth-test,
coefficient-operator, existence-theory, and weighted-estimate modules.
-/
