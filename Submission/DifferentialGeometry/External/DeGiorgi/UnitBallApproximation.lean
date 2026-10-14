-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 02: Unit-Ball Approximation

This module is the public entry point for the unit-ball approximation results.

It re-exports the detailed implementation from
`DeGiorgi.UnitBallApproximationCore`, so downstream files can import the
approximation material without depending on the internal proof layout.
-/
