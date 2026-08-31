module LR-narrow.LRNarrowAll where

-- File Charter:
--   * Type-checking aggregate for the GTSFImp interpreter logical relation.
--   * Exposes paired worlds, computation observations, the core LR, and the
--     fundamental dynamic-payload constructors.

open import LR-narrow.World public
open import LR-narrow.Computation public
open import LR-narrow.TargetEvaluation public
open import LR-narrow.LogicalRelation public
open import LR-narrow.DynamicPayload public
open import LR-narrow.Closure public
open import LR-narrow.ClosingSubstitution public
open import LR-narrow.ClosingSubstitutionProperties public
open import LR-narrow.TermRelation public
open import LR-narrow.ImmediateReturn public
open import LR-narrow.Variable public
open import LR-narrow.Constant public
open import LR-narrow.Blame public
open import LR-narrow.Primitive public
open import LR-narrow.FunctionApplication public
open import LR-narrow.BetaExpansion public
open import LR-narrow.Lambda public
open import LR-narrow.Application public
open import LR-narrow.TypeBetaExpansion public
open import LR-narrow.SlotSequence public
open import LR-narrow.UniversalFamily public
open import LR-narrow.Universal public
open import LR-narrow.UniversalInstantiation public
open import LR-narrow.TypeApplication public
open import LR-narrow.CastObligations public
import LR-narrow.Cast
open import LR-narrow.Fundamental public
open import LR-narrow.Insertion public
open import LR-narrow.FutureInsertion public

-- Assembly skeleton of the total theorem, parameterized by its remaining
-- obligations; imported so the aggregate check covers it.
import proof.LR-narrow.FundamentalAssembly

-- Reveal compatibility at a paired slot: evaluator facts and the atomic
-- imprecision forms.
import proof.LR-narrow.RevealSteps
import proof.LR-narrow.RevealAtomic
import proof.LR-narrow.FramePhases
import proof.LR-narrow.FrameComposition
import proof.LR-narrow.RevealFrames
import proof.LR-narrow.RevealLifting
import proof.LR-narrow.ConcealAtomic
import proof.LR-narrow.ArgumentFrame
import proof.LR-narrow.SlotLifting
import proof.LR-narrow.RevealStatements
import proof.LR-narrow.RevealStructural
import proof.LR-narrow.StarNoOccurrence
import proof.LR-narrow.KeepStepExpansion
import proof.LR-narrow.ValueExtraction
import proof.LR-narrow.PreciseReveal
import proof.LR-narrow.UniversalReveal
import proof.LR-narrow.ReplaceImprecision
import proof.LR-narrow.ImprecisionSize
import proof.LR-narrow.DynamicReveal
import proof.LR-narrow.UniversalFamilyKit

-- Alias-free scope experiment: a checked counterexample to the raw-store
-- return interface, without changing the live relation.
import proof.LR-narrow.ScopeExperiment
import proof.LR-narrow.RevealObligationsCounterexample
import proof.LR-narrow.ScopedReturnsExperiment
import proof.LR-narrow.EscapingSealExperiment
import proof.LR-narrow.PrivateSealBehavior
import proof.LR-narrow.PrivateSealInstantiationExperiment
import proof.LR-narrow.FunctionSealRetraction
import proof.LR-narrow.FunctionSealCompatibility
import proof.LR-narrow.FunctionSealClosureExperiment
import proof.LR-narrow.FunctionSealObservation
import proof.LR-narrow.FunctionSealObservationExperiment

-- Scope-aware semantic prototype: independent physical scopes, proved
-- index/future invariants, and non-identity private-seal closures.
import proof.LR-narrow.PhysicalScope
import proof.LR-narrow.ScopedBehavior
import proof.LR-narrow.ScopedFunctionSeal
import proof.LR-narrow.ScopedBehaviorExperiment
import proof.LR-narrow.ScopedFunctionSealExperiment
import proof.LR-narrow.ScopeRebase
import proof.LR-narrow.VisibleEnvironment
import proof.LR-narrow.VisibleEnvironmentExperiment
import proof.LR-narrow.ScopedIdentity
import proof.LR-narrow.ScopedUniversal
import proof.LR-narrow.ScopedUniversalExperiment

-- Body-derived result families and same-index right-only allocating steps.
import proof.LR-narrow.ScopedTypeSubstitution
import proof.LR-narrow.ScopedTypeEquivalence
import proof.LR-narrow.ScopedBodyInterpretation
import proof.LR-narrow.ScopedBodyFamily
import proof.LR-narrow.ScopedBodyFamilyExperiment
import proof.LR-narrow.ScopedStepExpansion
import proof.LR-narrow.ScopedStepExpansionExperiment

-- Structural paired conversions through interpreted bodies and fresh names.
import proof.LR-narrow.ScopedConversionTransport
import proof.LR-narrow.ScopedFrameComposition
import proof.LR-narrow.ScopedApplication
import proof.LR-narrow.ScopedConversionCompatibility
import proof.LR-narrow.ScopedBodyConversion
import proof.LR-narrow.ScopedBodyCompatibility
import proof.LR-narrow.ScopedFreshBodyCompatibility
import proof.LR-narrow.ScopedBodyCompatibilityExperiment
import proof.LR-narrow.ScopedFreshBodyCompatibilityExperiment

-- Precise-only nominal slots: the imprecise program remains unsealed.
import proof.LR-narrow.ScopedRightNominal
import proof.LR-narrow.ScopedRightFrameComposition
import proof.LR-narrow.ScopedRightSealCompatibility
import proof.LR-narrow.ScopedRightSealExperiment
import proof.LR-narrow.ScopedRightSealClosureExperiment

-- Structural precise-only body conversions, including arrow contravariance.
import proof.LR-narrow.ScopedRightBodyConversion
import proof.LR-narrow.ScopedRightBodyCompatibility
import proof.LR-narrow.ScopedRightBodyCompatibilityExperiment

-- Fresh precise-only body meanings, canonical generation, and type beta.
import proof.LR-narrow.ScopedRightFreshBodyCompatibility
import proof.LR-narrow.ScopedRightFreshBodyCompatibilityExperiment
import proof.LR-narrow.ScopedRightFreshInstantiationExperiment

-- Body-derived right families and small fresh-closed argument codes.
import proof.LR-narrow.ScopedRightArguments
import proof.LR-narrow.ScopedRightUniversalIdentity
import proof.LR-narrow.ScopedRightArgumentExperiment

-- Same-index identity universal reveal-wrapper closure for body families.
import proof.LR-narrow.ScopedRightUniversalWrapper
import proof.LR-narrow.ScopedRightUniversalWrapperExperiment
import proof.LR-narrow.ScopedVisibleUniversalWrapperExperiment

-- LR-design regression evidence: actual CTI examples and negative controls.
import proof.LR-narrow.WrapperImprecisionExamples
import proof.LR-narrow.NominalObservationExamples
import proof.LR-narrow.ReplacementImprecisionExamples
import proof.LR-narrow.DynamicWrapperExamples
import proof.LR-narrow.RepeatedCastExamples
import proof.LR-narrow.RepeatedSealExamples
import proof.LR-narrow.MixedBoundaryExamples
import proof.LR-narrow.RepeatedBoundaryControls

-- Integrated experimental observations retain persistent nominal worlds.
import proof.LR-narrow.IntegratedWorld
import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedSteps
import proof.LR-narrow.IntegratedData
import proof.LR-narrow.IntegratedDataExperiments
import proof.LR-narrow.IntegratedFrameComposition
import proof.LR-narrow.IntegratedProjection
import proof.LR-narrow.IntegratedSuite
import proof.LR-narrow.IntegratedEscapingProducer
import proof.LR-narrow.IntegratedProducerSteps
import proof.LR-narrow.IntegratedProducer
import proof.LR-narrow.IntegratedNominalProjection
import proof.LR-narrow.IntegratedUniversalSteps
import proof.LR-narrow.IntegratedUniversal
