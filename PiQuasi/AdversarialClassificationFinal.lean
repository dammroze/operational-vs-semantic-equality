import PiQuasi.UltrafinitaryPiFinalBarrier
import PiQuasi.IndependentClosureInterface

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. UNCONDITIONAL FINITE CORE
   ============================================================ -/

structure UnconditionalFiniteCore : Prop where

  noFiniteExhaustion :
    ¬ FiniteExhaustion

  noCompletedTotalityFiniteOrigin :
    ¬ CompletedTotalityHasFiniteOrigin

  everyFinitePiStageNonterminal :
    (s : TraditionalPiPotentialStage) →
    ¬ TraditionalPiTerminal s

  noFiniteRepresentationCompletionBridge :
    ¬ FiniteRepresentationBridgesCompletion


theorem unconditional_finite_core :
    UnconditionalFiniteCore := by

  exact
    {
      noFiniteExhaustion :=
        finite_exhaustion_impossible

      noCompletedTotalityFiniteOrigin :=
        completed_totality_has_no_finite_origin

      everyFinitePiStageNonterminal :=
        traditional_pi_stage_ne_terminal

      noFiniteRepresentationCompletionBridge :=
        no_finite_representation_bridges_completion
    }


/- ============================================================
   II. INDEPENDENT GEOMETRIC LAYER
   ============================================================ -/

/-
Closure means only finish = start.

No pi-terminal predicate occurs in EndpointClosed.
-/
structure ConditionalGeometricBarrier
    (G : FiniteEndpointGeometry) : Prop where

  noClosureUnderIndependentBridge :
    PiTerminalClosureBridge G →
    (s : TraditionalPiPotentialStage) →
    ¬ EndpointClosed G s

  noFiniteClosureWitnessUnderIndependentBridge :
    PiTerminalClosureBridge G →
    ¬ FiniteEndpointClosureWitness G


theorem conditional_geometric_barrier
    (G : FiniteEndpointGeometry) :
    ConditionalGeometricBarrier G := by

  exact
    {
      noClosureUnderIndependentBridge := by
        intro B s
        exact
          endpoint_closure_impossible_under_bridge
            G
            B
            s

      noFiniteClosureWitnessUnderIndependentBridge := by
        intro B
        exact
          no_finite_endpoint_closure_witness_under_bridge
            G
            B
    }


/- ============================================================
   III. NO SILENT GEOMETRY ASSUMPTION
   ============================================================ -/

/-
The final classification does NOT assert that an arbitrary geometry
possesses the bridge.

A concrete Euclidean interpretation must provide it separately.
-/
def ConcreteGeometryBridgeObligation
    (G : FiniteEndpointGeometry) :
    Prop :=
  PiTerminalClosureBridge G


theorem geometry_result_requires_explicit_bridge
    (G : FiniteEndpointGeometry)
    (B : ConcreteGeometryBridgeObligation G)
    (s : TraditionalPiPotentialStage) :
    ¬ EndpointClosed G s := by

  exact
    endpoint_closure_impossible_under_bridge
      G
      B
      s


/- ============================================================
   IV. FINAL ADVERSARIAL CLASSIFICATION
   ============================================================ -/

structure AdversariallyClassifiedFinal : Prop where

  unconditionalCore :
    UnconditionalFiniteCore

  endpointClosureIndependentOfTerminalDefinition :
    (G : FiniteEndpointGeometry) →
    (s : TraditionalPiPotentialStage) →
    EndpointClosed G s =
      (G.finish s = G.start s)

  geometricConclusionIsConditional :
    (G : FiniteEndpointGeometry) →
    PiTerminalClosureBridge G →
    (s : TraditionalPiPotentialStage) →
    ¬ EndpointClosed G s


theorem adversarially_classified_final :
    AdversariallyClassifiedFinal := by

  exact
    {
      unconditionalCore :=
        unconditional_finite_core

      endpointClosureIndependentOfTerminalDefinition := by
        intro G s
        rfl

      geometricConclusionIsConditional := by
        intro G B s
        exact
          endpoint_closure_impossible_under_bridge
            G
            B
            s
    }


end PiQuasi
