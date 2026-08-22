import PiQuasi.TraditionalPiPotential

set_option autoImplicit false

namespace PiQuasi


/-
A finite endpoint geometry.

Closure is defined only by equality of independently
supplied endpoints.

No terminality predicate occurs in this definition.
-/
structure FiniteEndpointGeometry : Type 1 where
  Point : Type
  start :
    TraditionalPiPotentialStage →
    Point
  finish :
    TraditionalPiPotentialStage →
    Point


def EndpointClosed
    (G : FiniteEndpointGeometry)
    (s : TraditionalPiPotentialStage) :
    Prop :=
  G.finish s = G.start s


/-
An explicit bridge obligation.

A geometry supports the pi-terminal interpretation
only if endpoint equality can independently be shown
to force zero next correction.
-/
structure PiTerminalClosureBridge
    (G : FiniteEndpointGeometry) :
    Prop where

  closureForcesTerminal :
    (s : TraditionalPiPotentialStage) →
    EndpointClosed G s →
    TraditionalPiTerminal s


/-
Generic non-circular theorem.

Endpoint closure is defined independently.

Terminality enters only through the separately
supplied bridge theorem.
-/
theorem endpoint_closure_impossible_under_bridge
    (G : FiniteEndpointGeometry)
    (B : PiTerminalClosureBridge G)
    (s : TraditionalPiPotentialStage) :
    ¬ EndpointClosed G s := by

  intro hClosed

  have hTerminal :
      TraditionalPiTerminal s :=
    B.closureForcesTerminal
      s
      hClosed

  exact
    traditional_pi_stage_ne_terminal
      s
      hTerminal


def FiniteEndpointClosureWitness
    (G : FiniteEndpointGeometry) :
    Prop :=
  ∃ s : TraditionalPiPotentialStage,
    EndpointClosed G s


theorem no_finite_endpoint_closure_witness_under_bridge
    (G : FiniteEndpointGeometry)
    (B : PiTerminalClosureBridge G) :
    ¬ FiniteEndpointClosureWitness G := by

  intro h

  cases h with
  | intro s hs =>
      exact
        endpoint_closure_impossible_under_bridge
          G
          B
          s
          hs


/-
The bridge itself is not constructed generically.

This is intentional:

a claim that some concrete geometry supplies the
bridge must prove that fact independently.
-/
def HasIndependentPiClosureBridge
    (G : FiniteEndpointGeometry) :
    Prop :=
  PiTerminalClosureBridge G


end PiQuasi
