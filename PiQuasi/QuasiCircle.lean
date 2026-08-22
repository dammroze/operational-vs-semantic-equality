import PiQuasi.FinitePotential

set_option autoImplicit false

namespace PiQuasi

/-
A pi construction admitted by this ultrafinite layer
contains only finite construction state.
-/
structure FinitePiArc : Type where
  stage : FStage

def refinePi (a : FinitePiArc) : FinitePiArc :=
  ⟨extend a.stage⟩

/-
A finite exact closure certificate requires endpoint
stability under one further exact refinement.
-/
structure FinitePiClosureCertificate
    (a : FinitePiArc) : Prop where
  stableEndpoint : refinePi a = a

theorem refine_pi_ne_self
    (a : FinitePiArc) :
    refinePi a ≠ a := by
  intro h

  have hs :
      extend a.stage = a.stage :=
    congrArg FinitePiArc.stage h

  exact extend_ne_self a.stage hs

theorem no_finite_pi_closure
    (a : FinitePiArc) :
    ¬ FinitePiClosureCertificate a := by
  intro h
  exact refine_pi_ne_self a h.stableEndpoint

structure PiQuasiCircle : Type where
  arc : FinitePiArc
  openUnderRefinement : refinePi arc ≠ arc

def quasiCircleOf
    (a : FinitePiArc) :
    PiQuasiCircle :=
  ⟨a, refine_pi_ne_self a⟩

theorem every_finite_pi_arc_is_open
    (a : FinitePiArc) :
    refinePi a ≠ a := by
  exact refine_pi_ne_self a

end PiQuasi
