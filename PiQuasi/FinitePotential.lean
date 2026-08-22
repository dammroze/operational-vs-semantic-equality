set_option autoImplicit false

namespace PiQuasi

/-
Only finitely constructed stages exist in this datatype.
There is no constructor for a completed infinite stage.
-/
inductive FStage : Type where
  | seed : FStage
  | next : FStage → FStage

def extend (s : FStage) : FStage :=
  FStage.next s

def Terminal (s : FStage) : Prop :=
  extend s = s

theorem extend_ne_self :
    (s : FStage) → extend s ≠ s
  | .seed => by
      intro h
      cases h

  | .next s => by
      intro h
      have hs : FStage.next s = s :=
        FStage.next.inj h
      exact extend_ne_self s hs

theorem no_terminal (s : FStage) :
    ¬ Terminal s := by
  exact extend_ne_self s

def CompletedWitness : Prop :=
  ∃ s : FStage, Terminal s

theorem no_completed_witness :
    ¬ CompletedWitness := by
  intro h
  cases h with
  | intro s hs =>
      exact no_terminal s hs

end PiQuasi
