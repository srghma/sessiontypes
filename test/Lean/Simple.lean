import SessionTypes

open SessionTypes
open SessionTypes.Indexed

def prog {M : Type → Type} [Monad M] : STTerm M ⟨[], .send Int .eps⟩ ⟨[], .eps⟩ Unit :=
  STTerm.send Int 5 (STTerm.ret ())

def prog2 {M : Type → Type} [Monad M] : STTerm M ⟨[], .send Int (.recv Bool .eps)⟩ ⟨[], .eps⟩ Unit :=
  MonadSession.send Int 5 ix_then
  (MonadSession.recv Bool ix_bind λ _ =>
  eps0)

def main : IO Unit := do
  IO.println "Test program built successfully"
