import SessionTypes
import SessionTypes.Interpreters

open SessionTypes
open SessionTypes.Indexed

def test_duality : IO Unit := do
  let s := ST.send Int (.recv Bool .eps)
  let d := dualST s
  IO.println "Testing duality..."
  match d with
  | .recv _ (.send _ .eps) => IO.println "Duality test passed"
  | _ => throw (IO.userError "Duality test failed")

def test_run : IO Unit := do
  IO.println "Testing run interpreter..."
  let prog : STTerm Id ⟨[], .send Int (.recv Bool .eps)⟩ ⟨[], .eps⟩ Unit :=
    STTerm.send Int 5 (STTerm.recv Bool (λ _ => STTerm.ret ()))

  let stm : STStream ⟨[], .send Int (.recv Bool .eps)⟩ :=
    .S_Send (.S_Recv Bool true .S_Eps)

  let out := run prog stm
  match out with
  | .O_Send _ 5 (.O_Recv _ true (.O_Eps ())) => IO.println "Run test passed"
  | _ => throw (IO.userError "Run test failed")

def test_monad_session : IO Unit := do
  IO.println "Testing MonadSession combinators..."
  let prog : STTerm Id ⟨[], .send Int (.recv Bool .eps)⟩ ⟨[], .eps⟩ Unit :=
    MonadSession.send Int 5 ix_then
    (MonadSession.recv Bool ix_bind λ _ =>
    eps0)

  let stm : STStream ⟨[], .send Int (.recv Bool .eps)⟩ :=
    .S_Send (.S_Recv Bool false .S_Eps)

  let out := run prog stm
  match out with
  | .O_Send _ 5 (.O_Recv _ false (.O_Eps ())) => IO.println "MonadSession test passed"
  | _ => throw (IO.userError "MonadSession test failed")

def main : IO Unit := do
  IO.println "Running SessionTypes Tests..."
  test_duality
  test_run
  test_monad_session
  IO.println "All tests passed!"
