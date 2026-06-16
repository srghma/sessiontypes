import SessionTypes.Types
import SessionTypes.Indexed
import SessionTypes.STTerm

namespace SessionTypes

open Indexed

class MonadSession (m : Cap → Cap → Type → Type 1) [IxMonad m] where
  send : {ctx : List ST} → {r : ST} → (T : Type) → T → m ⟨ctx, .send T r⟩ ⟨ctx, r⟩ Unit
  recv : {ctx : List ST} → {r : ST} → (T : Type) → m ⟨ctx, .recv T r⟩ ⟨ctx, r⟩ T
  sel1 : {ctx : List ST} → {s : ST} → {xs : List ST} → m ⟨ctx, .sel (s :: xs)⟩ ⟨ctx, s⟩ Unit
  sel2 : {ctx : List ST} → {s t : ST} → {xs : List ST} → m ⟨ctx, .sel (s :: t :: xs)⟩ ⟨ctx, .sel (t :: xs)⟩ Unit
  offZ : {ctx : List ST} → {s : ST} → {j : Cap} → {α : Type} → m ⟨ctx, s⟩ j α → m ⟨ctx, .off [s]⟩ j α
  offS : {ctx : List ST} → {s t : ST} → {xs : List ST} → {j : Cap} → {α : Type} → m ⟨ctx, s⟩ j α → m ⟨ctx, .off (t :: xs)⟩ j α → m ⟨ctx, .off (s :: t :: xs)⟩ j α
  recurse : {ctx : List ST} → {s : ST} → {j : Cap} → {α : Type} → m ⟨s :: ctx, s⟩ j α → m ⟨ctx, .r s⟩ j α
  weaken : {ctx : List ST} → {s t : ST} → {j : Cap} → {α : Type} → m ⟨ctx, s⟩ j α → m ⟨t :: ctx, .wk s⟩ j α
  var : {ctx : List ST} → {s : ST} → {j : Cap} → {α : Type} → m ⟨s :: ctx, s⟩ j α → m ⟨s :: ctx, .v⟩ j α
  eps : {ctx : List ST} → {α : Type} → α → m ⟨ctx, .eps⟩ ⟨ctx, .eps⟩ α

instance {M : Type → Type} [Monad M] : MonadSession (STTerm M) where
  send T v := STTerm.send T v (STTerm.ret ())
  recv T := STTerm.recv T (λ x => STTerm.ret x)
  sel1 := STTerm.sel1 (STTerm.ret ())
  sel2 := STTerm.sel2 (STTerm.ret ())
  offZ := STTerm.offZ
  offS := STTerm.offS
  recurse := STTerm.recur
  weaken := STTerm.weaken
  var := STTerm.var
  eps x := STTerm.ret x

/-- Monadic composable definition of empty context. -/
def empty0 [IxMonad m] [MonadSession m] {r : ST} : m ⟨[], r⟩ ⟨[], r⟩ Unit :=
  IxApplicative.pure ()

/-- Select the first branch of a selection. -/
def selN1 [IxMonad m] [MonadSession m] {ctx : List ST} {s : ST} {xs : List ST} : m ⟨ctx, .sel (s :: xs)⟩ ⟨ctx, s⟩ Unit :=
  MonadSession.sel1

/-- Select the second branch of a selection. -/
def selN2 [IxMonad m] [MonadSession m] {ctx : List ST} {s t : ST} {xs : List ST} : m ⟨ctx, .sel (s :: t :: xs)⟩ ⟨ctx, t⟩ Unit :=
  MonadSession.sel2 ix_then MonadSession.sel1

/-- Monadic composable definition of recurse. -/
def recurse0 [IxMonad m] [MonadSession m] {ctx : List ST} {s : ST} : m ⟨ctx, .r s⟩ ⟨s :: ctx, s⟩ Unit :=
  MonadSession.recurse (IxApplicative.pure ())

/-- Monadic composable definition of weaken. -/
def weaken0 [IxMonad m] [MonadSession m] {ctx : List ST} {s t : ST} : m ⟨t :: ctx, .wk s⟩ ⟨ctx, s⟩ Unit :=
  MonadSession.weaken (IxApplicative.pure ())

/-- Monadic composable definition of var. -/
def var0 [IxMonad m] [MonadSession m] {ctx : List ST} {s : ST} : m ⟨s :: ctx, .v⟩ ⟨s :: ctx, s⟩ Unit :=
  MonadSession.var (IxApplicative.pure ())

/-- Monadic composable definition of eps. -/
def eps0 [IxMonad m] [MonadSession m] {ctx : List ST} : m ⟨ctx, .eps⟩ ⟨ctx, .eps⟩ Unit :=
  MonadSession.eps ()

end SessionTypes
