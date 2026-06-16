import SessionTypes.STTerm
import SessionTypes.MonadSession
import SessionTypes.Indexed

namespace SessionTypes

open Indexed

/-- The indexed codensity monad.
Allows reducing quadratic complexity from repeated use of ix_bind to linear complexity.
-/
def IxC (M : Type → Type) [Monad M] (i j : Cap) (α : Type) : Type 1 :=
  {β : Type} → {k : Cap} → (α → STTerm M j k β) → STTerm M i k β

namespace IxC

variable {M : Type → Type} [Monad M]

def pure {α : Type} {i : Cap} (a : α) : IxC M i i α :=
  λ h => h a

def bind {α β : Type} {i j k : Cap} (m : IxC M i j α) (f : α → IxC M j k β) : IxC M i k β :=
  λ c => m (λ a => f a c)

instance : IxFunctor (IxC M) where
  map f m := λ c => m (λ a => c (f a))

instance : IxMonad (IxC M) where
  pure := pure
  bind := bind
  seq f x := bind f (λ f' => λ c => x (λ a => c (f' a)))

instance : MonadSession (IxC M) where
  send T v := λ h => STTerm.send T v (STTerm.ret ()) ix_then h ()
  recv T := λ h => STTerm.recv T (λ x => STTerm.ret x) ix_bind h
  sel1 := λ h => STTerm.sel1 (STTerm.ret ()) ix_then h ()
  sel2 := λ h => STTerm.sel2 (STTerm.ret ()) ix_then h ()
  offZ m := λ h => STTerm.offZ (m STTerm.ret) ix_bind h
  offS m n := λ h => STTerm.offS (m STTerm.ret) (n STTerm.ret) ix_bind h
  recurse m := λ h => STTerm.recur (m STTerm.ret) ix_bind h
  weaken m := λ h => STTerm.weaken (m STTerm.ret) ix_bind h
  var m := λ h => STTerm.var (m STTerm.ret) ix_bind h
  eps a := λ h => h a

/-- Turns the IxC representation of a program into the STTerm representation. -/
def run {α : Type} {i j : Cap} (m : IxC M i j α) : STTerm M i j α :=
  m STTerm.ret

/-- Transforms an STTerm program into a IxC representation. -/
def rep {α : Type} {i j : Cap} (m : STTerm M i j α) : IxC M i j α :=
  λ h => m ix_bind h

end IxC

end SessionTypes
