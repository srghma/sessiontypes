namespace SessionTypes

class IxFunctor {ι : Type u} (F : ι → ι → Type → Type 1) where
  map : {α β : Type} → {i j : ι} → (α → β) → F i j α → F i j β

class IxApplicative {ι : Type u} (F : ι → ι → Type → Type 1) extends IxFunctor F where
  pure : {α : Type} → {i : ι} → α → F i i α
  seq : {α β : Type} → {i j k : ι} → F i j (α → β) → F j k α → F i k β

class IxMonad {ι : Type u} (M : ι → ι → Type → Type 1) extends IxApplicative M where
  bind : {α β : Type} → {i j k : ι} → M i j α → (α → M j k β) → M i k β

namespace Indexed
scoped infixl:55 " ix_bind " => IxMonad.bind
scoped infixl:55 " ix_then " => fun m1 m2 => IxMonad.bind m1 (fun _ => m2)
end Indexed

class IxMonadT {ι : Type u} (T : (Type → Type) → ι → ι → Type → Type 1) where
  lift : {M : Type → Type} → [Monad M] → {α : Type} → {i : ι} → M α → T M i i α

class IxMonadIO {ι : Type u} (M : (Type → Type) → ι → ι → Type → Type 1) where
  liftIO : {m : Type → Type} → [Monad m] → {α : Type} → {i : ι} → IO α → M m i i α

end SessionTypes
