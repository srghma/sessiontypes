import SessionTypes.Types
import SessionTypes.Indexed

namespace SessionTypes

open Indexed

inductive STTerm (M : Type → Type) : Cap → Cap → Type → Type 1 where
  | ret : {s : Cap} → {α : Type} → α → STTerm M s s α
  | send : {ctx : List ST} → {r : ST} → {j : Cap} → {α : Type} → (T : Type) → T → STTerm M ⟨ctx, r⟩ j α → STTerm M ⟨ctx, .send T r⟩ j α
  | recv : {ctx : List ST} → {r : ST} → {j : Cap} → {α : Type} → (T : Type) → (T → STTerm M ⟨ctx, r⟩ j α) → STTerm M ⟨ctx, .recv T r⟩ j α
  | sel1 : {ctx : List ST} → {s : ST} → {xs : List ST} → {j : Cap} → {α : Type} → STTerm M ⟨ctx, s⟩ j α → STTerm M ⟨ctx, .sel (s :: xs)⟩ j α
  | sel2 : {ctx : List ST} → {t : ST} → {xs : List ST} → {s : ST} → {j : Cap} → {α : Type} → STTerm M ⟨ctx, .sel (t :: xs)⟩ j α → STTerm M ⟨ctx, .sel (s :: t :: xs)⟩ j α
  | offZ : {ctx : List ST} → {s : ST} → {j : Cap} → {α : Type} → STTerm M ⟨ctx, s⟩ j α → STTerm M ⟨ctx, .off [s]⟩ j α
  | offS : {ctx : List ST} → {s t : ST} → {xs : List ST} → {j : Cap} → {α : Type} → STTerm M ⟨ctx, s⟩ j α → STTerm M ⟨ctx, .off (t :: xs)⟩ j α → STTerm M ⟨ctx, .off (s :: t :: xs)⟩ j α
  | recur : {ctx : List ST} → {s : ST} → {j : Cap} → {α : Type} → STTerm M ⟨s :: ctx, s⟩ j α → STTerm M ⟨ctx, .r s⟩ j α
  | weaken : {ctx : List ST} → {t : ST} → {s : ST} → {j : Cap} → {α : Type} → STTerm M ⟨ctx, t⟩ j α → STTerm M ⟨s :: ctx, .wk t⟩ j α
  | var : {ctx : List ST} → {s : ST} → {j : Cap} → {α : Type} → STTerm M ⟨s :: ctx, s⟩ j α → STTerm M ⟨s :: ctx, .v⟩ j α
  | lift : {s j : Cap} → {α β : Type} → M β → (β → STTerm M s j α) → STTerm M s j α

namespace STTerm

variable {M : Type → Type}

def bind {α β : Type} {i j k : Cap} (m : STTerm M i j α) (f : α → STTerm M j k β) : STTerm M i k β :=
  match m with
  | .ret x => f x
  | .send T v next => send T v (bind next f)
  | .recv T k' => recv T (λ x => bind (k' x) f)
  | .sel1 s => sel1 (bind s f)
  | .sel2 s => sel2 (bind s f)
  | .offZ s => offZ (bind s f)
  | .offS s xs => offS (bind s f) (bind xs f)
  | .recur s => recur (bind s f)
  | .weaken s => weaken (bind s f)
  | .var s => var (bind s f)
  | .lift m' k' => lift m' (λ x => bind (k' x) f)

def map {α β : Type} {i j : Cap} (f : α → β) (st : STTerm M i j α) : STTerm M i j β :=
  bind st (λ x => .ret (f x))

instance : IxFunctor (STTerm M) where
  map := map

instance : IxMonad (STTerm M) where
  pure := ret
  bind := bind
  seq f x := bind f (λ f' => map f' x)

instance : IxMonadT STTerm where
  lift m := lift m (λ x => ret x)

end STTerm

end SessionTypes
