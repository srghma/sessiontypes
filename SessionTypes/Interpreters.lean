import SessionTypes.STTerm

namespace SessionTypes

/-- A Stream provides input for the receives in a session typed program. -/
inductive STStream : Cap → Type 1 where
  | S_Send : {ctx : List ST} → {s : ST} → {T : Type} → STStream ⟨ctx, s⟩ → STStream ⟨ctx, .send T s⟩
  | S_Recv : {ctx : List ST} → {s : ST} → (T : Type) → T → STStream ⟨ctx, s⟩ → STStream ⟨ctx, .recv T s⟩
  | S_Sel1 : {ctx : List ST} → {s : ST} → {xs : List ST} → STStream ⟨ctx, s⟩ → STStream ⟨ctx, .sel (s :: xs)⟩
  | S_Sel2 : {ctx : List ST} → {t : ST} → {xs : List ST} → STStream ⟨ctx, .sel (t :: xs)⟩ → STStream ⟨ctx, .sel (s :: t :: xs)⟩
  | S_OffZ : {ctx : List ST} → {s : ST} → STStream ⟨ctx, s⟩ → STStream ⟨ctx, .off [s]⟩
  | S_OffS : {ctx : List ST} → {s t : ST} → {xs : List ST} → STStream ⟨ctx, s⟩ → STStream ⟨ctx, .off (t :: xs)⟩ → STStream ⟨ctx, .off (s :: t :: xs)⟩
  | S_Rec : {ctx : List ST} → {s : ST} → STStream ⟨s :: ctx, s⟩ → STStream ⟨ctx, .r s⟩
  | S_Weaken : {ctx : List ST} → {s t : ST} → STStream ⟨ctx, s⟩ → STStream ⟨t :: ctx, .wk s⟩
  | S_Var : {ctx : List ST} → {s : ST} → STStream ⟨s :: ctx, s⟩ → STStream ⟨s :: ctx, .v⟩
  | S_Eps : STStream ⟨[], .eps⟩

/-- The Output data type describes the session type actions that were done. -/
inductive STOutput : Cap → Type → Type 1 where
  | O_Send : {ctx : List ST} → {r : ST} → {α : Type} → (T : Type) → T → STOutput ⟨ctx, r⟩ α → STOutput ⟨ctx, .send T r⟩ α
  | O_Recv : {ctx : List ST} → {r : ST} → {α : Type} → (T : Type) → T → STOutput ⟨ctx, r⟩ α → STOutput ⟨ctx, .recv T r⟩ α
  | O_Sel1 : {ctx : List ST} → {s : ST} → {xs : List ST} → {α : Type} → STOutput ⟨ctx, s⟩ α → STOutput ⟨ctx, .sel (s :: xs)⟩ α
  | O_Sel2 : {ctx : List ST} → {xs : List ST} → {s : ST} → {α : Type} → STOutput ⟨ctx, .sel xs⟩ α → STOutput ⟨ctx, .sel (s :: xs)⟩ α
  | O_OffZ : {ctx : List ST} → {s : ST} → {α : Type} → STOutput ⟨ctx, s⟩ α → STOutput ⟨ctx, .off [s]⟩ α
  | O_OffS : {ctx : List ST} → {s t : ST} → {xs : List ST} → {α : Type} → STOutput ⟨ctx, s⟩ α → STOutput ⟨ctx, .off (t :: xs)⟩ α → STOutput ⟨ctx, .off (s :: t :: xs)⟩ α
  | O_Rec : {ctx : List ST} → {s : ST} → {α : Type} → STOutput ⟨s :: ctx, s⟩ α → STOutput ⟨ctx, .r s⟩ α
  | O_Var : {ctx : List ST} → {s : ST} → {α : Type} → STOutput ⟨s :: ctx, s⟩ α → STOutput ⟨s :: ctx, .v⟩ α
  | O_Weaken : {ctx : List ST} → {s t : ST} → {α : Type} → STOutput ⟨ctx, s⟩ α → STOutput ⟨t :: ctx, .wk s⟩ α
  | O_Eps : {α : Type} → α → STOutput ⟨[], .eps⟩ α
  | O_Error : {i : Cap} → {α : Type} → STOutput i α

instance {i : Cap} {α : Type} : Inhabited (STOutput i α) where
  default := .O_Error

/-- A simple interpreter that evaluates STTerm using a STStream of inputs. -/
partial def run {α : Type} {i j : Cap} (st : STTerm Id i j α) (stm : STStream i) : STOutput i α :=
  match st with
  | .ret x => match stm with | .S_Eps => .O_Eps x | _ => default
  | .send T v next => match stm with | .S_Send s_r => .O_Send T v (run next s_r) | _ => default
  | .recv T k => match stm with | .S_Recv _ v s_r => .O_Recv T v (run (k v) s_r) | _ => default
  | .sel1 s => match stm with | .S_Sel1 s_s => .O_Sel1 (run s s_s) | _ => default
  | .sel2 s => match stm with | .S_Sel2 s_r => .O_Sel2 (run s s_r) | _ => default
  | .offZ s => match stm with | .S_OffZ s_s => .O_OffZ (run s s_s) | _ => default
  | .offS s r => match stm with | .S_OffS s_s s_r => .O_OffS (run s s_s) (run r s_r) | _ => default
  | .recur s => match stm with | .S_Rec s_r => .O_Rec (run s s_r) | _ => default
  | .weaken s => match stm with | .S_Weaken s_r => .O_Weaken (run s s_r) | _ => default
  | .var s => match stm with | .S_Var s_r => .O_Var (run s s_r) | _ => default
  | .lift m k => run (k m) stm

end SessionTypes
