namespace SessionTypes

/-- The session type data type.
Each constructor denotes a specific session type. -/
inductive ST : Type 1 where
  | recv : Type → ST → ST
  | send : Type → ST → ST
  | sel : List ST → ST
  | off : List ST → ST
  | r : ST → ST
  | wk : ST → ST
  | v : ST
  | eps : ST
  deriving Inhabited

infixr:6 " :?> " => ST.recv
infixr:6 " :!> " => ST.send

/-- A capability stores a context/scope (list of session types) and a session type. -/
structure Cap : Type 1 where
  ctx : List ST
  st : ST
  deriving Inhabited

mutual
  /-- Type family for calculating the dual of a session type. -/
  def dualST : ST → ST
    | .recv a r => .send a (dualST r)
    | .send a r => .recv a (dualST r)
    | .sel xs => .off (dualSTList xs)
    | .off xs => .sel (dualSTList xs)
    | .r s => .r (dualST s)
    | .wk s => .wk (dualST s)
    | .v => .v
    | .eps => .eps

  def dualSTList : List ST → List ST
    | [] => []
    | x :: xs => dualST x :: dualSTList xs
end

/-- Type family for calculating the dual of a capability. -/
def dual (c : Cap) : Cap :=
  ⟨c.ctx.map dualST, dualST c.st⟩

mutual
  /-- Type family for removing the send session type from the given session type. -/
  def removeSendST : ST → ST
    | .send _ r => removeSendST r
    | .recv a r => .recv a (removeSendST r)
    | .sel xs => .sel (removeSendSTList xs)
    | .off xs => .off (removeSendSTList xs)
    | .r s => .r (removeSendST s)
    | .wk s => .wk (removeSendST s)
    | s => s

  def removeSendSTList : List ST → List ST
    | [] => []
    | x :: xs => removeSendST x :: removeSendSTList xs
end

/-- Type family for removing the send session type from the given capability. -/
def removeSend (c : Cap) : Cap :=
  ⟨c.ctx.map removeSendST, removeSendST c.st⟩

mutual
  /-- Type family for removing the receive session type from the given session type. -/
  def removeRecvST : ST → ST
    | .send a r => .send a (removeRecvST r)
    | .recv _ r => removeRecvST r
    | .sel xs => .sel (removeRecvSTList xs)
    | .off xs => .off (removeRecvSTList xs)
    | .r s => .r (removeRecvST s)
    | .wk s => .wk (removeRecvST s)
    | s => s

  def removeRecvSTList : List ST → List ST
    | [] => []
    | x :: xs => removeRecvST x :: removeRecvSTList xs
end

/-- Type family for removing the receive session type from the given capability. -/
def removeRecv (c : Cap) : Cap :=
  ⟨c.ctx.map removeRecvST, removeRecvST c.st⟩

/-- Data type that can give us proof of membership of an element in a list of elements. -/
inductive Ref : ST → List ST → Type 1 where
  | RefZ : {s : ST} → {xs : List ST} → Ref s (s :: xs)
  | RefS : {s k t : ST} → {xs : List ST} → Ref s (k :: xs) → Ref s (t :: k :: xs)

end SessionTypes
