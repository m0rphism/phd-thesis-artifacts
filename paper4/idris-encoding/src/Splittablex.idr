module Splittablex

import Control.Linear.LIO
import Linear -- local version of System.Concurrency.Linear

import Sessionx

||| borrowed session types are regular session types that end with a `Ret`
data BSession : Type where
  Send : (ty : Type) -> (r : BSession) -> BSession
  Recv : (ty : Type) -> (r : BSession) -> BSession
  Ret  : BSession

||| composition of borrowed session and owned session
comp : BSession -> Session -> Session
comp (Send ty r) s = Send ty (comp r s)
comp (Recv ty r) s = Recv ty (comp r s)
comp Ret s         = s

||| composition of two borrowed sessions
bcomp : BSession -> BSession -> BSession
bcomp (Send ty r1) r2 = Send ty (bcomp r1 r2)
bcomp (Recv ty r1) r2 = Recv ty (bcomp r1 r2)
bcomp Ret r2          = r2

||| associativity of `comp` over `bcomp`
compBcompAssoc : (r1 : BSession) -> (r2 : BSession) -> (s : Session) ->
   comp r1 (comp r2 s) === comp (bcomp r1 r2) s
compBcompAssoc (Send ty r1) r2 s = cong (Send ty) (compBcompAssoc r1 r2 s)
compBcompAssoc (Recv ty r1) r2 s = cong (Recv ty) (compBcompAssoc r1 r2 s)
compBcompAssoc Ret r2 s = Refl

||| A cell is a one-shot channel to synchronize uses of an underlying primitive channel.
||| Cells are higher-order sessions that carry (primitive) channels.
Cell : Type -> Session
Cell ty = Recv ty Wait

read : LinearIO io =>
  Channel (Cell a) -@
  L1 io a
read cell = do
  (val # cell) <- recv cell
  wait cell
  pure1 val

write :
  a -@
  Channel (Dual (Cell a)) -@
  L1 IO ()
write x cell = do
  _ <- fork1 $ do
    cell <- send cell x
    close cell
  pure1 ()

||| type of the (single) owning reference to a session
||| it only accepts operations split, close, and wait
public export
data Owner : Session -> Type where
  MkOwner : Channel (Cell (Channel s)) -@ 
            Owner s

||| type of a borrowed reference to a session
||| it accepts operations split, send, recv, and so on
public export
data Borrow : BSession -> Type where
  MkBorrow : {0 s1 : BSession} ->
           (0 s2 : Session) -> 
           Channel (Cell (Channel (comp s1 s2))) -@ 
           Channel (Dual (Cell (Channel s2))) -@ 
           Borrow s1

wrap :
  Channel s ->
  L1 IO (Owner s)
wrap {s} ch = do
  (cin # cout) <- makeChannel (Cell (Channel s))
  write ch cout
  pure1 (MkOwner cin)

split : LinearIO io =>
  Owner (comp s1 s2) ->
  L1 io (LPair (Borrow s1) (Owner s2))
split {s1}{s2} (MkOwner cin) = do
  (linkin # linkout) <- makeChannel (Cell (Channel s2))
  let 1 left : Borrow s1 := MkBorrow s2 cin linkout
  let 1 rght : Owner s2 := MkOwner linkin
  pure1 (left # rght)

splitB : LinearIO io =>
  Borrow (bcomp s1 s2) ->
  L1 io (LPair (Borrow s1) (Borrow s2))
splitB {s1}{s2} (MkBorrow s3 cin cout) = do
  (linkin # linkout) <- makeChannel (Cell (Channel (comp s2 s3)))
  let 1 left : Borrow s1 := MkBorrow {s1} (comp s2 s3) (rewrite compBcompAssoc s1 s2 s3 in cin) linkout
  let 1 rght : Borrow s2 := MkBorrow s3 linkin cout
  pure1 (left # rght)

sendB :
  ty ->
  Borrow (Send ty Ret) ->
  L1 IO ()
sendB x ch@(MkBorrow s cin cout) = do
  p <- read cin
  p' <- send p x
  write p' cout

recvB :
  Borrow (Recv ty Ret) ->
  L1 IO ty
recvB ch@(MkBorrow s cin cout) = do
  p <- read cin
  (x # p') <- recv p
  write p' cout
  pure1 x  

closeO : LinearIO io =>
  Owner Close ->
  L io ()
closeO ch@(MkOwner cin) = do
  p <- read cin
  close p

waitO : LinearIO io =>
  Owner Wait ->
  L io ()
waitO ch@(MkOwner cin) = do
  p <- read cin
  wait p


-- Local Variables:
-- idris-load-packages: ("linear")
-- End:
