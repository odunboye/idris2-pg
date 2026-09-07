
module Network.Core

import Data.Maybe
import Data.Either
import Data.Bits
import Network.Socket

public export
data ConnStatus = Disconnected | Connected | Closed

public export
data CanTransition : ConnStatus -> ConnStatus -> Type where
  ToConnected : CanTransition Disconnected Connected
  ToClosed1   : CanTransition Connected Closed
  ToClosed2   : CanTransition Disconnected Closed


public export
interface Network (m : Type -> Type) where

  Connection : ConnStatus -> Type

  -- Establish a connection
  connect : Connection Disconnected -> m (Either String (Connection Connected))

  -- Send raw bytes
  send : Connection Connected -> List Bits8 -> m (Either String ())

  -- Receive up to N bytes
  receive : Connection Connected -> Int -> m (Either String (List Bits8))

  -- Close the connection
  close : {auto p : CanTransition s Closed} -> Connection s -> m (Connection Closed)

