module Network.RawSocket

import Network.Socket
import Network.Core
import Data.Either
import Data.List


public export
data RawConn : ConnStatus -> Type where
  MkDisconnected : SocketAddress -> Port -> RawConn Disconnected
  MkConnected    : Socket -> RawConn Connected
  MkClosed       : RawConn Closed

public export
Network IO where
  Connection = RawConn

  connect (MkDisconnected addr port) = do
    res <- socket AF_INET Stream 0
    case res of
      Left err => pure (Left (show err))
      Right sock => do
        rc <- connect sock addr port
        if rc == 0
          then pure (Right (MkConnected sock))
          else pure (Left "Connection failed")

  send (MkConnected sock) bytes = go bytes
    where
      -- sendBytes wraps a single raw send() call and may send fewer bytes
      -- than requested, so this loops until everything is delivered.
      go : List Bits8 -> IO (Either String ())
      go [] = pure (Right ())
      go remaining = do
        sent <- sendBytes sock remaining
        case sent of
             (Left x) => pure (Left "Send failed")
             (Right n) =>
               if n <= 0
                  then pure (Left "Send failed: connection closed")
                  else go (drop (cast n) remaining)

  receive (MkConnected sock) len = do
    resp <- recvBytes sock len
    case resp of
         (Left x) => pure (Left "Error receiving")
         (Right x) => pure (Right x)

  close {p=ToClosed1} (MkConnected sock) = do
    close sock
    pure MkClosed
  close {p=ToClosed2} (MkDisconnected _ _) = pure MkClosed

-- `receive` only reads up to N bytes in one underlying recv() call, so this
-- loops to guarantee exactly `total` bytes are collected (or an error if the
-- connection closes early). Needed for parsing fixed-size protocol fields
-- (tag byte, length header, payload of a known length).
public export
receiveExact : RawConn Connected -> Int -> IO (Either String (List Bits8))
receiveExact conn len = go len []
  where
    go : Int -> List Bits8 -> IO (Either String (List Bits8))
    go remaining acc =
      if remaining <= 0
         then pure (Right acc)
         else do
           res <- receive conn remaining
           case res of
                (Left err) => pure (Left err)
                (Right []) => pure (Left "receiveExact: connection closed before all bytes received")
                (Right bytes) => go (remaining - cast (length bytes)) (acc ++ bytes)

