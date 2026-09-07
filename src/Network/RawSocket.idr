module Network.RawSocket

import Network.Socket
import Network.Core
import Data.Either


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

  send (MkConnected sock) bytes = do
    sent <- sendBytes sock bytes
    case sent of
         (Left x) => pure (Left "Send failed")
         (Right y) => pure (Right ())

  receive (MkConnected sock) len = do
    resp <- recvBytes sock len
    case resp of
         (Left x) => pure (Left "Error receiving")
         (Right x) => pure (Right x)

  close {p=ToClosed1} (MkConnected sock) = do
    close sock
    pure MkClosed
  close {p=ToClosed2} (MkDisconnected _ _) = pure MkClosed

