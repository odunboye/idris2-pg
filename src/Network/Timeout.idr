module Network.Timeout

-- Idris2's `network` package has no support for socket-level timeouts
-- (no setsockopt/select/poll bindings at all - see the gap noted in
-- README.md), and adding that would mean shipping a hand-written C FFI
-- shared library that every consumer of this package would need to compile
-- before `pack build` works, which is a real regression to how easy this
-- package is to install today.
--
-- Instead, timeouts here are cooperative and thread-based, built entirely
-- on `fork` (Prelude.IO) and `Channel`/`channelGetWithTimeout`
-- (System.Concurrency, part of Idris2's base install - no new dependency).
-- `withTimeout` races the given action against a timer on a background
-- thread and returns as soon as either one finishes.
--
-- The tradeoff: this bounds how long the *caller* waits, not the
-- underlying resource. If `action` is a blocking syscall stuck on a truly
-- unresponsive server, timing out here does NOT close the socket or
-- interrupt that syscall - there is no way to do that from another Idris
-- thread without the socket-level C FFI this was written to avoid. The
-- abandoned action keeps running in the background (harmlessly - its
-- eventual result is just never read) until the OS's own TCP-level retry
-- limit gives up, or the process exits. Callers that need the connection
-- itself reclaimed after a timeout should close and reconnect rather than
-- reuse it.

import System.Concurrency

||| Runs `action`, but returns `Nothing` if it hasn't completed within
||| `millis` milliseconds instead of waiting for it. See the module
||| comment above for exactly what is and isn't bounded by this.
export
withTimeout : (millis : Nat) -> IO a -> IO (Maybe a)
withTimeout millis action = do
  chan <- makeChannel
  _ <- fork $ do
    result <- action
    channelPut chan result
  channelGetWithTimeout chan millis
