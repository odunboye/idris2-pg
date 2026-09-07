module Network.Timeout

-- Idris2's `network` package has no support for socket-level timeouts
-- (no setsockopt/select/poll bindings at all - see the gap noted in
-- README.md), and adding that would mean shipping a hand-written C FFI
-- shared library that every consumer of this package would need to compile
-- before `pack build` works, which is a real regression to how easy this
-- package is to install today.
--
-- Instead, timeouts here are cooperative and thread-based, built on `fork`
-- (Prelude.IO) and `Channel` (System.Concurrency, part of Idris2's base
-- install - no new dependency). `withTimeout` races the given action
-- against a deadline on the calling thread and returns as soon as either
-- one finishes.
--
-- This polls with `channelGetNonBlocking` against a deadline computed from
-- System.Clock, rather than using System.Concurrency's own
-- `channelGetWithTimeout` - that primitive (support/chez/support.ss in the
-- Idris2 compiler) tracks elapsed time by counting fixed "10 microsecond"
-- polling steps rather than checking a real clock, which assumes every
-- underlying `sleep` call actually takes ~10us. Under a loaded/CI/
-- container scheduler that assumption doesn't hold - a requested 200ms
-- timeout was measured taking 1.7 REAL seconds to fire in one such
-- environment - so a genuine wall-clock deadline is used here instead.
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
import System.Clock
import System

-- How often to poll the channel while waiting for either the action or the
-- deadline. Coarse enough not to trip the same short-sleep-is-unreliable
-- problem documented above; fine enough not to meaningfully add to the
-- latency of a real timeout firing.
pollIntervalUs : Int
pollIntervalUs = 2000

||| Runs `action`, but returns `Nothing` if it hasn't completed within
||| `millis` milliseconds instead of waiting for it. See the module
||| comment above for exactly what is and isn't bounded by this (and why
||| this polls a real clock rather than using channelGetWithTimeout).
export
withTimeout : (millis : Nat) -> IO a -> IO (Maybe a)
withTimeout millis action = do
  chan <- makeChannel
  _ <- fork $ do
    result <- action
    channelPut chan result
  now <- clockTime Monotonic
  let deadline = addDuration now (fromNano (cast millis * 1000000))
  poll chan deadline
  where
    partial
    poll : Channel a -> Clock Monotonic -> IO (Maybe a)
    poll chan deadline = do
      mv <- channelGetNonBlocking chan
      case mv of
           Just v  => pure (Just v)
           Nothing => do
             now <- clockTime Monotonic
             if now >= deadline
                then pure Nothing
                else do usleep pollIntervalUs
                        poll chan deadline
