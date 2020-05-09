module System.Clock

import PrimIO

||| The various types of system clock available.
public export
data ClockType
  = UTC       -- The time elapsed since some arbitrary point in the past
  | Monotonic -- The time elapsed since some arbitrary point in the past
  | Duration  -- Representing a time duration.
  | Process   -- The amount of CPU time used by the current process.
  | Thread    -- The amount of CPU time used by the current thread.
  | GCCPU     -- The current process's CPU time consumed by the garbage collector.
  | GCReal    -- The current process's real time consumed by the garbage collector.

export
Show ClockType where
  show UTC       = "UTC"
  show Monotonic = "monotonic"
  show Duration  = "duration"
  show Process   = "process"
  show Thread    = "thread"
  show GCCPU     = "gcCPU"
  show GCReal    = "gcReal"

public export
data Clock : (type : ClockType) -> Type where
  MkClock
    : {type : ClockType}
    -> (seconds : Integer)
    -> (nanoseconds : Integer)
    -> Clock type

public export
seconds : Clock type -> Integer
seconds (MkClock s _) = s

public export
nanoseconds : Clock type -> Integer
nanoseconds (MkClock _ ns) = ns

||| Opaque clock value manipulated by the back-end.
data OSClock : Type where [external]

public export
Eq (Clock type) where
  (MkClock seconds1 nanoseconds1) == (MkClock seconds2 nanoseconds2) =
    seconds1 == seconds2 && nanoseconds1 == nanoseconds2

public export
Ord (Clock type) where
  compare (MkClock seconds1 nanoseconds1) (MkClock seconds2 nanoseconds2) =
  case compare seconds1 seconds2 of
    LT => LT
    GT => GT
    EQ => compare nanoseconds1 nanoseconds2

public export
Show (Clock type) where
  show (MkClock {type} seconds nanoseconds) =
    show type ++ ": " ++ show seconds ++ "s " ++ show nanoseconds ++ "ns"

prim_clockTimeUTC : IO OSClock
prim_clockTimeUTC = schemeCall OSClock "blodwen-clock-time-utc" []

prim_clockTimeMonotonic : IO OSClock
prim_clockTimeMonotonic = schemeCall OSClock "blodwen-clock-time-monotonic" []

prim_clockTimeProcess : IO OSClock
prim_clockTimeProcess = schemeCall OSClock "blodwen-clock-time-process" []

prim_clockTimeThread : IO OSClock
prim_clockTimeThread = schemeCall OSClock "blodwen-clock-time-thread" []

prim_clockTimeGCCPU : IO OSClock
prim_clockTimeGCCPU = schemeCall OSClock "blodwen-clock-time-gccpu" []

prim_clockTimeGCReal : IO OSClock
prim_clockTimeGCReal = schemeCall OSClock "blodwen-clock-time-gcreal" []

||| Note: Back-ends are required to implement UTC, monotonic time, CPU time
||| in current process/thread, and time duration; the rest are optional.
data ClockTypeMandatory
  = Mandatory
  | Optional

public export
isClockMandatory : ClockType -> ClockTypeMandatory
isClockMandatory GCCPU  = Optional
isClockMandatory GCReal = Optional
isClockMandatory _      = Mandatory

fetchOSClock : ClockType -> IO OSClock
fetchOSClock UTC       = prim_clockTimeUTC
fetchOSClock Monotonic = prim_clockTimeMonotonic
fetchOSClock Process   = prim_clockTimeProcess
fetchOSClock Thread    = prim_clockTimeThread
fetchOSClock GCCPU     = prim_clockTimeGCCPU
fetchOSClock GCReal    = prim_clockTimeGCReal
fetchOSClock Duration  = prim_clockTimeMonotonic

||| A test to determine the status of optional clocks.
osClockValid : OSClock -> IO Int
osClockValid clk = schemeCall Int "blodwen-is-time?" [clk]

fromOSClock : {type : ClockType} -> OSClock -> IO (Clock type)
fromOSClock clk =
  pure $
    MkClock
      {type}
      !(schemeCall Integer "blodwen-clock-second" [clk])
      !(schemeCall Integer "blodwen-clock-nanosecond" [clk])

public export
clockTimeReturnType : (typ : ClockType) -> Type
clockTimeReturnType typ with (isClockMandatory typ)
  clockTimeReturnType typ | Optional = Maybe (Clock typ)
  clockTimeReturnType typ | Mandatory = Clock typ

||| Fetch the system clock of a given kind. If the clock is mandatory,
||| we return a (Clock type) else (Maybe (Clock type)).
public export
clockTime : (typ : ClockType) -> IO (clockTimeReturnType typ)
clockTime clockType with (isClockMandatory clockType)
  clockTime clockType | Mandatory = fetchOSClock clockType >>= fromOSClock
  clockTime clockType | Optional = do
    clk <- fetchOSClock clockType
    valid <- map (== 1) $ osClockValid clk
    if valid
      then map Just $ fromOSClock clk
      else pure Nothing

||| Make a duration value.
public export
makeDuration : Integer -> Integer -> Clock Duration
makeDuration = MkClock

toNano : Clock type -> Integer
toNano (MkClock seconds nanoseconds) =
  let scale = 1000000000
   in scale * seconds + nanoseconds

fromNano : {type : ClockType} -> Integer -> Clock type
fromNano n =
  let scale       = 1000000000
      seconds     = n `div` scale
      nanoseconds = n `mod` scale
   in MkClock seconds nanoseconds

||| Compute difference between two clocks of the same type.
public export
timeDifference : Clock type -> Clock type -> Clock Duration
timeDifference clock duration = fromNano $ toNano clock - toNano duration

||| Add a duration to a clock value.
public export
addDuration : {type : ClockType} -> Clock type -> Clock Duration -> Clock type
addDuration clock duration = fromNano $ toNano clock + toNano duration

||| Subtract a duration from a clock value.
public export
subtractDuration : {type : ClockType} -> Clock type -> Clock Duration -> Clock type
subtractDuration clock duration = fromNano $ toNano clock - toNano duration
