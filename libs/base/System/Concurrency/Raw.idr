module System.Concurrency.Raw

-- Mutexes and condition variables.

export
threadID : IO ThreadID
threadID = schemeCall ThreadID "blodwen-thisthread" []

export
setThreadData : {a : Type} -> a -> IO ()
setThreadData val = schemeCall () "blodwen-set-thread-data" [val]

export
getThreadData : (a : Type) -> IO a
getThreadData a = schemeCall a "blodwen-get-thread-data" []

export
data Mutex : Type where

export
makeMutex : IO Mutex
makeMutex = schemeCall Mutex "blodwen-mutex" []

export
mutexAcquire : Mutex -> IO ()
mutexAcquire m = schemeCall () "blodwen-lock" [m]

export
mutexRelease : Mutex -> IO ()
mutexRelease m = schemeCall () "blodwen-unlock" [m]

export
data Condition : Type where

export
makeCondition : IO Condition
makeCondition = schemeCall Condition "blodwen-condition" []

export
conditionWait : Condition -> Mutex -> IO ()
conditionWait c m = schemeCall () "blodwen-condition-wait" [c, m]

export
conditionWaitTimeout : Condition -> Mutex -> Int -> IO ()
conditionWaitTimeout c m t
    = schemeCall () "blodwen-condition-wait-timeout" [c, m, t]

export
conditionSignal : Condition -> IO ()
conditionSignal c = schemeCall () "blodwen-condition-signal" [c]

export
conditionBroadcast : Condition -> IO ()
conditionBroadcast c = schemeCall () "blodwen-condition-broadcast" [c]

