module System

import Data.So

%cg chicken (use posix)

export
sleep : Int -> IO ()
sleep sec = schemeCall () "blodwen-sleep" [sec]

export
usleep : (x : Int) -> So (x >= 0) => IO ()
usleep usec = schemeCall () "blodwen-usleep" [usec]

export
getArgs : IO (List String)
getArgs = schemeCall (List String) "blodwen-args" []

