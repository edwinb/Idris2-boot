module System

%cg chicken (use posix)

export
sleep : Int -> IO ()
sleep sec = schemeCall () "blodwen-sleep" [sec]

export
getArgs : IO (List String)
getArgs = schemeCall (List String) "blodwen-args" []

