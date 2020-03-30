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

%foreign "scheme:getenv"
prim_getEnv : String -> PrimIO String

%foreign "scheme:blodwen-hasenv"
prim_hasEnv : String -> PrimIO Int

export
getEnv : String -> IO (Maybe String)
getEnv var
   = do ok <- primIO $ prim_hasEnv var
        if ok == 0
           then pure Nothing
           else map pure $ primIO (prim_getEnv var)

%foreign "scheme:blodwen-system"
prim_system : String -> PrimIO Int

export
system : String -> IO Int
system cmd = primIO (prim_system cmd)

export
time : IO Integer
time = schemeCall Integer "blodwen-time" []
