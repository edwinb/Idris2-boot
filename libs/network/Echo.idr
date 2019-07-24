module Main

import Network.Socket
import Network.Socket.Data
import Network.Socket.Raw

runServer : IO (Either String (Port, Maybe ThreadID))
runServer = do
  osock <- socket AF_INET Stream 0
  case osock of
    Left fail => pure (Left $ "Failed to open socket: " ++ show fail)
    Right sock => do
      putStrLn "success"
      pure $ Right (0,Nothing)
     -- do
  --     res <- bind sock (Just (Hostname "localhost")) 0
  --     if res /= 0
  --       then pure (Left $ "Failed to bind socket with error: " ++ show res)
  --       else do
  --         port <- getSockPort sock
  --         res <- listen sock
  --         if res /= 0
  --           then pure (Left $ "Failed to listen on socket with error: " ++ show res)
  --           else do
  --             forked <- fork (serve sock)
  --             pure $ Right (port, forked)

  -- where
  --   serve : Socket -> IO ()
  --   serve sock = do
  --     res <- accept sock
  --     case res of
  --       Left err => do
  --         putStrLn ("Failed to accept on socket with error: " ++ show err)
  --       Right (s, _) => do
  --         received <- recv s 1024
  --         case received of
  --           Left err => do
  --             putStrLn ("Failed to accept on socket with error: " ++ show err)
  --           Right (str, _) => do
  --             putStrLn ("Received: " ++ str)
  --             sent <- send s ("echo: " ++ str)
  --             case sent of
  --               Left err => do
  --                 putStrLn ("Server failed to send data with error: " ++ show err)
  --               Right n =>
  --                 putStrLn ("Server sent " ++ show n ++ " bytes")

runClient : Port -> IO ()
runClient serverPort = do
  osock <- socket AF_INET Stream 0
  case osock of
    Left fail => putStrLn ("Failed to open socket: " ++ show fail)
    Right sock => do
      res <- connect sock (Hostname "localhost") serverPort
      if res /= 0
        then putStrLn ("Failed to connect client to port " ++ show serverPort)
        else do
          sent <- send sock ("hello world!")
          case sent of
            Left err => do
              putStrLn ("Client failed to send data with error: " ++ show err)
            Right n => do
              putStrLn ("Client sent " ++ show n ++ " bytes")
              received <- recv sock 1024
              case received of
                Left err => do
                  putStrLn ("Client failed to receive on socket with error: " ++ show err)
                Right (str, _) => do
                  putStrLn ("Received: " ++ str)

-- main : IO ()
-- main = do
--   server <- runServer
--   case server of
--     Left err => putStrLn $ "[server] " ++ err
--     Right (serverPort, tid) => runClient serverPort
