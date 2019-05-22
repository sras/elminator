main :: IO ()
main =
  putStrLn
    "This library is currently being tested using a small test Elm front end and a Haskell backend that roundtrips a bunch of encoded values between them. To access the test just clone this repo at `https://bitbucket.org/sras/elminator-test` and run the test.sh script. Make sure that you have `elm` command available in path. This will start a test server at port 4000. Just navigate to http://localhost:4000 in your browser. Keep the js console open. Look out for console errors from Elm or 400 bad request errors from Haskell backend."
