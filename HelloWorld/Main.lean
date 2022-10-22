def main : List String -> IO UInt32 :=
  fun _ => do
    IO.println "Hello, Twitch!"
    return 0

#eval main []
#eval Lean.versionString