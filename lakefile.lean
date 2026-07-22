import Lake
open Lake DSL

require formal_conjectures from git
  "https://github.com/akakabrian/formal-conjectures.git" @
    "022ad9b703d3ec4bf2943838211097a65f091641"

package WOW217 where

@[default_target]
lean_lib WOW217
