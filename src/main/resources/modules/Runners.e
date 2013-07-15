module Runners where

import DB

foreign

  data "com.clarifi.reporting.Run" Runner (f : * -> *)
  method "run" run : forall f a . Runner f -> f a -> IO a

