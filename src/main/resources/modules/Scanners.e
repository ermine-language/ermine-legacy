module Scanners where

import DB
import Native.Function
import Vector
import Native.Record
import Relation

foreign
  data "com.clarifi.reporting.relational.Scanner" Scanner (f: * -> *)

  private
    data "com.clarifi.reporting.backends.Scanners$" ScannersModule
    value "com.clarifi.reporting.backends.Scanners$" "MODULE$" scannersModule : ScannersModule

  method "StateScanner" stateScanner# : ScannersModule -> Scanner f

stateScanner = stateScanner# scannersModule

