module IO.Scanners where

import Scanners
import Runners
import DB
import Native.Relation

getRecords runner scanner rel = run runner (runRelation scanner rel)
