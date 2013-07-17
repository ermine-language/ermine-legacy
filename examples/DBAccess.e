module DBAccess where

import Prelude
import IO
import IO.DB
import Native.Function
import Relation
import Syntax.Relation
import Syntax.Monad
import Vector

field person_name, company_name, food_name: String
field age, person_id, company_id, food_id : Int

table person: [person_name, age, person_id]
table company: [company_name, company_id]
table person_company: [person_id, company_id]
table foods: [food_id, food_name]
table likes: [person_id, food_id]


scanOut' f r = ioMonad ` (_ -> run r) >>= v ->
               for_ (r _ -> printLn . toString $ f r) (toList v)
scanOut = scanOut' id

people = (person ** company ** person_company) # {person_name, age, company_name}

byAge order = (order {age} people) # {person_name, age}
oldest = byAge firstBy
youngest = byAge lastBy

conn = sqlite "jdbc:sqlite:examples/test.db"
run = getRecords conn

scanPeople = scanOut people
scanEdges = scanOut (oldest +++ youngest)

danFoods = person ** likes ** foods
         & { person_name = "Dan Doel" }
         # { food_name }

mhfDinnerParty = person ** likes ** foods ** company ** person_company
               & { company_name = "McGraw Hill Financial" }
               # { food_name }
