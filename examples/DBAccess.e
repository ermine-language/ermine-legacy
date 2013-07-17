module DBAccess where

import Prelude
import IO.DB
import Native.Function
import Relation

field person_name, company_name: String
field age, person_id, company_id: Int
table person: [person_name, age, person_id]
table company: [company_name, company_id]
table person_company: [person_id, company_id]

people = (person ** company ** person_company) # {person_name, age, company_name}

byAge order = (order {age} people) # {person_name, age}
oldest = byAge firstBy
youngest = byAge lastBy

conn = sqlite "jdbc:sqlite:examples/test.db"
run = getRecords conn

main = run people
main2 = run (oldest +++ youngest)
