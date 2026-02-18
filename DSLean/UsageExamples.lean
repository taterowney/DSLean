import DSLean.Command
open Lean Meta Qq


external translate_Python where
  "True" <==> True
  "False" <==> False

  "not" x <==> ¬ x


  "int(1)" <==> (1 : ℤ)
  "float(1)" <==> (1 : Float)
  a "+" b <==> a + b

  ($name) "=" val ";" rest <==> let name := val; rest

external translate_Python_one_way where
  "(" a "," b ")[0]" ==> a


#check toExternal translate_Python «False»

#check fromExternal translate_Python "not True"
#check toExternal translate_Python  ¬ «False» -- "not False" : String


#eval fromExternal translate_Python "int(1) + int(1)" -- (2 : ℤ)
#eval fromExternal translate_Python "float(1) + float(1)" -- (2 : Float)




#check fromExternal translate_Python "x = float(1); x"
