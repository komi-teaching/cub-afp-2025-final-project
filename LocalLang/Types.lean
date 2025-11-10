import LocalLang.AST

inductive LLType where
  | nat
  | func (paramTypes : List LLType) (retType : LLType)

abbrev TypeContext := List (String × LLType) -- context, list of vars
