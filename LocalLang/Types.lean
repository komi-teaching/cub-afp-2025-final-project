import LocalLang.AST

inductive LLType where
  | nat
  | func (paramTypes : List LLType) (retType : LLType)

def TypeContext := List (String × LLType)
