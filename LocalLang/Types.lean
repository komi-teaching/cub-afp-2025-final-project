import LocalLang.AST

inductive LLType where
  | nat
  | func (paramTypes : List LLType) (retType : LLType)

abbrev TypeContext := Std.HashMap String LLType
