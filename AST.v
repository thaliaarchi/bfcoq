Inductive ast : Type :=
  | ARight
  | ALeft
  | AInc
  | ADec
  | AOutput
  | AInput
  | ALoop (body : list ast).
