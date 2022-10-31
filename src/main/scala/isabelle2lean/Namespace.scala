package isabelle2lean

enum Namespace {
  case Var, Free, Theorem, Axiom, AxiomInstantiated, ConstantType, ConstantDef, ConstantInstantiated, AbsVar, TFree,
     TVar, TypeCon, ProofAbsVar, ProofAbsVarTerm
}
