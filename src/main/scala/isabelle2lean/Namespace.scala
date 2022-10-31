package isabelle2lean

enum Namespace {
  case Var, Free, Theorem, Axiom, AxiomInstantiated, Constant, ConstantInstantiated, AbsVar, TFree, TVar, TypeCon, ProofAbsVar, ProofAbsVarTerm
}
