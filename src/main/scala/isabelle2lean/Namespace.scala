package isabelle2lean

enum Namespace {
  case Var, Free, Theorem, Axiom, AxiomProof, AxiomInstantiated, ConstantType, ConstantDef, ConstantInstantiated, AbsVar, TFree,
     TVar, TypeCon, ProofAbsVar, ProofAbsVarTerm
}
