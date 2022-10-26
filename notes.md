# New plan

- Constants:
  - Do not produce output
  - Are represented by a unique name `fullName`
  - Are given as explicit arguments to everything else that uses them
  - When a constant is used in different instantiations, several arguments are given
- Axioms:
  - Have a `fullName`
  - `def fullName consts := prop_of_the_axiom consts`
  - `consts` are all the constants occurring in the prop
- Theorems:
  - Have a `fullName`
  - `def fullName consts assms := proofterm`
  - `consts` are all the constants occurring in the prop and the proof
  - `assms` = all axioms used in the proofterm (in the form `assmVar : axiom.fullName consts`)
