set_option linter.unusedVariables false
set_option autoImplicit false

axiom proof_omitted {p: Prop}: p

def prop := Prop
-- def Pure_imp x y := x -> y
-- def Pure_eq {a: Type} (x y : a) := x = y
-- def Pure_all {_a0 : Type} (f: _a0 -> prop) := ∀x, f x
-- def Pure_prop (x: Prop) := x
def HOL_bool := Bool
inductive itself (a: Type) : Type where
  | itself : itself a
def Nat_nat := Nat
def Set_set a := a -> Bool
def Nat_ind := Nat
inductive Num_num : Type where
  | One : Num_num
  | Bit0 : Num_num -> Num_num
  | Bit1 : Num_num -> Num_num
inductive Sum_Type_sum (a b: Type) : Type where
  | inl : a -> Sum_Type_sum a b
  | inr : b -> Sum_Type_sum a b
def Product_Type_unit := Unit
def Product_Type_prod := Prod
axiom Num_num_num_IITN_num : Type
def Int_int := Int
instance nonempty_HOL_bool: Nonempty HOL_bool := Nonempty.intro true
instance nonempty_Set_set a : Nonempty (Set_set a) :=
  Nonempty.intro fun _ => false
instance nonempty_Prop: Nonempty prop := Nonempty.intro True
instance nonempty_Nat_nat: Nonempty Nat_nat := Nonempty.intro (0 : Nat)
instance nonempty_Nat_ind: Nonempty Nat_ind := Nonempty.intro (0 : Nat)
instance nonempty_Num_num: Nonempty Num_num := Nonempty.intro Num_num.One
instance: Nonempty Product_Type_unit := Nonempty.intro ()
instance nonempty_Product_Type_prod (a b: Type) [sa: Nonempty a] [sb: Nonempty b]: Nonempty (Product_Type_prod a b) :=
  match sa with | Nonempty.intro xa => match sb with | Nonempty.intro xb => Nonempty.intro (xa,xb)
instance: Nonempty Int_int := Nonempty.intro (0 : Int)
instance (a b: Type) [sa: Nonempty a]: Nonempty (Sum_Type_sum a b) :=
  match sa with | Nonempty.intro xa => Nonempty.intro (Sum_Type_sum.inl xa)
instance: Nonempty Num_num_num_IITN_num := proof_omitted
