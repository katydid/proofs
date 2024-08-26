-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Decidability.lagda


-- data Dec (A: Set l):Set l where
--   yes: A → Dec A
--   no :¬A → Dec A
inductive Dec (α: Type u): Type u where
  | yes: α -> Dec α
  | no: (α -> PEmpty.{u}) -> Dec α

-- ⊥? : Dec ⊥
-- ⊥? =no(𝜆())
def empty? : Dec PEmpty :=
  Dec.no (by intro; contradiction)

def unit? : Dec PUnit :=
  Dec.yes PUnit.unit

def sum? (a: Dec α) (b: Dec β): Dec (α ⊕ β) :=
  match (a, b) with
  | (Dec.no a, Dec.no b) =>
    Dec.no (fun ab =>
      match ab with
      | Sum.inl sa => a sa
      | Sum.inr sb => b sb
    )
  | (Dec.yes a, Dec.no _) =>
    Dec.yes (Sum.inl a)
  | (_, Dec.yes b) =>
    Dec.yes (Sum.inr b)

def prod? (a: Dec α) (b: Dec β): Dec (α × β) :=
  match (a, b) with
  | (Dec.yes a, Dec.yes b) => Dec.yes (Prod.mk a b)
  | (Dec.no a, Dec.yes _) => Dec.no (fun ⟨a', _⟩ => a a')
  | (_, Dec.no b) => Dec.no (fun ⟨_, b'⟩ => b b')

def list?: Dec α -> Dec (List α) := fun _ => Dec.yes []
