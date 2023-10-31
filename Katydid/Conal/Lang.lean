open List

def Lang : Type (u + 1) := {α : Type u} -> List α -> Type u

def emptySet : Lang := fun _ => Empty

def universal : Lang := fun _ => Unit

-- def emptyStr : Lang := fun w => w = []
