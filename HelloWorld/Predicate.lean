import HelloWorld.Ordering

#eval lex Ordering.eq Ordering.lt

inductive Desc where
  | intro
    (name : String)
    (hash : UInt64)
    (params : List Desc)
    (reader : Bool)
  : Desc
  deriving Repr

def get_reader (desc: Desc): Bool :=
  match desc with
  | ⟨ _, _, _, reader⟩ => reader

def get_hash (desc: Desc): UInt64 :=
  match desc with
  | ⟨ _, hash, _, _ ⟩ => hash

def hashList (innit: UInt64) (list: List UInt64): UInt64 :=
  List.foldl (fun acc h => 31 * acc + h) innit list

def hashString (s: String): UInt64 :=
  hashList 0 (List.map (Nat.toUInt64 ∘ Char.toNat) (String.toList s))

def hashWithName (name: String) (params: List Desc): UInt64 :=
  hashList (31 * 17 + hashString name) (List.map get_hash params)

#eval hashString "abcdefghjasdfasdf"

def introDesc (name: String) (params: List Desc): Desc :=
  Desc.intro
    name
    (hashWithName name params)
    params
    (List.any params get_reader)

#eval introDesc "a" List.nil

def introReaderDesc (name: String) (params: List Desc): Desc :=
  ⟨
    name,
    hashWithName name params,
    params,
    true
  ⟩