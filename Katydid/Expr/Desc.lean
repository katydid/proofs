inductive Desc where
  | intro
    (name : String)
    (hash : UInt64)
    (params : List Desc)
    (reader: Bool)
  : Desc
  deriving Repr

def get_reader (desc: Desc): Bool :=
  match desc with
  | ⟨ _, _, _, reader⟩ => reader

def get_hash (desc: Desc): UInt64 :=
  match desc with
  | ⟨ _, hash, _, _ ⟩ => hash

def hash_list (innit: UInt64) (list: List UInt64): UInt64 :=
  List.foldl (fun acc h => 31 * acc + h) innit list

def hash_string (s: String): UInt64 :=
  hash_list 0 (List.map (Nat.toUInt64 ∘ Char.toNat) (String.toList s))

def hash_with_name (name: String) (params: List Desc): UInt64 :=
  hash_list (31 * 17 + hash_string name) (List.map get_hash params)

#eval hash_string "abcdefghjasdfasdf"

def introDesc (name: String) (params: List Desc): Desc :=
  Desc.intro
    name
    (hash_with_name name params)
    params
    (List.any params get_reader)

#eval introDesc "a" List.nil

def introReaderDesc (name: String) (params: List Desc): Desc :=
  ⟨
    name,
    hash_with_name name params,
    params,
    true
  ⟩

def cmp (x y: Desc): Ordering :=
  match x with
  | ⟨xname, xhash, xparams, _⟩ =>
    match y with
    | ⟨yname, yhash, yparams, _⟩ =>
      let chash := compare xhash yhash
      if chash != Ordering.eq
      then chash
      else
        let cname := compare xname yname
        if cname != Ordering.eq
        then cname
        else cmps xparams yparams
where cmps (xs ys : List Desc) : Ordering :=
  match xs, ys with
  | x::xs, y::ys =>
    let r := cmp x y
    if r != Ordering.eq
    then r
    else cmps xs ys
  | _, _ => Ordering.eq