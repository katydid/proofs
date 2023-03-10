inductive Description where
  | intro
    (name : String)
    (hash : UInt64)
    (params : List Description)
  : Description
  deriving Repr

def cmp (x y: Description): Ordering :=
  match x with
  | ⟨xname, xhash, xparams⟩ =>
    match y with
    | ⟨yname, yhash, yparams⟩ =>
      let chash := compare xhash yhash
      if chash != Ordering.eq
      then chash
      else
        let cname := compare xname yname
        if cname != Ordering.eq
        then cname
        else lexLists xparams yparams
where lexLists (xs ys : List Description) : Ordering :=
  match xs, ys with
  | x::xs, y::ys =>
    let r := cmp x y
    if r != Ordering.eq
    then r
    else lexLists xs ys
  | _, _ => Ordering.eq