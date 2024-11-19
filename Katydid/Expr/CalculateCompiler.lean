-- Based on: https://youtu.be/uMurx1a6Zck?t=20144
-- We want:
-- 1. A Compiler (comp)
-- 2. A Virtual Machine (exec)
-- 3. A proof that it is correct (comp, exec = eval)

inductive Regex where
  | emptyset: Regex
  | emptystr: Regex
  | char (c: Char): Regex
  | or (left: Regex) (right: Regex): Regex
  deriving BEq

def derive (r: Regex) (c: Char): Regex :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.char a => if a == c then Regex.emptystr else Regex.emptystr
  | Regex.or a b => Regex.or (derive a c) (derive b c)

-- `eval :: Expr -> Int`
-- `eval :: Expr -> m Int`
-- `eval :: Expr -> State s Int`
-- `newtype State s v = State (s -> (s, v))`
-- `eval :: Expr -> s -> (s, v)`
-- `eval :: Regex -> String -> (String, Regex)`
def eval (r: Regex) (s: List Char): (List Char × Regex) :=
  (]
  , List.foldl derive r s)

-- The instruction set
-- To Calculate: `data Code = ?`

-- The compiler
-- Intuition: `comp :: Expr -> Code`
-- Practically we need a continuation in the compiler:
--  `comp :: Expr -> Code -> Code`, where initial Code is empty code
--  `comp :: Regex -> NFA -> NFA`, where initial NFA is an empty NFA
def comp (r: Regex) (d: NFA): NFA :=
  sorry

-- The virtual machine
-- `type Stack :: [Int]`
-- `exec :: Code -> Stack -> Stack`
-- `exec :: Code -> Stack -> m Stack`
-- `exec :: Code -> Stack -> State s Stack`
-- `newtype State s v = State (s -> (s, v))`
-- `exec :: NFA -> List Regex -> String -> (String, List Regex)`
-- Regex = the NFA state, otherwise we cannot do an equality between eval and exec
def exec (d: NFA) (current: List Regex) (s: String): (String × List Regex) :=
  sorry

-- Intuition: `comp, exec = eval`
-- Intuition: `exec (comp e) s = eval e : s`
-- Practically: `exec (comp e c) s = exec c (eval e : s)`
-- With Effects: `exec (comp e c) s = do v <- eval e; exec c (v: s)`
-- Solve this equation with 3 unknowns: comp, exec and code
-- This equation has more unknowns that equations
-- We solve this via constructive induction
-- With Regex: `exec (comp initial_regex empty_dfa) empty_regex str`
--             `= let (dstr, dregex) := eval initial_regex str in exec empty_dfa (dregex: empty_regex) dstr`
-- c = any_dfa or empty_dfa
-- e = initial_regex
-- s = any_regexes or empty_regexs or []
-- s has to be a list of states, to keep this formula general enough
-- if s is a list then we compile to an NFA, instead of a DFA
-- if we are compiling an automaton then our states have to regexes to be equal to eval and eval has to return a regex.
-- So this means that derivatives are probably going to be evaluator.

-- e = Val n
-- do v <- eval (Val n); exec c (v: s)
-- ...
-- = exec c' s
-- c' = comp (Val n) c

-- initial_regex = char c
-- `let (dstr, dregex) := eval (char c) str in exec empty_dfa (dregex: empty_regex) dstr`
-- `let (dstr, dregex) := ("", String.foldl derive (char c) str) in exec empty_dfa (dregex: empty_regex) dstr`
-- `let dregex := String.foldl derive (char c) str in exec empty_dfa (dregex: empty_regex) ""`
-- `exec (comp initial_regex empty_dfa) empty_regex str`


-- comp, exec = eval
-- exec (comp regex dfa) char = derive regex char
-- exec (comp regex dfa) (char:str) = exec (derive regex char) str
-- exec (comp (Char c) dfa) char = derive (Char c) char
-- if a == c then Regex.emptystr else Regex.emptystr
-- (comp (Char c) dfa)
-- dfa.add[Regex.char c, c] => Regex.emptystr
-- dfa.add[Regex.char c, !c] => Regex.emptyset
-- = exec c' char where c' = (comp (Char c) dfa)
