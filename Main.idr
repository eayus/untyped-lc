-- Untyped lambda calculus implemntation in Idris

data Term
  = Var Nat          -- A variable is represented by its de-bruijn index
  | Abs Term         -- An abstraction introduces a new function
  | App Term Term    -- One term applied to another


-- Variables are either free or bound
data VarType
  = Free
  | Bound


-- Turns the type into a function that can be used to determine
-- whether a variable with brujin index 'i' within 'n' abstractions
-- is Free/Bound. ('i' -> 'n' -> Bool)
varPred : VarType -> Nat -> Nat -> Bool
varPred Free  = (>)
varPred Bound = (==)


-- Iterates through the AST of a Term, applying 'f' on
-- variables of type 'ty'.
termMap : VarType -> (Nat -> Nat -> Term) -> Term -> Term
termMap ty f = go 0 where
    -- 'n' represents the number of abstractions the current term is
    go : Nat -> Term -> Term
    go n (Var i) with (varPred ty i n)
        | True       = f n i                    -- If the variable matches the desired type, apply f
        | False      = Var i                    -- Else leave it unchanged
    go n (Abs body)  = Abs $ go (succ n) body   -- Recurse, incrementing n as we will be under another abstraction
    go n (App t1 t2) = App (go n t1) (go n t2)  -- Function application does not introduce an abstraction, so leave n unchanged


-- Apply a function to all of the indices of free variables
mapFreeIndices : (Nat -> Nat) -> Term -> Term
mapFreeIndices f t = termMap Free (const $ Var . f) t


-- Substitute 't1' into 't2' at the top level (replacing variables with index 0)
substitute : Term -> Term -> Term
substitute t1 t2 = termMap Bound (\n => const $ mapFreeIndices (+n) t1) t2


-- Perform a beta reduction (aka function application). First decrement all
-- free variable indices in the body, since function application removes the
-- top level abstraction. Then substitute the function argument into the body.
betaReduce : Term -> Term -> Term
betaReduce body arg = substitute arg $ mapFreeIndices Nat.pred body


-- Perform one reductive step. If no step could be applied, return Nothing
simplify : Term -> Maybe Term
simplify (App (Abs body) arg@(Abs _)) = Just $ betaReduce body arg            -- Use function application if possible
simplify (App f@(Abs _) arg)          = App f <$> simplify arg                -- Simplify the argument, so function application can be used next
simplify (App f arg)                  = flip App arg <$> simplify f           -- Simplify the function, so function application can be used next
simplify t                            = Nothing                               -- No simplification rules apply, so return Nothing


-- Evaluate a term down to it's normal form. This uses strict evaluation.
-- Note that this may not terminate: this a "feature" of untyped lc.
-- Here we keep simplifying until no more simplifying steps are available.
eval : Term -> Term
eval t = maybe t eval $ simplify t
