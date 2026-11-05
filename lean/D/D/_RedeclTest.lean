import D.Main

-- EXPERIMENT: does Lean 4.34 reject redeclaration of `Race.bound`
-- (already declared in D.Bound)? If this compiles, shadowing is allowed.
theorem Race.bound : True := trivial
