import Lake
open Lake DSL

package «sessiontypes» where
  -- add package configuration options here

@[default_target]
lean_lib «SessionTypes» where
  -- add library configuration options here

lean_exe «test_simple» where
  root := `test.Lean.Simple
