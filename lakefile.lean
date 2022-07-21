import Lake
open Lake DSL

--package automata {
--  -- add configuration options here
--  dependencies := #[{
--    name := `mathlib
--    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "800bc41"
--  }]
--  defaultFacet := PackageFacet.oleans
--}
package multisem {
  defaultFacet := PackageFacet.oleans
}