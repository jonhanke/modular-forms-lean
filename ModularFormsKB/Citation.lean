/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Lean

/-!
# The `@[kb]` citation attribute

Every result of the library that comes from the literature is tagged with where it comes from:

    @[kb "milne2017mf" "Theorem 6.1, pdf p. 88"]
    theorem foo : ... := ...

The first string is a key of `references.bib`, the second an optional locator in that source. The attribute records
the citation and nothing else: whether a declaration is proved is decided by the Lean kernel (its axioms), never by
the tag.
-/

namespace ModularFormsKB.Citation

open Lean

/-- One citation: a declaration and its literature source. -/
structure KBTag where
  decl : Name
  source : String
  locator : String
  deriving Inhabited, Repr

initialize kbExt : SimplePersistentEnvExtension KBTag (Array KBTag) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

/-- `@[kb "source" "locator"]` records a literature citation for a declaration. -/
syntax (name := kbAttr) "kb " str (ppSpace str)? : attr

initialize registerBuiltinAttribute {
  name := `kbAttr
  descr := "Tag a declaration with a literature citation (a key of references.bib and a locator)"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "the kb attribute must be global"
    match stx with
    | `(attr| kb $src:str $[$loc:str]?) =>
      modifyEnv fun env => kbExt.addEntry env
        { decl, source := src.getString, locator := (loc.map (·.getString)).getD "" }
    | _ => Elab.throwUnsupportedSyntax
}

/-- All tagged declarations visible in `env` (imported and local). -/
def kbEntries (env : Environment) : Array KBTag :=
  kbExt.getState env

end ModularFormsKB.Citation
