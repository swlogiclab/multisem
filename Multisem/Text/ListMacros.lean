def buildAppend (stx: Lean.Syntax) (l:List Lean.Syntax) : Lean.MacroM (Lean.TSyntax `term) :=
  match l with
  | [] => throw (Lean.Macro.Exception.error stx "Must have at least one word")
  | x::[] => match x with
             | Lean.Syntax.ident _ _ (Lean.Name.str _ txt) _ =>
               pure (Lean.Syntax.mkCApp `List.cons #[Lean.Syntax.mkStrLit txt, Lean.Syntax.mkCApp `List.nil #[]])
             | _ => --pure (Lean.Syntax.mkStrLit (toString x))
               throw  (Lean.Macro.Exception.error stx "Only individual words are valid")
  | x::xs => 
    do
      let rhs <- buildAppend stx xs;
      match x with
      | Lean.Syntax.ident _ _ (Lean.Name.str _ txt) _ =>
        pure (Lean.Syntax.mkCApp `List.cons #[Lean.Syntax.mkStrLit txt, rhs])
      | _ => throw (Lean.Macro.Exception.error stx "Only individual words are valid")

syntax (name := splitParser) "[|" ident+ "|]": term
@[macro splitParser] def implSplitParser : Lean.Macro :=
  fun stx =>
    let val := stx;
    let argc := Lean.Syntax.getNumArgs val;
    let text := Lean.Syntax.getArg val 1;
    --let stext := toString text;
    --let words := String.splitOn stext " ";
    do
      --let info <- Lean.MonadRef.mkInfoFromRefPos;
      match text with
      | Lean.Syntax.node _ _ mid => buildAppend val mid.data
      | _ => pure (Lean.Syntax.mkNumLit (toString argc))
      --pure (Lean.Syntax.mkStrLit stext)

#check [|a b c d|]