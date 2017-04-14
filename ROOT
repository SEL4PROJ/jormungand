session Sep_Algebra in "l4v/lib/sep_algebra" = HOL +
  options [document = false]
  theories
    "Generic_Separation_Algebras"
    "MonadSep"
    "Sep_Cancel_Example"
    "Sep_Eq"
    "Sep_Heap_Instance"
    "Sep_MP_Example"
    "Sep_Provers_Example"
    "Sep_Select_Example"
    "Sep_Solve_Example"

session Paper_Base = Sep_Algebra +
  options [document = false]
  theories [quick_and_dirty]
    "Paper_Defs"

session Paper = Paper_Base +
  options [document_output = output, document=pdf, show_question_marks = false,
           names_long = false, names_short = true, eta_contract = false]
  theories
    "Paper"
  document_files
    "build"
