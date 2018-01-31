(*<*)
theory Tree imports Main begin
(*>*)

text{*\noindent
Define the datatype of \rmindex{binary trees}:
*}

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"(*<*)

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"(*>*)

text{*\noindent
Define a function @{term"mirror"} that mirrors a binary tree
by swapping subtrees recursively. Prove
*}

lemma mirror_mirror: "mirror(mirror t) = t"
(*<*)
apply(induct_tac t)
by(auto)

primrec flatten :: "'a tree => 'a list" where
"flatten Tip = []" |
"flatten (Node l x r) = flatten l @ [x] @ flatten r"
(*>*)

text{*\noindent
Define a function @{term"flatten"} that flattens a tree into a list
by traversing it in infix order. Prove
*}

lemma "flatten(mirror t) = rev(flatten t)"
(*<*)
apply(induct_tac t)
by(auto)

end
(*>*)
