(*  Title:      CCL/Term.thy
    Author:     Martin Coen
    Copyright   1993  University of Cambridge
*)

section \<open>Definitions of usual program constructs in CCL\<close>

theory Term
imports CCL
begin

definition one :: "i"
  where "one == true"

definition "if" :: "[i,i,i]\<Rightarrow>i"  ("(3if _/ then _/ else _)" [0,0,60] 60)
  where "if b then t else u  == case(b, t, u, \<lambda> x y. bot, \<lambda>v. bot)"

definition inl :: "i\<Rightarrow>i"
  where "inl(a) == <true,a>"

definition inr :: "i\<Rightarrow>i"
  where "inr(b) == <false,b>"

definition split :: "[i,[i,i]\<Rightarrow>i]\<Rightarrow>i"
  where "split(t,f) == case(t, bot, bot, f, \<lambda>u. bot)"

definition "when" :: "[i,i\<Rightarrow>i,i\<Rightarrow>i]\<Rightarrow>i"
  where "when(t,f,g) == split(t, \<lambda>b x. if b then f(x) else g(x))"

definition fst :: "i\<Rightarrow>i"
  where "fst(t) == split(t, \<lambda>x y. x)"

definition snd :: "i\<Rightarrow>i"
  where "snd(t) == split(t, \<lambda>x y. y)"

definition thd :: "i\<Rightarrow>i"
  where "thd(t) == split(t, \<lambda>x p. split(p, \<lambda>y z. z))"

definition zero :: "i"
  where "zero == inl(one)"

definition succ :: "i\<Rightarrow>i"
  where "succ(n) == inr(n)"

definition ncase :: "[i,i,i\<Rightarrow>i]\<Rightarrow>i"
  where "ncase(n,b,c) == when(n, \<lambda>x. b, \<lambda>y. c(y))"


no_syntax
  "_Let" :: "[letbinds, 'a] => 'a"  ("(let (_)/ in (_))" 10)

definition "let" :: "[i,i\<Rightarrow>i]\<Rightarrow>i"
  where "let(t, f) == case(t,f(true),f(false), \<lambda>x y. f(<x,y>), \<lambda>u. f(lam x. u(x)))"

syntax
  "_Let" :: "[letbinds, 'a] => 'a"  ("(let (_)/ in (_))" 10)

definition letrec :: "[[i,i\<Rightarrow>i]\<Rightarrow>i,(i\<Rightarrow>i)\<Rightarrow>i]\<Rightarrow>i"
  where "letrec(h, b) == b(\<lambda>x. fix(\<lambda>f. lam x. h(x,\<lambda>y. f`y))`x)"

definition letrec2 :: "[[i,i,i\<Rightarrow>i\<Rightarrow>i]\<Rightarrow>i,(i\<Rightarrow>i\<Rightarrow>i)\<Rightarrow>i]\<Rightarrow>i"
  where "letrec2 (h, f) ==
    letrec (\<lambda>p g'. split(p,\<lambda>x y. h(x,y,\<lambda>u v. g'(<u,v>))), \<lambda>g'. f(\<lambda>x y. g'(<x,y>)))"

definition letrec3 :: "[[i,i,i,i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i]\<Rightarrow>i,(i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i)\<Rightarrow>i]\<Rightarrow>i"
  where "letrec3 (h, f) ==
    letrec (\<lambda>p g'. split(p,\<lambda>x xs. split(xs,\<lambda>y z. h(x,y,z,\<lambda>u v w. g'(<u,<v,w>>)))),
      \<lambda>g'. f(\<lambda>x y z. g'(<x,<y,z>>)))"

syntax
  "_let" :: "[id,i,i]\<Rightarrow>i"  ("(3let _ be _/ in _)" [0,0,60] 60)
  "_letrec" :: "[id,id,i,i]\<Rightarrow>i"  ("(3letrec _ _ be _/ in _)" [0,0,0,60] 60)
  "_letrec2" :: "[id,id,id,i,i]\<Rightarrow>i"  ("(3letrec _ _ _ be _/ in _)" [0,0,0,0,60] 60)
  "_letrec3" :: "[id,id,id,id,i,i]\<Rightarrow>i"  ("(3letrec _ _ _ _ be _/ in _)" [0,0,0,0,0,60] 60)

ML \<open>
(** Quantifier translations: variable binding **)

(* FIXME does not handle "_idtdummy" *)
(* FIXME should use Syntax_Trans.mark_bound, Syntax_Trans.variant_abs' *)

fun let_tr [Free x, a, b] = Const(@{const_syntax let},dummyT) $ a $ absfree x b;
fun let_tr' [a,Abs(id,T,b)] =
     let val (id',b') = Syntax_Trans.variant_abs(id,T,b)
     in Const(@{syntax_const "_let"},dummyT) $ Free(id',T) $ a $ b' end;

fun letrec_tr [Free f, Free x, a, b] =
      Const(@{const_syntax letrec}, dummyT) $ absfree x (absfree f a) $ absfree f b;
fun letrec2_tr [Free f, Free x, Free y, a, b] =
      Const(@{const_syntax letrec2}, dummyT) $ absfree x (absfree y (absfree f a)) $ absfree f b;
fun letrec3_tr [Free f, Free x, Free y, Free z, a, b] =
      Const(@{const_syntax letrec3}, dummyT) $
        absfree x (absfree y (absfree z (absfree f a))) $ absfree f b;

fun letrec_tr' [Abs(x,T,Abs(f,S,a)),Abs(ff,SS,b)] =
     let val (f',b') = Syntax_Trans.variant_abs(ff,SS,b)
         val (_,a'') = Syntax_Trans.variant_abs(f,S,a)
         val (x',a') = Syntax_Trans.variant_abs(x,T,a'')
     in Const(@{syntax_const "_letrec"},dummyT) $ Free(f',SS) $ Free(x',T) $ a' $ b' end;
fun letrec2_tr' [Abs(x,T,Abs(y,U,Abs(f,S,a))),Abs(ff,SS,b)] =
     let val (f',b') = Syntax_Trans.variant_abs(ff,SS,b)
         val ( _,a1) = Syntax_Trans.variant_abs(f,S,a)
         val (y',a2) = Syntax_Trans.variant_abs(y,U,a1)
         val (x',a') = Syntax_Trans.variant_abs(x,T,a2)
     in Const(@{syntax_const "_letrec2"},dummyT) $ Free(f',SS) $ Free(x',T) $ Free(y',U) $ a' $ b'
      end;
fun letrec3_tr' [Abs(x,T,Abs(y,U,Abs(z,V,Abs(f,S,a)))),Abs(ff,SS,b)] =
     let val (f',b') = Syntax_Trans.variant_abs(ff,SS,b)
         val ( _,a1) = Syntax_Trans.variant_abs(f,S,a)
         val (z',a2) = Syntax_Trans.variant_abs(z,V,a1)
         val (y',a3) = Syntax_Trans.variant_abs(y,U,a2)
         val (x',a') = Syntax_Trans.variant_abs(x,T,a3)
     in Const(@{syntax_const "_letrec3"},dummyT) $ Free(f',SS) $ Free(x',T) $ Free(y',U) $ Free(z',V) $ a' $ b'
      end;
\<close>

parse_translation \<open>
 [(@{syntax_const "_let"}, K let_tr),
  (@{syntax_const "_letrec"}, K letrec_tr),
  (@{syntax_const "_letrec2"}, K letrec2_tr),
  (@{syntax_const "_letrec3"}, K letrec3_tr)]
\<close>

print_translation \<open>
 [(@{const_syntax let}, K let_tr'),
  (@{const_syntax letrec}, K letrec_tr'),
  (@{const_syntax letrec2}, K letrec2_tr'),
  (@{const_syntax letrec3}, K letrec3_tr')]
\<close>


definition nrec :: "[i,i,[i,i]\<Rightarrow>i]\<Rightarrow>i"
  where "nrec(n,b,c) == letrec g x be ncase(x, b, \<lambda>y. c(y,g(y))) in g(n)"

definition nil :: "i"  ("([])")
  where "[] == inl(one)"

definition cons :: "[i,i]\<Rightarrow>i"  (infixr "$" 80)
  where "h$t == inr(<h,t>)"

definition lcase :: "[i,i,[i,i]\<Rightarrow>i]\<Rightarrow>i"
  where "lcase(l,b,c) == when(l, \<lambda>x. b, \<lambda>y. split(y,c))"

definition lrec :: "[i,i,[i,i,i]\<Rightarrow>i]\<Rightarrow>i"
  where "lrec(l,b,c) == letrec g x be lcase(x, b, \<lambda>h t. c(h,t,g(t))) in g(l)"

definition napply :: "[i\<Rightarrow>i,i,i]\<Rightarrow>i"  ("(_ ^ _ ` _)" [56,56,56] 56)
  where "f ^n` a == nrec(n,a,\<lambda>x g. f(g))"

lemmas simp_can_defs = one_def inl_def inr_def
  and simp_ncan_defs = if_def when_def split_def fst_def snd_def thd_def
lemmas simp_defs = simp_can_defs simp_ncan_defs

lemmas ind_can_defs = zero_def succ_def nil_def cons_def
  and ind_ncan_defs = ncase_def nrec_def lcase_def lrec_def
lemmas ind_defs = ind_can_defs ind_ncan_defs

lemmas data_defs = simp_defs ind_defs napply_def
  and genrec_defs = letrec_def letrec2_def letrec3_def


subsection \<open>Beta Rules, including strictness\<close>

lemma letB: "\<not> t=bot \<Longrightarrow> let x be t in f(x) = f(t)"
  apply (unfold let_def)
  apply (erule rev_mp)
  apply (rule_tac t = "t" in term_case)
      apply (simp_all add: caseBtrue caseBfalse caseBpair caseBlam)
  done

lemma letBabot: "let x be bot in f(x) = bot"
  apply (unfold let_def)
  apply (rule caseBbot)
  done

lemma letBbbot: "let x be t in bot = bot"
  apply (unfold let_def)
  apply (rule_tac t = t in term_case)
      apply (rule caseBbot)
     apply (simp_all add: caseBtrue caseBfalse caseBpair caseBlam)
  done

lemma applyB: "(lam x. b(x)) ` a = b(a)"
  apply (unfold apply_def)
  apply (simp add: caseBtrue caseBfalse caseBpair caseBlam)
  done

lemma applyBbot: "bot ` a = bot"
  apply (unfold apply_def)
  apply (rule caseBbot)
  done

lemma fixB: "fix(f) = f(fix(f))"
  apply (unfold fix_def)
  apply (rule applyB [THEN ssubst], rule refl)
  done

lemma letrecB:
    "letrec g x be h(x,g) in g(a) = h(a,\<lambda>y. letrec g x be h(x,g) in g(y))"
  apply (unfold letrec_def)
  apply (rule fixB [THEN ssubst], rule applyB [THEN ssubst], rule refl)
  done

lemmas rawBs = caseBs applyB applyBbot

method_setup beta_rl = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (CHANGED o
      simp_tac (ctxt addsimps @{thms rawBs} setloop (fn _ => stac ctxt @{thm letrecB}))))
\<close>

lemma ifBtrue: "if true then t else u = t"
  and ifBfalse: "if false then t else u = u"
  and ifBbot: "if bot then t else u = bot"
  unfolding data_defs by beta_rl+

lemma whenBinl: "when(inl(a),t,u) = t(a)"
  and whenBinr: "when(inr(a),t,u) = u(a)"
  and whenBbot: "when(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma splitB: "split(<a,b>,h) = h(a,b)"
  and splitBbot: "split(bot,h) = bot"
  unfolding data_defs by beta_rl+

lemma fstB: "fst(<a,b>) = a"
  and fstBbot: "fst(bot) = bot"
  unfolding data_defs by beta_rl+

lemma sndB: "snd(<a,b>) = b"
  and sndBbot: "snd(bot) = bot"
  unfolding data_defs by beta_rl+

lemma thdB: "thd(<a,<b,c>>) = c"
  and thdBbot: "thd(bot) = bot"
  unfolding data_defs by beta_rl+

lemma ncaseBzero: "ncase(zero,t,u) = t"
  and ncaseBsucc: "ncase(succ(n),t,u) = u(n)"
  and ncaseBbot: "ncase(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma nrecBzero: "nrec(zero,t,u) = t"
  and nrecBsucc: "nrec(succ(n),t,u) = u(n,nrec(n,t,u))"
  and nrecBbot: "nrec(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma lcaseBnil: "lcase([],t,u) = t"
  and lcaseBcons: "lcase(x$xs,t,u) = u(x,xs)"
  and lcaseBbot: "lcase(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma lrecBnil: "lrec([],t,u) = t"
  and lrecBcons: "lrec(x$xs,t,u) = u(x,xs,lrec(xs,t,u))"
  and lrecBbot: "lrec(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma letrec2B:
  "letrec g x y be h(x,y,g) in g(p,q) = h(p,q,\<lambda>u v. letrec g x y be h(x,y,g) in g(u,v))"
  unfolding data_defs letrec2_def by beta_rl+

lemma letrec3B:
  "letrec g x y z be h(x,y,z,g) in g(p,q,r) =
    h(p,q,r,\<lambda>u v w. letrec g x y z be h(x,y,z,g) in g(u,v,w))"
  unfolding data_defs letrec3_def by beta_rl+

lemma napplyBzero: "f^zero`a = a"
  and napplyBsucc: "f^succ(n)`a = f(f^n`a)"
  unfolding data_defs by beta_rl+

lemmas termBs = letB applyB applyBbot splitB splitBbot fstB fstBbot
  sndB sndBbot thdB thdBbot ifBtrue ifBfalse ifBbot whenBinl whenBinr
  whenBbot ncaseBzero ncaseBsucc ncaseBbot nrecBzero nrecBsucc
  nrecBbot lcaseBnil lcaseBcons lcaseBbot lrecBnil lrecBcons lrecBbot
  napplyBzero napplyBsucc


subsection \<open>Constructors are injective\<close>

lemma term_injs:
  "(inl(a) = inl(a')) \<longleftrightarrow> (a=a')"
  "(inr(a) = inr(a')) \<longleftrightarrow> (a=a')"
  "(succ(a) = succ(a')) \<longleftrightarrow> (a=a')"
  "(a$b = a'$b') \<longleftrightarrow> (a=a' \<and> b=b')"
  by (inj_rl applyB splitB whenBinl whenBinr ncaseBsucc lcaseBcons)


subsection \<open>Constructors are distinct\<close>

ML \<open>
ML_Thms.bind_thms ("term_dstncts",
  mkall_dstnct_thms @{context} @{thms data_defs} (@{thms ccl_injs} @ @{thms term_injs})
    [["bot","inl","inr"], ["bot","zero","succ"], ["bot","nil","cons"]]);
\<close>


subsection \<open>Rules for pre-order \<open>[=\<close>\<close>

lemma term_porews:
  "inl(a) [= inl(a') \<longleftrightarrow> a [= a'"
  "inr(b) [= inr(b') \<longleftrightarrow> b [= b'"
  "succ(n) [= succ(n') \<longleftrightarrow> n [= n'"
  "x$xs [= x'$xs' \<longleftrightarrow> x [= x' \<and> xs [= xs'"
  by (simp_all add: data_defs ccl_porews)


subsection \<open>Rewriting and Proving\<close>

ML \<open>
  ML_Thms.bind_thms ("term_injDs", XH_to_Ds @{thms term_injs});
\<close>

lemmas term_rews = termBs term_injs term_dstncts ccl_porews term_porews

lemmas [simp] = term_rews
lemmas [elim!] = term_dstncts [THEN notE]
lemmas [dest!] = term_injDs

end
