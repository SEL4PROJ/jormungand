section \<open>Examples\<close>

theory OG_Examples imports OG_Syntax begin

subsection \<open>Mutual Exclusion\<close>

subsubsection \<open>Peterson's Algorithm I\<close>

text \<open>Eike Best. "Semantics of Sequential and Parallel Programs", page 217.\<close>

record Petersons_mutex_1 =
 pr1 :: nat
 pr2 :: nat
 in1 :: bool
 in2 :: bool
 hold :: nat

lemma Petersons_mutex_1:
  "\<parallel>- \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1 \<and> \<acute>pr2=0 \<and> \<not>\<acute>in2 \<rbrace>
  COBEGIN \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace>
  WHILE True INV \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace>
  DO
  \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace> \<langle> \<acute>in1:=True,,\<acute>pr1:=1 \<rangle>;;
  \<lbrace>\<acute>pr1=1 \<and> \<acute>in1\<rbrace>  \<langle> \<acute>hold:=1,,\<acute>pr1:=2 \<rangle>;;
  \<lbrace>\<acute>pr1=2 \<and> \<acute>in1 \<and> (\<acute>hold=1 \<or> \<acute>hold=2 \<and> \<acute>pr2=2)\<rbrace>
  AWAIT (\<not>\<acute>in2 \<or> \<not>(\<acute>hold=1)) THEN \<acute>pr1:=3 END;;
  \<lbrace>\<acute>pr1=3 \<and> \<acute>in1 \<and> (\<acute>hold=1 \<or> \<acute>hold=2 \<and> \<acute>pr2=2)\<rbrace>
   \<langle>\<acute>in1:=False,,\<acute>pr1:=0\<rangle>
  OD \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace>
  \<parallel>
  \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>
  WHILE True INV \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>
  DO
  \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace> \<langle> \<acute>in2:=True,,\<acute>pr2:=1 \<rangle>;;
  \<lbrace>\<acute>pr2=1 \<and> \<acute>in2\<rbrace> \<langle>  \<acute>hold:=2,,\<acute>pr2:=2 \<rangle>;;
  \<lbrace>\<acute>pr2=2 \<and> \<acute>in2 \<and> (\<acute>hold=2 \<or> (\<acute>hold=1 \<and> \<acute>pr1=2))\<rbrace>
  AWAIT (\<not>\<acute>in1 \<or> \<not>(\<acute>hold=2)) THEN \<acute>pr2:=3  END;;
  \<lbrace>\<acute>pr2=3 \<and> \<acute>in2 \<and> (\<acute>hold=2 \<or> (\<acute>hold=1 \<and> \<acute>pr1=2))\<rbrace>
    \<langle>\<acute>in2:=False,,\<acute>pr2:=0\<rangle>
  OD \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>
  COEND
  \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1 \<and> \<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>"
apply oghoare
\<comment>\<open>104 verification conditions.\<close>
apply auto
done

subsubsection \<open>Peterson's Algorithm II: A Busy Wait Solution\<close>

text \<open>Apt and Olderog. "Verification of sequential and concurrent Programs", page 282.\<close>

record Busy_wait_mutex =
 flag1 :: bool
 flag2 :: bool
 turn  :: nat
 after1 :: bool
 after2 :: bool

lemma Busy_wait_mutex:
 "\<parallel>-  \<lbrace>True\<rbrace>
  \<acute>flag1:=False,, \<acute>flag2:=False,,
  COBEGIN \<lbrace>\<not>\<acute>flag1\<rbrace>
        WHILE True
        INV \<lbrace>\<not>\<acute>flag1\<rbrace>
        DO \<lbrace>\<not>\<acute>flag1\<rbrace> \<langle> \<acute>flag1:=True,,\<acute>after1:=False \<rangle>;;
           \<lbrace>\<acute>flag1 \<and> \<not>\<acute>after1\<rbrace> \<langle> \<acute>turn:=1,,\<acute>after1:=True \<rangle>;;
           \<lbrace>\<acute>flag1 \<and> \<acute>after1 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)\<rbrace>
            WHILE \<not>(\<acute>flag2 \<longrightarrow> \<acute>turn=2)
            INV \<lbrace>\<acute>flag1 \<and> \<acute>after1 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)\<rbrace>
            DO \<lbrace>\<acute>flag1 \<and> \<acute>after1 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)\<rbrace> SKIP OD;;
           \<lbrace>\<acute>flag1 \<and> \<acute>after1 \<and> (\<acute>flag2 \<and> \<acute>after2 \<longrightarrow> \<acute>turn=2)\<rbrace>
            \<acute>flag1:=False
        OD
       \<lbrace>False\<rbrace>
  \<parallel>
     \<lbrace>\<not>\<acute>flag2\<rbrace>
        WHILE True
        INV \<lbrace>\<not>\<acute>flag2\<rbrace>
        DO \<lbrace>\<not>\<acute>flag2\<rbrace> \<langle> \<acute>flag2:=True,,\<acute>after2:=False \<rangle>;;
           \<lbrace>\<acute>flag2 \<and> \<not>\<acute>after2\<rbrace> \<langle> \<acute>turn:=2,,\<acute>after2:=True \<rangle>;;
           \<lbrace>\<acute>flag2 \<and> \<acute>after2 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)\<rbrace>
            WHILE \<not>(\<acute>flag1 \<longrightarrow> \<acute>turn=1)
            INV \<lbrace>\<acute>flag2 \<and> \<acute>after2 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)\<rbrace>
            DO \<lbrace>\<acute>flag2 \<and> \<acute>after2 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)\<rbrace> SKIP OD;;
           \<lbrace>\<acute>flag2 \<and> \<acute>after2 \<and> (\<acute>flag1 \<and> \<acute>after1 \<longrightarrow> \<acute>turn=1)\<rbrace>
            \<acute>flag2:=False
        OD
       \<lbrace>False\<rbrace>
  COEND
  \<lbrace>False\<rbrace>"
apply oghoare
\<comment>\<open>122 vc\<close>
apply auto
done

subsubsection \<open>Peterson's Algorithm III: A Solution using Semaphores\<close>

record  Semaphores_mutex =
 out :: bool
 who :: nat

lemma Semaphores_mutex:
 "\<parallel>- \<lbrace>i\<noteq>j\<rbrace>
  \<acute>out:=True ,,
  COBEGIN \<lbrace>i\<noteq>j\<rbrace>
       WHILE True INV \<lbrace>i\<noteq>j\<rbrace>
       DO \<lbrace>i\<noteq>j\<rbrace> AWAIT \<acute>out THEN  \<acute>out:=False,, \<acute>who:=i END;;
          \<lbrace>\<not>\<acute>out \<and> \<acute>who=i \<and> i\<noteq>j\<rbrace> \<acute>out:=True OD
       \<lbrace>False\<rbrace>
  \<parallel>
       \<lbrace>i\<noteq>j\<rbrace>
       WHILE True INV \<lbrace>i\<noteq>j\<rbrace>
       DO \<lbrace>i\<noteq>j\<rbrace> AWAIT \<acute>out THEN  \<acute>out:=False,,\<acute>who:=j END;;
          \<lbrace>\<not>\<acute>out \<and> \<acute>who=j \<and> i\<noteq>j\<rbrace> \<acute>out:=True OD
       \<lbrace>False\<rbrace>
  COEND
  \<lbrace>False\<rbrace>"
apply oghoare
\<comment>\<open>38 vc\<close>
apply auto
done

subsubsection \<open>Peterson's Algorithm III: Parameterized version:\<close>

lemma Semaphores_parameterized_mutex:
 "0<n \<Longrightarrow> \<parallel>- \<lbrace>True\<rbrace>
  \<acute>out:=True ,,
 COBEGIN
  SCHEME [0\<le> i< n]
    \<lbrace>True\<rbrace>
     WHILE True INV \<lbrace>True\<rbrace>
      DO \<lbrace>True\<rbrace> AWAIT \<acute>out THEN  \<acute>out:=False,, \<acute>who:=i END;;
         \<lbrace>\<not>\<acute>out \<and> \<acute>who=i\<rbrace> \<acute>out:=True OD
    \<lbrace>False\<rbrace>
 COEND
  \<lbrace>False\<rbrace>"
apply oghoare
\<comment>\<open>20 vc\<close>
apply auto
done

subsubsection\<open>The Ticket Algorithm\<close>

record Ticket_mutex =
 num :: nat
 nextv :: nat
 turn :: "nat list"
 index :: nat

lemma Ticket_mutex:
 "\<lbrakk> 0<n; I=\<guillemotleft>n=length \<acute>turn \<and> 0<\<acute>nextv \<and> (\<forall>k l. k<n \<and> l<n \<and> k\<noteq>l
    \<longrightarrow> \<acute>turn!k < \<acute>num \<and> (\<acute>turn!k =0 \<or> \<acute>turn!k\<noteq>\<acute>turn!l))\<guillemotright> \<rbrakk>
   \<Longrightarrow> \<parallel>- \<lbrace>n=length \<acute>turn\<rbrace>
   \<acute>index:= 0,,
   WHILE \<acute>index < n INV \<lbrace>n=length \<acute>turn \<and> (\<forall>i<\<acute>index. \<acute>turn!i=0)\<rbrace>
    DO \<acute>turn:= \<acute>turn[\<acute>index:=0],, \<acute>index:=\<acute>index +1 OD,,
  \<acute>num:=1 ,, \<acute>nextv:=1 ,,
 COBEGIN
  SCHEME [0\<le> i< n]
    \<lbrace>\<acute>I\<rbrace>
     WHILE True INV \<lbrace>\<acute>I\<rbrace>
      DO \<lbrace>\<acute>I\<rbrace> \<langle> \<acute>turn :=\<acute>turn[i:=\<acute>num],, \<acute>num:=\<acute>num+1 \<rangle>;;
         \<lbrace>\<acute>I\<rbrace> WAIT \<acute>turn!i=\<acute>nextv END;;
         \<lbrace>\<acute>I \<and> \<acute>turn!i=\<acute>nextv\<rbrace> \<acute>nextv:=\<acute>nextv+1
      OD
    \<lbrace>False\<rbrace>
 COEND
  \<lbrace>False\<rbrace>"
apply oghoare
\<comment>\<open>35 vc\<close>
apply simp_all
\<comment>\<open>16 vc\<close>
apply(tactic \<open>ALLGOALS (clarify_tac @{context})\<close>)
\<comment>\<open>11 vc\<close>
apply simp_all
apply(tactic \<open>ALLGOALS (clarify_tac @{context})\<close>)
\<comment>\<open>10 subgoals left\<close>
apply(erule less_SucE)
 apply simp
apply simp
\<comment>\<open>9 subgoals left\<close>
apply(case_tac "i=k")
 apply force
apply simp
apply(case_tac "i=l")
 apply force
apply force
\<comment>\<open>8 subgoals left\<close>
prefer 8
apply force
apply force
\<comment>\<open>6 subgoals left\<close>
prefer 6
apply(erule_tac x=j in allE)
apply fastforce
\<comment>\<open>5 subgoals left\<close>
prefer 5
apply(case_tac [!] "j=k")
\<comment>\<open>10 subgoals left\<close>
apply simp_all
apply(erule_tac x=k in allE)
apply force
\<comment>\<open>9 subgoals left\<close>
apply(case_tac "j=l")
 apply simp
 apply(erule_tac x=k in allE)
 apply(erule_tac x=k in allE)
 apply(erule_tac x=l in allE)
 apply force
apply(erule_tac x=k in allE)
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply force
\<comment>\<open>8 subgoals left\<close>
apply force
apply(case_tac "j=l")
 apply simp
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply force
apply force
apply force
\<comment>\<open>5 subgoals left\<close>
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply(case_tac "j=l")
 apply force
apply force
apply force
\<comment>\<open>3 subgoals left\<close>
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply(case_tac "j=l")
 apply force
apply force
apply force
\<comment>\<open>1 subgoals left\<close>
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply(case_tac "j=l")
 apply force
apply force
done

subsection\<open>Parallel Zero Search\<close>

text \<open>Synchronized Zero Search. Zero-6\<close>

text \<open>Apt and Olderog. "Verification of sequential and concurrent Programs" page 294:\<close>

record Zero_search =
   turn :: nat
   found :: bool
   x :: nat
   y :: nat

lemma Zero_search:
  "\<lbrakk>I1= \<guillemotleft> a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> (a<\<acute>x \<and> f(\<acute>x)=0) \<or> (\<acute>y\<le>a \<and> f(\<acute>y)=0))
      \<and> (\<not>\<acute>found \<and> a<\<acute> x \<longrightarrow> f(\<acute>x)\<noteq>0) \<guillemotright> ;
    I2= \<guillemotleft>\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> (a<\<acute>x \<and> f(\<acute>x)=0) \<or> (\<acute>y\<le>a \<and> f(\<acute>y)=0))
      \<and> (\<not>\<acute>found \<and> \<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0) \<guillemotright> \<rbrakk> \<Longrightarrow>
  \<parallel>- \<lbrace>\<exists> u. f(u)=0\<rbrace>
  \<acute>turn:=1,, \<acute>found:= False,,
  \<acute>x:=a,, \<acute>y:=a+1 ,,
  COBEGIN \<lbrace>\<acute>I1\<rbrace>
       WHILE \<not>\<acute>found
       INV \<lbrace>\<acute>I1\<rbrace>
       DO \<lbrace>a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> \<acute>y\<le>a \<and> f(\<acute>y)=0) \<and> (a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)\<rbrace>
          WAIT \<acute>turn=1 END;;
          \<lbrace>a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> \<acute>y\<le>a \<and> f(\<acute>y)=0) \<and> (a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)\<rbrace>
          \<acute>turn:=2;;
          \<lbrace>a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> \<acute>y\<le>a \<and> f(\<acute>y)=0) \<and> (a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)\<rbrace>
          \<langle> \<acute>x:=\<acute>x+1,,
            IF f(\<acute>x)=0 THEN \<acute>found:=True ELSE SKIP FI\<rangle>
       OD;;
       \<lbrace>\<acute>I1  \<and> \<acute>found\<rbrace>
       \<acute>turn:=2
       \<lbrace>\<acute>I1 \<and> \<acute>found\<rbrace>
  \<parallel>
      \<lbrace>\<acute>I2\<rbrace>
       WHILE \<not>\<acute>found
       INV \<lbrace>\<acute>I2\<rbrace>
       DO \<lbrace>\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> a<\<acute>x \<and> f(\<acute>x)=0) \<and> (\<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)\<rbrace>
          WAIT \<acute>turn=2 END;;
          \<lbrace>\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> a<\<acute>x \<and> f(\<acute>x)=0) \<and> (\<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)\<rbrace>
          \<acute>turn:=1;;
          \<lbrace>\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> a<\<acute>x \<and> f(\<acute>x)=0) \<and> (\<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)\<rbrace>
          \<langle> \<acute>y:=(\<acute>y - 1),,
            IF f(\<acute>y)=0 THEN \<acute>found:=True ELSE SKIP FI\<rangle>
       OD;;
       \<lbrace>\<acute>I2 \<and> \<acute>found\<rbrace>
       \<acute>turn:=1
       \<lbrace>\<acute>I2 \<and> \<acute>found\<rbrace>
  COEND
  \<lbrace>f(\<acute>x)=0 \<or> f(\<acute>y)=0\<rbrace>"
apply oghoare
\<comment>\<open>98 verification conditions\<close>
apply auto
\<comment>\<open>auto takes about 3 minutes !!\<close>
done

text \<open>Easier Version: without AWAIT.  Apt and Olderog. page 256:\<close>

lemma Zero_Search_2:
"\<lbrakk>I1=\<guillemotleft> a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> (a<\<acute>x \<and> f(\<acute>x)=0) \<or> (\<acute>y\<le>a \<and> f(\<acute>y)=0))
    \<and> (\<not>\<acute>found \<and> a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)\<guillemotright>;
 I2= \<guillemotleft>\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> (a<\<acute>x \<and> f(\<acute>x)=0) \<or> (\<acute>y\<le>a \<and> f(\<acute>y)=0))
    \<and> (\<not>\<acute>found \<and> \<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)\<guillemotright>\<rbrakk> \<Longrightarrow>
  \<parallel>- \<lbrace>\<exists>u. f(u)=0\<rbrace>
  \<acute>found:= False,,
  \<acute>x:=a,, \<acute>y:=a+1,,
  COBEGIN \<lbrace>\<acute>I1\<rbrace>
       WHILE \<not>\<acute>found
       INV \<lbrace>\<acute>I1\<rbrace>
       DO \<lbrace>a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> \<acute>y\<le>a \<and> f(\<acute>y)=0) \<and> (a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)\<rbrace>
          \<langle> \<acute>x:=\<acute>x+1,,IF f(\<acute>x)=0 THEN  \<acute>found:=True ELSE  SKIP FI\<rangle>
       OD
       \<lbrace>\<acute>I1 \<and> \<acute>found\<rbrace>
  \<parallel>
      \<lbrace>\<acute>I2\<rbrace>
       WHILE \<not>\<acute>found
       INV \<lbrace>\<acute>I2\<rbrace>
       DO \<lbrace>\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> a<\<acute>x \<and> f(\<acute>x)=0) \<and> (\<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)\<rbrace>
          \<langle> \<acute>y:=(\<acute>y - 1),,IF f(\<acute>y)=0 THEN  \<acute>found:=True ELSE  SKIP FI\<rangle>
       OD
       \<lbrace>\<acute>I2 \<and> \<acute>found\<rbrace>
  COEND
  \<lbrace>f(\<acute>x)=0 \<or> f(\<acute>y)=0\<rbrace>"
apply oghoare
\<comment>\<open>20 vc\<close>
apply auto
\<comment>\<open>auto takes aprox. 2 minutes.\<close>
done

subsection \<open>Producer/Consumer\<close>

subsubsection \<open>Previous lemmas\<close>

lemma nat_lemma2: "\<lbrakk> b = m*(n::nat) + t; a = s*n + u; t=u; b-a < n \<rbrakk> \<Longrightarrow> m \<le> s"
proof -
  assume "b = m*(n::nat) + t" "a = s*n + u" "t=u"
  hence "(m - s) * n = b - a" by (simp add: diff_mult_distrib)
  also assume "\<dots> < n"
  finally have "m - s < 1" by simp
  thus ?thesis by arith
qed

lemma mod_lemma: "\<lbrakk> (c::nat) \<le> a; a < b; b - c < n \<rbrakk> \<Longrightarrow> b mod n \<noteq> a mod n"
apply(subgoal_tac "b=b div n*n + b mod n" )
 prefer 2  apply (simp add: div_mult_mod_eq [symmetric])
apply(subgoal_tac "a=a div n*n + a mod n")
 prefer 2
 apply(simp add: div_mult_mod_eq [symmetric])
apply(subgoal_tac "b - a \<le> b - c")
 prefer 2 apply arith
apply(drule le_less_trans)
back
 apply assumption
apply(frule less_not_refl2)
apply(drule less_imp_le)
apply (drule_tac m = "a" and k = n in div_le_mono)
apply(safe)
apply(frule_tac b = "b" and a = "a" and n = "n" in nat_lemma2, assumption, assumption)
apply assumption
apply(drule order_antisym, assumption)
apply(rotate_tac -3)
apply(simp)
done


subsubsection \<open>Producer/Consumer Algorithm\<close>

record Producer_consumer =
  ins :: nat
  outs :: nat
  li :: nat
  lj :: nat
  vx :: nat
  vy :: nat
  buffer :: "nat list"
  b :: "nat list"

text \<open>The whole proof takes aprox. 4 minutes.\<close>

lemma Producer_consumer:
  "\<lbrakk>INIT= \<guillemotleft>0<length a \<and> 0<length \<acute>buffer \<and> length \<acute>b=length a\<guillemotright> ;
    I= \<guillemotleft>(\<forall>k<\<acute>ins. \<acute>outs\<le>k \<longrightarrow> (a ! k) = \<acute>buffer ! (k mod (length \<acute>buffer))) \<and>
            \<acute>outs\<le>\<acute>ins \<and> \<acute>ins-\<acute>outs\<le>length \<acute>buffer\<guillemotright> ;
    I1= \<guillemotleft>\<acute>I \<and> \<acute>li\<le>length a\<guillemotright> ;
    p1= \<guillemotleft>\<acute>I1 \<and> \<acute>li=\<acute>ins\<guillemotright> ;
    I2 = \<guillemotleft>\<acute>I \<and> (\<forall>k<\<acute>lj. (a ! k)=(\<acute>b ! k)) \<and> \<acute>lj\<le>length a\<guillemotright> ;
    p2 = \<guillemotleft>\<acute>I2 \<and> \<acute>lj=\<acute>outs\<guillemotright> \<rbrakk> \<Longrightarrow>
  \<parallel>- \<lbrace>\<acute>INIT\<rbrace>
 \<acute>ins:=0,, \<acute>outs:=0,, \<acute>li:=0,, \<acute>lj:=0,,
 COBEGIN \<lbrace>\<acute>p1 \<and> \<acute>INIT\<rbrace>
   WHILE \<acute>li <length a
     INV \<lbrace>\<acute>p1 \<and> \<acute>INIT\<rbrace>
   DO \<lbrace>\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li<length a\<rbrace>
       \<acute>vx:= (a ! \<acute>li);;
      \<lbrace>\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li<length a \<and> \<acute>vx=(a ! \<acute>li)\<rbrace>
        WAIT \<acute>ins-\<acute>outs < length \<acute>buffer END;;
      \<lbrace>\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li<length a \<and> \<acute>vx=(a ! \<acute>li)
         \<and> \<acute>ins-\<acute>outs < length \<acute>buffer\<rbrace>
       \<acute>buffer:=(list_update \<acute>buffer (\<acute>ins mod (length \<acute>buffer)) \<acute>vx);;
      \<lbrace>\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li<length a
         \<and> (a ! \<acute>li)=(\<acute>buffer ! (\<acute>ins mod (length \<acute>buffer)))
         \<and> \<acute>ins-\<acute>outs <length \<acute>buffer\<rbrace>
       \<acute>ins:=\<acute>ins+1;;
      \<lbrace>\<acute>I1 \<and> \<acute>INIT \<and> (\<acute>li+1)=\<acute>ins \<and> \<acute>li<length a\<rbrace>
       \<acute>li:=\<acute>li+1
   OD
  \<lbrace>\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li=length a\<rbrace>
  \<parallel>
  \<lbrace>\<acute>p2 \<and> \<acute>INIT\<rbrace>
   WHILE \<acute>lj < length a
     INV \<lbrace>\<acute>p2 \<and> \<acute>INIT\<rbrace>
   DO \<lbrace>\<acute>p2 \<and> \<acute>lj<length a \<and> \<acute>INIT\<rbrace>
        WAIT \<acute>outs<\<acute>ins END;;
      \<lbrace>\<acute>p2 \<and> \<acute>lj<length a \<and> \<acute>outs<\<acute>ins \<and> \<acute>INIT\<rbrace>
       \<acute>vy:=(\<acute>buffer ! (\<acute>outs mod (length \<acute>buffer)));;
      \<lbrace>\<acute>p2 \<and> \<acute>lj<length a \<and> \<acute>outs<\<acute>ins \<and> \<acute>vy=(a ! \<acute>lj) \<and> \<acute>INIT\<rbrace>
       \<acute>outs:=\<acute>outs+1;;
      \<lbrace>\<acute>I2 \<and> (\<acute>lj+1)=\<acute>outs \<and> \<acute>lj<length a \<and> \<acute>vy=(a ! \<acute>lj) \<and> \<acute>INIT\<rbrace>
       \<acute>b:=(list_update \<acute>b \<acute>lj \<acute>vy);;
      \<lbrace>\<acute>I2 \<and> (\<acute>lj+1)=\<acute>outs \<and> \<acute>lj<length a \<and> (a ! \<acute>lj)=(\<acute>b ! \<acute>lj) \<and> \<acute>INIT\<rbrace>
       \<acute>lj:=\<acute>lj+1
   OD
  \<lbrace>\<acute>p2 \<and> \<acute>lj=length a \<and> \<acute>INIT\<rbrace>
 COEND
 \<lbrace> \<forall>k<length a. (a ! k)=(\<acute>b ! k)\<rbrace>"
apply oghoare
\<comment>\<open>138 vc\<close>
apply(tactic \<open>ALLGOALS (clarify_tac @{context})\<close>)
\<comment>\<open>112 subgoals left\<close>
apply(simp_all (no_asm))
\<comment>\<open>43 subgoals left\<close>
apply(tactic \<open>ALLGOALS (conjI_Tac @{context} (K all_tac))\<close>)
\<comment>\<open>419 subgoals left\<close>
apply(tactic \<open>ALLGOALS (clarify_tac @{context})\<close>)
\<comment>\<open>99 subgoals left\<close>
apply(simp_all only:length_0_conv [THEN sym])
\<comment>\<open>20 subgoals left\<close>
apply (simp_all del:length_0_conv length_greater_0_conv add: nth_list_update mod_lemma)
\<comment>\<open>9 subgoals left\<close>
apply (force simp add:less_Suc_eq)
apply(hypsubst_thin, drule sym)
apply (force simp add:less_Suc_eq)+
done

subsection \<open>Parameterized Examples\<close>

subsubsection \<open>Set Elements of an Array to Zero\<close>

record Example1 =
  a :: "nat \<Rightarrow> nat"

lemma Example1:
 "\<parallel>- \<lbrace>True\<rbrace>
   COBEGIN SCHEME [0\<le>i<n] \<lbrace>True\<rbrace> \<acute>a:=\<acute>a (i:=0) \<lbrace>\<acute>a i=0\<rbrace> COEND
  \<lbrace>\<forall>i < n. \<acute>a i = 0\<rbrace>"
apply oghoare
apply simp_all
done

text \<open>Same example with lists as auxiliary variables.\<close>
record Example1_list =
  A :: "nat list"
lemma Example1_list:
 "\<parallel>- \<lbrace>n < length \<acute>A\<rbrace>
   COBEGIN
     SCHEME [0\<le>i<n] \<lbrace>n < length \<acute>A\<rbrace> \<acute>A:=\<acute>A[i:=0] \<lbrace>\<acute>A!i=0\<rbrace>
   COEND
    \<lbrace>\<forall>i < n. \<acute>A!i = 0\<rbrace>"
apply oghoare
apply force+
done

subsubsection \<open>Increment a Variable in Parallel\<close>

text \<open>First some lemmas about summation properties.\<close>
(*
lemma Example2_lemma1: "!!b. j<n \<Longrightarrow> (\<Sum>i::nat<n. b i) = (0::nat) \<Longrightarrow> b j = 0 "
apply(induct n)
 apply simp_all
apply(force simp add: less_Suc_eq)
done
*)
lemma Example2_lemma2_aux: "!!b. j<n \<Longrightarrow>
 (\<Sum>i=0..<n. (b i::nat)) =
 (\<Sum>i=0..<j. b i) + b j + (\<Sum>i=0..<n-(Suc j) . b (Suc j + i))"
apply(induct n)
 apply simp_all
apply(simp add:less_Suc_eq)
 apply(auto)
apply(subgoal_tac "n - j = Suc(n- Suc j)")
  apply simp
apply arith
done

lemma Example2_lemma2_aux2:
  "!!b. j\<le> s \<Longrightarrow> (\<Sum>i::nat=0..<j. (b (s:=t)) i) = (\<Sum>i=0..<j. b i)"
apply(induct j)
 apply simp_all
done

lemma Example2_lemma2:
 "!!b. \<lbrakk>j<n; b j=0\<rbrakk> \<Longrightarrow> Suc (\<Sum>i::nat=0..<n. b i)=(\<Sum>i=0..<n. (b (j := Suc 0)) i)"
apply(frule_tac b="(b (j:=(Suc 0)))" in Example2_lemma2_aux)
apply(erule_tac  t="sum (b(j := (Suc 0))) {0..<n}" in ssubst)
apply(frule_tac b=b in Example2_lemma2_aux)
apply(erule_tac  t="sum b {0..<n}" in ssubst)
apply(subgoal_tac "Suc (sum b {0..<j} + b j + (\<Sum>i=0..<n - Suc j. b (Suc j + i)))=(sum b {0..<j} + Suc (b j) + (\<Sum>i=0..<n - Suc j. b (Suc j + i)))")
apply(rotate_tac -1)
apply(erule ssubst)
apply(subgoal_tac "j\<le>j")
 apply(drule_tac b="b" and t="(Suc 0)" in Example2_lemma2_aux2)
apply(rotate_tac -1)
apply(erule ssubst)
apply simp_all
done


record Example2 =
 c :: "nat \<Rightarrow> nat"
 x :: nat

lemma Example_2: "0<n \<Longrightarrow>
 \<parallel>- \<lbrace>\<acute>x=0 \<and> (\<Sum>i=0..<n. \<acute>c i)=0\<rbrace>
 COBEGIN
   SCHEME [0\<le>i<n]
  \<lbrace>\<acute>x=(\<Sum>i=0..<n. \<acute>c i) \<and> \<acute>c i=0\<rbrace>
   \<langle> \<acute>x:=\<acute>x+(Suc 0),, \<acute>c:=\<acute>c (i:=(Suc 0)) \<rangle>
  \<lbrace>\<acute>x=(\<Sum>i=0..<n. \<acute>c i) \<and> \<acute>c i=(Suc 0)\<rbrace>
 COEND
 \<lbrace>\<acute>x=n\<rbrace>"
apply oghoare
apply (simp_all cong del: sum.strong_cong)
apply (tactic \<open>ALLGOALS (clarify_tac @{context})\<close>)
apply (simp_all cong del: sum.strong_cong)
   apply(erule (1) Example2_lemma2)
  apply(erule (1) Example2_lemma2)
 apply(erule (1) Example2_lemma2)
apply(simp)
done

end
