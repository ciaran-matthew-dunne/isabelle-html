

(*We can use Isabelle's interpretation mechanism if we build the GZF locale
  on top of a quantifier locale,  but then we would have to port all of the
  HOL logic, and redefine blast, auto, simp, etc accordingly... *)

val add_variables = fold_aterms (fn a => (is_Var a orelse is_Free a) ? insert (op =) a);
fun variables_of t = rev (add_variables t []);
fun elem x xs = List.exists (fn y => x = y) xs

fun trans_conv _ (Const ("HOL.All", @{typ "('d \<Rightarrow> bool) \<Rightarrow> bool"})) = @{term mall}
  | trans_conv _ (Const ("HOL.All", @{typ "(('d \<Rightarrow> 'd) \<Rightarrow> bool) \<Rightarrow> bool"})) = @{term fun_mall}
  | trans_conv _ (Const ("HOL.All", @{typ "(('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> bool) \<Rightarrow> bool"})) = @{term binfun_mall}
  | trans_conv _ (Const ("HOL.Ex", @{typ "('d \<Rightarrow> bool) \<Rightarrow> bool"}))  = @{term mex}
  | trans_conv _ (Const ("HOL.Uniq", @{typ "('d \<Rightarrow> bool) \<Rightarrow> bool"}))  = @{term muniq}
  | trans_conv _ (c as Const _) = c
  | trans_conv f (c as Free _) = f c
  | trans_conv _ t = t

fun trans f trm = map_aterms (trans_conv f) trm

fun loc_consts ctxt loc_name = map (Free o fst) (Locale.params_of (Proof_Context.theory_of ctxt) loc_name)

fun loc_axs thy loc_name = case hd (Locale.hyp_spec_of thy loc_name) of
   Element.Assumes xs => map (fn (a,b) => (fst a, fst (hd b))) xs
 | _ => error ("Problem with applying hyp_spec_of to:" ^ loc_name) 

fun find_locale_name ctxt str = 
       case Syntax.read_term ctxt str of
          Const (name,_) => name
        | _ => error ("Can't find locale: " ^ str)

datatype model_sig = msig of 
  {name : string, target: string, 
   sigmap : string -> string}

fun name_of (Free (n,_)) = n
  | name_of (Const (n,_)) = n
  | name_of _ = error "not a free or const"  

fun loc_cnames ctxt lname =  map name_of (loc_consts ctxt lname)
fun mk_fun dom ran c = 
  case List.find (fn (x,_) => x = c) (ListPair.zip (dom,ran)) of
    SOME (_,y) => y
  | NONE   => c  

fun mk_msig str loc tstrs ctxt  = let 
    val lname = find_locale_name ctxt loc 
    val lcon_names = loc_cnames ctxt lname
  in 
    msig {name = str, target = lname,
          sigmap = mk_fun lcon_names tstrs}
  end;

fun get_lconsts mdl ctxt = let
  val msig {target, sigmap,...} = mdl 
  in map (Syntax.read_term ctxt) (loc_cnames ctxt target) end;

fun get_mconsts mdl ctxt = let
  val msig {target, sigmap,...} = mdl 
  in map (Syntax.read_term ctxt o sigmap) (loc_cnames ctxt target) end;

fun app_sigmap f ctxt c = Syntax.read_term ctxt (f (name_of c))

fun extend_msig m1 str loc tstrs ctxt = let 
    val msig {target = l1name, sigmap = smap, ...} = m1  
    val l2name = find_locale_name ctxt loc 
    val l1consts = loc_cnames ctxt l1name
    val l2consts = loc_cnames ctxt l2name
    val smap_ex = filter (fn c => not (elem c l1consts)) l2consts  
  in
    msig {name = str, target = l2name,
          sigmap = (fn c => 
            if smap c = c 
            then mk_fun smap_ex tstrs c 
            else smap c)}
  end
    
fun gen_goals ctxt lname smap =
  let
      val thy = Proof_Context.theory_of ctxt
      val axs = map snd (loc_axs thy lname)
      val f = (fn c => (Syntax.read_term ctxt (smap (name_of c))))
  in
   map (trans f) axs
  end


fun after_qed thm_name thms lthy =
      Local_Theory.note (thm_name, (flat thms)) lthy |> snd

structure Result = Proof_Data
  (type T = unit -> model_sig
   fun init _ () = error "Result")

val result_cookie = (Result.get, Result.put, "Result.put")

fun src_to_model src ctxt = let
    val (text, _) = Input.source_content src
    val model = Code_Runtime.value ctxt result_cookie ("", text)
  in model end;

fun model_interp_cmd (thm_name,src) ctxt = let
      val msig {name, target, sigmap} = src_to_model src ctxt
      val goals = gen_goals ctxt target sigmap 
    in 
      Proof.theorem NONE (after_qed thm_name) [map (fn t => (t,[])) goals] ctxt 
    end

val mGZF = mk_msig "mGZF" "GZF" 
      ["mMem", "mEmp", "mSet", "mUnion", 
       "mSubset", "mPow", "mSucc", "mInf", "mRepl"] @{context}

val mOrd = extend_msig mGZF "mOrd" "Ord_locale.Ord" 
       ["mOrd", "mlt","mzero", "msucc", "mLimit", "mpredSet", "mOrdRec", "momega"] @{context}

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "model_interpretation"}
        "sets up proof state for the translation of each axiom of a locale" 
        (Parse_Spec.opt_thm_name ":" -- Parse.ML_source >> model_interp_cmd)
