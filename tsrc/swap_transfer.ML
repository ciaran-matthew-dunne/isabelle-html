 fun swapty @{typ 'i} = @{typ 'j}
    | swapty @{typ 'j} = @{typ 'i}
    | swapty (Type ("fun",[u,t])) = swapty u --> swapty t
    | swapty ty = ty
  fun restrict_vars [] B = B
    | restrict_vars (x::xs) B = @{const conj} $ (@{term M} $ Var x) $ restrict_vars xs B
 
  fun swap i B = case fastype_of B of 
       (Type ("fun",[u,_])) => let
          val x = Var (("x",i), swapty u) in
          lambda x (swap (i+1) (B $ (swap (i+1) x))) end
     | @{typ 'i} => @{term Abs} $ B
     | @{typ 'j} => @{term Rep} $ B
     | @{typ bool} => B
     | _ => error "weird type!"

  fun gen_swaps mdl ctxt = let 
    val msig {name, target, sigmap} = mdl
    val cons = loc_consts ctxt target
    val mconst_of = app_sigmap sigmap ctxt
    val nameof = (fn (Free (n,_)) => n)
   in map (fn c => (mconst_of c, ("c" ^ nameof c, (swap 0 (mconst_of c))))) cons end

  fun make_defn name trm lthy = let
      val binding_const = (Binding.name name, NoSyn)
      val binding_fact = (Binding.name (name ^ "_def"), [])
      val arg = (binding_const, (binding_fact, trm))
      val ((_, (_ , thm)), lthy') = Local_Theory.define arg lthy
    in lthy' end;

  fun defn_swaps swaps ctxt = let
    fun get_def (n,t) = make_defn n t 
    fun add_def (n,t) = (Context.map_proof (get_def (n,t)) 
                        |> Context.proof_map)  
  in List.foldl (fn ((n,t),ct) => add_def (n,t) ct) ctxt swaps end 

fun type_transfer_rel @{typ 'j}   = @{term md}
  | type_transfer_rel @{typ bool} = @{term iff}
  | type_transfer_rel (Type ("fun",[u,t])) = 
      Const ("BNF_Def.rel_fun", 
         @{typ "(_ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow> (_ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow> (_ \<Rightarrow> _) \<Rightarrow> (_ \<Rightarrow> _) \<Rightarrow> bool"})
           $ type_transfer_rel u $  type_transfer_rel t

 fun gen_transfer_rule c1 c2 ctxt = let
   val ty = fastype_of c2
   val transfer_rel = Syntax.check_term ctxt (type_transfer_rel ty)
  in HOLogic.mk_Trueprop (transfer_rel $ c1 $ c2) end   

 fun gen_transfer_rules swaps ctxt = let
    val con_pairs = map (fn (mc, (n,_)) => (mc, Syntax.read_term ctxt n)) swaps 
  in map (fn (mc,c) => gen_transfer_rule mc c ctxt) con_pairs end; 
  
  fun lift_model_defs_cmd (thm_name, src) ctxt = let 
    val mdl = src_to_model src ctxt
    val swaps = gen_swaps mdl ctxt
    val ctxt' = defn_swaps (map snd swaps) ctxt
    val goals = gen_transfer_rules swaps ctxt'
    in Proof.theorem NONE (after_qed thm_name) [map (fn t => (t,[])) goals] ctxt' end

  val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "lift_model_defs"}
        "sets up proof state for showing model is closed under a sequence of constants" 
        (Parse_Spec.opt_thm_name ":" -- Parse.ML_source  >> lift_model_defs_cmd)