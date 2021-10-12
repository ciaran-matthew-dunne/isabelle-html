(*fun mclosed i t = case fastype_of t of 
       typ as Type ("fun",[u,_]) => 
        if body_type typ = @{typ bool} then HOLogic.mk_Trueprop @{term True} else
          let val varx = (Var (("x",i), u)) 
          in Logic.all_const u $ lambda varx
             (@{term Pure.imp} $ (mclosed (i+1) varx) $ (mclosed (i+1) (t $ varx))) end
     | @{typ 'd} =>  HOLogic.mk_Trueprop (@{term inModel} $ t)
     | @{typ bool} => HOLogic.mk_Trueprop @{term True}
     | _ => error "weird type!"*)

fun mclosed i t = case fastype_of t of 
       typ as Type ("fun",[u,_]) => 
        if body_type typ = @{typ bool} then HOLogic.mk_Trueprop @{term True} else
          let val varx = (Var (("x",i), u)) 
          in Logic.all_const u $ lambda varx
             (mclosed (i+1) (t $ varx)) end
     | @{typ 'd} =>  HOLogic.mk_Trueprop (@{term inModel} $ t)
     | @{typ bool} => HOLogic.mk_Trueprop @{term True}
     | _ => error "weird type!"

val before_qed = SOME (Method.Basic (fn ctxt => 
  (SIMPLE_METHOD (simp_tac (put_simpset HOL_basic_ss ctxt) 0))))

fun model_closed_cmd (thm_name, src) ctxt = let
    val mdl as msig {name, target, sigmap} = src_to_model src ctxt
    val mconsts = get_mconsts mdl ctxt 
    val props = map (mclosed 0) mconsts
    val goals = filter (fn p => not (p = @{prop "True"})) props
  in 
    Proof.theorem NONE (after_qed thm_name) [map (fn t => (t,[])) goals] ctxt 
  end

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "model_closed"}
        "sets up proof state for showing model is closed under a sequence of constants" 
        (Parse_Spec.opt_thm_name ":" -- Parse.ML_source >> model_closed_cmd) 