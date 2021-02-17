#if COQVERSION >= 81300
open Big_int_Z
#else
open Big_int
#endif

#if COQVERSION >= 81300
let get_current_context = Declare.Proof.get_current_context
#elif COQVERSION >= 81200
let get_current_context = Declare.get_current_context
#else
let get_current_context = Pfedit.get_current_context
#endif

let find_reference t x =
  lazy (EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Coqlib.gen_reference_in_modules "Interval" [t] x)))

let is_global evd c t = EConstr.eq_constr evd (Lazy.force c) t

let coq_ref_Datatypes = find_reference ["Coq"; "Init"; "Datatypes"]
let coq_cons = coq_ref_Datatypes "cons"
let coq_nil = coq_ref_Datatypes "nil"
let coq_pair = coq_ref_Datatypes "pair"

let coq_ref_BinNums = find_reference ["Coq"; "Numbers"; "BinNums"]
let coq_Z0 = coq_ref_BinNums "Z0"
let coq_Zpos = coq_ref_BinNums "Zpos"
let coq_Zneg = coq_ref_BinNums "Zneg"
let coq_xH = coq_ref_BinNums "xH"
let coq_xI = coq_ref_BinNums "xI"
let coq_xO = coq_ref_BinNums "xO"

let coq_ref_Rdefinitions = find_reference ["Coq"; "Reals"; "Rdefinitions"]
let coq_Rdiv = coq_ref_Rdefinitions "Rdiv"
let coq_IZR = coq_ref_Rdefinitions "IZR"

let interval_plot2 = find_reference ["Interval"; "Tactics"; "Plot_helper"] "plot2"

exception NotPlot of EConstr.t

let rec tr_positive evd p =
  match EConstr.kind evd p with
  | Constr.Construct _ when is_global evd coq_xH p ->
      unit_big_int
  | Constr.App (f, [|a|]) when is_global evd coq_xI f ->
      add_int_big_int 1 (shift_left_big_int (tr_positive evd a) 1)
  | Constr.App (f, [|a|]) when is_global evd coq_xO f ->
      shift_left_big_int (tr_positive evd a) 1
  | Constr.Cast (p, _, _) ->
      tr_positive evd p
  | _ ->
      raise (NotPlot p)

let rec tr_Z evd t =
  match EConstr.kind evd t with
  | Constr.Construct _ when is_global evd coq_Z0 t ->
      zero_big_int
  | Constr.App (f, [|a|]) when is_global evd coq_Zpos f ->
      tr_positive evd a
  | Constr.App (f, [|a|]) when is_global evd coq_Zneg f ->
      minus_big_int (tr_positive evd a)
  | Constr.Cast (t, _, _) ->
      tr_Z evd t
  | _ ->
      raise (NotPlot t)

type rval =
  | Rcst of big_int
  | Rdiv of rval * rval

let rec tr_R evd t =
  match EConstr.kind evd t with
  | Constr.App (f, [|a|]) when is_global evd coq_IZR f ->
      Rcst (tr_Z evd a)
  | Constr.App (f, [|a;b|]) when is_global evd coq_Rdiv f ->
      Rdiv (tr_R evd a, tr_R evd b)
  | Constr.Cast (t, _, _) ->
      tr_R evd t
  | _ ->
      raise (NotPlot t)

let rec tr_list evd t =
  match EConstr.kind evd t with
  | Constr.App (f, [|_|]) when is_global evd coq_nil f ->
      []
  | Constr.App (f, [|_;a;b|]) when is_global evd coq_cons f ->
      let h =
        match EConstr.kind evd a with
        | Constr.App (f, [|_;_;a;b|]) when is_global evd coq_pair f ->
            (tr_Z evd a, tr_Z evd b)
        | _ ->
            raise (NotPlot a) in
      h :: tr_list evd b
  | Constr.Cast (t, _, _) ->
      tr_list evd t
  | _ -> raise (NotPlot t)

let tr_goal evd p =
  match EConstr.decompose_app evd p with
  | c, [_; ox; dx; oy; dy; h; l] when is_global evd interval_plot2 c ->
      (tr_R evd ox, tr_R evd dx, tr_R evd oy, tr_R evd dy, tr_Z evd h, tr_list evd l)
  | _ ->
      raise (NotPlot p)

let rec pr_R fmt = function
  | Rcst n -> Format.fprintf fmt "%s." (string_of_big_int n)
  | Rdiv (a,b) -> Format.fprintf fmt "(%a / %a)" pr_R a pr_R b

let generate fmt h l =
  Format.fprintf fmt "set xrange [] noextend@\n";
  Format.fprintf fmt "plot '-' using (ox+dx*$1):(oy+dy*$2):(oy+dy*$3) notitle with filledcurves@\n";
  let z = ref (h, zero_big_int) in
  let print_row i y1 y2 =
    Format.fprintf fmt "%d %s %s@\n" i (string_of_big_int y1) (string_of_big_int y2) in
  List.iteri (fun i y ->
      let (z1, z2) = y in
      let z1 = min_big_int z1 (fst !z) in
      let z2 = max_big_int z2 (snd !z) in
      print_row i z1 z2;
      z := y) l;
  print_row (List.length l) (fst !z) (snd !z);
  Format.fprintf fmt "e@\npause mouse close@\n@."

let display_plot env evd p =
  match tr_goal evd p with
  | (ox, dx, oy, dy, h, l) ->
      let file = Filename.temp_file "interval_plot" "" in
      let ch = open_out file in
      let fmt = Format.formatter_of_out_channel ch in
      Format.fprintf fmt "ox = %a@\ndx = %a@\noy = %a@\ndy = %a@\n"
        pr_R ox pr_R dx pr_R oy pr_R dy;
      generate fmt h l;
      close_out ch;
      let e = Sys.command (Printf.sprintf "gnuplot %s &" file) in
      if e <> 0 then
        CErrors.user_err ~hdr:"plot"
          (Pp.str "Gnuplot not found")
  | exception (NotPlot e) ->
      CErrors.user_err ~hdr:"plot"
        Pp.(str "Cannot parse" ++ spc () ++ Printer.pr_econstr_env env evd e)

let display_plot ~pstate p =
  let evd, env =
    match pstate with
    | None -> let env = Global.env () in Evd.from_env env, env
    | Some lemma -> get_current_context lemma in
  let evd, p = Constrintern.interp_constr_evars env evd p in
  let p = Retyping.get_type_of env evd p in
  display_plot env evd p

let __coq_plugin_name = "interval_plot"
let _ = Mltop.add_known_module __coq_plugin_name

let () =
  Vernacextend.vernac_extend
    ~command:"VernacPlot"
    ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None
    [Vernacextend.TyML
       (false,
        Vernacextend.TyTerminal
          ("Plot",
           Vernacextend.TyNonTerminal
             (Extend.TUentry (Genarg.get_arg_tag Stdarg.wit_constr),
              Vernacextend.TyNil)),
#if COQVERSION >= 81400
        (fun r ?loc ~atts ->
#else
        (fun r ~atts ->
#endif
          Attributes.unsupported_attributes atts;
          Vernacextend.VtReadProofOpt (display_plot r)),
        None)]
