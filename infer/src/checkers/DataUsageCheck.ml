open! IStd
open! Graph
open! Hashtbl
module F = Format

module DomainData = struct
  type classification =
    |N
    |U
    |B 
    |W
    |BU 
    |NW 
  [@@deriving compare]

  let classi_leq ~lhs ~rhs = 
    if (phys_equal lhs rhs) then true
  else 
    match (lhs, rhs) with 
     |_,U -> true
     |U,_ -> false  
     |N,_ -> true
     |_,N -> false
     |_,_ -> true 


  let classi_join a b = 
    if (phys_equal a b) then a
  else 
    match (a, b) with 
     |_,U -> U
     |U,_ -> U
     |_, BU -> BU
     |BU, _ -> BU 
     |N, a -> a
     |a, N -> a
     |B,B -> B
     |W,W -> W
     |NW,NW -> NW
     |_ , _ -> raise (Invalid_argument "W,B or B,W cant be joined")                                              

  let pp_classi fmt classi = 
    let s =
      match classi with
      | N ->
          "NOT_USED"
      | U ->
          "USED"
      | B ->
          "BELLOW"
      | W ->
          "OVERWRITTEN"
      | BU ->
          "BELLOW (Used before PUSH)"
      | NW ->
          "NOT_USED (Overwritten before PUSH)"
    in
    F.fprintf fmt "%s" s


  type t = {loc: Location.t ; classi: classification}
  [@@deriving compare]

  let pp fmt {loc; classi} =
    F.fprintf fmt "%a at %a" pp_classi classi Location.pp loc

  let leq ~lhs ~rhs =
    classi_leq ~lhs:lhs.classi ~rhs:rhs.classi 

  let loc_join t1 t2 =
    let a=t1.loc in 
    let b=t2.loc in 
    if (a.line > b.line) then a
  else b
  
  let join elem1 elem2 =                                                     
    {loc = (loc_join elem1 elem2) ;classi= (classi_join elem1.classi elem2.classi)}

  let widen ~prev ~next ~num_iters:_ = join prev next     

  let push t =                                           
    let temp_loc = t.loc in
    match t.classi with 
      |U -> {loc=temp_loc; classi=BU}
      |W -> {loc=temp_loc; classi=NW}
      |B -> {loc=temp_loc; classi=B}
      |N -> {loc=temp_loc; classi=N}
      |BU -> {loc=temp_loc; classi=BU}
      |NW -> {loc=temp_loc; classi=NW}

  let pop t =                                           
    let temp_loc = t.loc in
    match t.classi with 
      |B -> {loc=temp_loc; classi=B} 
      |N -> {loc=temp_loc; classi=N} 
      |U -> {loc=temp_loc; classi=U} 
      |W -> {loc=temp_loc; classi=W}
      |BU -> {loc=temp_loc; classi=U}
      |NW -> {loc=temp_loc; classi=W}


end



(**)module Var_map = struct

  let leq ~lhs:_ ~rhs:_ = assert false

  let join _ b = b

  let widen ~prev ~next ~num_iters:_ = join prev next

  let pp fmt var = F.fprintf fmt "%a" Var.pp var

  type t = Var.t

end

module Map = AbstractDomain.Map (Var) (DomainData)

module Map_Vars = AbstractDomain.Map (Var) (Var_map)

module Domain =  struct
  type t = {map: Map.t; hash: (string, string) Hashtbl.t; map_vars: Map_Vars.t}

  let hash_join a b = if ((Hashtbl.length a) > (Hashtbl.length b)) then a else b

  let hash_pp fmt hash =
    Hashtbl.iteri hash ~f:(fun ~key ~data ->
      F.fprintf fmt "@[<1>%s: %s@]@." key data)

  let leq ~lhs ~rhs = Map.leq ~lhs:lhs.map ~rhs:rhs.map

  let join a b = {map = Map.join a.map b.map; hash= (hash_join a.hash b.hash); map_vars= (Map_Vars.join a.map_vars b.map_vars)} 

  let widen ~prev ~next ~num_iters:_ = join prev next     

  let pp fmt {map; hash; map_vars} = F.fprintf fmt "%a \nHASH: %a \nMAP_VARS %a" Map.pp map hash_pp hash Map_Vars.pp map_vars

  let change_map t new_map = 
    {map= new_map; hash = t.hash; map_vars=t.map_vars}

  let change_map_vars t new_map_vars =
    {map= t.map; hash = t.hash; map_vars=new_map_vars}


end


let has_2_preds cfg_node =
  match (List.length (Procdesc.Node.get_preds cfg_node)) with
  |0 -> false
  |1 -> false 
  |_ -> true

let is_statement_node cfg_node =                      
  match Procdesc.Node.get_kind cfg_node with 
  |Stmt_node _ -> true
  |Exit_node -> true
  | _ -> false

let check_if_used_assign astate e1 =
  if (Map.mem e1 astate) then 
  begin 
    let dd = Map.find e1 astate in           
    match dd.classi with
      |DomainData.U -> true
      |DomainData.B -> true
      |DomainData.N -> false 
      |DomainData.W -> false
      |DomainData.BU -> true
      |DomainData.NW -> false
  end 
  else false        

let is_e1_in_e2 e1 e2 =                        
  let seq1 = Var.get_all_vars_in_exp e2 in                     
  Sequence.exists seq1 ~f:(fun a -> phys_equal a e1)   

let update_e2_without_e1 astate e1 e2 loc=          
  let seq1 = Var.get_all_vars_in_exp e2 in                             
  Sequence.fold seq1 ~init:astate 
  ~f:(fun state a -> if (phys_equal a e1) then state else  Map.add a {loc; classi=U} state)                        

let check_exp_exists astate e loc=                                                        
  let seq = Var.get_all_vars_in_exp e in    
  Sequence.fold seq ~init:astate ~f:(fun state a -> if not (Map.mem a state) then (Map.add a {loc; classi=N} state) else state)

let check_exp astate id loc =                                                              
  if (Map.mem (Var.of_id id) astate) then astate else (Map.add (Var.of_id id) {loc; classi=N} astate) 

let change_key_in_map id e astate =   
  
  let temp_value = Map.find (Var.of_id id) astate in         

  let old_value = Map.find e astate in 
  let new_value = DomainData.join temp_value old_value in
  Map.add e new_value astate   


let load_helper id e astate =
  let seq = Var.get_all_vars_in_exp e in
  Sequence.fold seq ~init:astate ~f:(fun state a ->change_key_in_map id a state) 

let check_e1_used_helper astate e1 = 
  let seq = Var.get_all_vars_in_exp e1 in   
  Sequence.fold seq ~init:false ~f:(fun state a -> if (check_if_used_assign astate a) then true else state)      (*if any of the vars in e1 is true, then keeps that answer*)

let update_e2_without_e1_helper astate e1 e2 loc =        (*checks all e1 vars for equality with e2 and updates the different ones*)
  let seq = Var.get_all_vars_in_exp e1 in     
  Sequence.fold seq ~init:astate ~f:(fun _ a -> update_e2_without_e1 astate a e2 loc)

let is_e1_in_e2_helper e1 e2 = 
  let seq = Var.get_all_vars_in_exp e1 in      
  Sequence.fold seq ~init:false ~f:(fun state a -> if (is_e1_in_e2 a e2) then true else state)

let exp_classi_update astate e clas loc=                                    (*Update classification without changing location*)
  let seq = Var.get_all_vars_in_exp e in         
  Sequence.fold seq ~init:astate ~f:(fun state a -> 
    if not (Map.mem a state) then                             
      Map.add a {loc; classi=clas} state
    else 
      let old_loc = ((Map.find a astate).loc) in               
      Map.add a {loc = old_loc; classi=clas} state                                  
  )

let filter_prune2 astate expp loc=                                                                   
    if (Map.exists (fun _ value ->if  (phys_equal value.classi DomainData.U) then true else if (phys_equal value.classi DomainData.W) then true else false ) astate) then (exp_classi_update astate expp U loc) 
  else astate

let update_assign_e1_e2 astate e1 e2 loc = 
  let state = check_exp_exists (check_exp_exists astate e1 loc) e2 loc in      (*checks if e1 and e2 exists and adds them to domain if not*)
  if (check_e1_used_helper state e1) then                                        
    if (is_e1_in_e2_helper e1 e2) then (update_e2_without_e1_helper state e1 e2 loc)                     
    else exp_classi_update (exp_classi_update state e1 W loc) e2 U loc           
  else state   

let no_dollar_sign var =  (*checks the presence of sign $ in the string. To avoid false positives*)         
  let exp_string = Exp.to_string (Var.to_exp var) in 
  match (String.contains exp_string '$') with 
   |true -> false
   |false -> true

let remove_fp var =  (*checks the presence of "this" and "_"*)
  let exp_string = Exp.to_string (Var.to_exp var) in
  match exp_string with 
  |"&this" -> false 
  |"_" -> false
  |_ -> true 

let remove_signs_from_domain astate =          (*removes vars with character $ in it. to avoid false positives*)                       
  let state = Map.filter (fun key _ -> no_dollar_sign key) astate in 
  Map.filter (fun key _ -> remove_fp key) state  

let check_exists_arg_ts astate args loc =
  match args with 
    | (exp, _) -> check_exp_exists astate exp loc

let id_classi_update astate id clas =                                      
  let old_loc = ((Map.find (Var.of_id id) astate).loc) in               
  Map.add (Var.of_id id) {loc = old_loc; classi=clas} astate 

let arg_ts_update astate arg_ts clas loc =                     
  match arg_ts with 
    |(exp, _) -> exp_classi_update astate exp clas loc 

let arg_ts_fold astate arg_ts clas loc =                        
  List.fold arg_ts ~init:astate ~f:(fun state args -> arg_ts_update state args clas loc ) 

let update_exps_call astate ret_id arg_ts loc =                          
  let state0 = List.fold arg_ts ~init:astate ~f:(fun state args -> check_exists_arg_ts state args loc ) in 
  let state = check_exp state0 ret_id loc in 
  if (check_if_used_assign state (Var.of_id ret_id)) then  arg_ts_fold (id_classi_update state ret_id W) arg_ts U loc
  else state

let hash_logic_load id e key hash array1 =  (*gets the vars that we need in an array *) 
  let ns2_string = Hashtbl.find_exn hash (Ident.to_string id) in                     (*gets the value of v1 from the hashtable*)
  let n2s2 = "&"^ns2_string in
  if (Var.equal key (Var.of_pvar e)) then   
    (Array.set array1 0 key ; array1)(*update d with assign logic*)
  else if (String.equal (Exp.to_string (Var.to_exp key)) n2s2) then
    (Array.set array1 1 key ; array1)(*update v1 with assign logic*)
  else if (String.equal (Exp.to_string (Var.to_exp key)) ns2_string) then
    (Array.set array1 1 key ; array1)(*update v1 with assign logic*)
  else 
  begin 
    if ((Hashtbl.length hash)> 1) then
      begin 
      let second_key =Hashtbl.find_exn hash (";"^(Ident.to_string id)) in                            
      let key_modified = "&"^(second_key) in
        if (String.equal (Exp.to_string (Var.to_exp key)) key_modified) then  (Array.set array1 2 key ; array1)
        else if (String.equal (Exp.to_string (Var.to_exp key)) second_key) then  (Array.set array1 2 key ; array1)
        else array1
      end
    else array1
  end

let classi_update_map map e clas loc=                                    (*Update classification without changing location*)
  if not (Map.mem e map) then                              
    Map.add e {loc; classi=clas} map
  else 
    let old_loc = ((Map.find e map).loc) in               
    Map.add e {loc = old_loc; classi=clas} map                                  

let assign_logic_array map e1 e2 loc =  
  if (check_if_used_assign map e1) then 
    classi_update_map (classi_update_map map e1 W loc) e2 U loc
  else map 

let is_in_hashtbl hash id= 
  Hashtbl.existsi hash  ~f:(fun ~key ~data -> if (String.equal key (Ident.to_string id)) then true else if (String.equal data (Ident.to_string id)) then true else false)



let check_pvar_exists map pvar loc =                                                              
  if (Map.mem (Var.of_pvar pvar) map) then map else (Map.add (Var.of_pvar pvar) {loc; classi=N} map) 


let first_var_in_exp exp1 = (*gets the first var in an exp*)
  let vars_sequence = Var.get_all_vars_in_exp exp1 in 
  Sequence.nth_exn vars_sequence 0 

let already_in_domain exp_e1 ident_e2 map =
  let var_e1 = first_var_in_exp exp_e1 in 
  let var_e2 = Var.of_id ident_e2 in 
  let e1_exists = Map.mem (var_e1) map in
  let e2_exists = Map.mem (var_e2) map in
  e1_exists || e2_exists 

let separate_art_ts (a,_) =
  a

let is_printstream e_fun = 
  let a = String.split (Exp.to_string e_fun) ~on:'.' in
  let b = List.hd_exn a in
  String.equal b "_fun_void PrintStream"

let assign_logic_array_complex map e1 e2 e11 loc =  
  if (check_if_used_assign map e1) then 
    begin
    let map1 = classi_update_map map e11 U loc in 
    classi_update_map (classi_update_map map1 e1 W loc) e2 U loc
    end
  else map 

let is_object_in_string e_fun =
  let e_fun_string = Procname.to_string e_fun in 
  let list_of_words = String.split e_fun_string ~on:' ' in
  let first_word = List.hd_exn list_of_words in
  String.equal "Object" first_word

let check_update_map_vars var1 var2 map_vars = 
  if ((Var.is_none var1) ||(Var.is_none var2)) then
    map_vars 
  else (
    Map_Vars.mapi (fun _ value -> if(Var.equal var1 value) then var2 else value) map_vars
  )

let is_second_exp_no_vars arg_ts =
  if (Int.equal (List.length arg_ts) 2) then 
  begin
    let first_arg_exp1 = (separate_art_ts(List.nth_exn arg_ts 1)) in
    let first_arg_var_list1 = Var.get_all_vars_in_exp first_arg_exp1 in 
    let sequence_length1 = Sequence.length first_arg_var_list1 in
    if (Int.equal (sequence_length1) 0) then true
    else false
  end
  else false


(**)
let map_vars_key_of_value ret_id map_vars =  (*checks if ret_id is in the values of map_vars. returns the key if true. returns empty var if false*)
  let ret_var = Var.of_id ret_id in 
  let empty_var = Var.of_id (Ident.create_none ()) in 
  Map_Vars.fold (fun key vl var ->
    if (Var.equal ret_var vl) then key
    else var  
  ) map_vars empty_var

let is_irvar var =                     (*checks if the name of the var starts with "irvar" *)
  let exp_of_var = Var.to_exp var in 
  let string_of_exp = Exp.to_string exp_of_var in 
  if ((String.length string_of_exp) >6) then (
    let first_6_chars = String.sub string_of_exp ~pos:2 ~len:5 in 
    String.equal "irvar" first_6_chars
  )
  else false  

let is_value_in_map_vars var1 map_vars =
  let bol = false in 
  Map_Vars.fold (fun _ vl bl -> if (Var.equal var1 vl) then true else bl) map_vars bol


let update_value_in_map var1 var2 map =   
  
  let temp_value = Map.find (var1) map in         

  let old_value = Map.find var2 map in 
  let new_value = DomainData.join temp_value old_value in
  Map.add var2 new_value map 
(**)

let assign_logic_array_helper map map_vars ret_id arg_ts loc= 
    let key_of_map_vars_ret_id = map_vars_key_of_value ret_id map_vars in          (*key corresponding to the ret_id value in map_vars*)
    let first_arg = (separate_art_ts(List.nth_exn arg_ts 0)) in
    if ((List.length arg_ts > 1)) then(
      let second_arg = (separate_art_ts(List.nth_exn arg_ts 1)) in
      if((Exp.is_const first_arg) && (Exp.is_const second_arg) ) then (     (*both variables are constant*)
        map
      )
      else if (Exp.is_const first_arg) then (                             (*second var is constant*)      
        let second_arg_var = Sequence.nth_exn (Var.get_all_vars_in_exp second_arg) 0 in 
        assign_logic_array map key_of_map_vars_ret_id second_arg_var loc
      ) 
      else if (Exp.is_const second_arg) then (                                (*third var is constant*)
        let first_arg_var = Sequence.nth_exn (Var.get_all_vars_in_exp first_arg) 0 in         
        assign_logic_array map key_of_map_vars_ret_id first_arg_var loc
      )
      else (                                                                (*no vars are constant*)
        let first_arg_var = Sequence.nth_exn (Var.get_all_vars_in_exp first_arg) 0 in
        let second_arg_var = Sequence.nth_exn (Var.get_all_vars_in_exp second_arg) 0 in 
        assign_logic_array_complex map key_of_map_vars_ret_id first_arg_var second_arg_var  loc
      )
    )
    else if ((List.length arg_ts > 0) && (not (Exp.is_const first_arg))) then (                             (*logic for int i = example.get(a)*)
      let first_arg_var = Sequence.nth_exn (Var.get_all_vars_in_exp first_arg) 0 in
      assign_logic_array map key_of_map_vars_ret_id first_arg_var loc
    )
    else map 

let is_used var map = 
  let dd = Map.find var map in 
  match dd.classi with
  |DomainData.U -> true
  | _ -> false 


let is_arraylist_add_in_string e_fun =
  let e_fun_string = Procname.to_string e_fun in 
  let list_of_words = String.split e_fun_string ~on:'.' in
  let first_word = List.hd_exn list_of_words in
  String.equal "boolean ArrayList" first_word

module TransferFunctions = struct
  module Domain = Domain
  module CFG = ProcCfg.Backward (ProcCfg.Normal)

  type analysis_data = IntraproceduralAnalysis.t

  let pp_session_name _node fmt = F.pp_print_string fmt "DataUsageCheck"

  let exec_instr (astate : Domain.t) _ cfg_node (instr : Sil.instr) = 
    match instr with 

    | Prune (expp, loc, bol, _) ->
      if (bol) then (                      
        if (has_2_preds cfg_node) then                                                                           
          let map1 = Map.mapi (fun _ value -> DomainData.push (DomainData.pop value)) (filter_prune2 astate.map expp loc) in Domain.change_map astate map1
        else
          let map1 = Map.mapi (fun _ value -> DomainData.pop value) (filter_prune2 astate.map expp loc) in Domain.change_map astate map1
      ) 
      else(                                   
        if (has_2_preds cfg_node) then                                                                            
          let map1 = Map.mapi (fun _ value -> DomainData.push (DomainData.pop value)) astate.map in Domain.change_map astate map1
        else
          let map1 = Map.mapi (fun _ value -> DomainData.pop value) astate.map in Domain.change_map astate map1
      )

    | Load {id; e= Exp.Lvar e; loc} when is_in_hashtbl astate.hash id -> 
      let map0 = check_exp astate.map id loc in 
      let map1 = check_pvar_exists map0 e loc in
      if (Hashtbl.mem astate.hash (Ident.to_string id)) then 
      begin
        let empty_ident = Ident.create_none () in 

        let empty_var = Var.of_id empty_ident in 

        let array1 = Array.create ~len:3 empty_var in 
  
        let array2 = Map.fold (fun key _ aray ->hash_logic_load id e key astate.hash aray) map1 array1  in 

        if (Var.is_none (Array.get array2 2)) then 
          (let map2 = assign_logic_array map1 (Array.get array2 0) (Array.get array2 1) loc in Hashtbl.clear astate.hash ; Domain.change_map astate map2)
        else 
          (let map2 = assign_logic_array_complex map1 (Array.get array2 0) (Array.get array2 1) (Array.get array2 2) loc in Hashtbl.clear astate.hash ; Domain.change_map astate map2)
      end
      else 
        begin
          let init = "_" in
          let first_key = Hashtbl.fold astate.hash ~init:init ~f:(fun ~key ~data start-> if (String.equal data (Ident.to_string id)) then key else start) in 
          Hashtbl.update astate.hash first_key ~f:(fun _ -> (Pvar.to_string e))  ; Domain.change_map astate map1
        end


    | Load {id ; e = Exp.Lindex (e1,e2); loc} ->  (*when a = b[c] *)
      let map0 = check_exp_exists (check_exp_exists astate.map e1 loc) e2 loc in 
      let e1_var = (Sequence.nth_exn (Var.get_all_vars_in_exp e1) 0) in     
      let id_var0 = Var.of_id id in 
      let id_var = (
        if (is_value_in_map_vars id_var0 astate.map_vars) then (
          map_vars_key_of_value id astate.map_vars                   
        )
        else id_var0
      ) in 
      let map1 = (
        if (Exp.is_const e2) then (
          assign_logic_array map0 id_var e1_var loc
        )
        else(
          let e2_var = (Sequence.nth_exn (Var.get_all_vars_in_exp e2) 0) in
          assign_logic_array_complex map0 id_var e1_var e2_var loc
        ) 
      ) in 
      Domain.change_map astate map1

    | Load {id; e; loc} -> 
      let all_vars = Var.get_all_vars_in_exp e in 
      let sequence_length = Sequence.length all_vars in 
      let astate1 = (if (Int.equal (sequence_length) 1) then 
        begin 
          let map_vars_new = check_update_map_vars (Var.of_id id) (Sequence.nth_exn all_vars 0) astate.map_vars in 
           Domain.change_map_vars astate map_vars_new
        end 
        else astate
        ) in 

      let state0 = check_exp astate1.map id loc in 
      let state1 = check_exp_exists state0 e loc in                                                                         (*replaces n$_ values in domain to names of variables*)
      if Map.mem (Var.of_id id) state1 then let map1 = load_helper id e state1 in Domain.change_map astate1 map1
      else let map1 = state1 in Domain.change_map astate1 map1

    | Store {e1= Exp.Lindex (e1,e11); e2 = Exp.Var e2} when not (already_in_domain e1 e2 astate.map)-> 
      if (Exp.is_const e11) then 
      begin 
        Hashtbl.add_exn astate.hash ~key:(Exp.to_string e1) ~data:(Ident.to_string e2) ;astate
      end 
      else 
      begin 
        let e1_modified = String.concat ~sep:";" [""; (Exp.to_string e1)] in   
        Hashtbl.add_exn astate.hash ~key:(Exp.to_string e1) ~data:(Ident.to_string e2) ;
        Hashtbl.add_exn astate.hash ~key:e1_modified ~data:(Exp.to_string e11) ;
        astate 
      end

    | Store {e1= Exp.Lvar e1; e2= Exp.Var e2; loc} when Pvar.is_return e1 ->        
      if ((has_2_preds cfg_node) && (is_statement_node cfg_node)) then 
        let map1 = Map.mapi (fun _ value -> DomainData.push value) (Map.add (Var.of_id e2) {loc; classi=U} astate.map) in Domain.change_map astate map1
      else 
        let map1 = Map.add (Var.of_id e2) {loc; classi=U} astate.map in Domain.change_map astate map1

    | Store {e1= Exp.Lvar e1; e2 = Exp.Var e2; loc} -> (*add &_= n$_ to the map*)       
      let map_vars_new0 = check_update_map_vars (Var.of_pvar e1) (Var.of_id e2) astate.map_vars in 
      let astate0 = Domain.change_map_vars astate map_vars_new0 in  
      let e1_var = Var.of_pvar e1 in 
      let e2_var = Var.of_id e2 in 

      let map_vars_new = 
        (if (is_value_in_map_vars e2_var astate0.map_vars)then (
          astate0.map_vars 
        )
        else Map_Vars.add e1_var e2_var astate0.map_vars) in 

      let astate1 = Domain.change_map_vars astate0 map_vars_new in 
      let map0 = check_exp astate1.map e2 loc in 
      let map1 = check_pvar_exists map0 e1 loc in

      if ((has_2_preds cfg_node) && (is_statement_node cfg_node)) then 
        let map2 = Map.mapi (fun _ value -> DomainData.push value) (update_value_in_map e1_var e2_var map1) in Domain.change_map astate1 map2
      else 
        let map2 = (update_value_in_map e1_var e2_var map1) in Domain.change_map astate1 map2 

    | Store {e1; e2; loc} ->                                             
      let all_vars_e1 = Var.get_all_vars_in_exp e1 in 
      let sequence_length_e1 = Sequence.length all_vars_e1 in
      let all_vars_e2 = Var.get_all_vars_in_exp e2 in 
      let sequence_length_e2 = Sequence.length all_vars_e2 in 
      let astate1 = (if ((Int.equal sequence_length_e1 1)&& (Int.equal sequence_length_e2 1) ) then 
        begin 
          let map_vars_new = check_update_map_vars (Sequence.nth_exn all_vars_e1 0) (Sequence.nth_exn all_vars_e2 0) astate.map_vars in 
           Domain.change_map_vars astate map_vars_new
        end 
        else astate
        ) in 

      let state = check_exp_exists (check_exp_exists astate1.map e1 loc) e2 loc in 

      if ((has_2_preds cfg_node) && (is_statement_node cfg_node)) then 
        let map1 = Map.mapi (fun _ value -> DomainData.push value) (update_assign_e1_e2 state e1 e2 loc) in Domain.change_map astate1 map1
      else 
        let map1 = (update_assign_e1_e2 state e1 e2 loc) in Domain.change_map astate1 map1   

    | Call ((ret_id, _), Const (Const.Cfun e_fun), arg_ts, loc, _) when (is_object_in_string e_fun) ->       
      let map0 = check_exp astate.map ret_id loc in 
      let map1 = List.fold arg_ts ~init:map0 ~f:(fun state_map args -> check_exists_arg_ts state_map args loc ) in
      let key_of_map_vars_ret_id = map_vars_key_of_value ret_id astate.map_vars in          (*key corresponding to the ret_id value in map_vars*)
      let first_arg = (separate_art_ts(List.nth_exn arg_ts 0)) in

      if not (Var.is_none key_of_map_vars_ret_id) then(      (*checks if var is in map_vars*)
        if ((is_irvar key_of_map_vars_ret_id) && (is_used key_of_map_vars_ret_id map1)) then   (*logic for function called inside a prune *)
        (
          let map1 = arg_ts_fold astate.map arg_ts U loc in 
          Domain.change_map astate map1
        )
        else if (is_irvar key_of_map_vars_ret_id) then (           (*logic for example.put*)
          if ((List.length arg_ts > 2)) then(
            let second_arg = (separate_art_ts(List.nth_exn arg_ts 1)) in
            let third_arg = (separate_art_ts(List.nth_exn arg_ts 2)) in
            if((Exp.is_const second_arg) && (Exp.is_const third_arg) ) then (     (*both variables are constant*)
              Domain.change_map astate map1
            )
            else if (Exp.is_const second_arg) then (                             (*second var is constant*)      
              Hashtbl.add_exn astate.hash ~key:(Exp.to_string first_arg) ~data:(Exp.to_string third_arg) ; Domain.change_map astate map1
            ) 
            else if (Exp.is_const third_arg) then (                                (*third var is constant*)
              Hashtbl.add_exn astate.hash ~key:(Exp.to_string first_arg) ~data:(Exp.to_string second_arg) ; Domain.change_map astate map1
            )
            else (                                                                (*no vars are constant*)
              let first_arg_modified = String.concat ~sep:";" [""; (Exp.to_string first_arg)] in   
              Hashtbl.add_exn astate.hash ~key:(Exp.to_string first_arg) ~data:(Exp.to_string second_arg) ;
              Hashtbl.add_exn astate.hash ~key:first_arg_modified ~data:(Exp.to_string third_arg) ; Domain.change_map astate map1
            )
          )
          else if ((List.length arg_ts>1)&& (not (Exp.is_const (separate_art_ts(List.nth_exn arg_ts 1))))) then (   (*only has one var*)
            let second_arg = (separate_art_ts(List.nth_exn arg_ts 1)) in
            Hashtbl.add_exn astate.hash ~key:(Exp.to_string first_arg) ~data:(Exp.to_string second_arg) ; Domain.change_map astate map1
          )
          else (Domain.change_map astate map1)
        )
        else if ((List.length arg_ts > 0) && (not (Exp.is_const first_arg))) then (                             (*logic for int i = example.get(a)*)
          let map2 = assign_logic_array_helper map1 astate.map_vars ret_id arg_ts loc in Domain.change_map astate map2      (*logic that supports 2 variables*)
        ) 
        else (Domain.change_map astate map1)
      )  
      else (Domain.change_map astate map1)


    | Call ((ret_id, _), Const (Const.Cfun e_fun), arg_ts, loc, _) when (is_arraylist_add_in_string e_fun)->
      let map0 = check_exp astate.map ret_id loc in 
      let map1 = List.fold arg_ts ~init:map0 ~f:(fun state_map args -> check_exists_arg_ts state_map args loc ) in
      let key_of_map_vars_ret_id = map_vars_key_of_value ret_id astate.map_vars in          (*key corresponding to the ret_id value in map_vars*)
      let first_arg = (separate_art_ts(List.nth_exn arg_ts 0)) in

      if not (Var.is_none key_of_map_vars_ret_id) then(     (*checks if var is in map_vars*)
        if ((is_irvar key_of_map_vars_ret_id) && (is_used key_of_map_vars_ret_id map1)) then   (*logic for function called inside a prune *)
        (
          let map1 = arg_ts_fold astate.map arg_ts U loc in 
          Domain.change_map astate map1
        )
        else if (is_irvar key_of_map_vars_ret_id) then (           (*logic for example.put*)
          if ((List.length arg_ts > 2)) then(
            let second_arg = (separate_art_ts(List.nth_exn arg_ts 1)) in
            let third_arg = (separate_art_ts(List.nth_exn arg_ts 2)) in
            if((Exp.is_const second_arg) && (Exp.is_const third_arg) ) then (     (*both variables are constant*)
              Domain.change_map astate map1
            )
            else if (Exp.is_const second_arg) then (                             (*second var is constant*)      
              Hashtbl.add_exn astate.hash ~key:(Exp.to_string first_arg) ~data:(Exp.to_string third_arg) ; Domain.change_map astate map1
            ) 
            else if (Exp.is_const third_arg) then (                                (*third var is constant*)
              Hashtbl.add_exn astate.hash ~key:(Exp.to_string first_arg) ~data:(Exp.to_string second_arg) ; Domain.change_map astate map1
            )
            else (                                                                (*no vars are constant*)
              let first_arg_modified = String.concat ~sep:";" [""; (Exp.to_string first_arg)] in   
              Hashtbl.add_exn astate.hash ~key:(Exp.to_string first_arg) ~data:(Exp.to_string second_arg) ;
              Hashtbl.add_exn astate.hash ~key:first_arg_modified ~data:(Exp.to_string third_arg) ; Domain.change_map astate map1
            )
          )
          else if ((List.length arg_ts>1)&& (not (Exp.is_const (separate_art_ts(List.nth_exn arg_ts 1))))) then (   (*only has one var*)
            let second_arg = (separate_art_ts(List.nth_exn arg_ts 1)) in
            Hashtbl.add_exn astate.hash ~key:(Exp.to_string first_arg) ~data:(Exp.to_string second_arg) ; Domain.change_map astate map1
          )
          else (Domain.change_map astate map1)
        )
        else (Domain.change_map astate map1)
      )  
      else (Domain.change_map astate map1)

    | Call ((_, _), e_fun, arg_ts, loc, _) when (is_printstream e_fun) ->  (*turns a variable to used if printed*) 
      let first_arg = (separate_art_ts(List.nth_exn arg_ts 1)) in 
      let map1 = Sequence.fold (Var.get_all_vars_in_exp first_arg) ~init:astate.map ~f:(fun map a -> Map.add (a) {loc; classi=U} map) in 
      if ((has_2_preds cfg_node) && (is_statement_node cfg_node)) then 
        let map2 = Map.mapi (fun _ value -> DomainData.push value) map1 in Domain.change_map astate map2
      else 
        Domain.change_map astate map1
   
    | Call ((ret_id, _), _, arg_ts, loc, _) ->                                                           
      let astate1 = (
        if ((Int.equal (List.length arg_ts) 1) || (is_second_exp_no_vars arg_ts)) then 
        begin 
          let first_arg_exp = (separate_art_ts(List.nth_exn arg_ts 0)) in
          let first_arg_var_list = Var.get_all_vars_in_exp first_arg_exp in 
          let sequence_length = Sequence.length first_arg_var_list in
          if (Int.equal sequence_length 1) then 
            begin 
              let first_arg_var = Sequence.nth_exn first_arg_var_list 0 in
              let map_vars_new = check_update_map_vars (Var.of_id ret_id) (first_arg_var) astate.map_vars in 
              Domain.change_map_vars astate map_vars_new
            end
          else astate
        end
        else astate
      ) in
      let map1 = update_exps_call astate1.map ret_id arg_ts loc in Domain.change_map astate1 map1
    | _ -> astate

end 

let list_var_class domain = 
  let ls1 = Map.empty in 
  Map.fold (fun key vl ls -> if (phys_equal vl.classi DomainData.N) then (Map.add key vl ls) else ls) domain ls1 


let launch_final_error proc_desc err_log domain =
  let dom0 = remove_signs_from_domain domain in  
  let dom1 = list_var_class dom0 in  
  Map.iter (fun key vl -> let message  = F.asprintf "Variable not used: %a" Var.pp key in Reporting.log_issue proc_desc err_log ~loc:(vl.loc) DataUsageCheck IssueType.variable_unused message) dom1  

module Analyzer = AbstractInterpreter.MakeWTO (TransferFunctions)

let checker ({IntraproceduralAnalysis.proc_desc; err_log} as analysis_data) =
  let all_params = Procdesc.get_pvar_formals proc_desc in
  let initial_domain = {Domain.map= Map.empty; Domain.hash = Hashtbl.create (module String); Domain.map_vars = Map_Vars.empty} in 
  let initial_map = 
    List.fold_left ~init:initial_domain.map
      ~f:(fun state (pvar, _) -> classi_update_map state (Var.of_pvar pvar) N Location.dummy)
      all_params
  in
  let initial = Domain.change_map initial_domain initial_map in 
  match Analyzer.compute_post analysis_data ~initial proc_desc with
    | Some domain ->
        launch_final_error proc_desc err_log domain.map
    | None ->
        () 

