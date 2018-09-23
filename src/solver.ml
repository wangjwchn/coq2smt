open Plugin_utils

module type Solver =
sig
  val solve : debug:bool -> verbose:bool -> unit Proofview.tactic
end

module type Instance =
sig
  type instance

  val parse_conclusion : Environ.env -> _ Sigma.t ->
    Term.constr -> instance

  val parse_hypothesis : Environ.env -> _ Sigma.t ->
    Names.Id.t -> Term.constr -> instance -> instance

  val write_instance : ?pretty:bool -> Format.formatter -> instance -> unit

  val get_variable : string -> instance -> Term.constr

  (* Returning [None] means the conclusion *)
  val get_hypothesis : string -> instance -> Names.identifier option

end

module ParseOnlyProp (P : Instance) :
  (Instance with type instance = P.instance) =
struct
  type instance = P.instance

  let is_a_prop env evm t =
    let (_,ty) = Typing.type_of env (Sigma.to_evar_map evm) t in
    Term.eq_constr ty Term.mkProp

  let parse_conclusion env evm c =
    if is_a_prop env evm c then
      P.parse_conclusion env evm c
    else
      raise (Failure "Conclusion is not a proposition")

  let parse_hypothesis env evm name typ i =
    if is_a_prop env evm typ then
      P.parse_hypothesis env evm name typ i
    else i

  let write_instance = P.write_instance
  let get_variable = P.get_variable
  let get_hypothesis = P.get_hypothesis
end

type smt_result =
    Sat of (Term.constr * string) list
  | Unsat of (bool * Names.identifier list) option (* the core *)
  | Unknown

module type Exec =
sig
  type instance

  val execute : debug:((unit -> Pp.std_ppcmds) -> unit) -> instance -> smt_result
end

module Make
    (Inst : Instance)
    (Exec : Exec with type instance = Inst.instance) : Solver =
struct
  open Inst
  open Exec

  let parse_instance env evm hyps concl =
    let res = Inst.parse_conclusion env evm concl in
    List.fold_left (fun acc -> function
        | Context.Named.Declaration.LocalAssum (name, typ) ->
          Inst.parse_hypothesis env evm name typ acc
        | Context.Named.Declaration.LocalDef (name, _, typ) ->
          Inst.parse_hypothesis env evm name typ acc) res hyps

  module Std = Coqstd.Std
      (struct
        let contrib_name = "smt-check-real-instance"
      end)

  let false_type : Term.constr Lazy.t =
    Std.resolve_symbol ["Coq";"Init";"Logic"] "False"

  let pr_model env evm =
    Pp.pr_vertical_list
      (fun (var,value) ->
         Pp.(Printer.pr_constr_env env (Sigma.to_evar_map evm) var ++
             spc () ++ str "=" ++ spc () ++ str value))

  let solve ~debug ~verbose =
    let debug =
      if debug then (fun x -> Feedback.msg_debug (x ()))
      else fun _ -> ()
    in
    Proofview.Goal.nf_enter { Proofview.Goal.enter = fun gl ->
        let goal = Proofview.Goal.concl gl in
        let hyps = Proofview.Goal.hyps gl in
        let env  = Proofview.Goal.env gl in
        let evm  = Proofview.Goal.sigma gl in

        try
          let inst = parse_instance env evm hyps goal in
          match Exec.execute debug inst with
            Sat model when verbose ->
            let msg =
              Pp.(   str "solver failed to solve the goal."
                  ++ fnl ()
                  ++ pr_model env evm model)
            in
            Tacticals.New.tclFAIL 0 msg
          | Sat _ ->
            Tacticals.New.tclFAIL 0 Pp.(str "Satisfiable")
          | Unsat (Some (need_concl, core)) ->
            let open Proofview.Monad in
            (if not need_concl
             then Tactics.elim_type (Lazy.force false_type)
             else Proofview.tclUNIT ()) >>
            (Tactics.keep core)
          | Unsat None ->
            Tacticals.New.tclIDTAC
          | Unknown ->
            Tacticals.New.tclFAIL 0 Pp.(str "solver returned unkown")
        with
          Failure msg ->
          Tacticals.New.tclFAIL 0 Pp.(str "failed to parse the goal")
    }

end


module RealInstance : Instance =
struct

  module Std = Coqstd.Std
      (struct
        let contrib_name = "smt-check-instance"
      end)

  let logic_pkg     = ["Coq";"Init";"Logic"]
  let binnums_pkg   = ["Coq";"Numbers";"BinNums"]
  let z_pkg         = ["Coq";"ZArith";"BinInt";"Z"]
  let integers_pkg  = ["SMTC";"Integers"]
  let int32_pkg     = ["SMTC";"Integers";"Int"]
  let int64_pkg     = ["SMTC";"Integers";"Int64"]
  let int16_pkg     = ["SMTC";"Integers";"Int16"]
  let int8_pkg      = ["SMTC";"Integers";"Byte"]
  let datatypes_pkg = ["Coq";"Init";"Datatypes"]
  let nat_pkg       = ["Coq";"Init";"Nat"]
  let peano_pkg     = ["Coq";"Init";"Peano"]
  let r_pkg         = ["Coq";"Reals";"Rdefinitions"]

  let c_Z = Std.resolve_symbol binnums_pkg "Z"
  let c_xH = Std.resolve_symbol binnums_pkg "xH"
  let c_xO = Std.resolve_symbol binnums_pkg "xO"
  let c_xI = Std.resolve_symbol binnums_pkg "xI"
  let c_Z0 = Std.resolve_symbol binnums_pkg "Z0"
  let c_Zpos = Std.resolve_symbol binnums_pkg "Zpos"
  let c_Zneg = Std.resolve_symbol binnums_pkg "Zneg"

  let c_Zadd = Std.resolve_symbol z_pkg "add"
  let c_Zsub = Std.resolve_symbol z_pkg "sub"
  let c_Zmul = Std.resolve_symbol z_pkg "mul"
  let c_Zdiv = Std.resolve_symbol z_pkg "div"

  let c_Zlt = Std.resolve_symbol z_pkg "lt"
  let c_Zle = Std.resolve_symbol z_pkg "le"
  let c_Zge = Std.resolve_symbol z_pkg "ge"
  let c_Zgt = Std.resolve_symbol z_pkg "gt"
  let c_Zeq = Std.resolve_symbol logic_pkg "eq"
  let c_Zto_nat = Std.resolve_symbol z_pkg "to_nat"
  let c_Zof_nat = Std.resolve_symbol z_pkg "of_nat"
  let c_Zltb = Std.resolve_symbol z_pkg "ltb"
  let c_Zleb = Std.resolve_symbol z_pkg "leb"
  let c_Zgeb = Std.resolve_symbol z_pkg "geb"
  let c_Zgtb = Std.resolve_symbol z_pkg "gtb"
  let c_Zeqb = Std.resolve_symbol z_pkg "eqb"
  let c_Zshiftl = Std.resolve_symbol z_pkg "shiftl"
  let c_Zshiftr = Std.resolve_symbol z_pkg "shiftr"
  let c_Zpow = Std.resolve_symbol z_pkg "pow"
  let c_Zmodulo = Std.resolve_symbol z_pkg "modulo"
  let c_Zrem = Std.resolve_symbol z_pkg "rem"

  let c_and = Std.resolve_symbol logic_pkg "and"
  let c_or = Std.resolve_symbol logic_pkg "or"
  let c_True = Std.resolve_symbol logic_pkg "True"
  let c_False = Std.resolve_symbol logic_pkg "False"
  let c_Not = Std.resolve_symbol logic_pkg "not"
  let c_Prop = Term.mkProp

  let c_int8 = Std.resolve_symbol integers_pkg "int8"
  let c_int8_is = Std.resolve_symbol logic_pkg "eq"
  let c_int8_wordsize = Std.resolve_symbol int8_pkg "wordsize"
  let c_int8_zwordsize = Std.resolve_symbol int8_pkg "zwordsize"
  let c_int8_iwordsize = Std.resolve_symbol int8_pkg "iwordsize"
  let c_int8_modulus = Std.resolve_symbol int8_pkg "modulus"
  let c_int8_half_modulus = Std.resolve_symbol int8_pkg "half_modulus"
  let c_int8_max_unsigned = Std.resolve_symbol int8_pkg "max_unsigned"
  let c_int8_max_signed = Std.resolve_symbol int8_pkg "max_signed"
  let c_int8_min_signed = Std.resolve_symbol int8_pkg "min_signed"
  let c_int8_unsigned = Std.resolve_symbol int8_pkg "unsigned"
  let c_int8_signed = Std.resolve_symbol int8_pkg "signed"
  let c_int8_repr = Std.resolve_symbol int8_pkg "repr"
  let c_int8_zero = Std.resolve_symbol int8_pkg "zero"
  let c_int8_one = Std.resolve_symbol int8_pkg "one"
  let c_int8_eq = Std.resolve_symbol int8_pkg "eq"
  let c_int8_lt = Std.resolve_symbol int8_pkg "lt"
  let c_int8_ltu = Std.resolve_symbol int8_pkg "ltu"
  let c_int8_neg = Std.resolve_symbol int8_pkg "neg"
  let c_int8_add = Std.resolve_symbol int8_pkg "add"
  let c_int8_sub = Std.resolve_symbol int8_pkg "sub"
  let c_int8_mul = Std.resolve_symbol int8_pkg "mul"
  let c_int8_divs = Std.resolve_symbol int8_pkg "divs"
  let c_int8_mods = Std.resolve_symbol int8_pkg "mods"
  let c_int8_divu = Std.resolve_symbol int8_pkg "divu"
  let c_int8_modu = Std.resolve_symbol int8_pkg "modu"
  let c_int8_and = Std.resolve_symbol int8_pkg "and"
  let c_int8_or = Std.resolve_symbol int8_pkg "or"
  let c_int8_xor = Std.resolve_symbol int8_pkg "xor"
  let c_int8_not = Std.resolve_symbol int8_pkg "not"
  let c_int8_shl = Std.resolve_symbol int8_pkg "shl"
  let c_int8_shru = Std.resolve_symbol int8_pkg "shru"
  let c_int8_shr = Std.resolve_symbol int8_pkg "shr"

  let c_int16 = Std.resolve_symbol integers_pkg "int16"
  let c_int16_is = Std.resolve_symbol logic_pkg "eq"
  let c_int16_wordsize = Std.resolve_symbol int16_pkg "wordsize"
  let c_int16_zwordsize = Std.resolve_symbol int16_pkg "zwordsize"
  let c_int16_iwordsize = Std.resolve_symbol int16_pkg "iwordsize"
  let c_int16_modulus = Std.resolve_symbol int16_pkg "modulus"
  let c_int16_half_modulus = Std.resolve_symbol int16_pkg "half_modulus"
  let c_int16_max_unsigned = Std.resolve_symbol int16_pkg "max_unsigned"
  let c_int16_max_signed = Std.resolve_symbol int16_pkg "max_signed"
  let c_int16_min_signed = Std.resolve_symbol int16_pkg "min_signed"
  let c_int16_unsigned = Std.resolve_symbol int16_pkg "unsigned"
  let c_int16_signed = Std.resolve_symbol int16_pkg "signed"
  let c_int16_repr = Std.resolve_symbol int16_pkg "repr"
  let c_int16_zero = Std.resolve_symbol int16_pkg "zero"
  let c_int16_one = Std.resolve_symbol int16_pkg "one"
  let c_int16_eq = Std.resolve_symbol int16_pkg "eq"
  let c_int16_lt = Std.resolve_symbol int16_pkg "lt"
  let c_int16_ltu = Std.resolve_symbol int16_pkg "ltu"
  let c_int16_neg = Std.resolve_symbol int16_pkg "neg"
  let c_int16_add = Std.resolve_symbol int16_pkg "add"
  let c_int16_sub = Std.resolve_symbol int16_pkg "sub"
  let c_int16_mul = Std.resolve_symbol int16_pkg "mul"
  let c_int16_divs = Std.resolve_symbol int16_pkg "divs"
  let c_int16_mods = Std.resolve_symbol int16_pkg "mods"
  let c_int16_divu = Std.resolve_symbol int16_pkg "divu"
  let c_int16_modu = Std.resolve_symbol int16_pkg "modu"
  let c_int16_and = Std.resolve_symbol int16_pkg "and"
  let c_int16_or = Std.resolve_symbol int16_pkg "or"
  let c_int16_xor = Std.resolve_symbol int16_pkg "xor"
  let c_int16_not = Std.resolve_symbol int16_pkg "not"
  let c_int16_shl = Std.resolve_symbol int16_pkg "shl"
  let c_int16_shru = Std.resolve_symbol int16_pkg "shru"
  let c_int16_shr = Std.resolve_symbol int16_pkg "shr"

  let c_int32 = Std.resolve_symbol integers_pkg "int"
  let c_int32_is = Std.resolve_symbol logic_pkg "eq"
  let c_int32_wordsize = Std.resolve_symbol int32_pkg "wordsize"
  let c_int32_zwordsize = Std.resolve_symbol int32_pkg "zwordsize"
  let c_int32_iwordsize = Std.resolve_symbol int32_pkg "iwordsize"
  let c_int32_modulus = Std.resolve_symbol int32_pkg "modulus"
  let c_int32_half_modulus = Std.resolve_symbol int32_pkg "half_modulus"
  let c_int32_max_unsigned = Std.resolve_symbol int32_pkg "max_unsigned"
  let c_int32_max_signed = Std.resolve_symbol int32_pkg "max_signed"
  let c_int32_min_signed = Std.resolve_symbol int32_pkg "min_signed"
  let c_int32_unsigned = Std.resolve_symbol int32_pkg "unsigned"
  let c_int32_signed = Std.resolve_symbol int32_pkg "signed"
  let c_int32_repr = Std.resolve_symbol int32_pkg "repr"
  let c_int32_zero = Std.resolve_symbol int32_pkg "zero"
  let c_int32_one = Std.resolve_symbol int32_pkg "one"
  let c_int32_eq = Std.resolve_symbol int32_pkg "eq"
  let c_int32_lt = Std.resolve_symbol int32_pkg "lt"
  let c_int32_ltu = Std.resolve_symbol int32_pkg "ltu"
  let c_int32_neg = Std.resolve_symbol int32_pkg "neg"
  let c_int32_add = Std.resolve_symbol int32_pkg "add"
  let c_int32_sub = Std.resolve_symbol int32_pkg "sub"
  let c_int32_mul = Std.resolve_symbol int32_pkg "mul"
  let c_int32_divs = Std.resolve_symbol int32_pkg "divs"
  let c_int32_mods = Std.resolve_symbol int32_pkg "mods"
  let c_int32_divu = Std.resolve_symbol int32_pkg "divu"
  let c_int32_modu = Std.resolve_symbol int32_pkg "modu"
  let c_int32_and = Std.resolve_symbol int32_pkg "and"
  let c_int32_or = Std.resolve_symbol int32_pkg "or"
  let c_int32_xor = Std.resolve_symbol int32_pkg "xor"
  let c_int32_not = Std.resolve_symbol int32_pkg "not"
  let c_int32_shl = Std.resolve_symbol int32_pkg "shl"
  let c_int32_shru = Std.resolve_symbol int32_pkg "shru"
  let c_int32_shr = Std.resolve_symbol int32_pkg "shr"

  let c_int64 = Std.resolve_symbol integers_pkg "int64"
  let c_int64_is = Std.resolve_symbol logic_pkg "eq"
  let c_int64_wordsize = Std.resolve_symbol int64_pkg "wordsize"
  let c_int64_zwordsize = Std.resolve_symbol int64_pkg "zwordsize"
  let c_int64_iwordsize = Std.resolve_symbol int64_pkg "iwordsize"
  let c_int64_modulus = Std.resolve_symbol int64_pkg "modulus"
  let c_int64_half_modulus = Std.resolve_symbol int64_pkg "half_modulus"
  let c_int64_max_unsigned = Std.resolve_symbol int64_pkg "max_unsigned"
  let c_int64_max_signed = Std.resolve_symbol int64_pkg "max_signed"
  let c_int64_min_signed = Std.resolve_symbol int64_pkg "min_signed"
  let c_int64_unsigned = Std.resolve_symbol int64_pkg "unsigned"
  let c_int64_signed = Std.resolve_symbol int64_pkg "signed"
  let c_int64_repr = Std.resolve_symbol int64_pkg "repr"
  let c_int64_zero = Std.resolve_symbol int64_pkg "zero"
  let c_int64_one = Std.resolve_symbol int64_pkg "one"
  let c_int64_eq = Std.resolve_symbol int64_pkg "eq"
  let c_int64_lt = Std.resolve_symbol int64_pkg "lt"
  let c_int64_ltu = Std.resolve_symbol int64_pkg "ltu"
  let c_int64_neg = Std.resolve_symbol int64_pkg "neg"
  let c_int64_add = Std.resolve_symbol int64_pkg "add"
  let c_int64_sub = Std.resolve_symbol int64_pkg "sub"
  let c_int64_mul = Std.resolve_symbol int64_pkg "mul"
  let c_int64_divs = Std.resolve_symbol int64_pkg "divs"
  let c_int64_mods = Std.resolve_symbol int64_pkg "mods"
  let c_int64_divu = Std.resolve_symbol int64_pkg "divu"
  let c_int64_modu = Std.resolve_symbol int64_pkg "modu"
  let c_int64_and = Std.resolve_symbol int64_pkg "and"
  let c_int64_or = Std.resolve_symbol int64_pkg "or"
  let c_int64_xor = Std.resolve_symbol int64_pkg "xor"
  let c_int64_not = Std.resolve_symbol int64_pkg "not"
  let c_int64_shl = Std.resolve_symbol int64_pkg "shl"
  let c_int64_shru = Std.resolve_symbol int64_pkg "shru"
  let c_int64_shr = Std.resolve_symbol int64_pkg "shr"

  let c_bool = Std.resolve_symbol datatypes_pkg "bool"
  let c_true = Std.resolve_symbol datatypes_pkg "true"
  let c_false = Std.resolve_symbol datatypes_pkg "false"
  let c_beq = Std.resolve_symbol logic_pkg "eq"

  let c_nat = Std.resolve_symbol datatypes_pkg "nat"
  let c_nat_S = Std.resolve_symbol datatypes_pkg "S"
  let c_nat_O = Std.resolve_symbol datatypes_pkg "O"
  let c_nat_eq = Std.resolve_symbol logic_pkg "eq"
  let c_nat_add = Std.resolve_symbol nat_pkg "add"
  let c_nat_sub = Std.resolve_symbol nat_pkg "sub"
  let c_nat_mul = Std.resolve_symbol nat_pkg "mul"
  let c_nat_lt = Std.resolve_symbol peano_pkg "lt"
  let c_nat_le = Std.resolve_symbol peano_pkg "le"
  let c_nat_gt = Std.resolve_symbol peano_pkg "gt"
  let c_nat_ge = Std.resolve_symbol peano_pkg "ge"

  let c_R = Std.resolve_symbol r_pkg "R"
  let c_0 = Std.resolve_symbol r_pkg "R0"
  let c_1 = Std.resolve_symbol r_pkg "R1"
  let c_Rplus = Std.resolve_symbol r_pkg "Rplus"
  let c_Rminus = Std.resolve_symbol r_pkg "Rminus"
  let c_Rdiv = Std.resolve_symbol r_pkg "Rdiv"
  let c_Rmult = Std.resolve_symbol r_pkg "Rmult"
  let c_Ropp = Std.resolve_symbol r_pkg "Ropp"
  let c_Rinv = Std.resolve_symbol r_pkg "Rinv"

  let c_Rlt = Std.resolve_symbol r_pkg "Rlt"
  let c_Rle = Std.resolve_symbol r_pkg "Rle"
  let c_Rgt = Std.resolve_symbol r_pkg "Rgt"
  let c_Rge = Std.resolve_symbol r_pkg "Rge"
  let c_Req = Std.resolve_symbol logic_pkg "eq"

  module ConstrOrd =
  struct
    type t = Term.constr
    let compare = Term.constr_ord
  end

  module Cmap = Map.Make (ConstrOrd)

  type all_type = Prop | Z | I8 | I16 | I32 | I64 |Bool | Nat | R | List of all_type

  type r_expr =
      RConst of float
    | Rplus of r_expr * r_expr
    | Rminus of r_expr * r_expr
    | Rmult of r_expr * r_expr
    | Rdiv of r_expr * r_expr
    | Ropp of r_expr
    | Rinv of r_expr
    | Ropaque of int

  and int8_expr =
      I8opaque of int
    | I8add of int8_expr * int8_expr
    | I8sub of int8_expr * int8_expr
    | I8mul of int8_expr * int8_expr
    | I8divs of int8_expr * int8_expr
    | I8mods of int8_expr * int8_expr
    | I8divu of int8_expr * int8_expr
    | I8modu of int8_expr * int8_expr
    | I8and of int8_expr * int8_expr
    | I8or of int8_expr * int8_expr
    | I8xor of int8_expr * int8_expr
    | I8not of int8_expr 
    | I8shl of int8_expr * int8_expr
    | I8shru of int8_expr * int8_expr
    | I8shr of int8_expr * int8_expr
    | I8repr of z_expr

  and int16_expr =
      I16opaque of int
    | I16add of int16_expr * int16_expr
    | I16sub of int16_expr * int16_expr
    | I16mul of int16_expr * int16_expr
    | I16divs of int16_expr * int16_expr
    | I16mods of int16_expr * int16_expr
    | I16divu of int16_expr * int16_expr
    | I16modu of int16_expr * int16_expr
    | I16and of int16_expr * int16_expr
    | I16or of int16_expr * int16_expr
    | I16xor of int16_expr * int16_expr
    | I16not of int16_expr
    | I16shl of int16_expr * int16_expr
    | I16shru of int16_expr * int16_expr
    | I16shr of int16_expr * int16_expr
    | I16repr of z_expr


  and int32_expr =
      I32opaque of int
    | I32add of int32_expr * int32_expr
    | I32sub of int32_expr * int32_expr
    | I32mul of int32_expr * int32_expr
    | I32divs of int32_expr * int32_expr
    | I32mods of int32_expr * int32_expr
    | I32divu of int32_expr * int32_expr
    | I32modu of int32_expr * int32_expr
    | I32and of int32_expr * int32_expr
    | I32or of int32_expr * int32_expr
    | I32xor of int32_expr * int32_expr
    | I32not of int32_expr
    | I32shl of int32_expr * int32_expr
    | I32shru of int32_expr * int32_expr
    | I32shr of int32_expr * int32_expr
    | I32repr of z_expr

  and int64_expr =
      I64opaque of int
    | I64add of int64_expr * int64_expr
    | I64sub of int64_expr * int64_expr
    | I64mul of int64_expr * int64_expr
    | I64divs of int64_expr * int64_expr
    | I64mods of int64_expr * int64_expr
    | I64divu of int64_expr * int64_expr
    | I64modu of int64_expr * int64_expr
    | I64and of int64_expr * int64_expr
    | I64or of int64_expr * int64_expr
    | I64xor of int64_expr * int64_expr
    | I64not of int64_expr
    | I64shl of int64_expr * int64_expr
    | I64shru of int64_expr * int64_expr
    | I64shr of int64_expr * int64_expr
    | I64repr of z_expr

  and z_expr =
      Zp2 of int
    | Zp2m1 of int
    | ZxO of z_expr
    | ZxI of z_expr
    | ZofN of nat_expr
    | Zneg of z_expr
    | Zadd of z_expr * z_expr
    | Zsub of z_expr * z_expr
    | Zmul of z_expr * z_expr
    | Zdiv of z_expr * z_expr
    | Zshiftl of z_expr * z_expr
    | Zshiftr of z_expr * z_expr
    | Zpow of z_expr * z_expr
    | Zmodulo of z_expr * z_expr
    | Zrem of z_expr * z_expr
    | I8signed of int8_expr
    | I8unsigned of int8_expr
    | I16signed of int16_expr
    | I16unsigned of int16_expr
    | I32signed of int32_expr
    | I32unsigned of int32_expr
    | I64signed of int64_expr
    | I64unsigned of int64_expr
    | Zopaque of int


  and bool_expr = 
      Btrue
    | Bfalse
    | I8lt of int8_expr * int8_expr
    | I8ltu of int8_expr * int8_expr
    | I8eq of int8_expr * int8_expr
    | I16lt of int16_expr * int16_expr
    | I16ltu of int16_expr * int16_expr
    | I16eq of int16_expr * int16_expr
    | I32lt of int32_expr * int32_expr
    | I32ltu of int32_expr * int32_expr
    | I32eq of int32_expr * int32_expr
    | I64lt of int64_expr * int64_expr
    | I64ltu of int64_expr * int64_expr
    | I64eq of int64_expr * int64_expr
    | Zeqb of z_expr * z_expr
    | Zleb of z_expr * z_expr
    | Zltb of z_expr * z_expr
    | Zgeb of z_expr * z_expr
    | Zgtb of z_expr * z_expr
    | Bopaque of int

  and nat_expr = 
      Nadd of nat_expr * nat_expr
    | Nsub of nat_expr * nat_expr
    | Nmul of nat_expr * nat_expr
    | NofZ of z_expr
    | NSucc of nat_expr
    | Nopaque of int

  type prop_expr =
    | Ptrue
    | Pfalse
    | Zlt of z_expr * z_expr
    | Zle of z_expr * z_expr
    | Zgt of z_expr * z_expr
    | Zge of z_expr * z_expr
    | Zeq of z_expr * z_expr
    | Pand of prop_expr * prop_expr
    | Por of prop_expr * prop_expr
    | Pimpl of prop_expr * prop_expr
    | Pnot of prop_expr
    | Popaque of int
    | I8is of int8_expr * int8_expr
    | I16is of int16_expr * int16_expr
    | I32is of int32_expr * int32_expr
    | I64is of int64_expr * int64_expr
    | Beq of bool_expr * bool_expr
    | Nlt of nat_expr * nat_expr
    | Nle of nat_expr * nat_expr
    | Ngt of nat_expr * nat_expr
    | Nge of nat_expr * nat_expr
    | Neq of nat_expr * nat_expr
    | Rlt of r_expr * r_expr
    | Rle of r_expr * r_expr
    | Rgt of r_expr * r_expr
    | Rge of r_expr * r_expr
    | Req of r_expr * r_expr


  type instance =
    { vars : (int * all_type) Cmap.t
    ; assertions : (Names.identifier * prop_expr) list
    ; concl : prop_expr }

  let get_opaque x t i =
    try fst (Cmap.find x i), i
    with
      Not_found ->
      let nxt = Cmap.cardinal i in
      nxt, (Cmap.add x (nxt, t) i)


  let parse_uop recur constr op =
    (Term_match.apps (Term_match.Glob constr)
		     [Term_match.get 0],
     fun tbl bindings ->
     let (res,tbl) = recur tbl (Hashtbl.find bindings 0) in
     (op res, tbl))

  let parse_bop recur constr op =
    (Term_match.apps (Term_match.Glob constr)
		     [Term_match.get 0;Term_match.get 1],
     fun tbl bindings ->
     let (l,tbl) = recur tbl (Hashtbl.find bindings 0) in
     let (r,tbl) = recur tbl (Hashtbl.find bindings 1) in
     (op l r, tbl))

  let rec parse_r_expr tbl =
    Term_match.matches tbl
      [ (Term_match.Glob c_0, fun tbl _ -> (RConst 0., tbl))
      ; (Term_match.Glob c_1, fun tbl _ -> (RConst 1., tbl))
      ; parse_bop parse_r_expr c_Rplus (fun a b -> Rplus (a,b))
      ; parse_bop parse_r_expr c_Rminus (fun a b -> Rminus (a,b))
      ; parse_bop parse_r_expr c_Rmult (fun a b -> Rmult (a,b))
      ; parse_bop parse_r_expr c_Rdiv (fun a b -> Rdiv (a,b))
      ; parse_uop parse_r_expr c_Ropp (fun a -> Ropp a)
      ; parse_uop parse_r_expr c_Rinv (fun a -> Rinv a)
      ; (Term_match.get 0,
	 fun tbl binders ->
	 let trm = Hashtbl.find binders 0 in
	 try
	   (Ropaque (fst (Cmap.find trm tbl)), tbl)
	 with
	   Not_found ->
	   let nxt = Cmap.cardinal tbl in
	   (Ropaque nxt, Cmap.add trm (nxt,R) tbl))
      ]

  and parse_int8_expr tbl =
    Term_match.matches tbl
      [ (Term_match.Glob c_int8_zero, fun tbl _ -> (I8repr (Zp2m1 0), tbl))
      ; (Term_match.Glob c_int8_one, fun tbl _ -> (I8repr (Zp2 0), tbl))
      ; (Term_match.Glob c_int8_iwordsize, fun tbl _ -> (I8repr (Zp2 3), tbl))
      ; parse_bop parse_int8_expr c_int8_add (fun a b -> I8add (a,b))
      ; parse_bop parse_int8_expr c_int8_sub (fun a b -> I8sub (a,b))
      ; parse_bop parse_int8_expr c_int8_mul (fun a b -> I8mul (a,b))
      ; parse_bop parse_int8_expr c_int8_divu (fun a b -> I8divu (a,b))
      ; parse_bop parse_int8_expr c_int8_modu (fun a b -> I8modu (a,b))
      ; parse_bop parse_int8_expr c_int8_divs (fun a b -> I8divs (a,b))
      ; parse_bop parse_int8_expr c_int8_mods (fun a b -> I8mods (a,b))
      ; parse_uop parse_z_expr c_int8_repr (fun a -> I8repr a)
      ; parse_uop parse_int8_expr c_int8_not (fun a -> I8not a)
      ; parse_bop parse_int8_expr c_int8_and (fun a b -> I8and (a,b))
      ; parse_bop parse_int8_expr c_int8_or (fun a b -> I8or (a,b))
      ; parse_bop parse_int8_expr c_int8_xor (fun a b -> I8xor (a,b))
      ; parse_bop parse_int8_expr c_int8_shl (fun a b -> I8shl (a,b))
      ; parse_bop parse_int8_expr c_int8_shru (fun a b -> I8shru (a,b))
      ; parse_bop parse_int8_expr c_int8_shr (fun a b -> I8shr (a,b))
      ; (Term_match.get 0,
         fun tbl binders ->
         let trm = Hashtbl.find binders 0 in
         try
           (I8opaque (fst (Cmap.find trm tbl)), tbl)
         with
           Not_found ->
           let nxt = Cmap.cardinal tbl in
           (I8opaque nxt, Cmap.add trm (nxt,I8) tbl))
      ]

  and parse_int16_expr tbl =
    Term_match.matches tbl
      [ (Term_match.Glob c_int16_zero, fun tbl _ -> (I16repr (Zp2m1 0), tbl))
      ; (Term_match.Glob c_int16_one, fun tbl _ -> (I16repr (Zp2 0), tbl))
      ; (Term_match.Glob c_int16_iwordsize, fun tbl _ -> (I16repr (Zp2 4), tbl))
      ; parse_bop parse_int16_expr c_int16_add (fun a b -> I16add (a,b))
      ; parse_bop parse_int16_expr c_int16_sub (fun a b -> I16sub (a,b))
      ; parse_bop parse_int16_expr c_int16_mul (fun a b -> I16mul (a,b))
      ; parse_bop parse_int16_expr c_int16_divu (fun a b -> I16divu (a,b))
      ; parse_bop parse_int16_expr c_int16_modu (fun a b -> I16modu (a,b))
      ; parse_bop parse_int16_expr c_int16_divs (fun a b -> I16divs (a,b))
      ; parse_bop parse_int16_expr c_int16_mods (fun a b -> I16mods (a,b))
      ; parse_uop parse_z_expr c_int16_repr (fun a -> I16repr a)
      ; parse_uop parse_int16_expr c_int16_not (fun a -> I16not a)
      ; parse_bop parse_int16_expr c_int16_and (fun a b -> I16and (a,b))
      ; parse_bop parse_int16_expr c_int16_or (fun a b -> I16or (a,b))
      ; parse_bop parse_int16_expr c_int16_xor (fun a b -> I16xor (a,b))
      ; parse_bop parse_int16_expr c_int16_shl (fun a b -> I16shl (a,b))
      ; parse_bop parse_int16_expr c_int16_shru (fun a b -> I16shru (a,b))
      ; parse_bop parse_int16_expr c_int16_shr (fun a b -> I16shr (a,b))
      ; (Term_match.get 0,
         fun tbl binders ->
         let trm = Hashtbl.find binders 0 in
         try
           (I16opaque (fst (Cmap.find trm tbl)), tbl)
         with
           Not_found ->
           let nxt = Cmap.cardinal tbl in
           (I16opaque nxt, Cmap.add trm (nxt,I16) tbl))
      ]


  and parse_int32_expr tbl =
    Term_match.matches tbl
      [ (Term_match.Glob c_int32_zero, fun tbl _ -> (I32repr (Zp2m1 0), tbl))
      ; (Term_match.Glob c_int32_one, fun tbl _ -> (I32repr (Zp2 0), tbl))
      ; (Term_match.Glob c_int32_iwordsize, fun tbl _ -> (I32repr (Zp2 5), tbl))
      ; parse_bop parse_int32_expr c_int32_add (fun a b -> I32add (a,b))
      ; parse_bop parse_int32_expr c_int32_sub (fun a b -> I32sub (a,b))
      ; parse_bop parse_int32_expr c_int32_mul (fun a b -> I32mul (a,b))
      ; parse_bop parse_int32_expr c_int32_divu (fun a b -> I32divu (a,b))
      ; parse_bop parse_int32_expr c_int32_modu (fun a b -> I32modu (a,b))
      ; parse_bop parse_int32_expr c_int32_divs (fun a b -> I32divs (a,b))
      ; parse_bop parse_int32_expr c_int32_mods (fun a b -> I32mods (a,b))
      ; parse_uop parse_z_expr c_int32_repr (fun a -> I32repr a)
      ; parse_uop parse_int32_expr c_int32_not (fun a -> I32not a)
      ; parse_bop parse_int32_expr c_int32_and (fun a b -> I32and (a,b))
      ; parse_bop parse_int32_expr c_int32_or (fun a b -> I32or (a,b))
      ; parse_bop parse_int32_expr c_int32_xor (fun a b -> I32xor (a,b))
      ; parse_bop parse_int32_expr c_int32_shl (fun a b -> I32shl (a,b))
      ; parse_bop parse_int32_expr c_int32_shru (fun a b -> I32shru (a,b))
      ; parse_bop parse_int32_expr c_int32_shr (fun a b -> I32shr (a,b))
      ; (Term_match.get 0,
         fun tbl binders ->
         let trm = Hashtbl.find binders 0 in
         try
           (I32opaque (fst (Cmap.find trm tbl)), tbl)
         with
           Not_found ->
           let nxt = Cmap.cardinal tbl in
           (I32opaque nxt, Cmap.add trm (nxt,I32) tbl))
      ]

  and parse_int64_expr tbl =
    Term_match.matches tbl
      [ (Term_match.Glob c_int64_zero, fun tbl _ -> (I64repr (Zp2m1 0), tbl))
      ; (Term_match.Glob c_int64_one, fun tbl _ -> (I64repr (Zp2 0), tbl))
      ; (Term_match.Glob c_int64_iwordsize, fun tbl _ -> (I64repr (Zp2 6), tbl))
      ; parse_bop parse_int64_expr c_int64_add (fun a b -> I64add (a,b))
      ; parse_bop parse_int64_expr c_int64_sub (fun a b -> I64sub (a,b))
      ; parse_bop parse_int64_expr c_int64_mul (fun a b -> I64mul (a,b))
      ; parse_bop parse_int64_expr c_int64_divu (fun a b -> I64divu (a,b))
      ; parse_bop parse_int64_expr c_int64_modu (fun a b -> I64modu (a,b))
      ; parse_bop parse_int64_expr c_int64_divs (fun a b -> I64divs (a,b))
      ; parse_bop parse_int64_expr c_int64_mods (fun a b -> I64mods (a,b))
      ; parse_uop parse_z_expr c_int64_repr (fun a -> I64repr a)
      ; parse_uop parse_int64_expr c_int64_not (fun a -> I64not a)
      ; parse_bop parse_int64_expr c_int64_and (fun a b -> I64and (a,b))
      ; parse_bop parse_int64_expr c_int64_or (fun a b -> I64or (a,b))
      ; parse_bop parse_int64_expr c_int64_xor (fun a b -> I64xor (a,b))
      ; parse_bop parse_int64_expr c_int64_shl (fun a b -> I64shl (a,b))
      ; parse_bop parse_int64_expr c_int64_shru (fun a b -> I64shru (a,b))
      ; parse_bop parse_int64_expr c_int64_shr (fun a b -> I64shr (a,b))
      ; (Term_match.get 0,
         fun tbl binders ->
         let trm = Hashtbl.find binders 0 in
         try
           (I64opaque (fst (Cmap.find trm tbl)), tbl)
         with
           Not_found ->
           let nxt = Cmap.cardinal tbl in
           (I64opaque nxt, Cmap.add trm (nxt,I64) tbl))
      ]

  and parse_bool_expr tbl =
    Term_match.matches tbl
      [ (Term_match.Glob c_true, fun tbl _ -> (Btrue, tbl))
      ; (Term_match.Glob c_false, fun tbl _ -> (Bfalse, tbl))
      ; parse_bop parse_z_expr c_Zeqb (fun a b -> Zeqb (a,b))
      ; parse_bop parse_z_expr c_Zleb (fun a b -> Zleb (a,b))
      ; parse_bop parse_z_expr c_Zltb (fun a b -> Zltb (a,b))
      ; parse_bop parse_z_expr c_Zgeb (fun a b -> Zgeb (a,b))
      ; parse_bop parse_z_expr c_Zgtb (fun a b -> Zgtb (a,b))  
      ; parse_bop parse_int8_expr c_int8_lt (fun a b -> I8lt (a,b))
      ; parse_bop parse_int8_expr c_int8_ltu (fun a b -> I8ltu (a,b))
      ; parse_bop parse_int8_expr c_int8_eq (fun a b -> I8eq (a,b))
      ; parse_bop parse_int16_expr c_int16_lt (fun a b -> I16lt (a,b))
      ; parse_bop parse_int16_expr c_int16_ltu (fun a b -> I16ltu (a,b))
      ; parse_bop parse_int16_expr c_int16_eq (fun a b -> I16eq (a,b))
      ; parse_bop parse_int32_expr c_int32_lt (fun a b -> I32lt (a,b))
      ; parse_bop parse_int32_expr c_int32_ltu (fun a b -> I32ltu (a,b))
      ; parse_bop parse_int32_expr c_int32_eq (fun a b -> I32eq (a,b))
      ; parse_bop parse_int64_expr c_int64_lt (fun a b -> I64lt (a,b))
      ; parse_bop parse_int64_expr c_int64_ltu (fun a b -> I64ltu (a,b))
      ; parse_bop parse_int64_expr c_int64_eq (fun a b -> I64eq (a,b))    
      ; (Term_match.get 0,
         fun tbl binders ->
         let trm = Hashtbl.find binders 0 in
         try
           (Bopaque (fst (Cmap.find trm tbl)), tbl)
         with
           Not_found ->
           let nxt = Cmap.cardinal tbl in
           (Bopaque nxt, Cmap.add trm (nxt,Bool) tbl))
      ]

   and parse_z_expr tbl =
    Term_match.matches tbl
      [ (Term_match.Glob c_Z0, fun tbl _ -> (Zp2m1 0, tbl))
      ; (Term_match.Glob c_xH, fun tbl _ -> (Zp2 0, tbl))
      ; (Term_match.Glob c_int8_max_unsigned, fun tbl _ -> (Zp2m1 8, tbl))
      ; (Term_match.Glob c_int8_max_signed, fun tbl _ -> (Zp2m1 7, tbl))
      ; (Term_match.Glob c_int8_min_signed, fun tbl _ -> (Zneg (Zp2 7), tbl))
      ; (Term_match.Glob c_int8_modulus, fun tbl _ -> (Zp2 8, tbl))
      ; (Term_match.Glob c_int8_half_modulus, fun tbl _ -> (Zp2 7, tbl))
      ; (Term_match.Glob c_int8_zwordsize, fun tbl _ -> (Zp2 3, tbl))
      ; (Term_match.Glob c_int16_max_unsigned, fun tbl _ -> (Zp2m1 16, tbl))
      ; (Term_match.Glob c_int16_max_signed, fun tbl _ -> (Zp2m1 15, tbl))
      ; (Term_match.Glob c_int16_min_signed, fun tbl _ -> (Zneg (Zp2 15), tbl))
      ; (Term_match.Glob c_int16_modulus, fun tbl _ -> (Zp2 16, tbl))
      ; (Term_match.Glob c_int16_half_modulus, fun tbl _ -> (Zp2 15, tbl))
      ; (Term_match.Glob c_int16_zwordsize, fun tbl _ -> (Zp2 4, tbl))
      ; (Term_match.Glob c_int32_max_unsigned, fun tbl _ -> (Zp2m1 32, tbl))
      ; (Term_match.Glob c_int32_max_signed, fun tbl _ -> (Zp2m1 31, tbl))
      ; (Term_match.Glob c_int32_min_signed, fun tbl _ -> (Zneg (Zp2 31), tbl))
      ; (Term_match.Glob c_int32_modulus, fun tbl _ -> (Zp2 32, tbl))
      ; (Term_match.Glob c_int32_half_modulus, fun tbl _ -> (Zp2 31, tbl))
      ; (Term_match.Glob c_int32_zwordsize, fun tbl _ -> (Zp2 5, tbl))
      ; (Term_match.Glob c_int64_max_unsigned, fun tbl _ -> (Zp2m1 64, tbl))
      ; (Term_match.Glob c_int64_max_signed, fun tbl _ -> (Zp2m1 63, tbl))
      ; (Term_match.Glob c_int64_min_signed, fun tbl _ -> (Zneg (Zp2 63), tbl))
      ; (Term_match.Glob c_int64_modulus, fun tbl _ -> (Zp2 64, tbl))
      ; (Term_match.Glob c_int64_half_modulus, fun tbl _ -> (Zp2 63, tbl))
      ; (Term_match.Glob c_int64_zwordsize, fun tbl _ -> (Zp2 6, tbl))
      ; parse_bop parse_z_expr c_Zadd (fun a b -> Zadd (a,b))
      ; parse_bop parse_z_expr c_Zsub (fun a b -> Zsub (a,b))
      ; parse_bop parse_z_expr c_Zmul (fun a b -> Zmul (a,b))
      ; parse_bop parse_z_expr c_Zdiv (fun a b -> Zdiv (a,b))
      ; parse_bop parse_z_expr c_Zshiftl (fun a b -> Zshiftl (a,b))
      ; parse_bop parse_z_expr c_Zshiftr (fun a b -> Zshiftr (a,b))
      ; parse_bop parse_z_expr c_Zpow (fun a b -> Zpow (a,b))
      ; parse_bop parse_z_expr c_Zmodulo (fun a b -> Zmodulo (a,b))
      ; parse_bop parse_z_expr c_Zrem (fun a b -> Zrem (a,b))
      ; parse_uop parse_nat_expr c_Zof_nat (fun a -> ZofN a)
      ; parse_uop parse_z_expr c_xO (fun a -> ZxO a)
      ; parse_uop parse_z_expr c_xI (fun a -> ZxI a)
      ; parse_uop parse_z_expr c_Zpos (fun a -> a)
      ; parse_uop parse_z_expr c_Zneg (fun a -> Zneg a)
      ; parse_uop parse_int8_expr c_int8_signed (fun a -> I8signed a)
      ; parse_uop parse_int8_expr c_int8_unsigned (fun a -> I8unsigned a)
      ; parse_uop parse_int16_expr c_int16_signed (fun a -> I16signed a)
      ; parse_uop parse_int16_expr c_int16_unsigned (fun a -> I16unsigned a)
      ; parse_uop parse_int32_expr c_int32_signed (fun a -> I32signed a)
      ; parse_uop parse_int32_expr c_int32_unsigned (fun a -> I32unsigned a)
      ; parse_uop parse_int64_expr c_int64_signed (fun a -> I64signed a)
      ; parse_uop parse_int64_expr c_int64_unsigned (fun a -> I64unsigned a)
      ; (Term_match.get 0,
         fun tbl binders ->
         let trm = Hashtbl.find binders 0 in
         try
           (Zopaque (fst (Cmap.find trm tbl)), tbl)
         with
           Not_found ->
           let nxt = Cmap.cardinal tbl in
           (Zopaque nxt, Cmap.add trm (nxt,Z) tbl))
      ]

   and parse_nat_expr tbl =
    Term_match.matches tbl
      [ (Term_match.Glob c_nat_O, fun tbl _ -> (NofZ (Zp2m1 0), tbl))
      ; (Term_match.Glob c_int8_wordsize, fun tbl _ -> (NofZ (Zp2 3), tbl))
      ; (Term_match.Glob c_int16_wordsize, fun tbl _ -> (NofZ (Zp2 4), tbl))
      ; (Term_match.Glob c_int32_wordsize, fun tbl _ -> (NofZ (Zp2 5), tbl))
      ; (Term_match.Glob c_int64_wordsize, fun tbl _ -> (NofZ (Zp2 6), tbl))
      ; parse_bop parse_nat_expr c_nat_add (fun a b -> Nadd (a,b))
      ; parse_bop parse_nat_expr c_nat_sub (fun a b -> Nsub (a,b))
      ; parse_bop parse_nat_expr c_nat_mul (fun a b -> Nmul (a,b))
      ; parse_uop parse_nat_expr c_nat_S (fun a -> NSucc a)
      ; parse_uop parse_z_expr c_Zto_nat (fun a -> NofZ a)
      ; (Term_match.get 0,
         fun tbl binders ->
         let trm = Hashtbl.find binders 0 in
         try
           (Nopaque (fst (Cmap.find trm tbl)), tbl)
         with
           Not_found ->
           let nxt = Cmap.cardinal tbl in
           (Nopaque nxt, Cmap.add trm (nxt,Nat) tbl))
      ]
  
  
  let rec parse_prop tbl =
    Term_match.matches tbl
      [ parse_bop parse_z_expr c_Zlt (fun a b -> Zlt (a,b))
      ; parse_bop parse_z_expr c_Zle (fun a b -> Zle (a,b))
      ; parse_bop parse_z_expr c_Zgt (fun a b -> Zgt (a,b))
      ; parse_bop parse_z_expr c_Zge (fun a b -> Zge (a,b))
      ; (Term_match.apps (Term_match.Glob c_Zeq)
			 [Term_match.Glob c_Z;
			  Term_match.get 0;
			  Term_match.get 1],
	 fun tbl bindings ->
	 let (l,tbl) = parse_z_expr tbl (Hashtbl.find bindings 0) in
	 let (r,tbl) = parse_z_expr tbl (Hashtbl.find bindings 1) in
	 (Zeq (l, r), tbl))
      ; (Term_match.apps (Term_match.Glob c_int8_is)
                         [Term_match.Glob c_int8;
                          Term_match.get 0;
                          Term_match.get 1],
         fun tbl bindings ->
         let (l,tbl) = parse_int8_expr tbl (Hashtbl.find bindings 0) in
         let (r,tbl) = parse_int8_expr tbl (Hashtbl.find bindings 1) in
         (I8is (l, r), tbl))
      ; (Term_match.apps (Term_match.Glob c_int16_is)
                         [Term_match.Glob c_int16;
                          Term_match.get 0;
                          Term_match.get 1],
         fun tbl bindings ->
         let (l,tbl) = parse_int16_expr tbl (Hashtbl.find bindings 0) in
         let (r,tbl) = parse_int16_expr tbl (Hashtbl.find bindings 1) in
         (I16is (l, r), tbl))
      ; (Term_match.apps (Term_match.Glob c_int32_is)
                         [Term_match.Glob c_int32;
                          Term_match.get 0;
                          Term_match.get 1],
         fun tbl bindings ->
         let (l,tbl) = parse_int32_expr tbl (Hashtbl.find bindings 0) in
         let (r,tbl) = parse_int32_expr tbl (Hashtbl.find bindings 1) in
         (I32is (l, r), tbl))
      ; (Term_match.apps (Term_match.Glob c_int64_is)
                         [Term_match.Glob c_int64;
                          Term_match.get 0;
                          Term_match.get 1],
         fun tbl bindings ->
         let (l,tbl) = parse_int64_expr tbl (Hashtbl.find bindings 0) in
         let (r,tbl) = parse_int64_expr tbl (Hashtbl.find bindings 1) in
         (I64is (l, r), tbl))
      ; (Term_match.apps (Term_match.Glob c_beq)
                         [Term_match.Glob c_bool;
                          Term_match.get 0;
                          Term_match.get 1],
         fun tbl bindings ->
         let (l,tbl) = parse_bool_expr tbl (Hashtbl.find bindings 0) in
         let (r,tbl) = parse_bool_expr tbl (Hashtbl.find bindings 1) in
         (Beq (l, r), tbl))
      ; parse_bop parse_nat_expr c_nat_lt (fun a b -> Nlt (a,b))
      ; parse_bop parse_nat_expr c_nat_le (fun a b -> Nle (a,b))
      ; parse_bop parse_nat_expr c_nat_gt (fun a b -> Ngt (a,b))
      ; parse_bop parse_nat_expr c_nat_ge (fun a b -> Nge (a,b))
      ; (Term_match.apps (Term_match.Glob c_nat_eq)
                         [Term_match.Glob c_nat;
                          Term_match.get 0;
                          Term_match.get 1],
         fun tbl bindings ->
         let (l,tbl) = parse_nat_expr tbl (Hashtbl.find bindings 0) in
         let (r,tbl) = parse_nat_expr tbl (Hashtbl.find bindings 1) in
         (Neq (l, r), tbl))
      ; parse_bop parse_r_expr c_Rlt (fun a b -> Rlt (a,b))
      ; parse_bop parse_r_expr c_Rle (fun a b -> Rle (a,b))
      ; parse_bop parse_r_expr c_Rgt (fun a b -> Rgt (a,b))
      ; parse_bop parse_r_expr c_Rge (fun a b -> Rge (a,b))
      ; (Term_match.apps (Term_match.Glob c_Req)
                         [Term_match.Glob c_R;
                          Term_match.get 0;
                          Term_match.get 1],
         fun tbl bindings ->
         let (l,tbl) = parse_r_expr tbl (Hashtbl.find bindings 0) in
         let (r,tbl) = parse_r_expr tbl (Hashtbl.find bindings 1) in
         (Req (l, r), tbl))
      ; parse_bop parse_prop c_and (fun a b -> Pand (a,b))
      ; parse_bop parse_prop c_or  (fun a b -> Por (a,b))
      ; (Term_match.apps (Term_match.Glob c_Not)
	   [Term_match.get 0], fun tbl bindings ->
	     let (l,tbl) = parse_prop tbl (Hashtbl.find bindings 0) in
	     (Pnot l, tbl))
      ; (Term_match.Glob c_True, fun tbl _ -> (Ptrue, tbl))
      ; (Term_match.Glob c_False, fun tbl _ -> (Pfalse, tbl))
      ; (Term_match.get 0,
	 fun tbl binders ->
           let trm = Hashtbl.find binders 0 in
           let (o,tbl) = get_opaque trm Prop tbl in
	   (Popaque o, tbl))
      ]

  let parse_hypothesis _ _ name typ i =
    let (h,vs) = parse_prop i.vars typ in
    { i with vars = vs ; assertions = (name, h) :: i.assertions }

  let parse_conclusion _ _ x =
    let (c,vs) = parse_prop Cmap.empty x in
    { vars = vs ; assertions = [] ; concl = c }

  (** Printing **)

  let rec print_type out t =
    match t with
      Prop -> Format.fprintf out "Bool"
    | Z -> Format.fprintf out "Int"
    | I8 -> Format.fprintf out "(_ BitVec 8)"
    | I16 -> Format.fprintf out "(_ BitVec 16)"
    | I32 -> Format.fprintf out "(_ BitVec 32)"
    | I64 -> Format.fprintf out "(_ BitVec 64)"
    | Bool -> Format.fprintf out "Bool"
    | Nat -> Format.fprintf out "Int"
    | R -> Format.fprintf out "Real"
    | List l -> Format.fprintf out "(List %a)" print_type l


   let rec print_r_expr out e =
    match e with
      RConst f -> Format.fprintf out "%f" f
    | Rplus (l,r) -> Format.fprintf out "(+ %a %a)" print_r_expr l print_r_expr r
    | Rminus (l,r) -> Format.fprintf out "(- %a %a)" print_r_expr l print_r_expr r
    | Rmult (l,r) -> Format.fprintf out "(* %a %a)" print_r_expr l print_r_expr r
    | Rdiv (l,r) -> Format.fprintf out "(/ %a %a)" print_r_expr l print_r_expr r
    | Ropp l -> Format.fprintf out "(- 0 %a)" print_r_expr l
    | Rinv l -> Format.fprintf out "(/ 1 %a)" print_r_expr l
    | Ropaque l -> Format.fprintf out "x%d" l

  and print_int8_expr out e =
    match e with
      I8and (l,r) -> Format.fprintf out "(bvand %a %a)" print_int8_expr l print_int8_expr r
    | I8or (l,r) -> Format.fprintf out "(bvor %a %a)" print_int8_expr l print_int8_expr r
    | I8opaque l -> Format.fprintf out "x%d" l
    | I8repr l -> Format.fprintf out "((_ int2bv 8) %a)" print_z_expr l
    | I8add (l,r) -> Format.fprintf out "(bvadd %a %a)" print_int8_expr l print_int8_expr r
    | I8sub (l,r) -> Format.fprintf out "(bvsub %a %a)" print_int8_expr l print_int8_expr r
    | I8mul (l,r) -> Format.fprintf out "(bvmul %a %a)" print_int8_expr l print_int8_expr r
    | I8divu (l,r) -> Format.fprintf out "(bvudiv %a %a)" print_int8_expr l print_int8_expr r
    | I8modu (l,r) -> Format.fprintf out "(bvurem %a %a)" print_int8_expr l print_int8_expr r
    | I8xor (l,r) -> Format.fprintf out "(bvxor %a %a)" print_int8_expr l print_int8_expr r
    | I8shl (l,r) -> Format.fprintf out "(bvshl %a %a)" print_int8_expr l print_int8_expr r
    | I8shru (l,r) -> Format.fprintf out "(bvlshr %a %a)" print_int8_expr l print_int8_expr r
    | I8not l -> Format.fprintf out "(bvnot %a)" print_int8_expr l
    | I8divs (l,r) -> Format.fprintf out "(bvsdiv %a %a)" print_int8_expr l print_int8_expr r
    | I8mods (l,r) -> Format.fprintf out "(bvsrem %a %a)" print_int8_expr l print_int8_expr r
    | I8shr (l,r) -> Format.fprintf out "(bvashr %a %a)" print_int8_expr l print_int8_expr r

   and print_int16_expr out e =
    match e with
      I16and (l,r) -> Format.fprintf out "(bvand %a %a)" print_int16_expr l print_int16_expr r
    | I16or (l,r) -> Format.fprintf out "(bvor %a %a)" print_int16_expr l print_int16_expr r
    | I16opaque l -> Format.fprintf out "x%d" l
    | I16repr l -> Format.fprintf out "((_ int2bv 16) %a)" print_z_expr l
    | I16add (l,r) -> Format.fprintf out "(bvadd %a %a)" print_int16_expr l print_int16_expr r
    | I16sub (l,r) -> Format.fprintf out "(bvsub %a %a)" print_int16_expr l print_int16_expr r
    | I16mul (l,r) -> Format.fprintf out "(bvmul %a %a)" print_int16_expr l print_int16_expr r
    | I16divu (l,r) -> Format.fprintf out "(bvudiv %a %a)" print_int16_expr l print_int16_expr r
    | I16modu (l,r) -> Format.fprintf out "(bvurem %a %a)" print_int16_expr l print_int16_expr r
    | I16xor (l,r) -> Format.fprintf out "(bvxor %a %a)" print_int16_expr l print_int16_expr r
    | I16shl (l,r) -> Format.fprintf out "(bvshl %a %a)" print_int16_expr l print_int16_expr r
    | I16shru (l,r) -> Format.fprintf out "(bvlshr %a %a)" print_int16_expr l print_int16_expr r
    | I16not l -> Format.fprintf out "(bvnot %a)" print_int16_expr l
    | I16divs (l,r) -> Format.fprintf out "(bvsdiv %a %a)" print_int16_expr l print_int16_expr r
    | I16mods (l,r) -> Format.fprintf out "(bvsrem %a %a)" print_int16_expr l print_int16_expr r
    | I16shr (l,r) -> Format.fprintf out "(bvashr %a %a)" print_int16_expr l print_int16_expr r

   and print_int32_expr out e =
    match e with
      I32and (l,r) -> Format.fprintf out "(bvand %a %a)" print_int32_expr l print_int32_expr r
    | I32or (l,r) -> Format.fprintf out "(bvor %a %a)" print_int32_expr l print_int32_expr r
    | I32opaque l -> Format.fprintf out "x%d" l
    | I32repr l -> Format.fprintf out "((_ int2bv 32) %a)" print_z_expr l
    | I32add (l,r) -> Format.fprintf out "(bvadd %a %a)" print_int32_expr l print_int32_expr r
    | I32sub (l,r) -> Format.fprintf out "(bvsub %a %a)" print_int32_expr l print_int32_expr r
    | I32mul (l,r) -> Format.fprintf out "(bvmul %a %a)" print_int32_expr l print_int32_expr r
    | I32divu (l,r) -> Format.fprintf out "(bvudiv %a %a)" print_int32_expr l print_int32_expr r
    | I32modu (l,r) -> Format.fprintf out "(bvurem %a %a)" print_int32_expr l print_int32_expr r
    | I32xor (l,r) -> Format.fprintf out "(bvxor %a %a)" print_int32_expr l print_int32_expr r
    | I32shl (l,r) -> Format.fprintf out "(bvshl %a %a)" print_int32_expr l print_int32_expr r
    | I32shru (l,r) -> Format.fprintf out "(bvlshr %a %a)" print_int32_expr l print_int32_expr r
    | I32not l -> Format.fprintf out "(bvnot %a)" print_int32_expr l
    | I32divs (l,r) -> Format.fprintf out "(bvsdiv %a %a)" print_int32_expr l print_int32_expr r
    | I32mods (l,r) -> Format.fprintf out "(bvsrem %a %a)" print_int32_expr l print_int32_expr r
    | I32shr (l,r) -> Format.fprintf out "(bvashr %a %a)" print_int32_expr l print_int32_expr r

   and print_int64_expr out e =
    match e with
      I64and (l,r) -> Format.fprintf out "(bvand %a %a)" print_int64_expr l print_int64_expr r
    | I64or (l,r) -> Format.fprintf out "(bvor %a %a)" print_int64_expr l print_int64_expr r
    | I64opaque l -> Format.fprintf out "x%d" l
    | I64repr l -> Format.fprintf out "((_ int2bv 64) %a)" print_z_expr l
    | I64add (l,r) -> Format.fprintf out "(bvadd %a %a)" print_int64_expr l print_int64_expr r
    | I64sub (l,r) -> Format.fprintf out "(bvsub %a %a)" print_int64_expr l print_int64_expr r
    | I64mul (l,r) -> Format.fprintf out "(bvmul %a %a)" print_int64_expr l print_int64_expr r
    | I64divu (l,r) -> Format.fprintf out "(bvudiv %a %a)" print_int64_expr l print_int64_expr r
    | I64modu (l,r) -> Format.fprintf out "(bvurem %a %a)" print_int64_expr l print_int64_expr r
    | I64xor (l,r) -> Format.fprintf out "(bvxor %a %a)" print_int64_expr l print_int64_expr r
    | I64shl (l,r) -> Format.fprintf out "(bvshl %a %a)" print_int64_expr l print_int64_expr r
    | I64shru (l,r) -> Format.fprintf out "(bvlshr %a %a)" print_int64_expr l print_int64_expr r
    | I64not l -> Format.fprintf out "(bvnot %a)" print_int64_expr l
    | I64divs (l,r) -> Format.fprintf out "(bvsdiv %a %a)" print_int64_expr l print_int64_expr r
    | I64mods (l,r) -> Format.fprintf out "(bvsrem %a %a)" print_int64_expr l print_int64_expr r
    | I64shr (l,r) -> Format.fprintf out "(bvashr %a %a)" print_int64_expr l print_int64_expr r

  and print_z_expr out e =
    match e with
      Zp2 l -> Format.fprintf out "(^ 2 %d)" l
    | Zp2m1 l -> Format.fprintf out "(- (^ 2 %d) 1)" l
    | Zadd (l,r) -> Format.fprintf out "(+ %a %a)" print_z_expr l print_z_expr r
    | Zsub (l,r) -> Format.fprintf out "(- %a %a)" print_z_expr l print_z_expr r
    | Zmul (l,r) -> Format.fprintf out "(* %a %a)" print_z_expr l print_z_expr r
    | Zdiv (l,r) -> Format.fprintf out "(div %a %a)" print_z_expr l print_z_expr r
    | Zshiftl (l,r) -> Format.fprintf out "(* %a (^ 2 %a))" print_z_expr l print_z_expr r
    | Zshiftr (l,r) -> Format.fprintf out "(div %a (^ 2 %a))" print_z_expr l print_z_expr r
    | Zpow (l,r) -> Format.fprintf out "(ite (< %a 0) 0 (^ %a %a))" print_z_expr r print_z_expr l print_z_expr r
    | Zmodulo (l,r) -> Format.fprintf out "(ite (< %a 0) (+ (mod %a %a) %a) (mod %a %a))" print_z_expr r print_z_expr l print_z_expr r print_z_expr r print_z_expr l print_z_expr r
    | Zrem (l,r) -> Format.fprintf out "(ite (< %a 0) (- 0 (rem (abs %a) (abs %a))) (rem (abs %a) (abs %a)))" print_z_expr l print_z_expr l print_z_expr r print_z_expr l print_z_expr r
    | Zneg l -> Format.fprintf out "(- 0 %a)" print_z_expr l
    | ZxO l -> Format.fprintf out "(+ (* 2 %a) 0)" print_z_expr l
    | ZxI l -> Format.fprintf out "(+ (* 2 %a) 1)" print_z_expr l
    | Zopaque l -> Format.fprintf out "x%d" l
    | I8signed l -> Format.fprintf out "(ite (< (bv2int %a) (^ 2 7)) (bv2int %a) (- (bv2int %a) (^ 2 8)))" print_int8_expr l print_int8_expr l print_int8_expr l
    | I16signed l -> Format.fprintf out "(ite (< (bv2int %a) (^ 2 15)) (bv2int %a) (- (bv2int %a) (^ 2 16)))" print_int16_expr l print_int16_expr l print_int16_expr l
    | I32signed l -> Format.fprintf out "(ite (< (bv2int %a) (^ 2 31)) (bv2int %a) (- (bv2int %a) (^ 2 32)))" print_int32_expr l print_int32_expr l print_int32_expr l
    | I64signed l -> Format.fprintf out "(ite (< (bv2int %a) (^ 2 63)) (bv2int %a) (- (bv2int %a) (^ 2 64)))" print_int64_expr l print_int64_expr l print_int64_expr l
    | I8unsigned l -> Format.fprintf out "(bv2int %a)" print_int8_expr l
    | I16unsigned l -> Format.fprintf out "(bv2int %a)" print_int16_expr l
    | I32unsigned l -> Format.fprintf out "(bv2int %a)" print_int32_expr l
    | I64unsigned l -> Format.fprintf out "(bv2int %a)" print_int64_expr l
    | ZofN l -> Format.fprintf out "%a" print_nat_expr l


  and print_bool_expr out e =
    match e with
      Btrue  -> Format.fprintf out "true"
    | Bfalse -> Format.fprintf out "false"
    | I8lt (l,r) -> Format.fprintf out "(bvslt %a %a)" print_int8_expr l print_int8_expr r
    | I8ltu (l,r) -> Format.fprintf out "(bvult %a %a)" print_int8_expr l print_int8_expr r
    | I8eq (l,r) -> Format.fprintf out "(= %a %a)" print_int8_expr l print_int8_expr r
    | I16lt (l,r) -> Format.fprintf out "(bvslt %a %a)" print_int16_expr l print_int16_expr r
    | I16ltu (l,r) -> Format.fprintf out "(bvult %a %a)" print_int16_expr l print_int16_expr r
    | I16eq (l,r) -> Format.fprintf out "(= %a %a)" print_int16_expr l print_int16_expr r
    | I32lt (l,r) -> Format.fprintf out "(bvslt %a %a)" print_int32_expr l print_int32_expr r
    | I32ltu (l,r) -> Format.fprintf out "(bvult %a %a)" print_int32_expr l print_int32_expr r
    | I32eq (l,r) -> Format.fprintf out "(= %a %a)" print_int32_expr l print_int32_expr r
    | I64lt (l,r) -> Format.fprintf out "(bvslt %a %a)" print_int64_expr l print_int64_expr r
    | I64ltu (l,r) -> Format.fprintf out "(bvult %a %a)" print_int64_expr l print_int64_expr r
    | I64eq (l,r) -> Format.fprintf out "(= %a %a)" print_int64_expr l print_int64_expr r
    | Zeqb (l,r) -> Format.fprintf out "(= %a %a)" print_z_expr l print_z_expr r
    | Zleb (l,r) -> Format.fprintf out "(<= %a %a)" print_z_expr l print_z_expr r
    | Zltb (l,r) -> Format.fprintf out "(< %a %a)" print_z_expr l print_z_expr r
    | Zgeb (l,r) -> Format.fprintf out "(>= %a %a)" print_z_expr l print_z_expr r
    | Zgtb (l,r) -> Format.fprintf out "(> %a %a)" print_z_expr l print_z_expr r
    | Bopaque l -> Format.fprintf out "x%d" l

  and print_nat_expr out e =
    match e with
      Nadd (l,r) -> Format.fprintf out "(+ %a %a)" print_nat_expr l print_nat_expr r
    | Nsub (l,r) -> Format.fprintf out "(ite (> (- %a %a) 0) (- %a %a) 0)" print_nat_expr l print_nat_expr r print_nat_expr l print_nat_expr r
    | Nmul (l,r) -> Format.fprintf out "(* %a %a)" print_nat_expr l print_nat_expr r 
    | NSucc l -> Format.fprintf out "(+ 1 %a)" print_nat_expr l
    | Nopaque l -> Format.fprintf out "x%d" l
    | NofZ l -> Format.fprintf out "(ite (> %a 0) %a 0)" print_z_expr l print_z_expr l


  let rec print_prop_expr out e =
    match e with
      Ptrue -> Format.fprintf out "true"
    | Pfalse -> Format.fprintf out "false"
    | Pnot l -> Format.fprintf out "(not %a)" print_prop_expr l
    | Popaque x -> Format.fprintf out "x%d" x
    | Pand (l,r) -> Format.fprintf out "(and %a %a)" print_prop_expr l print_prop_expr r
    | Por (l,r) -> Format.fprintf out "(or %a %a)" print_prop_expr l print_prop_expr r
    | Pimpl (l,r) -> Format.fprintf out "(=> %a %a)" print_prop_expr l print_prop_expr r
    | Zle (l,r) -> Format.fprintf out "(<= %a %a)" print_z_expr l print_z_expr r
    | Zlt (l,r) -> Format.fprintf out "(< %a %a)" print_z_expr l print_z_expr r
    | Zge (l,r) -> Format.fprintf out "(>= %a %a)" print_z_expr l print_z_expr r
    | Zgt (l,r) -> Format.fprintf out "(> %a %a)" print_z_expr l print_z_expr r
    | Zeq (l,r) -> Format.fprintf out "(= %a %a)" print_z_expr l print_z_expr r
    | I8is (l,r) -> Format.fprintf out "(= %a %a)" print_int8_expr l print_int8_expr r
    | I16is (l,r) -> Format.fprintf out "(= %a %a)" print_int16_expr l print_int16_expr r
    | I32is (l,r) -> Format.fprintf out "(= %a %a)" print_int32_expr l print_int32_expr r
    | I64is (l,r) -> Format.fprintf out "(= %a %a)" print_int64_expr l print_int64_expr r
    | Beq (l,r) -> Format.fprintf out "(= %a %a)" print_bool_expr l print_bool_expr r
    | Nle (l,r) -> Format.fprintf out "(<= %a %a)" print_nat_expr l print_nat_expr r
    | Nlt (l,r) -> Format.fprintf out "(< %a %a)" print_nat_expr l print_nat_expr r
    | Nge (l,r) -> Format.fprintf out "(>= %a %a)" print_nat_expr l print_nat_expr r
    | Ngt (l,r) -> Format.fprintf out "(> %a %a)" print_nat_expr l print_nat_expr r
    | Neq (l,r) -> Format.fprintf out "(= %a %a)" print_nat_expr l print_nat_expr r
    | Rle (l,r) -> Format.fprintf out "(<= %a %a)" print_r_expr l print_r_expr r
    | Rlt (l,r) -> Format.fprintf out "(< %a %a)" print_r_expr l print_r_expr r
    | Rge (l,r) -> Format.fprintf out "(>= %a %a)" print_r_expr l print_r_expr r
    | Rgt (l,r) -> Format.fprintf out "(> %a %a)" print_r_expr l print_r_expr r
    | Req (l,r) -> Format.fprintf out "(= %a %a)" print_r_expr l print_r_expr r


  let replace_apostrophe = fun c ->
    match c with
        '\'' -> '_'
       | _ -> c

  let print_identifier out id =
    Format.fprintf out "%s" (String.map replace_apostrophe (Names.string_of_id id))

  let print_named_assert pr_id out (nm,e) =
    Format.fprintf out "(assert (! %a :named %a))" print_prop_expr e pr_id nm

  let pr_list sep pr =
    let rec pr_list out ls =
      match ls with
	[] -> ()
      | [l] -> Format.fprintf out "%a" pr l
      | l :: ls -> Format.fprintf out "%a%s%a" pr l sep pr_list ls
    in
    pr_list

  let pr_decls out =
    Cmap.iter (fun _ (k,v) ->
      match v with
         Nat -> Format.fprintf out "(declare-const x%d %a)(assert (>= x%d 0))" k print_type v k
        | _ -> Format.fprintf out "(declare-const x%d %a)" k print_type v)

  let print_a_string out s =
    Format.fprintf out "%s" s

  let conclusion_name = "__CONCLUSION__"

  let write_instance ?pretty:(pretty=false) out inst =
    let sep = if pretty then "\n" else "" in
    Format.fprintf out "%a%a%s%a"
      pr_decls inst.vars
      (pr_list sep (print_named_assert print_identifier)) inst.assertions
      sep
      (print_named_assert print_a_string) (conclusion_name, Pnot inst.concl)

  let get_variable x inst =
    assert (String.length x > 1) ;
    let x =
      let rest = String.sub x 1 (String.length x - 1) in
      int_of_string rest
    in
    match
      Cmap.fold (fun k (var, _) acc ->
          if var = x then Some k else acc)
        inst.vars None
    with
      None -> raise Not_found
    | Some x -> x

  let get_hypothesis x inst =
    if x = conclusion_name then None
    else Some (Names.id_of_string x)

end
