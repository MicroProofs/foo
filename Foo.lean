def hello := "world"
-- open String
-- open Nat
-- open List

-- inductive Constant where
--   | integer : Nat -> Constant
--   | string : String -> Constant


-- inductive DefaultFunction where
--   | addinteger : DefaultFunction
--   | subinteger : DefaultFunction
--   | fst_pair : DefaultFunction

-- mutual
-- inductive Builtin where
--   | no_force : DefaultFunction -> List Term -> Builtin
--   | need_force : DefaultFunction -> Nat -> Builtin

-- inductive Term where
--   | var : String -> Term
--   | delay: Term -> Term
--   | lambda: String -> Term -> Term
--   | apply: Term -> Term -> Term
--   | const: Constant -> Term
--   | force: Term -> Term
--   | error: String -> Term
--   | builtin: Builtin -> Term
-- end

-- def builtin_force : Builtin -> Term
--   | .need_force default_fun (forces + 1) =>
--     if forces = 0 then
--      .builtin (.no_force default_fun ([] : List Term))
--     else
--       .builtin (.need_force default_fun forces)
--   | _ => .error "Forced on no force"

-- inductive EnvVar where
--   | vr : String -> Term -> EnvVar

-- inductive Env where
--   | env : List EnvVar -> List String -> Term -> Env

-- def force : Env -> Env
--   |.env env_vars logs term =>
--     match term with
--       | .delay term => .env env_vars logs term
--       | .builtin b => .env env_vars logs (builtin_force b)
--       | _ => .env env_vars logs (.error "bad force")

-- def add_var_to_env : List EnvVar -> String -> Term -> List EnvVar
--   | [], name, term => [.vr name term]
--   | var_list, name, term => .vr name term :: var_list

-- def eval_builtin : Builtin -> Term
--   | .no_force func args => .builtin (.no_force func args)
--   | _ => .error "func still needs force"


-- def check_builtin_arg : DefaultFunction -> Term -> Term
--   | .addinteger, .const (.integer a) => .const (.integer a)
--   | _, _ => .error "func still needs force"

-- def apply_builtin : Builtin -> Term -> Term
--   | .no_force func args, next_arg => eval_builtin (.no_force func ((check_builtin_arg func next_arg) :: args))
--   | _ , _ => .error "func still needs force"

-- def apply_arg : Env -> Term -> Env
--   | .env env_vars logs func, arg =>
--     match func with
--       |.lambda name term => .env (add_var_to_env env_vars name arg) logs term
--       |.builtin func => .env env_vars logs (apply_builtin func arg)
--       | _ => .env env_vars logs (.error "failed apply")

-- def lookup_var : Env -> String -> Env
--   | .env env_vars logs t, var_name =>
--       match env_vars with
--         | [] => .env env_vars logs (.error "failed lookup")
--         | .vr name term :: xs =>
--           if name == var_name then
--             .env env_vars logs term
--           else
--             lookup_var (.env xs logs t) var_name


-- def stack_frame : Env -> Env
--   | .env env_vars logs term =>
--     match term with
--       |.force inner_term => force (stack_frame (.env env_vars logs inner_term))
--       |.apply func arg =>
--         let func_env := (stack_frame (.env env_vars logs func));
--         let .env _ _ arg := (stack_frame (.env env_vars logs arg));
--         let .env env_vars logs new_term := (apply_arg func_env arg);
--         (.env env_vars logs new_term)
--       | .var name => lookup_var (.env env_vars logs term) name
--       | _ => .env env_vars logs term



-- def reduce : Env -> Env
--   | .env env_list logs term =>
--     match term with
--       | .var name => lookup_var (.env env_list logs term) name
--       | .delay term => .env env_list logs (.delay term)
--       | .lambda name term => .env env_list logs (.lambda name term)
--       | .apply _ _ => stack_frame (.env env_list logs term)
--       | .const const => .env env_list logs (.const const)
--       | .force _ => stack_frame (.env env_list logs term)
--       | .error s => .env env_list logs (.error s)
--       | .builtin b => .env env_list logs (.builtin b)

-- def loop : Env -> Env
--   | .env env_list logs term =>
--     match term with
--       | .apply _ _ => loop (reduce (.env env_list logs term))
--       | _ => .env env_list logs term
-- decreasing_by sorry




-- def test1 : Term := .force (.delay (.builtin (.no_force .addinteger ([] : List Term))))

-- def test2 : Term := .apply (.lambda "wow" (.apply (.builtin (.no_force .addinteger ([] : List Term))) (.var "wow"))) (.const (Constant.integer 2))

-- def test3 : Term := .force (.lambda "wow" (.builtin (.no_force .addinteger ([] : List Term))))

-- def test4 : Term := .force (.builtin (.need_force .fst_pair 2))


-- set_option maxRecDepth 8000
-- set_option maxHeartbeats 1000000

-- def test1_env : Env := .env ([]: List EnvVar) ([]: List String) test1
-- def test2_env : Env := .env ([]: List EnvVar) ([]: List String) test2
-- def test3_env : Env := .env ([]: List EnvVar) ([]: List String) test3
-- def test4_env : Env := .env ([]: List EnvVar) ([]: List String) test4

-- #reduce reduce test1_env

-- #reduce reduce (reduce (reduce test2_env))

-- #reduce reduce test3_env

-- #reduce reduce test4_env
