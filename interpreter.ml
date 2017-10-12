type oper = Sqrt | Plus | Minus | Times | Divide | PreDivide | Remainder;;

type token = Number of float | Operation of oper | LParen | RParen | Semicolon | Space;;

type syntaxTree =
    Uninode of oper * syntaxTree
  | Binode of syntaxTree * oper * syntaxTree
  | Leaf of float;;

exception GrammarException of string;;

exception ExtraException of (token list);;

exception ParenthesesException;;

let rec num_next_token s n =
  if       n >= String.length s then n
  else let code = Char.code (String.get s n)
       in if (code = 46 || (code >= 48 && code <= 57))
          then num_next_token s (n+1) else n;;

let rec bs_next_token s n =
  if       n >= String.length s then n
  else let code = Char.code (String.get s n)
       in if (code = 40 || code = 41 || (code >= 48 && code <= 57) || 
                (code >= 65 && code <= 90) || (code >= 97 && code <= 122))
          then bs_next_token s (n+1) else n;;


let rec tokenize s n =
  if n >= String.length s then []
  else let code = Char.code (String.get s n)
       in if (code = 46 || (code >= 48 && code <= 57))
          then let index = num_next_token s (n+1)
          in (Number (float_of_string (String.sub s n (index-n))))::tokenize s index
  else match (String.get s n) with
  | '\\' -> let index = bs_next_token s (n+1)
            in  (match (String.sub s (n+1) (index-n-1)) with
                  | "sqrt" -> (Operation Sqrt)::tokenize s (n+5)
                  | "frac" -> (Operation PreDivide)::tokenize s (n+5)
                  | "left(" -> (LParen)::tokenize s (n+6)
                  | "right)" -> (RParen)::tokenize s (n+7))
  | '+'  -> (Operation Plus)::tokenize s (n+1)
  | '-'  -> (Operation Minus)::tokenize s (n+1)
  | '*'  -> (Operation Times)::tokenize s (n+1)
  | '/'  -> (Operation Divide)::tokenize s (n+1)
  | '%'  -> (Operation Remainder)::tokenize s (n+1)
  | '(' -> (LParen)::tokenize s (n+1)
  | '{' -> (LParen)::tokenize s (n+1)
  | ')' -> (RParen)::tokenize s (n+1)
  | '}' -> (RParen)::tokenize s (n+1)
  | ' ' -> tokenize s (n+1);;

let rec parens tokens n =
  match tokens with
  | LParen::ts -> let (parens_expn, rest) = parens ts (n+1)
                 in (LParen::parens_expn, rest)
  | RParen::ts -> if n = 0 then ([], ts)
                 else let (parens_expn, rest) = parens ts (n-1)
                      in (RParen::parens_expn, rest)
  | t::ts     -> let (parens_expn, rest) = parens ts n
                 in (t::parens_expn, rest)
  | _         -> raise ParenthesesException;;

let num tokens =
  match tokens with
  | (Number x)::ts -> (Leaf x, ts)
  | _              -> raise (GrammarException "number expected");;

let rec fact tokens = 
  match tokens with
  | LParen::ts -> let (parens_expn, rest) = parens ts 0
                  in  (parse parens_expn, rest)
  | ts         -> num ts

and fun_fact tokens =
  match tokens with
  | (Operation Minus)::ts -> let (tree, rest) = fun_fact ts
                             in  (Uninode (Minus, tree), rest)
  | (Operation Sqrt)::ts  -> let (tree, rest) = fun_fact ts
                             in  (Uninode (Sqrt, tree), rest)
  | (Operation PreDivide)::ts -> let (tree1, rest1) = fun_fact ts in
                                 let (tree2, rest2) = fun_fact rest1
                                 in (Binode (tree1, Divide, tree2), rest2) 
  | ts                    -> fact ts

and term half_parsed = 
  match half_parsed with
  | (tree, (Operation Times)::ts) -> let (rtree, rrest) = fun_fact ts
                                     in term (Binode (tree, Times, rtree), rrest)
  | (tree, (Operation Divide)::ts) -> let (rtree, rrest) = fun_fact ts
                                     in term (Binode (tree, Divide, rtree), rrest)
  | (tree, (Operation Remainder)::ts) -> let (rtree, rrest) = fun_fact ts
                                     in term (Binode (tree, Remainder, rtree), rrest)
  | (tree, ts)                    -> (tree, ts)

and expn half_parsed = 
  match half_parsed with
  | (tree, (Operation Plus)::ts) -> let (rtree, rrest) = term (fun_fact ts)
                                     in expn (Binode (tree, Plus, rtree), rrest)
  | (tree, (Operation Minus)::ts) -> let (rtree, rrest) = term (fun_fact ts)
                                     in expn (Binode (tree, Minus, rtree), rrest)
  | (tree, ts)                    -> (tree, ts)

and parse tokens = let (tree, extra) = expn (term (fun_fact tokens))
                   in if extra <> [] then raise (ExtraException extra)
                      else tree;;

let rec integral f a b res = if res = 0. then 0.
                             else f (a+.(b-.a)/.res/.2.) *. (b-.a)/.res +. integral f (a+.(b-.a)/.res) b (res-.1.);;

let derivative f x dx = (f (x+.dx/.2.) -. f (x-.dx/.2.))/.dx;;


let rec eval tree =
  match tree with
  | (Binode(ltree, op, rtree)) -> let left = eval ltree and right = eval rtree
                                  in if   op = Plus then left +. right
                                  else if op = Minus then left -. right
                                  else if op = Times then left *. right
                                  else if op = Divide then left /. right
                                  else if op = Remainder then mod_float left right
                                  else raise (GrammarException "what binode")   
  | (Uninode(op, mtree))       -> let mid = eval mtree
                                  in if   op = Minus then -1. *. mid
                                  else if op = Sqrt then sqrt mid
                                  else raise (GrammarException "what uninode")
  | Leaf x                     -> x;;

let calculate latex = eval (parse (tokenize latex 0));;