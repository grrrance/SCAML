  $ ./demoParse.exe <<-EOF
  > let test = 1
  > EOF
  [(Define ("test", (Value ((VInt 1), )), ))]

  $ ./demoParse.exe <<-EOF
  > let test = true
  > EOF
  [(Define ("test", (Value ((VBool true), )), ))]

  $ ./demoParse.exe <<-EOF
  > let then = true
  > EOF
  Parsing error

  $ ./demoParse.exe <<-EOF
  > let test = 1 + 2 * 3 - 10
  > EOF
  [(Define ("test",
      (BinOp ((Value ((VInt 1), )),
         (BinOp ((BinOp ((Value ((VInt 2), )), (Value ((VInt 3), )), Mul, )),
            (Value ((VInt 10), )), Sub, )),
         Add, )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let test = 1 + 2 * 3 / 10 - 10 % 5
  > EOF
  [(Define ("test",
      (BinOp ((Value ((VInt 1), )),
         (BinOp (
            (BinOp ((Value ((VInt 2), )),
               (BinOp ((Value ((VInt 3), )), (Value ((VInt 10), )), Div, )),
               Mul, )),
            (BinOp ((Value ((VInt 10), )), (Value ((VInt 5), )), Mod, )), Sub, 
            )),
         Add, )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let test var = 10
  > EOF
  [(Define ("test", (Func ("var", (Value ((VInt 10), )), )), ))]

  $ ./demoParse.exe <<-EOF
  > let id var = var
  > EOF
  [(Define ("id", (Func ("var", (Variable ("var", )), )), ))]

  $ ./demoParse.exe <<-EOF
  > let id var = var < 10 && var < 5 || var <> 4
  > EOF
  [(Define ("id",
      (Func ("var",
         (BinOp (
            (BinOp (
               (BinOp ((Variable ("var", )), (Value ((VInt 10), )), Less, )),
               (BinOp ((Variable ("var", )), (Value ((VInt 5), )), Less, )),
               And, )),
            (BinOp ((Variable ("var", )), (Value ((VInt 4), )), NotEqual, )),
            Or, )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let id var = (var < 10 && var < 5) || var <> 4
  > EOF
  [(Define ("id",
      (Func ("var",
         (BinOp (
            (BinOp (
               (BinOp ((Variable ("var", )), (Value ((VInt 10), )), Less, )),
               (BinOp ((Variable ("var", )), (Value ((VInt 5), )), Less, )),
               And, )),
            (BinOp ((Variable ("var", )), (Value ((VInt 4), )), NotEqual, )),
            Or, )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let id var = (var < 10 && var < 5) || var <> 4
  > EOF
  [(Define ("id",
      (Func ("var",
         (BinOp (
            (BinOp (
               (BinOp ((Variable ("var", )), (Value ((VInt 10), )), Less, )),
               (BinOp ((Variable ("var", )), (Value ((VInt 5), )), Less, )),
               And, )),
            (BinOp ((Variable ("var", )), (Value ((VInt 4), )), NotEqual, )),
            Or, )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let var x = if x > 15 || x < 10 then x else 9
  > EOF
  [(Define ("var",
      (Func ("x",
         (IfThenElse (
            (BinOp (
               (BinOp ((Variable ("x", )), (Value ((VInt 15), )), More, )),
               (BinOp ((Variable ("x", )), (Value ((VInt 10), )), Less, )), Or, 
               )),
            (Variable ("x", )), (Value ((VInt 9), )), )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let var x = fun y z -> (x + y * z)
  > EOF
  [(Define ("var",
      (Func ("x",
         (Func ("y",
            (Func ("z",
               (BinOp ((Variable ("x", )),
                  (BinOp ((Variable ("y", )), (Variable ("z", )), Mul, )), Add, 
                  )),
               )),
            )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let rec func x =
  > if x > 15 then x else func (x + x)
  > EOF
  [(RecDefine ("func",
      (Func ("x",
         (IfThenElse (
            (BinOp ((Variable ("x", )), (Value ((VInt 15), )), More, )),
            (Variable ("x", )),
            (Apply ((Variable ("func", )),
               (BinOp ((Variable ("x", )), (Variable ("x", )), Add, )), )),
            )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let f x =
  >   let rec g y =
  >      if y <= 1 then x 
  >      else
  >         x * y + g (y - 1)
  >   in g x
  > EOF
  [(Define ("f",
      (Func ("x",
         (RecLetIn ("g",
            (Func ("y",
               (IfThenElse (
                  (BinOp ((Variable ("y", )), (Value ((VInt 1), )), LessOrEq, 
                     )),
                  (Variable ("x", )),
                  (BinOp (
                     (BinOp ((Variable ("x", )), (Variable ("y", )), Mul, )),
                     (Apply ((Variable ("g", )),
                        (BinOp ((Variable ("y", )), (Value ((VInt 1), )), Sub, 
                           )),
                        )),
                     Add, )),
                  )),
               )),
            (Apply ((Variable ("g", )), (Variable ("x", )), )), )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let func x =
  >   let test1 = 15
  >   in
  >   let rec test2 y =
  >     if y > 10 then 30 + test1
  >     else test1 + test2 (y + 1)
  >   in
  >   test1 + test2 x
  > EOF
  [(Define ("func",
      (Func ("x",
         (LetIn ("test1", (Value ((VInt 15), )),
            (RecLetIn ("test2",
               (Func ("y",
                  (IfThenElse (
                     (BinOp ((Variable ("y", )), (Value ((VInt 10), )), More, 
                        )),
                     (BinOp ((Value ((VInt 30), )), (Variable ("test1", )),
                        Add, )),
                     (BinOp ((Variable ("test1", )),
                        (Apply ((Variable ("test2", )),
                           (BinOp ((Variable ("y", )), (Value ((VInt 1), )),
                              Add, )),
                           )),
                        Add, )),
                     )),
                  )),
               (BinOp ((Variable ("test1", )),
                  (Apply ((Variable ("test2", )), (Variable ("x", )), )), Add, 
                  )),
               )),
            )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let rec fac n = if n = 1 then 1 else n * fac (n - 1)
  > EOF
  [(RecDefine ("fac",
      (Func ("n",
         (IfThenElse (
            (BinOp ((Variable ("n", )), (Value ((VInt 1), )), Equal, )),
            (Value ((VInt 1), )),
            (BinOp ((Variable ("n", )),
               (Apply ((Variable ("fac", )),
                  (BinOp ((Variable ("n", )), (Value ((VInt 1), )), Sub, )), )),
               Mul, )),
            )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let fac n =
  >   let rec helper num acc =
  >     if num = 1 then acc
  >     else helper (num - 1) (acc * num)
  >   in
  >   helper n 1
  > EOF
  [(Define ("fac",
      (Func ("n",
         (RecLetIn ("helper",
            (Func ("num",
               (Func ("acc",
                  (IfThenElse (
                     (BinOp ((Variable ("num", )), (Value ((VInt 1), )), Equal, 
                        )),
                     (Variable ("acc", )),
                     (Apply (
                        (Apply ((Variable ("helper", )),
                           (BinOp ((Variable ("num", )), (Value ((VInt 1), )),
                              Sub, )),
                           )),
                        (BinOp ((Variable ("acc", )), (Variable ("num", )),
                           Mul, )),
                        )),
                     )),
                  )),
               )),
            (Apply ((Apply ((Variable ("helper", )), (Variable ("n", )), )),
               (Value ((VInt 1), )), )),
            )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let simple_func x = x + 1
  > let if_func x = if x > 0 then true else false
  > let val = 15
  > EOF
  [(Define ("simple_func",
      (Func ("x", (BinOp ((Variable ("x", )), (Value ((VInt 1), )), Add, )), )),
      ));
    (Define ("if_func",
       (Func ("x",
          (IfThenElse (
             (BinOp ((Variable ("x", )), (Value ((VInt 0), )), More, )),
             (Value ((VBool true), )), (Value ((VBool false), )), )),
          )),
       ));
    (Define ("val", (Value ((VInt 15), )), ))]

  $ ./demoParse.exe <<-EOF
  > let f = (fun x ->
  >  let g x = x in 
  > (if x then g else (fun y -> y + 5)) 4)
  > EOF
  [(Define ("f",
      (Func ("x",
         (LetIn ("g", (Func ("x", (Variable ("x", )), )),
            (Apply (
               (IfThenElse ((Variable ("x", )), (Variable ("g", )),
                  (Func ("y",
                     (BinOp ((Variable ("y", )), (Value ((VInt 5), )), Add, )), 
                     )),
                  )),
               (Value ((VInt 4), )), )),
            )),
         )),
      ))
    ]

  $ ./demoParse.exe <<-EOF
  > let f = (let g x = x in g) 42
  > EOF
  [(Define ("f",
      (Apply (
         (LetIn ("g", (Func ("x", (Variable ("x", )), )), (Variable ("g", )), 
            )),
         (Value ((VInt 42), )), )),
      ))
    ]
