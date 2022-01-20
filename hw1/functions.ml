
(* Return the larger of the two provided numbers *)
let max (n : int) (m : int) : int =
  if n > m then n else m;;

(* Determines the nth number in the Fibonacci sequence *)
let rec fibonacci (n : int) : int =
  if n <= 1 then n
  else (fibonacci (n - 1)) + (fibonacci (n - 2));;

(* Fibonacci Evaluation
(fibonacci 3)
if 3 <= 1 then 3 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))
if false then 3 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))
(fibonacci (3 - 1)) + (fibonacci (3 - 2))
(fibonacci 2) + (fibonacci 1)
(if 2 <= 1 then 2 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci 1)
(if false then 2 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci 1)
((fibonacci 2 - 1) + (fibonacci 2 - 2)) + (fibonacci 1)
((fibonacci 1) + (fibonacci 0)) + (fibonacci 1)
(((if 1 <= 1 then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2))) + (fibonacci 0))) + (fibonacci 1)
(((if true then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2))) + (fibonacci 0))) + (fibonacci 1)
(1 + (fibonacci 0)) + (fibonacci 1)
(1 + (if 0 <= 1 then 0 else (fibonacci (0 - 1)) + (fibonacci (0 - 2)))) + (fibonacci 1)
(1 + (if true then 0 else (fibonacci (0 - 1)) + (fibonacci (0 - 2)))) + (fibonacci 1)
(1 + 0) + (fibonacci 1)
1 + (fibonacci 1)
1 + (if 1 <= 1 then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2))))
1 + (if true then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2))))
1 + 1
2
*)