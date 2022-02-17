open Printf


let t (name : string) (program : string) (expected : string) = 
  let oc = open_out (Printf.sprintf "hw4/input/do_pass/%s.cobra" name) in
    (Printf.fprintf oc "%s\n" expected);
    close_out oc;;
let te (name : string) (program : string) (expected : string) = 
  let oc = open_out (Printf.sprintf "hw4/input/do_err/%s.cobra" name) in
    (Printf.fprintf oc "%s\n" expected);
    close_out oc;;

let main =
  t "forty_one" "41" "41";
  t "basic_let" "let a = 1 in a" "1";

  t "if1" "if 5: 4 else: 2" "4";
  t "if2" "if 0: 4 else: 2" "2";

  t "multi_let" "let a = 1, b = a in b" "1";

  t "let_in_let_in_if_it_1"
    ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
      "(let abcd = 10 in add1(abcd)) " ^
      "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
    "0";

  t "let_in_let_in_if_it_2"
    ("if (let x = 4, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
      "(let abcd = 10 in add1(abcd)) " ^
      "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
    "11";

  t "let_in_let_in_if_it_3"
    ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
      "(let abcd = 10 in add1(abcd)) " ^
      "else: (let x = 1, y = sub1(if x: x else: 2) in y)")
    "0";

  t "let_in_let_in_if_it_4"
    ("if (let x = 4, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
      "(let abcd = 10 in add1(abcd)) " ^
      "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
    "11";


  t "complex_conditional_it_1" 
    ("(let x = (if (5 - 10): sub1(5 + 5) else: sub1(6 * 2)) in " ^
      "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "22";

  t "complex_conditional_it_2" 
    ("(let x = (if (5 - 5): sub1(5 + 5) else: sub1(6 * 2)) in " ^
      "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "26";

  t "complex_conditional_it_3" 
    ("(let x = (if (5 - 10): sub1(5 + 5) else: sub1(6 * 2)) in " ^
      "(let y = sub1(if (x * 1): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "25";

  t "complex_conditional_it_4" 
    ("(let x = (if (5 - 5): sub1(5 + 5) else: sub1(6 * 2)) in " ^
      "(let y = sub1(if (x * 1): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "31";

  t "wrapped_let_and_if"
    ("((let x = 10, z = (let x = (x + 1), y = (x * 2) in x - y), " ^
      "y = (if z: 1 else: z) in (if sub1(y): z else: (z - y))) - " ^
      "(if (let abcd = 25 in abcd): 11 else: -11))") "-23";
