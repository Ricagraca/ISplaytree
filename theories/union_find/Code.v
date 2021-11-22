From iris_time.heap_lang Require Import notation lib.assert.

Notation ROOT x := (InjL x).
Notation ROOTV x := (InjLV x).
Notation LINK x := (InjR x).
Notation LINKV x := (InjRV x).

Notation "'match:' e0 'with' 'ROOT' ( r , v ) => e1 | 'LINK' x => e2 'end'" :=
  (Match e0
         "__x" (let: r%bind := Fst "__x" in let: v%bind := Snd "__x" in e1)
         x%bind e2)
  (e0, r, v, e1, x, e2 at level 200, only parsing) : expr_scope.

Definition make : val := λ: "v",
  ref (ROOT (#(mach_int_0), "v")).

Definition find : val := rec: "find" "x" :=
  match: !"x" with
    ROOT (<>, <>) => "x"
  | LINK "y" =>
    let: "z" := "find" "y" in
    "x" <- LINK "z";;
    "z"
  end.

Definition eq : val := λ: "x" "y",
  find "x" = find "y".

Definition get : val := λ: "x",
  let: "x" := find "x" in
  match: !"x" with
    ROOT (<>, "v") => "v"
  | LINK <> => assert: #false
  end.

Definition set : val := λ: "x" "v",
  let: "x" := find "x" in
  match: !"x" with
    ROOT ("r", <>) => "x" <- ROOT ("r", "v")
  | LINK <> => assert: #false
  end.

Definition link : val := λ: "x" "y",
  if: "x" = "y" then "x"
  else
    match: !"x" with
      ROOT ("rx", "vx") =>
        match: !"y" with
          ROOT ("ry", <>) =>
            if: "rx" < "ry" then
              "x" <- LINK "y";;
              "y"
            else if: "ry" < "rx" then
              "y" <- LINK "x";;
              "x"
            else
              "y" <- LINK "x";;
              "x" <- ROOT ("rx" + #mach_int_1, "vx");;
              "x"
        | LINK <> =>
          assert: #false
        end
    | LINK <> =>
        assert: #false
    end.

Definition union : val := λ: "x" "y",
  link (find "x") (find "y").
