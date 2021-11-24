(**
  Non Deterministic Finite State Automaton
*)

module StateSet = Set.Make(Int)

module Triplet = struct
  type t = (int * char * int)
  let compare = compare
  let shift n (p, c, q) = (p + n, c, q + n)
end

module Relation = Set.Make(Triplet)

type nfa = {
  n_states: int; (** automaton has states 0...(states - 1) *)
  relation: Relation.t;
  initials: StateSet.t;
  finals: StateSet.t;
}

let dump f {n_states; relation; initials; finals} =
  let out = open_out f in
  Printf.fprintf out "Digraph {\n";
  StateSet.iter (fun s ->
    Printf.fprintf out "  %d [label = \"init(%d)\"];\n" s s
  ) initials;
  List.iter (fun s ->
    if StateSet.mem s finals then
      Printf.fprintf out "  %d [shape = doublecircle];\n" s
    else
      Printf.fprintf out "  %d [shape = circle];\n" s
  ) (List.init n_states Fun.id);
  Relation.iter (fun (p, c, q) ->
    Printf.fprintf out "  %d -> %d [label=\"%c\"];\n" p q c
  ) relation;
  Printf.fprintf out "}\n";
  close_out out


let shift (n : int) (a : nfa) = {
  a with
  relation = Relation.map (Triplet.shift n) a.relation;
  initials = StateSet.map ((+) n) a.initials;
  finals = StateSet.map ((+) n) a.finals;
}

let union a1 a2 : nfa =
  let a2 = shift a1.n_states a2 in
  { n_states = a1.n_states + a2.n_states
  ; relation = Relation.union a1.relation a2.relation
  ; initials = StateSet.union a1.initials a2.initials
  ; finals = StateSet.union a1.finals a2.finals
  }

let inter a1 a2 : nfa =
  let num p p' = p * a2.n_states + p' in
  let relation = Relation.fold (fun (p, c, q) rel ->
    Relation.fold (fun (p', c', q') rel' ->
      if c = c' then Relation.add (num p p', c, num q q') rel'
      else rel'
    ) a2.relation rel
  ) a1.relation Relation.empty
  in
  let finals = StateSet.fold (fun s rel ->
    StateSet.fold (fun s' rel' ->
      StateSet.add (num s s') rel'
    ) a2.finals rel
  ) a1.finals StateSet.empty
  in
  let initials = StateSet.fold (fun s rel -> 
    StateSet.fold (fun s' rel' ->
      StateSet.add (num s s') rel'
    ) a2.initials rel
  ) a1.initials StateSet.empty
  in
  { n_states = a1.n_states * a2.n_states
  ; relation
  ; initials
  ; finals
  }

let concat a1 a2 : nfa =
  let a2 = shift a1.n_states a2 in
  let relation = Relation.fold (fun (p, c, q) rel ->
    if StateSet.mem q a1.finals then
      StateSet.fold (fun i rel' ->
        Relation.add (p, c, i) rel'
      ) a2.initials rel
    else rel
  ) a1.relation (Relation.union a1.relation a2.relation)
  in
  { n_states = a1.n_states + a2.n_states
  ; relation
  ; finals = a2.finals
  ; initials = a1.initials
  }

let single_init a : nfa =
  if not StateSet.(is_empty (inter a.finals a.initials)) then
    failwith "single_init: cannot process automaton accepting 'ϵ'"
  else
  let relation = Relation.fold (fun (p, c, q) rel ->
    if StateSet.mem p a.initials then
      Relation.add (a.n_states, c, q) rel
    else
      rel
  ) a.relation a.relation in
  { n_states = a.n_states + 1
  ; relation
  ; finals = a.finals
  ; initials = StateSet.singleton a.n_states
  }

let omega a : nfa =
  let a = single_init a in
  let qf = StateSet.choose a.initials in
  let relation = Relation.fold (fun (p, c, q) rel ->
    if StateSet.mem q a.finals then
      Relation.add (p, c, qf) rel
    else rel
  ) a.relation a.relation in
  { n_states = a.n_states
  ; finals = a.initials
  ; initials = a.initials
  ; relation
  }

let succ (a : nfa) s =
  Relation.fold (fun (p, c, q) set ->
    if p = s then StateSet.add q set else set
  ) a.relation StateSet.empty

let pred (a : nfa) s =
  Relation.fold (fun (p, c, q) set ->
    if q = s then StateSet.add p set else set
  ) a.relation StateSet.empty

(**
    Computes the least fixpoint of an increasing function [StateSet.t -> StateSet.t]
    starting from a pre fixpoint [s0]
*)
let fix f s0 =
  let rec iterate s =
    let fs = f s in
    if StateSet.equal fs s then s
    else iterate fs
  in iterate s0

(**
  Computes the reachable states starting from state [s0] in automaton [a]
*)
let reach (a : nfa) s0 =
  let open StateSet in
  let image states =
    fold (fun s -> union (succ a s)) states empty
  in
  fix image (singleton s0)

let a1 =
  { n_states = 2
  ; relation = Relation.of_list [(0, 'a', 1); (1, 'd', 0)]
  ; initials = StateSet.singleton 0
  ; finals = StateSet.singleton 0
  }

let a2 =
  { n_states = 2
  ; relation = Relation.of_list [(0, 'a', 1); (1, 'c', 0)]
  ; initials = StateSet.singleton 0
  ; finals = StateSet.singleton 0
  }

let a3 =
  { n_states = 2
  ; relation = Relation.of_list [(0, 'b', 0); (0, 'a', 1)]
  ; initials = StateSet.singleton 0
  ; finals = StateSet.singleton 1
  }

let () =
  inter a1 a2 |> dump "inter.dot";
  union a1 a2 |> dump "union.dot";
  concat a1 a2 |> dump "concat.dot";
  single_init a3 |> dump "single_init.dot";
  omega a3 |> dump "omega.dot";
  StateSet.iter (Printf.printf "(%d)\n") (reach (omega a3) 2)