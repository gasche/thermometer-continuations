(* first use the single-call, two-choices example in the paper, then

   one single call, but with a list unknown length

   we cannot pre-allocate an index in advance as we don't know what
   the length of the choice list will be!

   So we have to start with an "empty state", and the first call to
   "choose" will record the range of indices we will iterate on.
*)

let state = ref None

(* in case the list is empty, we need to abort => exception *)
exception Empty

(* auxiliary functions for indices in a list:
   start index, next index (or end), get at index

   (Jimmy: this replace your indexing-from-end scheme,
   it's perfectly equivalent but a bit easier to follow)
*)
let start_idx xs = (0, List.length xs)

let next_idx (k, len) =
  if k + 1 = len then None
  else Some (k + 1, len)

let get xs (k, len) = List.nth xs k

let choose = function
  | [] -> raise Empty
  | xs ->
    match !state with
    | None ->
      (* if no state, we are in the first call;
         create the index and store it in the state *)
      let i = start_idx xs in
      state := Some i;
      get xs i
    | Some i ->
      (* otherwise, we are in another call,
         get the index that was fixed for us *)
      get xs i

(* notice that `choose` leaves the index untouched,
   so it must be incremented by `withNondeterminism` instead;
   this mirrors the way `withNondeterminism` sets
   the `firstTime` reference in the boolean version. *)

let rec withNondeterminism f =
  let v = try [f ()] with Empty -> [] in
  match !state with
  | None -> 
    (* no state set after running f(): `choose` was not called at all *)
    v
  | Some i ->
    (* otherwise, we must iterate with the next index *)
    match next_idx i with
    | None ->
      (* no next index, return *)
      v
    | Some i' ->
      begin
        state := Some i';
        v @ withNondeterminism f
      end

(* many calls:

   more complex state structure

   at any given call to `node`, we may know what lays ahead of us
   (the "future", which corresponds to the past above), or be in new
   territory (the state has not been set)

   at each node, push what we did into the past, so that we know what
   to replay next
*)

let past = ref []
let future = ref []

(* auxiliary stack functions *)
let push stack x = (stack := x :: !stack)
let pop stack = match !stack with
  | [] -> None
  | x::xs -> stack := xs; Some x

let choose = function
  | [] -> raise Empty
  | xs ->
    (* checking the state => looking into the future *)
    match pop future with
    | None ->
      (* no future: start a new index and push it into the past *)
      let i = start_idx xs in
      push past i;
      get xs i
    | Some i ->
      (* future: push the choice into the past and take it *)
      push past i;
      get xs i

(* next_path works on the past, which has the deepest (most recent)
   choice first *)
let rec next_path = function
  | [] -> []
  | i::is ->
    (* if the most recent choice has terminated,
       peel it off from the path *)
    match next_idx i with
    | None -> next_path is
    | Some i' -> i'::is

let rec withNondeterminism f =
  let v = try [f ()] with Empty -> [] in
  (* next_path returns a most-recent-first path,
     we need to reverse it to get a root-first future *)
  let next_future = List.rev (next_path !past) in
  past := [];
  future := next_future;
  if !future = [] then
    (* if no future, return

       notice: at this point we have !past = [], !future = [],
       as at the beginning of the computation;
       one can call withNondeterminism several times in sequence
    *)
    v
  else v @ withNondeterminism f


(* but nested withNondeterminism calls don't work: if
   withNondeterminism is called in the middle of a replay, the 'future'
   stack is erased *)

(* safe nesting: stack of zippers (past * future) *)
let nest = ref []

let withNondeterminism f =
  (* by the way, let's use a tail-rec function *)
  let rec loop acc f =
    let v = try [f ()] with Empty -> [] in
    let acc = v @ acc in
    let next_future = List.rev (next_path !past) in
    past := [];
    future := next_future;
    if !future = [] then List.rev acc
    else loop acc f
  in
  (* before we run, save current !past and !future value *)
  push nest (!past, !future);
  past := [];
  future := [];
  let result = loop [] f in
  (* then restore them after the run *)
  match pop nest with
  | None -> assert false
  | Some (p, f) ->
    past := p;
    future := f;
    result


(* thermometers for replay-based shift/reset *)

(* at this point we stop showing code to explain what shift/reset are,
   as currently in the paper. *)

(* auxiliary universal stuff (I'm not sure how to motivate them well) *)
module type UNIVERSAL = sig
  type u
  val to_u : 'a -> u
  val from_u : u -> 'a
end

module Universal : UNIVERSAL = struct
  type u = Obj.t
  let to_u = Obj.repr
  let from_u = Obj.obj
end

(* control operators are tricky to type;
   we use a fixed answer type -- enough for our applications *)
module type Answer = sig type ans end

module type CONTROL = sig
    include Answer
    val reset : (unit -> ans) -> ans
    val shift : (('a -> ans) -> ans) -> 'a
end

module Control (Ans : Answer) : CONTROL with type ans = Ans.ans = struct
  include Ans

  (* represents a state of a node
  
     `choose [a, b, c]` would call its future with either a, b or c

     node state: the index of element to return


     `shift (fun k => e)` either starts computing `e`, or evaluates to `k v`
     for a `v` passed to `k` from within `e`

     node state:
     - Ret v: the continuation produced at this point was passed `v`
       (like choose, we must return v)
     - Enter: the body of the 'shift' at this point is being evaluated
  *)
  type frame = Ret of Universal.u | Enter

  exception Done of ans
  let nest = ref []
  let past = ref []
  let future = ref []

  (* in nondeterminism, each time we replay, we replay the whole
     expression

     with shift/reset we only replay the expression passed to the last
     reset (this is a *delimited* continuation), this is what cur_expr
     stores *)
  let cur_expr = ref (fun () -> assert false)

  (* because a continuation can be invoked after some effects have
     already been performed, `invoke_cont` generalizes `withNondetermism` 
     to take a computation to run `f` and its "past" `f_past`

     otherwise this is exactly like withNondeterminism
  *)
  let invoke_cont f f_past =
    push nest (!cur_expr, !past, !future);
    past := [];
    future := List.rev f_past;
    cur_expr := f;
    let res = try f () with Done x -> x in
    match pop nest with
    | None -> assert false
    | Some (prev_expr, prev_past, prev_future) ->
      cur_expr := prev_expr;
      past := prev_past;
      future := prev_future;
      res

  (* reset is just invoke_cont with no past *)
  let reset f = invoke_cont f []

  let shift f = match pop future with
    | Some (Ret u) ->
      (* ret u: just return u *)
      push past (Ret u);
      Universal.from_u u
    | Some Enter | None ->
      (* None: first time we run into this `shift`
         Enter: *)
      let our_past = !past in
      let our_expr = !cur_expr in
      push past Enter;
      let k v = invoke_cont our_expr (Ret (Universal.to_u v) :: our_past) in
      let v = f k in
      raise (Done v)
end

(* unit tests *)    
module Test = struct
  module C = Control(struct type ans = int end)
  open C

  let () = assert (1 + reset (fun () -> 2) = 3)
  let () = assert (1 + reset (fun () -> (2 + shift (fun k -> 3))) = 4)
  let () = assert (1 + reset (fun () -> (2 + shift (fun k -> k 3))) = 6)
  let () = assert (1 + reset (fun () -> (2 + shift (fun k -> k (k 3)))) = 8)
  let () = assert (1 + reset (fun () -> (2 + shift (fun k -> k (k 3)))) = 8)
  let () =
    assert
      (1 + reset (fun () ->
           (2 + reset (fun () ->
                3 + shift (fun k -> k (k 3)))))
       = 1 + (2 + (3 + (3 + 3))))
  let () =
    assert
      (1 + reset (fun () ->
           4 + shift (fun k1 -> 2 + reset (fun () ->
               3 * shift (fun k2 -> k1 (k2 3)))))
       = 1 + 2 + (4 + (3 * 3)))
  let () =
    assert
      (1 + reset (fun () ->
           4 + shift (fun k1 -> 2 + reset (fun () ->
               3 * shift (fun k2 -> k2 (k1 3)))))
       = 1 + (2 + 3 * (4 + 3)))
  let () =
    assert
      (1 + reset (fun () ->
           2 + shift (fun k1 ->
               3 * shift (fun k2 -> k2 (k1 10))))
       = 1 + 3 * (2 + 10))
end
