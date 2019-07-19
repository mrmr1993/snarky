open Core
open Snarky

(* Welcome!

   Snarky is a library for constructing R1CS SNARKs.

   TODO: Explanation of R1CSs, how it makes addition and scalar mult 'free' but
   multiplication of variables costs 1.
*)
(* 0. First we instantiate Snarky with a 'backend' *)
module Impl = Snark.Make (Backends.Bn128.Default)
open Impl

(* 1. There is a monad called 'Checked'. It has an extra type parameter but let's
  ignore that for now *)

let _foo () : (unit, _) Checked.t = Checked.return ()

(* The point of this monad is to describe "checked computations"
   which are computations that may "request" values from their environment,
   and make assertions about values that arise in the computation.

   You "run" Checked.t's in two ways:
   1. To generate a constraint system for the SNARK
   2. To generate proofs.

   We'll see exactly how this works later.

   First let's understand "field var"s which are the main primitive type we
   have access to in Checked.t's.
*)
(* A [Field.t] represents an element of the finite field of order [Field.size]
   It is a prime order field so you can think about it as "integers mod Field.size".
*)

let () =
  let x = Field.of_int 23 in
  let x_cubed = Field.mul x (Field.square x) in
  let z = Field.(x_cubed / x) in
  assert (Field.equal z (Field.square x))

(* Try seeing what operations there are in the [Field] module by using
   your editor's auto-completion feature
*)
(* Inside Checked.t's we work with "Field.var"s. These are sort of like
   Field.t's but we can make assertions about them.

   Field.Checked provides "Checked" versions of the usual field operations.
*)
(* [assert_equal : Field.var -> Field.var -> (unit, _) Checked.t] lets us
   make an assertion that two field elements are equal.

   Here we assert that [x] is a square root of 9.
*)
let assert_is_square_root_of_9 (x : Field.Var.t) : (unit, _) Checked.t =
  let%bind x_squared = Field.Checked.mul x x in
  Field.Checked.Assert.equal x_squared (Field.Var.constant (Field.of_int 9))

(* Exercise 1:
   Write a function
   [assert_is_cube_root_of_1 : Field.var -> (unit, _) Checked.t]
   that asserts its argument is a cube root of 1.

   Aside:
   In finite fields there may be either 1 or 3 cube roots of 1.
   This is because

   x^3 - 1 = (x - 1)(x^2 + x + 1)

   so if [x^2 + x + 1] has a root in the field, then we will get
   another cube root of 1. By quadratic formula,

   x^2 + x + 1 = 0 iff
   x = ( -1 +/- sqrt (1 - 4) ) / 2

   so if sqrt(1 - 4) = sqrt(-3) exists in the field then there will
   be two additional cube roots of 1.
*)
(* In this field, it happens to be the case that -3 is a square. *)
let () = assert (Field.is_square (Field.of_int (-3)))

let assert_is_cube_root_of_1 (x : Field.Var.t) =
  let%bind x2 = Field.Checked.mul x x in
  let%bind x3 = Field.Checked.mul x2 x in
  Field.Checked.Assert.equal x3 (Field.Var.constant Field.one)

let cube_root_of_1 =
  let open Field in
  (of_int (-1) + sqrt (of_int (-3))) / of_int 2

let exercise1 () =
  (* Before we generate a constraint system or a proof for our checked
     computation we must first specify the "data spec" of the input.

     This is actually an HList which we can represent in OCaml by overriding the
     list type constructors. We also need to make input a function over unit due
     to value restriction reasons.

     Here our function `assert_is_cube_root_of_1` takes a single Field.var as
     input. The type of that var is `Field.typ`.
   *)
  let input () = Data_spec.[Field.typ] in
  (* Now we generate a keypair that we can use produce and verify proofs *)
  let keypair =
    generate_keypair ~exposing:(input ()) assert_is_cube_root_of_1
  in
  (* Now we prove: Here is an input to `assert_is_cube_root_of_1` such that the
     checked computation terminates without failing any assertions. In other
     words, there exists some cube_root_of_1.
   *)
  let proof =
    prove (Keypair.pk keypair) (input ()) () assert_is_cube_root_of_1
      cube_root_of_1
  in
  (* We can verify a proof as follows *)
  let is_valid = verify proof (Keypair.vk keypair) (input ()) cube_root_of_1 in
  printf !"is %{sexp:Field.t} a cube root of 1? %b\n%!" cube_root_of_1 is_valid

(* Exercise 1: Comment this out when you're ready to test it! *)
let () = exercise1 ()

let exercise2 () =
  (* Now let's prove that there are two cube roots of 1. *)
  let distinct_cube_roots_of_1 x y =
    let%map () = assert_is_cube_root_of_1 x
    and () = assert_is_cube_root_of_1 y
    and () = Field.Checked.Assert.not_equal x y in
    ()
  in
  (* Exercise 2:
     Now you try: Creating a data spec, keypair, proof, and verifying that proof
     for `distinct_cube_roots_of_1`.
   *)
  let another_cube_root_of_1 = Field.mul cube_root_of_1 cube_root_of_1 in
  let input () = Data_spec.[Field.typ; Field.typ] in
  let keypair =
    generate_keypair ~exposing:(input ()) distinct_cube_roots_of_1
  in
  let proof =
    prove (Keypair.pk keypair) (input ()) () distinct_cube_roots_of_1
      cube_root_of_1 another_cube_root_of_1
  in
  let is_valid =
    verify proof (Keypair.vk keypair) (input ()) cube_root_of_1
      another_cube_root_of_1
  in
  printf
    !"Are %{sexp:Field.t} and %{sexp:Field.t} two distinct cube roots of 1? %b\n\
      %!"
    cube_root_of_1 another_cube_root_of_1 is_valid

(* Exercise 2: Comment this out when you're ready to test it! *)
let () = exercise2 ()

(* We can encode other data types in terms of the underlying fields. An
   extremely useful one is boolean values -- true and false.

   Within our field, a Boolean is a Field element that is either zero or one.
   With this simple concept, we can start writing checked programs that make
   decisions!

   For example, `ifeqxy_x_else_z` checks if x and y are equal and if so
   returns x. If not, we return z.

   This is also an example of a Checked computation that doesn't return unit!
*)
let ifeqxy_x_else_z x y z =
  let%bind b = Field.Checked.equal x y in
  Field.Checked.if_ b ~then_:x ~else_:z

(* We can combine booleans in the usual ways: `a && b` for 'and', `a || b`
   for 'or'.
*)
let if_both x y a b =
  let%bind x_and_y = Boolean.(x && y) in
  Field.Checked.if_ x_and_y ~then_:a ~else_:b

(* Exercise 3:
   Write a function
   [zero_or_inverse : Field.var -> (Field.var, _) Checked.t]
   that returns zero if the input is zero, or the inverse of the input
   otherwise.
*)
let zero_or_inverse (x : Field.Var.t) =
  let%bind b = Field.Checked.equal x (Field.Var.constant Field.zero) in
  let%bind invertable =
    Field.Checked.if_ b ~then_:(Field.Var.constant Field.one) ~else_:x
  in
  let%bind inverse = Field.Checked.inv invertable in
  Field.Checked.if_ b ~then_:x ~else_:inverse

let exercise3 () =
  (* Unchecked reference implementation. *)
  let zero_or_inverse_unchecked x =
    let b = Field.equal x Field.zero in
    let invertable = if b then Field.one else x in
    if b then x else Field.inv invertable
  in
  (* Check the value matches [expected_value]. *)
  let matches_unchecked x expected_value =
    let%bind y = zero_or_inverse x in
    Field.Checked.Assert.equal y expected_value
  in
  let input () = Data_spec.[Field.typ; Field.typ] in
  let keypair = generate_keypair ~exposing:(input ()) matches_unchecked in
  let proof x =
    prove (Keypair.pk keypair) (input ()) () matches_unchecked x
      (zero_or_inverse_unchecked x)
  in
  let proof_0 = proof Field.zero in
  let proof_1 = proof Field.one in
  let proof_15 = proof (Field.of_int 15) in
  let is_valid proof x =
    verify proof (Keypair.vk keypair) (input ()) x
      (zero_or_inverse_unchecked x)
  in
  let is_valid_0 = is_valid proof_0 Field.zero in
  let is_valid_1 = is_valid proof_1 Field.one in
  let is_valid_15 = is_valid proof_15 (Field.of_int 15) in
  printf "Matched expected output for\n0? %b\n1? %b\n15? %b\n" is_valid_0
    is_valid_1 is_valid_15

(* Exercise 3: Comment this out when you're ready to test it! *)
let () = exercise3 ()

(* So far, the only data we have passed to [prove] have been Field elements.
   To pass other kinds of data, we will need to change the values that we pass
   as the [Data_spec].

   The values in our [Data_spec] list are [Typ.t]s, which tell [prove] how to
   convert our normal data into [Field.Var.t]s.

   For example, [Boolean.typ] has type [(Boolean.var, bool) Typ.t]; this tells
   us that we can pass a [bool] value to [prove] and it will turn it into a
   [Boolean.var].

   Exercise 4:
   Create a Data_spec for [either].
*)
let exercise4 () =
  let either x y =
    let%bind z = Boolean.(x && y) in
    Boolean.Assert.is_true z
  in
  let input () = Data_spec.[Boolean.typ; Boolean.typ] in
  let keypair = generate_keypair ~exposing:(input ()) either in
  let proof = prove (Keypair.pk keypair) (input ()) () either true true in
  let is_valid proof x y = verify proof (Keypair.vk keypair) (input ()) x y in
  let proved x y = is_valid proof x y in
  printf
    "Proved that:\n true && true is true? %b\n true && false is true? %b\n"
    (proved true true) (proved true false)

(* Exercise 4: Comment this out when you're ready to test it! *)
let () = exercise4 ()

(* We can encode richer data types in the same way; as long as we can tell
   [prove] how to turn our OCaml value into field elements with a [Typ.t], we
   can pass any value we like!

   The [Typ] module has some useful functions for building new [Typ.t]s out of
   [Typ.t]s we already have.

   Exercise 5:
   Fill in [product] below, and use [Typ.list] to create a proof from
   [product_equals] that it gives the correct value.

   Hint: the functions in [Checked.List] are useful for working with checked
   functions over lists!
*)

let product (l : Field.Var.t list) : (Field.Var.t, _) Checked.t =
  List.fold l
    ~init:(Checked.return (Field.Var.constant Field.one))
    ~f:(fun product term ->
      let%bind product = product in
      Field.Checked.mul product term )

let product_equals (l : Field.Var.t list) (expected_total : Field.Var.t) =
  let%bind total = product l in
  Field.Checked.Assert.equal total expected_total

let product_unchecked (l : Field.t list) =
  List.fold ~init:Field.one ~f:Field.mul l

let exercise5 () =
  let input () = Data_spec.[Typ.list ~length:5 Field.typ; Field.typ] in
  let keypair = generate_keypair ~exposing:(input ()) product_equals in
  let proof l expected_total =
    prove (Keypair.pk keypair) (input ()) () product_equals l expected_total
  in
  let is_valid proof l expected_total =
    verify proof (Keypair.vk keypair) (input ()) l expected_total
  in
  let proved (l : int list) =
    let l : Field.t list = List.map ~f:Field.of_int l in
    let expected_total = product_unchecked l in
    is_valid (proof l expected_total) l expected_total
  in
  printf "Does product [1; 2; 3; 4; 5] = 120? %b\n" (proved [1; 2; 3; 4; 5])

(* Exercise 5: Comment this out when you're ready to test it! *)
let () = exercise5 ()

(* Exercise 6:
   Adapt your solution to exercise 5 to create a checked version of
   [product_triple] below.
*)

let product_triple ((x, y, z) : Field.t * Field.t * Field.t) : Field.t =
  Field.(x * y * z)

let product_triple_checked
    ((x, y, z) : Field.Var.t * Field.Var.t * Field.Var.t) :
    (Field.Var.t, _) Checked.t =
  let%bind xy = Field.Checked.mul x y in
  Field.Checked.mul xy z

let product_triple_equals triple (expected_total : Field.Var.t) =
  let%bind total = product_triple_checked triple in
  Field.Checked.Assert.equal total expected_total

let exercise6 () =
  let input () =
    Data_spec.[Typ.tuple3 Field.typ Field.typ Field.typ; Field.typ]
  in
  let keypair = generate_keypair ~exposing:(input ()) product_triple_equals in
  let proof = prove (Keypair.pk keypair) (input ()) () product_triple_equals in
  let is_valid proof = verify proof (Keypair.vk keypair) (input ()) in
  let proved (x, y, z) =
    let triple = (Field.of_int x, Field.of_int y, Field.of_int z) in
    let expected_total = product_triple triple in
    is_valid (proof triple expected_total) triple expected_total
  in
  printf "Does product (2, 3, 5) = 30? %b\n" (proved (2, 3, 5))

(* Exercise 6: Comment this out when you're ready to test it! *)
let () = exercise6 ()

(* At this point, we have covered one way to pass data to a checked
   computation: describing what types the data has in our [Data_spec], and
   then passing the data into [prove]. This works perfectly well, but we have
   to hand the same data to the verifier before they can check our proof! To
   avoid handing over data that we want to keep 'secret', we need a different
   strategy.

   The most general way to do this is using the [exists] function. It takes a
   [Typ.t] argument, so that it knows how to translate the data, and two
   (optional) arguments
   * [~compute] passes a computation of type [('value, _) As_prover.t] which
     describes how to compute the value
   * [~request] passes a computation of type
     [('value Request.t, _) As_prover.t], which describes how to build a
     'request' for the a value of type ['value].

   For now, we will focus on the [~compute] argument.

   Exercise 7:
   Rework your solution to exercise 5 to provide a proof that [product] and
   [product_unchecked] return the same value, but without exposing the
   result from [product_unchecked].
*)

let product (l : Field.Var.t list) : (Field.Var.t, _) Checked.t =
  List.fold l
    ~init:(Checked.return (Field.Var.constant Field.one))
    ~f:(fun product term ->
      let%bind product = product in
      Field.Checked.mul product term )

let product_unchecked (l : Field.t list) =
  List.fold ~init:Field.one ~f:Field.mul l

let product_equals (l : Field.Var.t list) =
  let%bind total = product l in
  let%bind expected_total =
    exists Field.typ
      ~compute:
        As_prover.(
          (* Everything in this block is run 'as the prover'.

             This means that we have special powers, like reading the values
             from our checked computation back into normal OCaml values.
          *)
          let%map l = read (Typ.list ~length:(List.length l) Field.typ) l in
          (* Now we have l back as a [Field.t list], so we can call
             [product_unchecked] on it.
          *)
          product_unchecked l)
  in
  Field.Checked.Assert.equal total expected_total

let exercise7 () =
  let input () = Data_spec.[Typ.list ~length:5 Field.typ] in
  let keypair = generate_keypair ~exposing:(input ()) product_equals in
  let proof = prove (Keypair.pk keypair) (input ()) () product_equals in
  let is_valid proof = verify proof (Keypair.vk keypair) (input ()) in
  let proved (l : int list) =
    let l : Field.t list = List.map ~f:Field.of_int l in
    is_valid (proof l) l
  in
  printf
    "Have we proved that we've calculated the product of the list [1; 2; 3; \
     4; 5]? %b\n"
    (proved [1; 2; 3; 4; 5])

(* Exercise 7: Comment this out when you're ready to test it! *)
let () = exercise7 ()

(* Now we can say that a value 'exists' without giving it away to the verifier,
   but we have to say right there in our checked computation how we're going to
   work it out.

   If we don't have all the information we need yet, we can build a Request for
   it instead, and use [exists ~request] to send it. New kinds of request can
   be made by extending the [Request.t] type.

   When we are ready to handle the request, we use the [handle] function.
   A handler looks like [fun (With {request; respond}) -> ...], where [request]
   is the request received and respond lets us send back the new value.

   Exercise 8:
   Fill in [in_list] and [choose_two_from_list].
*)

(* Add a new type of request [Choose_two_from_list], which takes an ['a list].
   Handlers for this request have to return a value of type ['a].
*)
type _ Request.t += Choose_two_from_list : 'a list -> ('a * 'a) Request.t

let in_list (x : Field.Var.t) (l : Field.Var.t list) =
  (* Assert that x is equal to one of the values in l. *)
  let%bind x_in_l =
    List.fold l ~init:(Checked.return Boolean.false_) ~f:(fun in_prefix y ->
        let%bind in_prefix = in_prefix in
        let%bind x_eq_y = Field.Checked.equal x y in
        Boolean.(in_prefix || x_eq_y) )
  in
  Boolean.Assert.is_true x_in_l

let choose_two_from_list (l : Field.Var.t list) =
  exists
    Typ.(Field.typ * Field.typ)
    ~request:
      As_prover.(
        (* Read the values from l and create a [Choose_two_from_list] request
           with them. *)
        let%map l = read Typ.(list ~length:(List.length l) Field.typ) l in
        Choose_two_from_list l)

let chosen_two_different (l : Field.Var.t list) =
  let%bind choice1, choice2 = choose_two_from_list l in
  let%bind () = in_list choice1 l in
  let%bind () = in_list choice2 l in
  Field.Checked.Assert.not_equal choice1 choice2

let exercise8 () =
  let input () = Data_spec.[Typ.list ~length:5 Field.typ] in
  let keypair = generate_keypair ~exposing:(input ()) chosen_two_different in
  let secret1 = 1 in
  let secret2 = 3 in
  let handled_chosen_two_different l =
    (* Add a handler for our [Choose_two_from_list] request *)
    handle (chosen_two_different l) (fun (With {request; respond}) ->
        match request with
        | Choose_two_from_list l ->
            let choice1 = List.nth_exn l secret1 in
            let choice2 = List.nth_exn l secret2 in
            respond (Provide (choice1, choice2))
        | _ ->
            unhandled )
  in
  let proof l =
    prove (Keypair.pk keypair) (input ()) () handled_chosen_two_different l
  in
  let is_valid proof l = verify proof (Keypair.vk keypair) (input ()) l in
  let proved (l : int list) =
    let l : Field.t list = List.map ~f:Field.of_int l in
    is_valid (proof l) l
  in
  printf "Have we chosen two different values from list [1; 2; 3; 4; 5]? %b\n"
    (proved [1; 2; 3; 4; 5])

(* Exercise 8: Comment this out when you're ready to test it! *)
let () = exercise8 ()

module Exercise9 = struct
  (* We can define a matrix over some ring as follows *)
  module Matrix (R : sig
    type t [@@deriving sexp]

    val zero : t

    val mul : t -> t -> t

    val add : t -> t -> t
  end) =
  struct
    type t = R.t array array [@@deriving sexp]

    let rows t = Array.length t

    let row t i = t.(i)

    let col t i = Array.map t ~f:(fun xs -> xs.(i))

    let cols t = Array.length t.(0)

    let mul a b =
      (* n x m * m x p -> n x p *)
      assert (cols a = rows b) ;
      Array.init (rows a) ~f:(fun i ->
          Array.init (cols b) ~f:(fun j ->
              Array.fold2_exn (row a i) (col b j) ~init:R.zero
                ~f:(fun acc aik bkj -> R.add acc (R.mul aik bkj)) ) )
  end

  (* A Field is a ring *)
  module Mat = Matrix (Field)

  (* We can multiply *)
  let a =
    Field.
      [|[|of_int 1; of_int 2; of_int 3|]; [|of_int 4; of_int 5; of_int 6|]|]

  let b =
    let open Field in
    [|[|of_int 1; of_int 2|]; [|of_int 3; of_int 4|]; [|of_int 5; of_int 6|]|]

  let () = printf !"Result %{sexp: Mat.t}\n%!" (Mat.mul a b)

  (* Exercise 9:
     To bring everything together, we want to prove something more substantial.
     Here, we will build a program that
     * creates a secret matrix
     * squares it
     * proves that it knows the square root of the result
     * reveals that result and the proof to the verifier.

     To start, fill in [random_matrix], making sure that the number of rows and
     columns in the matrix are the same.
     (Feel free to hard-code a matrix here to start with; it makes it much
     easier to track down any small bugs!)
  *)
  let random_matrix ~rows ~cols =
    Array.init rows ~f:(fun _ -> Array.init cols ~f:(fun _ -> Field.random ()))

  module Array_iter (M : Monad.S2) = struct
    let rec loop min max ~f =
      let open M.Let_syntax in
      if min < max then
        let%bind () = f min in
        loop (min + 1) max ~f
      else M.return ()

    let init count ~f =
      if count <= 0 then M.return [||]
      else
        let open M.Let_syntax in
        (* Calculate the initial value, so we have something to pre-fill the
           array with. For most types, OCaml will use pointers and this
           pre-filling will have no allocation overhead.
        *)
        let%bind x0 = f 0 in
        let array = Array.create ~len:count x0 in
        (* Overwrite the values in subsequent array positions to the desired
           values.
        *)
        let%map () =
          loop 1 count ~f:(fun i ->
              let%map x = f i in
              array.(i) <- x )
        in
        array

    let iter array ~f = loop 0 (Array.length array) ~f:(fun i -> f array.(i))

    let iter2 array1 array2 ~f =
      let len = Array.length array1 in
      assert (len = Array.length array2) ;
      loop 0 len ~f:(fun i -> f array1.(i) array2.(i))
  end

  module Checked_array = Array_iter (Checked)

  module Mat_checked = struct
    type t = Field.Var.t array array

    let rows t = Array.length t

    let row t i = t.(i)

    let col t i = Array.map t ~f:(fun xs -> xs.(i))

    let cols t = Array.length t.(0)

    (* Next, we need to make a checked version of [Matrix.mul] from above.
       This should feel familiar: we did a very similar thing when we were
       finding the product of a list!
     *)
    let mul : t -> t -> (t, _) Checked.t =
     fun a b ->
      assert (cols a = rows b) ;
      Checked_array.init (rows a) ~f:(fun i ->
          Checked_array.init (cols b) ~f:(fun j ->
              Array.fold2_exn (row a i) (col b j)
                ~init:(Checked.return (Field.Var.constant Field.zero))
                ~f:(fun acc aik bkj ->
                  let%map acc = acc and p = Field.Checked.mul aik bkj in
                  Field.Var.add acc p ) ) )

    module Assert = struct
      (* Now, we want a way to say that two matrices are equal. *)
      let equal : t -> t -> (unit, _) Checked.t =
       fun a b ->
        Checked_array.iter2 a b ~f:(fun a b ->
            Checked_array.iter2 a b ~f:(fun a b ->
                Field.Checked.Assert.equal a b ) )
    end

    (* Bonus: Try an adjust the Matrix definition above to functor over a
        monad, making mul monadic. Then instantiate the Field version with the
        identity monad, and the Field.Checked version with the Checked monad.
     *)
  end

  module Store_array = Array_iter (Typ_monads.Store)
  module Read_array = Array_iter (Typ_monads.Read)
  module Alloc_array = Array_iter (Typ_monads.Alloc)

  (* Create a [Typ.t] to let us convert between [Mat.t] and [Mat_checked.t].

     NB: SNARKs require fixed-size inputs, so this Typ.t will have to describe
     matrices of a fixed-size. Make sure that this size matches your
     [random_matrix]'s output size!
  *)
  let typ ~rows ~cols : (Mat_checked.t, Mat.t) Typ.t =
    { store=
        (fun mat ->
          assert (Array.length mat = rows) ;
          Store_array.init rows ~f:(fun i ->
              let row = mat.(i) in
              assert (Array.length row = cols) ;
              Store_array.init cols ~f:(fun j -> Typ.Store.store row.(j)) ) )
    ; read=
        (fun mat ->
          assert (Array.length mat = rows) ;
          Read_array.init rows ~f:(fun i ->
              let row = mat.(i) in
              assert (Array.length row = cols) ;
              Read_array.init cols ~f:(fun j -> Typ.Read.read row.(j)) ) )
    ; alloc=
        Alloc_array.init rows ~f:(fun _i ->
            Alloc_array.init cols ~f:(fun _j -> Typ.Alloc.alloc) )
    ; check= (fun _ -> Checked.return ()) }

  (* Fill in this function to check that [sqrt_x] squares to [x]. *)
  let assert_is_sqrt (x : Mat_checked.t) (sqrt_x : Mat_checked.t) =
    let%bind sqrt_x2 = Mat_checked.mul sqrt_x sqrt_x in
    Mat_checked.Assert.equal x sqrt_x2

  type _ Request.t += Get_matrix_sqrt : Mat.t Request.t

  (* Add a new kind of [Request.t] that asks for the square root matrix that we
     will generate later, and use [assert_is_sqrt] to check that it squares to
     the matrix we've been given. *)
  let assert_exists_sqrt ~length (x : Mat_checked.t) =
    let%bind sqrt_x =
      exists
        (typ ~rows:length ~cols:length)
        ~request:(As_prover.return Get_matrix_sqrt)
    in
    assert_is_sqrt x sqrt_x

  let input ~rows ~cols = Data_spec.[typ ~rows ~cols]

  let keypair ~length =
    generate_keypair
      ~exposing:(input ~rows:length ~cols:length)
      (assert_exists_sqrt ~length)

  (* Build a proof.
     This should consist of:
     * creating a random matrix (to use as our square root)
     * squaring this matrix, to work out what our public input should be
     * setting a handler for the [Request.t] that [assert_exists_sqrt] sends
     * creating a proof for [assert_exists_sqrt]

     NB: This function should return the public input and the proof, so that
     the input can be passed to the verifier.
  *)
  let proof ~length keypair : Mat.t * Proof.t =
    let sqrt_x = random_matrix ~rows:length ~cols:length in
    let x = Mat.mul sqrt_x sqrt_x in
    let assert_exists_sqrt x =
      handle (assert_exists_sqrt ~length x) (fun (With {request; respond}) ->
          match request with
          | Get_matrix_sqrt ->
              respond (Provide sqrt_x)
          | _ ->
              respond Unhandled )
    in
    let proof =
      prove (Keypair.pk keypair)
        (input ~rows:length ~cols:length)
        () assert_exists_sqrt x
    in
    (x, proof)

  (* Verify the proof. *)
  let is_valid ~length keypair proof (x : Mat.t) =
    verify proof (Keypair.vk keypair) (input ~rows:length ~cols:length) x

  let run ~length =
    let keypair = keypair ~length in
    let x, proof = proof ~length keypair in
    printf
      !"Does %{sexp: Mat.t} have a square root?\n%b%!"
      x
      (is_valid ~length keypair proof x)
end

(* Exercise 9: Comment this out when you're ready to test it! *)
let () = Exercise9.run ~length:5

(* TODO: To_bits of_bits *)
