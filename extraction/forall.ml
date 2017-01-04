open Format

exception TestFailure of int
exception TestFailure2 of int * int

(* let report *)

let forall_int wordsize test_f =
  let upb = (1 lsl wordsize) - 1       in
  let upc = upb / 20                   in
  let rtm = ref (Unix.gettimeofday ()) in
  printf "Starting, number of words: %d@\n%!" upb;

  try
    for i = 0 to upb do
      if (i mod upc) = 0 then
        begin
          let rtn = Unix.gettimeofday () in
          if i != 0 then
            let percent = i*100/upb + 1                             in
            let it_time = int_of_float ((rtn -. !rtm) *. 1000000.0) in
            let msecs   = it_time * (upb-i) / upc / 1000            in
            let secs    = msecs / 1000                              in
            printf "\r %3d %% done, time remaining %4d.%3d secs     (it_time: %8d ns)%!" percent secs msecs it_time;
          rtm := rtn
        end;
      if not (test_f i) then raise (TestFailure i)
    done;
    printf "@\n%!";
    true
  with
  | TestFailure i -> eprintf "failed at number %d\n%!" i;
    false

let forall_int2 wordsize test_f =
  let upb = (1 lsl wordsize) - 1         in
  let upc = upb / 100                    in
  let up_inner = upb / 20                in
  let rtm   = ref (Unix.gettimeofday ()) in
  printf "Starting, [upc: %d, up_inner:%d] number of words^2: %d@\n%!" upc up_inner upb;

  try
    for i = 0 to upb do
      if (i mod upc) = 0 then
        begin
          let rtn = Unix.gettimeofday () in
          if i != 0 then
            let percent = i*100/upb + 1                             in
            let it_time = int_of_float ((rtn -. !rtm) *. 1000000.0) in
            let msecs   = it_time * (upb-i) / upc / 1000            in
            let secs    = msecs / 1000                              in
            printf "\x1b[1A \r %3d %% done, time remaining %4d.%3d secs     (it_time: %8d ns)@\n%!" percent secs msecs it_time;
          rtm := rtn
        end;
      (* We do upc*upb loops thus j*i has to be: *)
      for j = 0 to upb do
        (* if ((i*j) mod (up_inner * upc)) = 0 then ( *)
        if (j mod up_inner) = 0 then (
          printf "\r  [Inner loop: %3d %% done]%!" (j*10/up_inner * (i mod upc))
        );
        if not (test_f i j) then raise (TestFailure2 (i, j))
      done;
    done;
    printf "@\n%!";
    true
  with
  | TestFailure2 (i,j) -> eprintf "failed at numbers %d, %d\n%!" i j;
    false
