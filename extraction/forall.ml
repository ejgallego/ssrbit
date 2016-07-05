open Format

exception TestFailure of int

let forall_int wordsize k =
  let upb = (1 lsl wordsize) - 1       in
  let upc = upb / 100                  in
  let rtm = ref (Unix.gettimeofday ()) in
  printf "Starting, upb: %d@\n%!" upb;

  try
    for i = 0 to upb do
      if (i mod upc) = 0 then
        begin
          printf "%3d %% done@\n%!" (i*100/upb + 1);
          let rtn = Unix.gettimeofday () in
          if i != 0 then
            printf "time remaining %d secs@\n%!" ((int_of_float (rtn -. !rtm)) * (upb-i) / upc);
          rtm := rtn
        end;
      if not (k i)       then raise (TestFailure i)
    done;
    true
  with
  | TestFailure i -> eprintf "failed at number %d\n%!" i;
    false
