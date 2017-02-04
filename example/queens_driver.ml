open Queens

let max = 16
let output = open_out "queens_coq.dat"

let solutions =
  (* counting from 1 *)
  [| 1 ; 0 ; 0 ; 2 ; 10 ; 4 ; 40 ; 92 ; 352 ; 724 ; 
     2680 ; 14200 ; 73712 ; 365596 ; 2279184 ; 14772512 ;
     95815104 ; 666090624 ; 4968057848 ; 39029188884 ; 
     314666222712 ; 2691008701644 ; 24233937684440 |]

let _ = 
  for i = 1 to max do
    let m = (module 
      struct
        let sizep = nat_of_int (i-1)
        let n = S sizep 
      end : BOARDSIZE)
    in
    let module M = (val m) in
    let time = Unix.gettimeofday() in
    let module Q = Extractor((M)) in
    let time = 1000. *. (Unix.gettimeofday() -. time) in
    Printf.printf "%d queens: %f ms.\n%!" i time;
    Printf.fprintf output "%d\t%f\n" i time;
    let solution = int_of_nat Q.nqueens in
    assert (solutions.(i-1) = solution)
  done
